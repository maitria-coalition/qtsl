import Mathlib

/-!
# The Poincaré–Miranda theorem

A self-contained proof by the combinatorial route: the discrete core is
a cubical Sperner lemma on the Freudenthal triangulation, followed by a
compactness passage to the continuous statement. (At the mathlib
version this development pins, no Brouwer fixed-point theorem,
topological degree, or simplicial Sperner machinery is available to
reduce to.)
-/

namespace PPLC
namespace Stair

open Finset

noncomputable section

open scoped Classical

theorem even_card_of_involutive {α : Type*} [DecidableEq α]
    (s : Finset α) (g : α → α)
    (hmem : ∀ a ∈ s, g a ∈ s) (hinv : ∀ a ∈ s, g (g a) = a)
    (hne : ∀ a ∈ s, g a ≠ a) : Even s.card := by
  suffices h : ∀ n (s : Finset α), s.card ≤ n →
      (∀ a ∈ s, g a ∈ s) → (∀ a ∈ s, g (g a) = a) →
      (∀ a ∈ s, g a ≠ a) → Even s.card from
    h s.card s le_rfl hmem hinv hne
  intro n
  induction n with
  | zero =>
    intro s hcard _ _ _
    have : s.card = 0 := by omega
    rw [this]
    exact ⟨0, rfl⟩
  | succ n ih =>
    intro s hcard hmem hinv hne
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨a, ha⟩
    · rw [Finset.card_empty]
      exact ⟨0, rfl⟩
    · have hga : g a ∈ s := hmem a ha
      have hgane : g a ≠ a := hne a ha
      have hsub : ({a, g a} : Finset α) ⊆ s := by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact ha
        · rcases Finset.mem_singleton.1 hx with rfl
          exact hga
      have hcardpair : ({a, g a} : Finset α).card = 2 :=
        Finset.card_pair (Ne.symm hgane)
      have hs2 : 2 ≤ s.card := by
        calc 2 = ({a, g a} : Finset α).card := hcardpair.symm
        _ ≤ s.card := Finset.card_le_card hsub
      have hcard' : (s \ {a, g a}).card = s.card - 2 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.2 hsub, hcardpair]
      have hmem' : ∀ b ∈ s \ {a, g a}, g b ∈ s \ {a, g a} := by
        intro b hb
        rw [Finset.mem_sdiff] at hb ⊢
        obtain ⟨hbs, hbne⟩ := hb
        refine ⟨hmem b hbs, fun hgb => hbne ?_⟩
        rcases Finset.mem_insert.1 hgb with hgb | hgb
        ·
          have hb_eq : b = g a := by
            have h1 := hinv b hbs
            rw [hgb] at h1
            exact h1.symm
          rw [hb_eq]
          exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton_self _))
        ·
          rcases Finset.mem_singleton.1 hgb with hgb
          have hb_eq : b = a := by
            have h1 := hinv b hbs
            have h2 := hinv a ha
            rw [hgb, h2] at h1
            exact h1.symm
          rw [hb_eq]
          exact Finset.mem_insert_self _ _
      have hev' : Even (s \ {a, g a}).card := by
        refine ih _ (by omega) hmem'
          (fun b hb => hinv b (Finset.mem_sdiff.1 hb).1)
          (fun b hb => hne b (Finset.mem_sdiff.1 hb).1)
      have hsplit : s.card = (s \ {a, g a}).card + 2 := by omega
      rw [hsplit]
      exact hev'.add ⟨1, rfl⟩

theorem card_modtwo_eq_fixed {α : Type*} [DecidableEq α]
    (s : Finset α) (g : α → α)
    (hmem : ∀ a ∈ s, g a ∈ s) (hinv : ∀ a ∈ s, g (g a) = a) :
    (s.card : ZMod 2) = ((s.filter fun a => g a = a).card : ZMod 2) := by
  have hsplit :
      (s.filter fun a => g a = a).card
        + (s.filter fun a => ¬ g a = a).card = s.card :=
    Finset.card_filter_add_card_filter_not _
  have hevenmoved : Even (s.filter fun a => ¬ g a = a).card := by
    apply even_card_of_involutive _ g
    · intro a hamem
      rw [Finset.mem_filter] at hamem ⊢
      obtain ⟨has, hane⟩ := hamem
      refine ⟨hmem a has, fun hgg => hane ?_⟩
      rw [hinv a has] at hgg
      exact hgg.symm
    · intro a hamem
      exact hinv a (Finset.mem_filter.1 hamem).1
    · intro a hamem
      exact (Finset.mem_filter.1 hamem).2
  obtain ⟨t, ht⟩ := hevenmoved
  have hcast : (s.card : ZMod 2)
      = ((s.filter fun a => g a = a).card : ZMod 2)
        + ((s.filter fun a => ¬ g a = a).card : ZMod 2) := by
    rw [← Nat.cast_add, hsplit]
  rw [hcast, ht]
  push_cast
  rw [CharTwo.add_self_eq_zero, add_zero]

theorem odd_iff_zmodtwo (n : ℕ) : Odd n ↔ (n : ZMod 2) = 1 := by
  rw [Nat.odd_iff, ← ZMod.natCast_mod n 2]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> decide

variable {m : ℕ}

abbrev ChainData (m k : ℕ) := (Fin m → ℕ) × (Fin k → Fin m)

variable {p k : ℕ}

def vtx (C : ChainData m k) (j : ℕ) : Fin m → ℕ :=
  fun i => C.1 i + (if ∃ t : Fin k, (t : ℕ) < j ∧ C.2 t = i then 1 else 0)

def Valid (p k : ℕ) (C : ChainData m k) : Prop :=
  Function.Injective C.2 ∧ (∀ t, (C.2 t : ℕ) < k) ∧
    (∀ i : Fin m, (i : ℕ) < k → C.1 i < p) ∧
    (∀ i : Fin m, k ≤ (i : ℕ) → C.1 i = p)

def InGrid (p k : ℕ) (x : Fin m → ℕ) : Prop :=
  (∀ i : Fin m, (i : ℕ) < k → x i ≤ p) ∧
    ∀ i : Fin m, k ≤ (i : ℕ) → x i = p

lemma vtx_zero (C : ChainData m k) : vtx C 0 = C.1 := by
  funext i; simp [vtx]

lemma vtx_le_succ_base (C : ChainData m k) (j : ℕ) (i : Fin m) :
    vtx C j i ≤ C.1 i + 1 := by
  unfold vtx; split <;> omega

lemma base_le_vtx (C : ChainData m k) (j : ℕ) (i : Fin m) :
    C.1 i ≤ vtx C j i := by
  unfold vtx; split <;> omega

lemma vtx_of_forall_ne (C : ChainData m k) (j : ℕ) (i : Fin m)
    (h : ∀ t : Fin k, C.2 t ≠ i) : vtx C j i = C.1 i := by
  unfold vtx
  rw [if_neg]; · omega
  rintro ⟨t, -, ht⟩; exact h t ht

lemma vtx_pinned (C : ChainData m k) (hC : Valid p k C) (j : ℕ)
    (i : Fin m) (hi : k ≤ (i : ℕ)) : vtx C j i = p := by
  rw [vtx_of_forall_ne]
  · exact hC.2.2.2 i hi
  · intro t ht
    have := hC.2.1 t
    rw [ht] at this
    omega

lemma inGrid_vtx (C : ChainData m k) (hC : Valid p k C) (j : ℕ) :
    InGrid p k (vtx C j) := by
  refine ⟨fun i hi => ?_, fun i hi => vtx_pinned C hC j i hi⟩
  have h1 := vtx_le_succ_base C j i
  have h2 := hC.2.2.1 i hi
  omega

lemma vtx_bumped (C : ChainData m k) {j : ℕ} {t : Fin k}
    (ht : (t : ℕ) < j) : vtx C j (C.2 t) = C.1 (C.2 t) + 1 := by
  unfold vtx
  rw [if_pos ⟨t, ht, rfl⟩]

lemma vtx_not_bumped (C : ChainData m k)
    (hinj : Function.Injective C.2) {j : ℕ} {t : Fin k}
    (ht : j ≤ (t : ℕ)) : vtx C j (C.2 t) = C.1 (C.2 t) := by
  unfold vtx
  rw [if_neg]; · omega
  rintro ⟨t', ht', hteq⟩
  cases hinj hteq
  omega

def Pan (k : ℕ) (L : (Fin m → ℕ) → ℕ) (C : ChainData m k) : Prop :=
  ∀ v ≤ k, ∃ j ≤ k, L (vtx C j) = v

def Door (k : ℕ) (L : (Fin m → ℕ) → ℕ) (C : ChainData m k) (j : ℕ) :
    Prop :=
  ∀ v < k, ∃ j' ≤ k, j' ≠ j ∧ L (vtx C j') = v

def chains (m p k : ℕ) : Finset (ChainData m k) :=
  ((Fintype.piFinset fun _ : Fin m => Finset.range (p + 1)) ×ˢ
      (Finset.univ : Finset (Fin k → Fin m))).filter (Valid p k)

lemma mem_chains {C : ChainData m k} :
    C ∈ chains m p k ↔ Valid p k C := by
  unfold chains
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩, h⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    rcases lt_or_ge (i : ℕ) k with hi | hi
    · have := h.2.2.1 i hi; omega
    · have := h.2.2.2 i hi; omega

def panChains (m p k : ℕ) (L : (Fin m → ℕ) → ℕ) :
    Finset (ChainData m k) :=
  (chains m p k).filter (Pan k L)

def doorPairs (m p k : ℕ) (L : (Fin m → ℕ) → ℕ) :
    Finset (ChainData m k × ℕ) :=
  (chains m p k).biUnion fun C =>
    (((Finset.range (k + 1)).filter (Door k L C)).image fun j => (C, j))

lemma mem_doorPairs {L : (Fin m → ℕ) → ℕ} {Cj : ChainData m k × ℕ} :
    Cj ∈ doorPairs m p k L ↔
      Valid p k Cj.1 ∧ Cj.2 ≤ k ∧ Door k L Cj.1 Cj.2 := by
  unfold doorPairs
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨C, hC, hmem⟩
    rw [Finset.mem_image] at hmem
    obtain ⟨j, hj, rfl⟩ := hmem
    rw [Finset.mem_filter, Finset.mem_range] at hj
    exact ⟨mem_chains.1 hC, by omega, hj.2⟩
  · rintro ⟨hval, hle, hdoor⟩
    refine ⟨Cj.1, mem_chains.2 hval, ?_⟩
    rw [Finset.mem_image]
    exact ⟨Cj.2, by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hdoor⟩, rfl⟩

lemma card_doorPairs (L : (Fin m → ℕ) → ℕ) :
    (doorPairs m p k L).card
      = ∑ C ∈ chains m p k,
          ((Finset.range (k + 1)).filter (Door k L C)).card := by
  unfold doorPairs
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun C _ => ?_
    apply Finset.card_image_of_injective
    intro a b hab
    exact (Prod.ext_iff.1 hab).2
  · intro C₁ h₁ C₂ h₂ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_image] at ha hb
    obtain ⟨j₁, -, rfl⟩ := ha
    obtain ⟨j₂, -, hEq⟩ := hb
    exact hne ((Prod.ext_iff.1 hEq).1.symm)

theorem doorCount_zmodtwo (C : ChainData m k) (hC : Valid p k C)
    (L : (Fin m → ℕ) → ℕ) (hL : ∀ x, InGrid p k x → L x ≤ k) :
    ((((Finset.range (k + 1)).filter (Door k L C)).card : ZMod 2))
      = if Pan k L C then 1 else 0 := by
  have hlbl : ∀ j, L (vtx C j) ≤ k := fun j => hL _ (inGrid_vtx C hC j)
  by_cases hpan : Pan k L C
  ·

    rw [if_pos hpan]
    have himeq :
        (Finset.range (k + 1)).image (fun j => L (vtx C j))
          = Finset.range (k + 1) := by
      apply Finset.Subset.antisymm
      · intro v hv
        rw [Finset.mem_image] at hv
        obtain ⟨j, -, rfl⟩ := hv
        rw [Finset.mem_range]
        have := hlbl j
        omega
      · intro v hv
        rw [Finset.mem_range] at hv
        obtain ⟨j, hjle, hjlbl⟩ := hpan v (by omega)
        rw [Finset.mem_image]
        exact ⟨j, Finset.mem_range.2 (by omega), hjlbl⟩
    have hinj : Set.InjOn (fun j => L (vtx C j))
        ↑(Finset.range (k + 1)) := by
      apply Finset.injOn_of_card_image_eq
      rw [himeq]
    obtain ⟨jk, hjkle, hjklbl⟩ := hpan k le_rfl
    have hdoors :
        (Finset.range (k + 1)).filter (Door k L C) = {jk} := by
      ext j
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hjmem, hdoor⟩
        rw [Finset.mem_range] at hjmem
        have hlblj : L (vtx C j) = k := by
          by_contra hne
          have hlt : L (vtx C j) < k := lt_of_le_of_ne (hlbl j) hne
          obtain ⟨j', hj'le, hj'ne, hj'lbl⟩ := hdoor _ hlt
          exact hj'ne (hinj (Finset.mem_coe.2 (Finset.mem_range.2
            (by omega))) (Finset.mem_coe.2 (Finset.mem_range.2
            (by omega)))
            (by show L (vtx C j') = L (vtx C j); rw [hj'lbl]))
        exact hinj (Finset.mem_coe.2 (Finset.mem_range.2 (by omega)))
          (Finset.mem_coe.2 (Finset.mem_range.2 (by omega)))
          (by show L (vtx C j) = L (vtx C jk); rw [hlblj, hjklbl])
      · rintro rfl
        refine ⟨Finset.mem_range.2 (by omega), fun v hv => ?_⟩
        obtain ⟨jv, hjvle, hjvlbl⟩ := hpan v (by omega)
        refine ⟨jv, hjvle, fun heq => ?_, hjvlbl⟩
        rw [heq, hjklbl] at hjvlbl
        omega
    rw [hdoors, Finset.card_singleton, Nat.cast_one]
  ·

    rw [if_neg hpan]
    by_cases hmiss : ∃ v, v < k ∧ ∀ j ≤ k, L (vtx C j) ≠ v
    · obtain ⟨v₀, hv₀lt, hv₀abs⟩ := hmiss
      have hdoors :
          (Finset.range (k + 1)).filter (Door k L C) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro j hj
        rw [Finset.mem_filter] at hj
        obtain ⟨j', hj'le, -, hj'lbl⟩ := hj.2 v₀ hv₀lt
        exact hv₀abs j' hj'le hj'lbl
      rw [hdoors, Finset.card_empty, Nat.cast_zero]
    · push Not at hmiss
      have hall : ∀ v < k, ∃ j ≤ k, L (vtx C j) = v := by
        intro v hv
        obtain ⟨j, hjle, hjlbl⟩ := hmiss v hv
        exact ⟨j, hjle, hjlbl⟩
      have habsk : ∀ j ≤ k, L (vtx C j) ≠ k := by
        intro j hjle hjlbl
        apply hpan
        intro v hvle
        rcases Nat.lt_or_ge v k with hvlt | hvge
        · exact hall v hvlt
        · have : v = k := by omega
          exact ⟨j, hjle, by rw [hjlbl, this]⟩
      have hlblt : ∀ j ≤ k, L (vtx C j) < k := by
        intro j hjle
        have h1 := hlbl j
        have h2 := habsk j hjle
        omega

      have hmapsto : ∀ j ∈ Finset.range (k + 1),
          L (vtx C j) ∈ Finset.range k := by
        intro j hj
        rw [Finset.mem_range] at hj ⊢
        exact hlblt j (by omega)
      obtain ⟨j₁, hj₁, j₂, hj₂, hj₁₂, hcoll⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to
          (by rw [Finset.card_range, Finset.card_range]; omega) hmapsto
      set F : ℕ → ℕ := fun v =>
        ((Finset.range (k + 1)).filter
          (fun j => L (vtx C j) = v)).card with hF
      set v₂ : ℕ := L (vtx C j₁) with hv₂
      have hv₂mem : v₂ ∈ Finset.range k := hmapsto j₁ hj₁
      have hk1 : 1 ≤ k := by
        rw [Finset.mem_range] at hv₂mem
        omega
      have hsum : ∑ v ∈ Finset.range k, F v = k + 1 := by
        have h := Finset.card_eq_sum_card_fiberwise hmapsto
        rw [Finset.card_range] at h
        exact h.symm
      have hpos : ∀ v ∈ Finset.range k, 1 ≤ F v := by
        intro v hv
        rw [Finset.mem_range] at hv
        obtain ⟨j, hjle, hjlbl⟩ := hall v hv
        rw [hF]
        apply Finset.card_pos.2
        exact ⟨j, Finset.mem_filter.2
          ⟨Finset.mem_range.2 (by omega), hjlbl⟩⟩
      have hF2 : 2 ≤ F v₂ := by
        rw [hF]
        calc 2 = ({j₁, j₂} : Finset ℕ).card :=
              (Finset.card_pair hj₁₂).symm
        _ ≤ _ := by
              apply Finset.card_le_card
              intro j hj
              rcases Finset.mem_insert.1 hj with rfl | hj
              · exact Finset.mem_filter.2 ⟨hj₁, rfl⟩
              · rcases Finset.mem_singleton.1 hj with rfl
                exact Finset.mem_filter.2 ⟨hj₂, hcoll.symm⟩

      have herase_sum :
          ∑ v ∈ (Finset.range k).erase v₂, F v + F v₂ = k + 1 := by
        rw [Finset.sum_erase_add _ _ hv₂mem]
        exact hsum
      have herase_ge :
          ((Finset.range k).erase v₂).card
            ≤ ∑ v ∈ (Finset.range k).erase v₂, F v := by
        calc ((Finset.range k).erase v₂).card
            = ∑ _v ∈ (Finset.range k).erase v₂, 1 := by
              rw [Finset.card_eq_sum_ones]
        _ ≤ _ := Finset.sum_le_sum fun v hv =>
              hpos v (Finset.mem_of_mem_erase hv)
      have herase_card :
          ((Finset.range k).erase v₂).card = k - 1 := by
        rw [Finset.card_erase_of_mem hv₂mem, Finset.card_range]
      have hF2eq : F v₂ = 2 := by omega
      have hFone : ∀ v ∈ (Finset.range k).erase v₂, F v = 1 := by
        intro v₀ hv₀
        by_contra hne
        have h2 : 2 ≤ F v₀ := by
          have := hpos v₀ (Finset.mem_of_mem_erase hv₀)
          omega
        have hsplit :
            ∑ v ∈ ((Finset.range k).erase v₂).erase v₀, F v + F v₀
              = ∑ v ∈ (Finset.range k).erase v₂, F v :=
          Finset.sum_erase_add _ _ hv₀
        have hge2 :
            (((Finset.range k).erase v₂).erase v₀).card
              ≤ ∑ v ∈ ((Finset.range k).erase v₂).erase v₀, F v := by
          calc ((((Finset.range k).erase v₂).erase v₀)).card
              = ∑ _v ∈ (((Finset.range k).erase v₂).erase v₀), 1 := by
                rw [Finset.card_eq_sum_ones]
          _ ≤ _ := Finset.sum_le_sum fun v hv =>
                hpos v (Finset.mem_of_mem_erase
                  (Finset.mem_of_mem_erase hv))
        have hcard2 :
            (((Finset.range k).erase v₂).erase v₀).card = k - 2 := by
          rw [Finset.card_erase_of_mem hv₀, herase_card]
          omega
        omega

      have hdoors :
          (Finset.range (k + 1)).filter (Door k L C)
            = (Finset.range (k + 1)).filter
                (fun j => L (vtx C j) = v₂) := by
        ext j
        rw [Finset.mem_filter, Finset.mem_filter]
        constructor
        · rintro ⟨hjmem, hdoor⟩
          refine ⟨hjmem, ?_⟩
          rw [Finset.mem_range] at hjmem
          have hvlt : L (vtx C j) < k := hlblt j (by omega)
          obtain ⟨j', hj'le, hj'ne, hj'lbl⟩ := hdoor _ hvlt
          by_contra hnev₂
          have hmemv : L (vtx C j) ∈ (Finset.range k).erase v₂ :=
            Finset.mem_erase.2 ⟨hnev₂, Finset.mem_range.2 hvlt⟩
          have hone := hFone _ hmemv
          have h2 : 2 ≤ F (L (vtx C j)) := by
            rw [hF]
            calc 2 = ({j, j'} : Finset ℕ).card := by
                  rw [Finset.card_pair (fun h => hj'ne h.symm)]
            _ ≤ _ := by
                  apply Finset.card_le_card
                  intro a ha
                  rcases Finset.mem_insert.1 ha with rfl | ha
                  · exact Finset.mem_filter.2
                      ⟨Finset.mem_range.2 (by omega), rfl⟩
                  · rcases Finset.mem_singleton.1 ha with rfl
                    exact Finset.mem_filter.2
                      ⟨Finset.mem_range.2 (by omega), hj'lbl⟩
          omega
        · rintro ⟨hjmem, hjlbl⟩
          refine ⟨hjmem, fun v hv => ?_⟩
          by_cases hvv₂ : v = v₂
          · subst hvv₂
            have hpair : ∃ j' ∈ (Finset.range (k + 1)).filter
                (fun j'' => L (vtx C j'') = v₂), j' ≠ j := by
              by_contra hno
              push Not at hno
              have hsub : (Finset.range (k + 1)).filter
                  (fun j'' => L (vtx C j'') = v₂) ⊆ {j} := by
                intro a hamem
                rw [Finset.mem_singleton]
                exact hno a hamem
              have hle := Finset.card_le_card hsub
              rw [Finset.card_singleton] at hle
              have h2 : ((Finset.range (k + 1)).filter
                  (fun j'' => L (vtx C j'') = v₂)).card = 2 := by
                have h3 := hF2eq
                rw [hF] at h3
                exact h3
              omega
            obtain ⟨j', hj'mem, hj'ne⟩ := hpair
            rw [Finset.mem_filter, Finset.mem_range] at hj'mem
            exact ⟨j', by omega, hj'ne, hj'mem.2⟩
          · obtain ⟨jv, hjvle, hjvlbl⟩ := hall v hv
            refine ⟨jv, hjvle, fun heq => ?_, hjvlbl⟩
            rw [heq, hjlbl] at hjvlbl
            exact hvv₂ hjvlbl.symm
      rw [hdoors]
      have : ((Finset.range (k + 1)).filter
          (fun j => L (vtx C j) = v₂)).card = 2 := by
        rw [hF] at hF2eq
        exact hF2eq
      rw [this]
      decide

section Pivot

variable {K : ℕ}

def bumpAt (α : Fin m) (b : Fin m → ℕ) : Fin m → ℕ :=
  fun i => if i = α then b i + 1 else b i

def unbumpAt (α : Fin m) (b : Fin m → ℕ) : Fin m → ℕ :=
  fun i => if i = α then b i - 1 else b i

lemma unbumpAt_bumpAt (α : Fin m) (b : Fin m → ℕ) :
    unbumpAt α (bumpAt α b) = b := by
  funext i
  unfold unbumpAt bumpAt
  by_cases h : i = α <;> simp [h]

lemma bumpAt_unbumpAt (α : Fin m) (b : Fin m → ℕ) (hb : 1 ≤ b α) :
    bumpAt α (unbumpAt α b) = b := by
  funext i
  unfold unbumpAt bumpAt
  by_cases h : i = α
  · subst h; simp; omega
  · simp [h]

lemma bumpAt_apply_self (α : Fin m) (b : Fin m → ℕ) :
    bumpAt α b α = b α + 1 := by simp [bumpAt]

lemma bumpAt_apply_ne (α : Fin m) (b : Fin m → ℕ) {i : Fin m}
    (h : i ≠ α) : bumpAt α b i = b i := by simp [bumpAt, h]

lemma unbumpAt_apply_self (α : Fin m) (b : Fin m → ℕ) :
    unbumpAt α b α = b α - 1 := by simp [unbumpAt]

lemma unbumpAt_apply_ne (α : Fin m) (b : Fin m → ℕ) {i : Fin m}
    (h : i ≠ α) : unbumpAt α b i = b i := by simp [unbumpAt, h]

def appendMove (C : ChainData m (K + 1)) : ChainData m (K + 1) :=
  (bumpAt (C.2 0) C.1, C.2 ∘ (· + 1))

def prependMove (C : ChainData m (K + 1)) : ChainData m (K + 1) :=
  (unbumpAt (C.2 (Fin.last K)) C.1, C.2 ∘ (· - 1))

lemma prependMove_appendMove (C : ChainData m (K + 1)) :
    prependMove (appendMove C) = C := by
  unfold prependMove appendMove
  refine Prod.ext ?_ ?_
  · show unbumpAt ((C.2 ∘ (· + 1)) (Fin.last K)) (bumpAt (C.2 0) C.1)
      = C.1
    have h : (C.2 ∘ (· + 1)) (Fin.last K) = C.2 0 := by
      simp [Function.comp, Fin.last_add_one]
    rw [h, unbumpAt_bumpAt]
  · show (C.2 ∘ (· + 1)) ∘ (· - 1) = C.2
    funext t
    simp [Function.comp, sub_add_cancel]

lemma appendMove_prependMove (C : ChainData m (K + 1))
    (hb : 1 ≤ C.1 (C.2 (Fin.last K))) :
    appendMove (prependMove C) = C := by
  unfold prependMove appendMove
  have h0 : (C.2 ∘ (· - 1)) 0 = C.2 (Fin.last K) := by
    have : (0 : Fin (K + 1)) - 1 = Fin.last K := by
      rw [← Fin.last_add_one (n := K)]
      exact add_sub_cancel_right _ _
    simp [Function.comp, this]
  refine Prod.ext ?_ ?_
  · show bumpAt ((C.2 ∘ (· - 1)) 0) (unbumpAt (C.2 (Fin.last K)) C.1)
      = C.1
    rw [h0, bumpAt_unbumpAt _ _ hb]
  · show (C.2 ∘ (· - 1)) ∘ (· + 1) = C.2
    funext t
    simp [Function.comp, add_sub_cancel_right]

lemma valid_appendMove {C : ChainData m (K + 1)}
    (hC : Valid p (K + 1) C) (hguard : C.1 (C.2 0) + 2 ≤ p) :
    Valid p (K + 1) (appendMove C) := by
  obtain ⟨hinj, hrange, hroom, hpin⟩ := hC
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hshift : Function.Injective
        (fun t : Fin (K + 1) => t + 1) := by
      intro a b hab
      have h := congrArg (fun t : Fin (K + 1) => t - 1) hab
      simpa only [add_sub_cancel_right] using h
    exact hinj.comp hshift
  · intro t; exact hrange _
  · intro i hi
    by_cases hiα : i = C.2 0
    · subst hiα
      show bumpAt (C.2 0) C.1 (C.2 0) < p
      rw [bumpAt_apply_self]
      omega
    · show bumpAt (C.2 0) C.1 i < p
      rw [bumpAt_apply_ne _ _ hiα]
      exact hroom i hi
  · intro i hi
    have hiα : i ≠ C.2 0 := by
      intro h
      have := hrange 0
      rw [← h] at this
      omega
    show bumpAt (C.2 0) C.1 i = p
    rw [bumpAt_apply_ne _ _ hiα]
    exact hpin i hi

lemma valid_prependMove {C : ChainData m (K + 1)}
    (hC : Valid p (K + 1) C) : Valid p (K + 1) (prependMove C) := by
  obtain ⟨hinj, hrange, hroom, hpin⟩ := hC
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hshift : Function.Injective
        (fun t : Fin (K + 1) => t - 1) := by
      intro a b hab
      have h := congrArg (fun t : Fin (K + 1) => t + 1) hab
      simpa only [sub_add_cancel] using h
    exact hinj.comp hshift
  · intro t; exact hrange _
  · intro i hi
    by_cases hiα : i = C.2 (Fin.last K)
    · subst hiα
      rw [show (prependMove C).1 (C.2 (Fin.last K))
          = unbumpAt (C.2 (Fin.last K)) C.1 (C.2 (Fin.last K)) from rfl,
        unbumpAt_apply_self]
      have := hroom _ hi
      omega
    · rw [show (prependMove C).1 i
          = unbumpAt (C.2 (Fin.last K)) C.1 i from rfl,
        unbumpAt_apply_ne _ _ hiα]
      exact hroom i hi
  · intro i hi
    have hiα : i ≠ C.2 (Fin.last K) := by
      intro h
      have := hrange (Fin.last K)
      rw [← h] at this
      omega
    rw [show (prependMove C).1 i
        = unbumpAt (C.2 (Fin.last K)) C.1 i from rfl,
      unbumpAt_apply_ne _ _ hiα]
    exact hpin i hi

lemma vtx_appendMove {C : ChainData m (K + 1)}
    (hC : Valid p (K + 1) C) {j : ℕ} (hj : j ≤ K) :
    vtx (appendMove C) j = vtx C (j + 1) := by
  obtain ⟨hinj, hrange, -, -⟩ := hC
  funext i
  show bumpAt (C.2 0) C.1 i
      + (if ∃ t : Fin (K + 1), (t : ℕ) < j ∧ C.2 (t + 1) = i then 1
          else 0)
    = C.1 i
      + (if ∃ t : Fin (K + 1), (t : ℕ) < j + 1 ∧ C.2 t = i then 1
          else 0)
  by_cases hiα : i = C.2 0
  · subst hiα
    rw [bumpAt_apply_self]
    have hno : ¬ ∃ t : Fin (K + 1), (t : ℕ) < j ∧ C.2 (t + 1) = C.2 0 := by
      rintro ⟨t, htlt, hteq⟩
      have h01 : t + 1 = 0 := hinj hteq
      have hval : ((t + 1 : Fin (K + 1)) : ℕ) = (t : ℕ) + 1 := by
        apply Fin.val_add_one_of_lt
        rw [Fin.lt_def, Fin.val_last]
        omega
      rw [h01] at hval
      simp at hval
    have hyes : ∃ t : Fin (K + 1), (t : ℕ) < j + 1 ∧ C.2 t = C.2 0 :=
      ⟨0, by simp only [Fin.val_zero]; omega, rfl⟩
    rw [if_neg hno, if_pos hyes]
  · rw [bumpAt_apply_ne _ _ hiα]
    congr 1
    apply if_congr _ rfl rfl
    constructor
    · rintro ⟨t, htlt, hteq⟩
      refine ⟨t + 1, ?_, hteq⟩

      have hval : ((t + 1 : Fin (K + 1)) : ℕ) = (t : ℕ) + 1 := by
        apply Fin.val_add_one_of_lt
        rw [Fin.lt_def, Fin.val_last]
        omega
      omega
    · rintro ⟨t, htlt, hteq⟩
      have ht0 : t ≠ 0 := by
        intro h
        rw [h] at hteq
        exact hiα hteq.symm
      refine ⟨t - 1, ?_, ?_⟩
      · have hval : ((t - 1 : Fin (K + 1)) : ℕ) = (t : ℕ) - 1 := by
          rw [Fin.coe_sub_one, if_neg ht0]
        have htpos : 0 < (t : ℕ) := by
          rcases Nat.eq_zero_or_pos (t : ℕ) with h | h
          · exact absurd (Fin.ext h) ht0
          · exact h
        omega
      · rw [sub_add_cancel]
        exact hteq

lemma vtx_prependMove {C : ChainData m (K + 1)}
    (hC : Valid p (K + 1) C) (hb : 1 ≤ C.1 (C.2 (Fin.last K)))
    {j : ℕ} (hj : j ≤ K) :
    vtx (prependMove C) (j + 1) = vtx C j := by
  have happ : appendMove (prependMove C) = C :=
    appendMove_prependMove C hb
  have hval : Valid p (K + 1) (prependMove C) := valid_prependMove hC
  have := vtx_appendMove (C := prependMove C) hval hj
  rw [happ] at this
  exact this.symm

lemma vtx_midSwap {C : ChainData m (K + 1)} {jd : ℕ}
    (hjd1 : 1 ≤ jd) (hjdK : jd ≤ K) {j : ℕ} (hne : j ≠ jd) :
    vtx (C.1, C.2 ∘ (Equiv.swap (⟨jd - 1, by omega⟩ : Fin (K + 1))
        ⟨jd, by omega⟩)) j = vtx C j := by
  set a : Fin (K + 1) := ⟨jd - 1, by omega⟩ with ha
  set b : Fin (K + 1) := ⟨jd, by omega⟩ with hb
  funext i
  show C.1 i + (if ∃ t : Fin (K + 1), (t : ℕ) < j
      ∧ C.2 (Equiv.swap a b t) = i then 1 else 0) = _
  congr 1
  apply if_congr _ rfl rfl
  have hswapval : ∀ t : Fin (K + 1), (t : ℕ) < j ↔
      ((Equiv.swap a b t : Fin (K + 1)) : ℕ) < j := by
    intro t
    by_cases hta : t = a
    · subst hta
      rw [Equiv.swap_apply_left]
      show ((a : ℕ) < j ↔ (b : ℕ) < j)
      rw [ha, hb]
      show (jd - 1 < j ↔ jd < j)
      omega
    · by_cases htb : t = b
      · subst htb
        rw [Equiv.swap_apply_right]
        show ((b : ℕ) < j ↔ (a : ℕ) < j)
        rw [ha, hb]
        show (jd < j ↔ jd - 1 < j)
        omega
      · rw [Equiv.swap_apply_of_ne_of_ne hta htb]
  constructor
  · rintro ⟨t, htlt, hteq⟩
    exact ⟨Equiv.swap a b t, ((hswapval t).1 htlt), hteq⟩
  · rintro ⟨t, htlt, hteq⟩
    refine ⟨Equiv.swap a b t, ?_, ?_⟩
    · have := (hswapval (Equiv.swap a b t)).2
      rw [Equiv.swap_apply_self] at this
      exact this htlt
    · rw [Equiv.swap_apply_self]
      exact hteq

lemma door_appendMove {L : (Fin m → ℕ) → ℕ} {C : ChainData m (K + 1)}
    (hC : Valid p (K + 1) C) (hdoor : Door (K + 1) L C 0) :
    Door (K + 1) L (appendMove C) (K + 1) := by
  intro v hv
  obtain ⟨j', hj'le, hj'ne, hj'lbl⟩ := hdoor v hv
  refine ⟨j' - 1, by omega, by omega, ?_⟩
  rw [vtx_appendMove hC (by omega : j' - 1 ≤ K),
    show j' - 1 + 1 = j' by omega]
  exact hj'lbl

lemma door_prependMove {L : (Fin m → ℕ) → ℕ} {C : ChainData m (K + 1)}
    (hC : Valid p (K + 1) C) (hb : 1 ≤ C.1 (C.2 (Fin.last K)))
    (hdoor : Door (K + 1) L C (K + 1)) :
    Door (K + 1) L (prependMove C) 0 := by
  intro v hv
  obtain ⟨j', hj'le, hj'ne, hj'lbl⟩ := hdoor v hv
  refine ⟨j' + 1, by omega, by omega, ?_⟩
  rw [vtx_prependMove hC hb (by omega : j' ≤ K)]
  exact hj'lbl

lemma door_midSwap {L : (Fin m → ℕ) → ℕ} {C : ChainData m (K + 1)}
    {jd : ℕ} (hjd1 : 1 ≤ jd) (hjdK : jd ≤ K)
    (hdoor : Door (K + 1) L C jd) :
    Door (K + 1) L
      (C.1, C.2 ∘ (Equiv.swap (⟨jd - 1, by omega⟩ : Fin (K + 1))
        ⟨jd, by omega⟩)) jd := by
  intro v hv
  obtain ⟨j', hj'le, hj'ne, hj'lbl⟩ := hdoor v hv
  refine ⟨j', hj'le, hj'ne, ?_⟩
  rw [vtx_midSwap hjd1 hjdK hj'ne]
  exact hj'lbl

lemma door_top_base_pos {L : (Fin m → ℕ) → ℕ}
    {C : ChainData m (K + 1)} (hC : Valid p (K + 1) C)
    (hA : ∀ x, InGrid p (K + 1) x → ∀ i : Fin m, (i : ℕ) < K + 1 →
      x i = 0 → L x ≠ (i : ℕ))
    (hdoor : Door (K + 1) L C (K + 1)) :
    1 ≤ C.1 (C.2 (Fin.last K)) := by
  by_contra hb
  push Not at hb
  have hb0 : C.1 (C.2 (Fin.last K)) = 0 := by omega
  obtain ⟨j', hj'le, hj'ne, hj'lbl⟩ :=
    hdoor ((C.2 (Fin.last K)) : ℕ) (hC.2.1 (Fin.last K))
  have hfacet : vtx C j' (C.2 (Fin.last K)) = 0 := by
    rw [vtx_not_bumped C hC.1 (by rw [Fin.val_last]; omega), hb0]
  exact hA (vtx C j') (inGrid_vtx C hC j') (C.2 (Fin.last K))
    (hC.2.1 (Fin.last K)) hfacet hj'lbl

lemma door_zero_top_coord {L : (Fin m → ℕ) → ℕ}
    {C : ChainData m (K + 1)} (hC : Valid p (K + 1) C)
    (hB : ∀ x, InGrid p (K + 1) x → ∀ i : Fin m, (i : ℕ) < K + 1 →
      x i = p → L x ≤ (i : ℕ))
    (hdoor : Door (K + 1) L C 0)
    (hfix : C.1 (C.2 0) + 1 = p) :
    ((C.2 0 : Fin m) : ℕ) = K := by
  by_contra hne
  have hlt : ((C.2 0 : Fin m) : ℕ) < K := by
    have := hC.2.1 0
    omega
  obtain ⟨j', hj'le, hj'ne, hj'lbl⟩ := hdoor K (by omega)
  have hfacet : vtx C j' (C.2 0) = p := by
    rw [vtx_bumped C
      (by simp only [Fin.val_zero]; omega : ((0 : Fin (K + 1)) : ℕ) < j')]
    omega
  have := hB (vtx C j') (inGrid_vtx C hC j') (C.2 0)
    (hC.2.1 0) hfacet
  rw [hj'lbl] at this
  omega

def pivot (p K : ℕ) (Cj : ChainData m (K + 1) × ℕ) :
    ChainData m (K + 1) × ℕ :=
  if Cj.2 = 0 then
    (if Cj.1.1 (Cj.1.2 0) + 2 ≤ p then (appendMove Cj.1, K + 1)
      else Cj)
  else if Cj.2 = K + 1 then (prependMove Cj.1, 0)
  else if h : 1 ≤ Cj.2 ∧ Cj.2 ≤ K then
    ((Cj.1.1, Cj.1.2 ∘ (Equiv.swap
      (⟨Cj.2 - 1, by omega⟩ : Fin (K + 1)) ⟨Cj.2, by omega⟩)), Cj.2)
  else Cj

lemma pivot_zero_matched {C : ChainData m (K + 1)}
    (hg : C.1 (C.2 0) + 2 ≤ p) :
    pivot p K (C, 0) = (appendMove C, K + 1) := by
  simp [pivot, hg]

lemma pivot_zero_unmatched {C : ChainData m (K + 1)}
    (hg : ¬ C.1 (C.2 0) + 2 ≤ p) :
    pivot p K (C, 0) = (C, 0) := by
  simp [pivot, hg]

lemma pivot_top {C : ChainData m (K + 1)} :
    pivot p K (C, K + 1) = (prependMove C, 0) := by
  simp [pivot]

lemma pivot_mid {C : ChainData m (K + 1)} {j : ℕ} (h1 : 1 ≤ j)
    (h2 : j ≤ K) :
    pivot p K (C, j) = ((C.1, C.2 ∘ (Equiv.swap
      (⟨j - 1, by omega⟩ : Fin (K + 1)) ⟨j, by omega⟩)), j) := by
  have hj0 : ¬ (j = 0) := by omega
  have hjt : ¬ (j = K + 1) := by omega
  simp [pivot, hj0, hjt, h1, h2]

variable {L : (Fin m → ℕ) → ℕ}

lemma pivot_mem (_hp : 0 < p)
    (hA : ∀ x, InGrid p (K + 1) x → ∀ i : Fin m, (i : ℕ) < K + 1 →
      x i = 0 → L x ≠ (i : ℕ)) :
    ∀ Cj ∈ doorPairs m p (K + 1) L,
      pivot p K Cj ∈ doorPairs m p (K + 1) L := by
  rintro ⟨C, j⟩ hmem
  rw [mem_doorPairs] at hmem
  obtain ⟨hval, hjle, hdoor⟩ := hmem
  dsimp only at hval hjle hdoor
  by_cases hj0 : j = 0
  · subst hj0
    by_cases hg : C.1 (C.2 0) + 2 ≤ p
    · rw [pivot_zero_matched hg, mem_doorPairs]
      exact ⟨valid_appendMove hval hg, le_rfl,
        door_appendMove hval hdoor⟩
    · rw [pivot_zero_unmatched hg, mem_doorPairs]
      exact ⟨hval, by omega, hdoor⟩
  · by_cases hjK1 : j = K + 1
    · subst hjK1
      rw [pivot_top, mem_doorPairs]
      have hb := door_top_base_pos hval hA hdoor
      exact ⟨valid_prependMove hval, by omega,
        door_prependMove hval hb hdoor⟩
    · have h1 : 1 ≤ j := by omega
      have h2 : j ≤ K := by omega
      rw [pivot_mid h1 h2, mem_doorPairs]
      refine ⟨?_, by omega, door_midSwap h1 h2 hdoor⟩
      obtain ⟨hinj, hrange, hroom, hpin⟩ := hval
      exact ⟨hinj.comp (Equiv.injective _), fun t => hrange _,
        hroom, hpin⟩

lemma pivot_invol (_hp : 0 < p)
    (hA : ∀ x, InGrid p (K + 1) x → ∀ i : Fin m, (i : ℕ) < K + 1 →
      x i = 0 → L x ≠ (i : ℕ)) :
    ∀ Cj ∈ doorPairs m p (K + 1) L, pivot p K (pivot p K Cj) = Cj := by
  rintro ⟨C, j⟩ hmem
  rw [mem_doorPairs] at hmem
  obtain ⟨hval, hjle, hdoor⟩ := hmem
  dsimp only at hval hjle hdoor
  by_cases hj0 : j = 0
  · subst hj0
    by_cases hg : C.1 (C.2 0) + 2 ≤ p
    · rw [pivot_zero_matched hg, pivot_top, prependMove_appendMove]
    · rw [pivot_zero_unmatched hg, pivot_zero_unmatched hg]
  · by_cases hjK1 : j = K + 1
    · subst hjK1
      have hb := door_top_base_pos hval hA hdoor
      rw [pivot_top]
      have hα : (prependMove C).2 0 = C.2 (Fin.last K) := by
        show (C.2 ∘ (· - 1)) 0 = C.2 (Fin.last K)
        have hz : (0 : Fin (K + 1)) - 1 = Fin.last K := by
          rw [← Fin.last_add_one (n := K)]
          exact add_sub_cancel_right _ _
        simp only [Function.comp_apply, hz]
      have hg2 : (prependMove C).1 ((prependMove C).2 0) + 2 ≤ p := by
        rw [hα]
        have hbase : (prependMove C).1 (C.2 (Fin.last K))
            = C.1 (C.2 (Fin.last K)) - 1 := unbumpAt_apply_self _ _
        rw [hbase]
        have hroom := hval.2.2.1 (C.2 (Fin.last K))
          (hval.2.1 (Fin.last K))
        omega
      rw [pivot_zero_matched hg2, appendMove_prependMove C hb]
    · have h1 : 1 ≤ j := by omega
      have h2 : j ≤ K := by omega
      rw [pivot_mid h1 h2, pivot_mid h1 h2]
      refine Prod.ext (Prod.ext rfl ?_) rfl
      show (C.2 ∘ _) ∘ _ = C.2
      funext t
      simp [Function.comp, Equiv.swap_apply_self]

lemma pivot_fixed_iff (_hp : 0 < p) {Cj : ChainData m (K + 1) × ℕ}
    (hmem : Cj ∈ doorPairs m p (K + 1) L) :
    pivot p K Cj = Cj ↔ Cj.2 = 0 ∧ Cj.1.1 (Cj.1.2 0) + 1 = p := by
  rw [mem_doorPairs] at hmem
  obtain ⟨C, j⟩ := Cj
  obtain ⟨hval, hjle, hdoor⟩ := hmem
  dsimp only at hval hjle hdoor ⊢
  constructor
  · intro hfix
    by_cases hj0 : j = 0
    · subst hj0
      refine ⟨rfl, ?_⟩
      by_cases hg : C.1 (C.2 0) + 2 ≤ p
      · exfalso
        rw [pivot_zero_matched hg] at hfix
        have h2 : K + 1 = 0 := congrArg Prod.snd hfix
        omega
      · have hroom := hval.2.2.1 (C.2 0) (hval.2.1 0)
        omega
    · exfalso
      by_cases hjK1 : j = K + 1
      · subst hjK1
        rw [pivot_top] at hfix
        have h2 : 0 = K + 1 := congrArg Prod.snd hfix
        omega
      · have h1 : 1 ≤ j := by omega
        have h2 : j ≤ K := by omega
        rw [pivot_mid h1 h2] at hfix
        have hord : C.2 ∘ (Equiv.swap
            (⟨j - 1, by omega⟩ : Fin (K + 1)) ⟨j, by omega⟩) = C.2 :=
          congrArg (fun Cj => Cj.1.2) hfix
        have happ := congrArg
          (fun σ => σ (⟨j - 1, by omega⟩ : Fin (K + 1))) hord
        simp only [Function.comp_apply, Equiv.swap_apply_left] at happ
        have heq := hval.1 happ
        have hvals : j = j - 1 := congrArg Fin.val heq
        omega
  · rintro ⟨hj0, hfixval⟩
    subst hj0
    have hg : ¬ C.1 (C.2 0) + 2 ≤ p := by omega
    exact pivot_zero_unmatched hg

def toFacet (C : ChainData m (K + 1)) : ChainData m K :=
  (bumpAt (C.2 0) C.1, fun t : Fin K => C.2 t.succ)

def fromFacet (hKm : K < m) (D : ChainData m K) : ChainData m (K + 1) :=
  (unbumpAt ⟨K, hKm⟩ D.1, Fin.cases ⟨K, hKm⟩ D.2)

lemma fromFacet_ord_zero (hKm : K < m) (D : ChainData m K) :
    (fromFacet hKm D).2 0 = ⟨K, hKm⟩ := by
  show (Fin.cases ⟨K, hKm⟩ D.2 : Fin (K + 1) → Fin m) 0 = ⟨K, hKm⟩
  exact Fin.cases_zero

lemma fromFacet_ord_succ (hKm : K < m) (D : ChainData m K)
    (t : Fin K) : (fromFacet hKm D).2 t.succ = D.2 t := by
  show (Fin.cases ⟨K, hKm⟩ D.2 : Fin (K + 1) → Fin m) t.succ = D.2 t
  exact Fin.cases_succ t

lemma vtx_toFacet {C : ChainData m (K + 1)} (hC : Valid p (K + 1) C)
    {j : ℕ} (_hj : j ≤ K) : vtx (toFacet C) j = vtx C (j + 1) := by
  obtain ⟨hinj, hrange, -, -⟩ := hC
  funext i
  show bumpAt (C.2 0) C.1 i
      + (if ∃ t : Fin K, (t : ℕ) < j ∧ C.2 t.succ = i then 1 else 0)
    = C.1 i
      + (if ∃ t : Fin (K + 1), (t : ℕ) < j + 1 ∧ C.2 t = i then 1
          else 0)
  by_cases hiα : i = C.2 0
  · subst hiα
    rw [bumpAt_apply_self]
    have hno : ¬ ∃ t : Fin K, (t : ℕ) < j ∧ C.2 t.succ = C.2 0 := by
      rintro ⟨t, htlt, hteq⟩
      exact Fin.succ_ne_zero t (hinj hteq)
    have hyes : ∃ t : Fin (K + 1), (t : ℕ) < j + 1 ∧ C.2 t = C.2 0 :=
      ⟨0, by simp only [Fin.val_zero]; omega, rfl⟩
    rw [if_neg hno, if_pos hyes]
  · rw [bumpAt_apply_ne _ _ hiα]
    congr 1
    apply if_congr _ rfl rfl
    constructor
    · rintro ⟨t, htlt, hteq⟩
      exact ⟨t.succ, by rw [Fin.val_succ]; omega, hteq⟩
    · rintro ⟨t, htlt, hteq⟩
      have ht0 : t ≠ 0 := by
        intro h
        rw [h] at hteq
        exact hiα hteq.symm
      obtain ⟨u, rfl⟩ := Fin.eq_succ_of_ne_zero ht0
      refine ⟨u, ?_, hteq⟩
      rw [Fin.val_succ] at htlt
      omega

lemma toFacet_fromFacet (hp : 0 < p) (hKm : K < m)
    {D : ChainData m K} (hD : Valid p K D) :
    toFacet (fromFacet hKm D) = D := by
  have hpinK : D.1 ⟨K, hKm⟩ = p := hD.2.2.2 ⟨K, hKm⟩ le_rfl
  refine Prod.ext ?_ ?_
  · show bumpAt ((fromFacet hKm D).2 0) (unbumpAt ⟨K, hKm⟩ D.1) = D.1
    rw [fromFacet_ord_zero]
    apply bumpAt_unbumpAt
    omega
  · show (fun t : Fin K => (fromFacet hKm D).2 t.succ) = D.2
    funext t
    exact fromFacet_ord_succ hKm D t

lemma valid_fromFacet (hp : 0 < p) (hKm : K < m)
    {D : ChainData m K} (hD : Valid p K D) :
    Valid p (K + 1) (fromFacet hKm D) := by
  obtain ⟨hinj, hrange, hroom, hpin⟩ := hD
  have hpinK : D.1 ⟨K, hKm⟩ = p := hpin ⟨K, hKm⟩ le_rfl
  have h00 : (fromFacet hKm D).2 0 = ⟨K, hKm⟩ := fromFacet_ord_zero hKm D
  have hsucc : ∀ t : Fin K, (fromFacet hKm D).2 t.succ = D.2 t :=
    fun t => fromFacet_ord_succ hKm D t
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
    · rfl
    · exfalso
      have h3 : (⟨K, hKm⟩ : Fin m) = D.2 b' :=
        (h00.symm).trans (hab.trans (hsucc b'))
      have hv : K = ((D.2 b' : Fin m) : ℕ) := congrArg Fin.val h3
      have := hrange b'
      omega
    · exfalso
      have h3 : (⟨K, hKm⟩ : Fin m) = D.2 a' :=
        (h00.symm).trans (hab.symm.trans (hsucc a'))
      have hv : K = ((D.2 a' : Fin m) : ℕ) := congrArg Fin.val h3
      have := hrange a'
      omega
    · have h3 : D.2 a' = D.2 b' :=
        ((hsucc a').symm).trans (hab.trans (hsucc b'))
      rw [hinj h3]
  · intro t
    rcases Fin.eq_zero_or_eq_succ t with rfl | ⟨t', rfl⟩
    · show ((fromFacet hKm D).2 0 : ℕ) < K + 1
      rw [h00]
      exact Nat.lt_succ_self K
    · show ((fromFacet hKm D).2 t'.succ : ℕ) < K + 1
      rw [hsucc t']
      exact Nat.lt_succ_of_lt (hrange t')
  · intro i hi
    by_cases hiK : i = ⟨K, hKm⟩
    · subst hiK
      show unbumpAt ⟨K, hKm⟩ D.1 ⟨K, hKm⟩ < p
      rw [unbumpAt_apply_self, hpinK]
      omega
    · show unbumpAt ⟨K, hKm⟩ D.1 i < p
      rw [unbumpAt_apply_ne _ _ hiK]
      apply hroom
      have : (i : ℕ) ≠ K := fun h => hiK (Fin.ext h)
      omega
  · intro i hi
    have hiK : i ≠ ⟨K, hKm⟩ := by
      intro h
      subst h
      have h2 : K + 1 ≤ K := hi
      omega
    show unbumpAt ⟨K, hKm⟩ D.1 i = p
    rw [unbumpAt_apply_ne _ _ hiK]
    exact hpin i (by omega)

theorem card_fixedDoors (hp : 0 < p) (hKm : K < m)
    (_hA : ∀ x, InGrid p (K + 1) x → ∀ i : Fin m, (i : ℕ) < K + 1 →
      x i = 0 → L x ≠ (i : ℕ))
    (hB : ∀ x, InGrid p (K + 1) x → ∀ i : Fin m, (i : ℕ) < K + 1 →
      x i = p → L x ≤ (i : ℕ)) :
    ((doorPairs m p (K + 1) L).filter
        fun Cj => pivot p K Cj = Cj).card
      = (panChains m p K L).card := by
  apply Finset.card_bij (fun Cj _ => toFacet Cj.1)
  ·
    rintro ⟨C, j⟩ hmem
    rw [Finset.mem_filter] at hmem
    obtain ⟨hdmem, hfix⟩ := hmem
    have hfixc := (pivot_fixed_iff hp hdmem).1 hfix
    rw [mem_doorPairs] at hdmem
    obtain ⟨hval, hjle, hdoor⟩ := hdmem
    have hj0 : j = 0 := hfixc.1
    subst hj0
    have hval' : Valid p (K + 1) C := hval
    have hdoor' : Door (K + 1) L C 0 := hdoor
    have hfixval : C.1 (C.2 0) + 1 = p := hfixc.2
    have htop : ((C.2 0 : Fin m) : ℕ) = K :=
      door_zero_top_coord hval' hB hdoor' hfixval
    rw [panChains, Finset.mem_filter, mem_chains]
    obtain ⟨hinj, hrange, hroom, hpin⟩ := hval'
    constructor
    ·
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro a b hab
        have := hinj hab
        exact Fin.succ_injective _ this
      · intro t
        show ((C.2 t.succ : Fin m) : ℕ) < K
        have h1 := hrange t.succ
        have hne : C.2 t.succ ≠ C.2 0 := fun h =>
          Fin.succ_ne_zero t (hinj h)
        have hvalne : ((C.2 t.succ : Fin m) : ℕ) ≠ K := fun h =>
          hne (Fin.ext (h.trans htop.symm))
        omega
      · intro i hi
        show bumpAt (C.2 0) C.1 i < p
        have hine : i ≠ C.2 0 := by
          intro h
          rw [h, htop] at hi
          omega
        rw [bumpAt_apply_ne _ _ hine]
        exact hroom i (by omega)
      · intro i hi
        show bumpAt (C.2 0) C.1 i = p
        by_cases hiα : i = C.2 0
        · subst hiα
          rw [bumpAt_apply_self]
          exact hfixval
        · rw [bumpAt_apply_ne _ _ hiα]
          apply hpin
          have : (i : ℕ) ≠ K := fun h => hiα (Fin.ext (h.trans htop.symm))
          omega
    ·
      intro v hv
      obtain ⟨j', hj'le, hj'ne, hj'lbl⟩ := hdoor' v (by omega)
      refine ⟨j' - 1, by omega, ?_⟩
      rw [vtx_toFacet hval (by omega : j' - 1 ≤ K),
        show j' - 1 + 1 = j' by omega]
      exact hj'lbl
  ·
    rintro ⟨C₁, j₁⟩ hmem₁ ⟨C₂, j₂⟩ hmem₂ heq
    rw [Finset.mem_filter] at hmem₁ hmem₂
    have hfix₁ := (pivot_fixed_iff hp hmem₁.1).1 hmem₁.2
    have hfix₂ := (pivot_fixed_iff hp hmem₂.1).1 hmem₂.2
    rw [mem_doorPairs] at hmem₁ hmem₂
    obtain ⟨hval₁, -, hdoor₁⟩ := hmem₁.1
    obtain ⟨hval₂, -, hdoor₂⟩ := hmem₂.1
    have hj₁ : j₁ = 0 := hfix₁.1
    have hj₂ : j₂ = 0 := hfix₂.1
    subst hj₁
    subst hj₂
    have hval₁' : Valid p (K + 1) C₁ := hval₁
    have hval₂' : Valid p (K + 1) C₂ := hval₂
    have hdoor₁' : Door (K + 1) L C₁ 0 := hdoor₁
    have hdoor₂' : Door (K + 1) L C₂ 0 := hdoor₂
    have hfv₁ : C₁.1 (C₁.2 0) + 1 = p := hfix₁.2
    have hfv₂ : C₂.1 (C₂.2 0) + 1 = p := hfix₂.2
    have htop₁ : ((C₁.2 0 : Fin m) : ℕ) = K :=
      door_zero_top_coord hval₁' hB hdoor₁' hfv₁
    have htop₂ : ((C₂.2 0 : Fin m) : ℕ) = K :=
      door_zero_top_coord hval₂' hB hdoor₂' hfv₂
    have hα : C₁.2 0 = C₂.2 0 := Fin.ext (by rw [htop₁, htop₂])
    have hbase : bumpAt (C₁.2 0) C₁.1 = bumpAt (C₂.2 0) C₂.1 :=
      congrArg Prod.fst heq
    have hord : (fun t : Fin K => C₁.2 t.succ)
        = (fun t : Fin K => C₂.2 t.succ) :=
      congrArg Prod.snd heq
    have hbase' : C₁.1 = C₂.1 := by
      funext i
      by_cases hiα : i = C₁.2 0
      · subst hiα
        have h1 : bumpAt (C₁.2 0) C₁.1 (C₁.2 0)
            = bumpAt (C₂.2 0) C₂.1 (C₁.2 0) :=
          congrArg (fun b => b (C₁.2 0)) hbase
        rw [bumpAt_apply_self, hα, bumpAt_apply_self] at h1
        have h2 : C₁.1 (C₁.2 0) = C₂.1 (C₂.2 0) := by omega
        rw [h2, hα]
      · have h1 : bumpAt (C₁.2 0) C₁.1 i
            = bumpAt (C₂.2 0) C₂.1 i :=
          congrArg (fun b => b i) hbase
        rw [bumpAt_apply_ne _ _ hiα,
          bumpAt_apply_ne _ _ (fun h => hiα (h.trans hα.symm))] at h1
        exact h1
    have hord' : C₁.2 = C₂.2 := by
      funext s
      rcases Fin.eq_zero_or_eq_succ s with rfl | ⟨t, rfl⟩
      · exact hα
      · exact congrArg (fun σ => σ t) hord
    exact Prod.ext (Prod.ext hbase' hord') rfl
  ·
    intro D hD
    rw [panChains, Finset.mem_filter, mem_chains] at hD
    obtain ⟨hval, hpan⟩ := hD
    refine ⟨(fromFacet hKm D, 0), ?_, toFacet_fromFacet hp hKm hval⟩
    have hvalC := valid_fromFacet hp hKm hval
    have hpinKD : D.1 ⟨K, hKm⟩ = p := hval.2.2.2 ⟨K, hKm⟩ le_rfl
    have hbase0 : (fromFacet hKm D).1 ((fromFacet hKm D).2 0) + 1
        = p := by
      have h0 : (fromFacet hKm D).1 ((fromFacet hKm D).2 0)
          = D.1 ⟨K, hKm⟩ - 1 := by
        rw [fromFacet_ord_zero]
        show unbumpAt ⟨K, hKm⟩ D.1 ⟨K, hKm⟩ = D.1 ⟨K, hKm⟩ - 1
        exact unbumpAt_apply_self _ _
      rw [h0]
      omega
    have hdoor : Door (K + 1) L (fromFacet hKm D) 0 := by
      intro v hv
      obtain ⟨j'', hj''le, hj''lbl⟩ := hpan v (by omega)
      refine ⟨j'' + 1, by omega, by omega, ?_⟩
      have hcorr : vtx (fromFacet hKm D) (j'' + 1) = vtx D j'' := by
        have h1 := vtx_toFacet (C := fromFacet hKm D) hvalC
          (j := j'') (by omega)
        rw [toFacet_fromFacet hp hKm hval] at h1
        exact h1.symm
      rw [hcorr]
      exact hj''lbl
    rw [Finset.mem_filter, mem_doorPairs]
    refine ⟨⟨hvalC, by omega, hdoor⟩, ?_⟩
    have hg : ¬ (fromFacet hKm D).1 ((fromFacet hKm D).2 0) + 2 ≤ p := by
      omega
    exact pivot_zero_unmatched hg

theorem stair_parity (m : ℕ) :
    ∀ k ≤ m, 0 < p → ∀ L : (Fin m → ℕ) → ℕ,
    (∀ x, InGrid p k x → L x ≤ k) →
    (∀ x, InGrid p k x → ∀ i : Fin m, (i : ℕ) < k → x i = 0 →
      L x ≠ (i : ℕ)) →
    (∀ x, InGrid p k x → ∀ i : Fin m, (i : ℕ) < k → x i = p →
      L x ≤ (i : ℕ)) →
    ((panChains m p k L).card : ZMod 2) = 1 := by
  intro k
  induction k with
  | zero =>
    intro hkm hp L hL hA hB
    have hsingle : panChains m p 0 L
        = {((fun _ => p : Fin m → ℕ), Fin.elim0)} := by
      unfold panChains
      ext C
      rw [Finset.mem_filter, mem_chains, Finset.mem_singleton]
      constructor
      · rintro ⟨hval, -⟩
        refine Prod.ext ?_ ?_
        · funext i
          exact hval.2.2.2 i (by omega)
        · funext t
          exact t.elim0
      · rintro rfl
        have hgrid : InGrid p 0 (fun _ : Fin m => p) :=
          ⟨fun i hi => by omega, fun i _ => rfl⟩
        refine ⟨⟨by intro a b hab; exact a.elim0,
          by intro t; exact t.elim0,
          by intro i hi; omega, fun i _ => rfl⟩, ?_⟩
        intro v hv
        refine ⟨0, le_rfl, ?_⟩
        rw [vtx_zero]
        show L (fun _ : Fin m => p) = v
        have := hL _ hgrid
        omega
    rw [hsingle, Finset.card_singleton, Nat.cast_one]
  | succ K ih =>
    intro hkm hp L hL hA hB

    have hgrid_up : ∀ x : Fin m → ℕ, InGrid p K x →
        InGrid p (K + 1) x := by
      rintro x ⟨hbnd, hpin⟩
      refine ⟨fun i hi => ?_, fun i hi => hpin i (by omega)⟩
      rcases Nat.lt_or_ge (i : ℕ) K with h | h
      · exact hbnd i h
      · rw [hpin i h]
    have hKm : K < m := by omega
    have hL_K : ∀ x, InGrid p K x → L x ≤ K := by
      intro x hx
      have hxK : x ⟨K, hKm⟩ = p := hx.2 ⟨K, hKm⟩ le_rfl
      have h := hB x (hgrid_up x hx) ⟨K, hKm⟩
        (Nat.lt_succ_self K) hxK
      exact h
    have hA_K : ∀ x, InGrid p K x → ∀ i : Fin m, (i : ℕ) < K →
        x i = 0 → L x ≠ (i : ℕ) := fun x hx i hi =>
      hA x (hgrid_up x hx) i (by omega)
    have hB_K : ∀ x, InGrid p K x → ∀ i : Fin m, (i : ℕ) < K →
        x i = p → L x ≤ (i : ℕ) := fun x hx i hi =>
      hB x (hgrid_up x hx) i (by omega)

    have hstep1 : ((panChains m p (K + 1) L).card : ZMod 2)
        = ((doorPairs m p (K + 1) L).card : ZMod 2) := by
      have h1 : ((panChains m p (K + 1) L).card : ZMod 2)
          = ∑ C ∈ chains m p (K + 1),
              (if Pan (K + 1) L C then (1 : ZMod 2) else 0) := by
        rw [Finset.sum_boole]
        rfl
      have h2 : ∀ C ∈ chains m p (K + 1),
          (if Pan (K + 1) L C then (1 : ZMod 2) else 0)
            = ((((Finset.range (K + 1 + 1)).filter
                (Door (K + 1) L C)).card : ZMod 2)) :=
        fun C hC => (doorCount_zmodtwo C (mem_chains.1 hC) L hL).symm
      rw [h1, Finset.sum_congr rfl h2, card_doorPairs, Nat.cast_sum]

    have hstep2 : ((doorPairs m p (K + 1) L).card : ZMod 2)
        = (((doorPairs m p (K + 1) L).filter
            fun Cj => pivot p K Cj = Cj).card : ZMod 2) :=
      card_modtwo_eq_fixed _ _ (pivot_mem hp hA) (pivot_invol hp hA)

    have hstep3 := card_fixedDoors hp hKm hA hB (L := L)

    have hstep4 := ih (by omega) hp L hL_K hA_K hB_K
    rw [hstep1, hstep2, hstep3, hstep4]

theorem exists_pan_chain (hp : 0 < p) (L : (Fin m → ℕ) → ℕ)
    (hL : ∀ x, InGrid p m x → L x ≤ m)
    (hA : ∀ x, InGrid p m x → ∀ i : Fin m, (i : ℕ) < m → x i = 0 →
      L x ≠ (i : ℕ))
    (hB : ∀ x, InGrid p m x → ∀ i : Fin m, (i : ℕ) < m → x i = p →
      L x ≤ (i : ℕ)) :
    ∃ C : ChainData m m, Valid p m C ∧ Pan m L C := by
  have h := stair_parity (p := p) m m le_rfl hp L hL hA hB
  by_contra hno
  push Not at hno
  have hempty : panChains m p m L = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro C hC
    unfold panChains at hC
    rw [Finset.mem_filter, mem_chains] at hC
    exact hno C hC.1 hC.2
  rw [hempty] at h
  simp only [Finset.card_empty, Nat.cast_zero] at h
  exact zero_ne_one h

end Pivot

section Decode

variable {p : ℕ}

def minLabel (ℓ : (Fin m → ℕ) → Fin m → Prop) (x : Fin m → ℕ) : ℕ :=
  if h : (Finset.univ.filter fun i : Fin m => ℓ x i).Nonempty then
    (((Finset.univ.filter fun i : Fin m => ℓ x i).min' h : Fin m) : ℕ)
  else m

lemma minLabel_le (ℓ : (Fin m → ℕ) → Fin m → Prop) (x : Fin m → ℕ) :
    minLabel ℓ x ≤ m := by
  unfold minLabel
  split
  · exact le_of_lt (Fin.is_lt _)
  · exact le_rfl

lemma minLabel_of_holds {ℓ : (Fin m → ℕ) → Fin m → Prop}
    {x : Fin m → ℕ} {i : Fin m} (h : ℓ x i) :
    minLabel ℓ x ≤ (i : ℕ) := by
  have hi : i ∈ Finset.univ.filter fun i : Fin m => ℓ x i :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
  have hne : (Finset.univ.filter fun i : Fin m => ℓ x i).Nonempty :=
    ⟨i, hi⟩
  unfold minLabel
  rw [dif_pos hne]
  exact Finset.min'_le _ _ hi

lemma minLabel_ne_of_not_holds {ℓ : (Fin m → ℕ) → Fin m → Prop}
    {x : Fin m → ℕ} {i : Fin m} (h : ¬ ℓ x i) :
    minLabel ℓ x ≠ (i : ℕ) := by
  intro heq
  unfold minLabel at heq
  split at heq
  · next hne =>
    have hmem := Finset.min'_mem
      (Finset.univ.filter fun i : Fin m => ℓ x i) hne
    rw [Finset.mem_filter] at hmem
    have : (Finset.univ.filter fun i : Fin m => ℓ x i).min' hne = i :=
      Fin.ext heq
    rw [this] at hmem
    exact h hmem.2
  · have := i.is_lt
    omega

lemma all_not_holds_of_minLabel_eq {ℓ : (Fin m → ℕ) → Fin m → Prop}
    {x : Fin m → ℕ} (h : minLabel ℓ x = m) :
    ∀ i : Fin m, ¬ ℓ x i := by
  intro i hi
  have h1 := minLabel_of_holds hi
  have h2 := i.is_lt
  omega

lemma holds_of_minLabel_eq_coord {ℓ : (Fin m → ℕ) → Fin m → Prop}
    {x : Fin m → ℕ} {i : Fin m} (h : minLabel ℓ x = (i : ℕ)) :
    ℓ x i := by
  by_contra hn
  exact minLabel_ne_of_not_holds hn h

theorem kuhn_cell (hp : 0 < p) (ℓ : (Fin m → ℕ) → Fin m → Prop)
    (hlo : ∀ x, (∀ i, x i ≤ p) → ∀ i, x i = 0 → ¬ ℓ x i)
    (hhi : ∀ x, (∀ i, x i ≤ p) → ∀ i, x i = p → ℓ x i) :
    ∃ q : Fin m → ℕ, (∀ i, q i + 1 ≤ p) ∧
      (∃ r, (∀ i', q i' ≤ r i' ∧ r i' ≤ q i' + 1) ∧ ∀ i, ¬ ℓ r i) ∧
      (∀ i, ∃ s, (∀ i', q i' ≤ s i' ∧ s i' ≤ q i' + 1) ∧ ℓ s i) := by
  have hbounds : ∀ x : Fin m → ℕ, InGrid p m x → ∀ i, x i ≤ p :=
    fun x hx i => hx.1 i i.is_lt
  obtain ⟨C, hval, hpan⟩ := exists_pan_chain hp (minLabel ℓ)
    (fun x _ => minLabel_le ℓ x)
    (fun x hx i _ hxi =>
      minLabel_ne_of_not_holds (hlo x (hbounds x hx) i hxi))
    (fun x hx i _ hxi =>
      minLabel_of_holds (hhi x (hbounds x hx) i hxi))
  refine ⟨C.1, fun i => hval.2.2.1 i i.is_lt, ?_, ?_⟩
  · obtain ⟨jz, hjzle, hjzlbl⟩ := hpan m le_rfl
    refine ⟨vtx C jz, fun i' =>
      ⟨base_le_vtx C jz i', vtx_le_succ_base C jz i'⟩,
      all_not_holds_of_minLabel_eq hjzlbl⟩
  · intro i
    obtain ⟨ji, hjile, hjilbl⟩ := hpan (i : ℕ) (le_of_lt i.is_lt)
    exact ⟨vtx C ji, fun i' =>
      ⟨base_le_vtx C ji i', vtx_le_succ_base C ji i'⟩,
      holds_of_minLabel_eq_coord hjilbl⟩

end Decode

section Analytic

open Filter Topology

theorem miranda_unitCube {m : ℕ} (g : (Fin m → ℝ) → (Fin m → ℝ))
    (hg : ContinuousOn g (Set.Icc 0 1))
    (hlo : ∀ i, ∀ w ∈ Set.Icc (0 : Fin m → ℝ) 1, w i = 0 → g w i ≤ 0)
    (hhi : ∀ i, ∀ w ∈ Set.Icc (0 : Fin m → ℝ) 1, w i = 1 →
      0 ≤ g w i) :
    ∃ w ∈ Set.Icc (0 : Fin m → ℝ) 1, g w = 0 := by

  set sc : ℕ → (Fin m → ℕ) → (Fin m → ℝ) :=
    fun n x i => (x i : ℝ) / ((n : ℝ) + 1) with hsc
  have hden : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hscmem : ∀ n (x : Fin m → ℕ), (∀ i, x i ≤ n + 1) →
      sc n x ∈ Set.Icc (0 : Fin m → ℝ) 1 := by
    intro n x hx
    rw [Set.mem_Icc]
    constructor
    · intro i
      show (0 : ℝ) ≤ (x i : ℝ) / ((n : ℝ) + 1)
      positivity
    · intro i
      show (x i : ℝ) / ((n : ℝ) + 1) ≤ 1
      rw [div_le_one (hden n)]
      exact_mod_cast hx i

  set lab : ℕ → (Fin m → ℕ) → Fin m → Prop :=
    fun n x i =>
      0 < g (sc n x) i + (1 / ((n : ℝ) + 1)) * sc n x i with hlab
  have hlo' : ∀ n, ∀ x : Fin m → ℕ, (∀ i, x i ≤ n + 1) →
      ∀ i, x i = 0 → ¬ lab n x i := by
    intro n x hx i hxi
    have hsc0 : sc n x i = 0 := by
      show ((x i : ℝ)) / _ = 0
      rw [hxi]
      simp
    rw [hlab]
    simp only [hsc0, mul_zero, add_zero, not_lt]
    exact hlo i (sc n x) (hscmem n x hx) hsc0
  have hhi' : ∀ n, ∀ x : Fin m → ℕ, (∀ i, x i ≤ n + 1) →
      ∀ i, x i = n + 1 → lab n x i := by
    intro n x hx i hxi
    have hsc1 : sc n x i = 1 := by
      show ((x i : ℝ)) / _ = 1
      rw [hxi]
      push_cast
      exact div_self (ne_of_gt (hden n))
    rw [hlab]
    have h1 := hhi i (sc n x) (hscmem n x hx) hsc1
    have h2 : (0 : ℝ) < (1 / ((n : ℝ) + 1)) * sc n x i := by
      rw [hsc1, mul_one]
      positivity
    linarith

  have hcells := fun n : ℕ =>
    kuhn_cell (p := n + 1) (by omega) (lab n) (hlo' n) (hhi' n)
  choose q hqbnd hrpart hspart using hcells
  choose r hrcell hrfalse using hrpart
  choose s hscell hstrue using hspart

  have hqmem : ∀ n, sc n (q n) ∈ Set.Icc (0 : Fin m → ℝ) 1 := by
    intro n
    apply hscmem
    intro i
    have := hqbnd n i
    omega
  obtain ⟨w, hwmem, φ, hφmono, hφtend⟩ :=
    (isCompact_Icc (a := (0 : Fin m → ℝ)) (b := 1)).tendsto_subseq
      hqmem

  have hinvtend : Tendsto (fun t : ℕ => 1 / ((φ t : ℝ) + 1)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact h1.comp hφmono.tendsto_atTop
  have cell_tendsto : ∀ y : ℕ → (Fin m → ℕ),
      (∀ t i', q (φ t) i' ≤ y t i' ∧ y t i' ≤ q (φ t) i' + 1) →
      Tendsto (fun t => sc (φ t) (y t)) atTop (𝓝 w) := by
    intro y hy
    rw [tendsto_pi_nhds]
    intro i'
    have hqcoord : Tendsto (fun t => sc (φ t) (q (φ t)) i') atTop
        (𝓝 (w i')) := by
      have := hφtend
      rw [tendsto_pi_nhds] at this
      exact this i'
    have hdiff : Tendsto
        (fun t => sc (φ t) (y t) i' - sc (φ t) (q (φ t)) i') atTop
        (𝓝 0) := by
      apply squeeze_zero
      · intro t
        show (0 : ℝ) ≤ (y t i' : ℝ) / _ - (q (φ t) i' : ℝ) / _
        rw [div_sub_div_same]
        apply div_nonneg _ (le_of_lt (hden (φ t)))
        rw [sub_nonneg]
        exact_mod_cast (hy t i').1
      · intro t
        show (y t i' : ℝ) / _ - (q (φ t) i' : ℝ) / _
            ≤ 1 / ((φ t : ℝ) + 1)
        rw [div_sub_div_same]
        have h1 : (y t i' : ℝ) - (q (φ t) i' : ℝ) ≤ 1 := by
          have h2 : (y t i' : ℝ) ≤ (q (φ t) i' : ℝ) + 1 := by
            exact_mod_cast (hy t i').2
          linarith
        gcongr
      · exact hinvtend
    have hsum := hdiff.add hqcoord
    rw [zero_add] at hsum
    have heq : (fun t => (sc (φ t) (y t) i'
        - sc (φ t) (q (φ t)) i') + sc (φ t) (q (φ t)) i')
        = fun t => sc (φ t) (y t) i' := by
      funext t
      ring
    rw [heq] at hsum
    exact hsum

  have hzero : ∀ i, g w i = 0 := by
    intro i

    have hrtend : Tendsto (fun t => sc (φ t) (r (φ t))) atTop (𝓝 w) :=
      cell_tendsto (fun t => r (φ t)) (fun t => hrcell (φ t))
    have hrmem : ∀ t, sc (φ t) (r (φ t)) ∈
        Set.Icc (0 : Fin m → ℝ) 1 := by
      intro t
      apply hscmem
      intro i'
      have h1 := (hrcell (φ t) i').2
      have h2 := hqbnd (φ t) i'
      omega
    have hgrtend : Tendsto (fun t => g (sc (φ t) (r (φ t)))) atTop
        (𝓝 (g w)) := by
      have hwithin : Tendsto (fun t => sc (φ t) (r (φ t))) atTop
          (𝓝[Set.Icc (0 : Fin m → ℝ) 1] w) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
          _ hrtend (Eventually.of_forall hrmem)
      exact Filter.Tendsto.comp (hg w hwmem) hwithin
    have hgle : ∀ t, g (sc (φ t) (r (φ t))) i ≤ 0 := by
      intro t
      have hfalse := hrfalse (φ t) i
      rw [hlab] at hfalse
      push Not at hfalse
      have hnn : (0 : ℝ) ≤ (1 / ((φ t : ℝ) + 1))
          * sc (φ t) (r (φ t)) i := by
        apply mul_nonneg
        · positivity
        · exact ((hrmem t).1 i : (0:ℝ) ≤ _)
      linarith
    have hle : g w i ≤ 0 := by
      have hcoord : Tendsto (fun t => g (sc (φ t) (r (φ t))) i) atTop
          (𝓝 (g w i)) := by
        have := hgrtend
        rw [tendsto_pi_nhds] at this
        exact this i
      exact le_of_tendsto hcoord (Eventually.of_forall hgle)

    have hstend : Tendsto (fun t => sc (φ t) (s (φ t) i)) atTop
        (𝓝 w) :=
      cell_tendsto (fun t => s (φ t) i) (fun t => hscell (φ t) i)
    have hsmem : ∀ t, sc (φ t) (s (φ t) i) ∈
        Set.Icc (0 : Fin m → ℝ) 1 := by
      intro t
      apply hscmem
      intro i'
      have h1 := (hscell (φ t) i i').2
      have h2 := hqbnd (φ t) i'
      omega
    have hgstend : Tendsto (fun t => g (sc (φ t) (s (φ t) i)) i) atTop
        (𝓝 (g w i)) := by
      have hwithin : Tendsto (fun t => sc (φ t) (s (φ t) i)) atTop
          (𝓝[Set.Icc (0 : Fin m → ℝ) 1] w) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
          _ hstend (Eventually.of_forall hsmem)
      have hcomp : Tendsto (fun t => g (sc (φ t) (s (φ t) i))) atTop
          (𝓝 (g w)) := Filter.Tendsto.comp (hg w hwmem) hwithin
      rw [tendsto_pi_nhds] at hcomp
      exact hcomp i
    have hgs : ∀ t, -(1 / ((φ t : ℝ) + 1))
        ≤ g (sc (φ t) (s (φ t) i)) i := by
      intro t
      have htrue := hstrue (φ t) i
      rw [hlab] at htrue
      have hub : (1 / ((φ t : ℝ) + 1)) * sc (φ t) (s (φ t) i) i
          ≤ 1 / ((φ t : ℝ) + 1) := by
        have hle1 : sc (φ t) (s (φ t) i) i ≤ 1 := (hsmem t).2 i
        have hpos : (0 : ℝ) < 1 / ((φ t : ℝ) + 1) := by positivity
        calc (1 / ((φ t : ℝ) + 1)) * sc (φ t) (s (φ t) i) i
            ≤ (1 / ((φ t : ℝ) + 1)) * 1 :=
              mul_le_mul_of_nonneg_left hle1 (le_of_lt hpos)
        _ = 1 / ((φ t : ℝ) + 1) := mul_one _
      linarith
    have hge : 0 ≤ g w i := by
      have hnegtend : Tendsto (fun t : ℕ => -(1 / ((φ t : ℝ) + 1)))
          atTop (𝓝 0) := by
        have := hinvtend.neg
        rw [neg_zero] at this
        exact this
      exact le_of_tendsto_of_tendsto' hnegtend hgstend hgs
    linarith
  exact ⟨w, hwmem, funext fun i => by rw [hzero i]; rfl⟩

/-- **Poincaré–Miranda.** A map continuous on a box whose `i`-th component
is nonpositive on the lower `i`-face and nonnegative on the upper
`i`-face has a zero in the box. -/
theorem poincare_miranda_box {m : ℕ} {a b : Fin m → ℝ}
    (hab : ∀ i, a i ≤ b i) (g : (Fin m → ℝ) → (Fin m → ℝ))
    (hg : ContinuousOn g (Set.Icc a b))
    (hlo : ∀ i, ∀ w ∈ Set.Icc a b, w i = a i → g w i ≤ 0)
    (hhi : ∀ i, ∀ w ∈ Set.Icc a b, w i = b i → 0 ≤ g w i) :
    ∃ w ∈ Set.Icc a b, g w = 0 := by
  set h : (Fin m → ℝ) → (Fin m → ℝ) :=
    fun t i => a i + t i * (b i - a i) with hh
  have hcont : Continuous h := by
    apply continuous_pi
    intro i
    exact continuous_const.add ((continuous_apply i).mul
      continuous_const)
  have hmaps : Set.MapsTo h (Set.Icc 0 1) (Set.Icc a b) := by
    intro t ht
    rw [Set.mem_Icc] at ht ⊢
    constructor
    · intro i
      show a i ≤ a i + t i * (b i - a i)
      have h1 : (0 : ℝ) ≤ t i := ht.1 i
      have h2 : (0 : ℝ) ≤ b i - a i := sub_nonneg.2 (hab i)
      nlinarith
    · intro i
      show a i + t i * (b i - a i) ≤ b i
      have h1 : t i ≤ 1 := ht.2 i
      have h2 : (0 : ℝ) ≤ b i - a i := sub_nonneg.2 (hab i)
      nlinarith
  obtain ⟨t, htmem, htzero⟩ :=
    miranda_unitCube (fun t => g (h t))
      (hg.comp hcont.continuousOn hmaps)
      (fun i t htmem hti => by
        have hhti : h t i = a i := by
          show a i + t i * (b i - a i) = a i
          rw [hti]; ring
        exact hlo i (h t) (hmaps htmem) hhti)
      (fun i t htmem hti => by
        have hhti : h t i = b i := by
          show a i + t i * (b i - a i) = b i
          rw [hti]; ring
        exact hhi i (h t) (hmaps htmem) hhti)
  exact ⟨h t, hmaps htmem, htzero⟩

end Analytic

end

end Stair
end PPLC
