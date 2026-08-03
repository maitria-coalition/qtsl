import Qtsl.OrderAssembly
import Mathlib.Data.Fintype.Lattice

/-!
# The eventual-member construction

Assigns to each orbit the minimal lattice member containing a forward
tail, shows it join-irreducible, and brackets every visited cell
between the forward member and its backward twin — the orbit-interval
conclusion of the Morse decomposition's interval lemma, run entirely on
the join-irreducible index of the cell order.
-/

namespace PPLC
namespace Qtsl
namespace Semiflow

open scoped NNReal
open Set

variable {X : Type*}

theorem CompleteOrbit.forward_mem {φ : Semiflow X} {γ : ℝ → X}
    {N : Set X} (horb : φ.CompleteOrbit γ) (hN : φ.Invariant N)
    {s t : ℝ} (hst : s ≤ t) (hs : γ s ∈ N) : γ t ∈ N := by
  have hrepr : s + ((t - s).toNNReal : ℝ) = t := by
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hst)]; ring
  have h := horb s (t - s).toNNReal
  rw [hrepr] at h
  rw [h]
  exact hN _ hs _

theorem exists_forall_rel_of_directedOn {α : Type*} [Finite α]
    {r : α → α → Prop} (htrans : ∀ {a b c}, r a b → r b c → r a c)
    {s : Set α} (hne : s.Nonempty)
    (hdir : ∀ a ∈ s, ∀ b ∈ s, ∃ c ∈ s, r c a ∧ r c b) :
    ∃ m ∈ s, ∀ a ∈ s, r m a := by
  classical
  have key : ∀ t : Finset α, ↑t ⊆ s → ∃ m ∈ s, ∀ a ∈ t, r m a := by
    intro t
    induction t using Finset.cons_induction with
    | empty =>
        intro _
        obtain ⟨x, hx⟩ := hne
        exact ⟨x, hx, by simp⟩
    | cons a t' ha IH =>
        intro hsub
        rw [Finset.coe_cons, Set.insert_subset_iff] at hsub
        obtain ⟨m', hm's, hm'⟩ := IH hsub.2
        obtain ⟨c, hcs, hcm', hca⟩ := hdir m' hm's a hsub.1
        refine ⟨c, hcs, fun x hx => ?_⟩
        rcases Finset.mem_cons.mp hx with rfl | hx'
        · exact hca
        · exact htrans hcm' (hm' x hx')
  obtain ⟨m, hms, hm⟩ := key (Set.toFinite s).toFinset
    (by simp [Set.Finite.coe_toFinset])
  exact ⟨m, hms, fun a haS => hm a ((Set.Finite.mem_toFinset _).mpr haS)⟩

section EventualMember

variable {ι β : Type*} [Finite ι]

omit [Finite ι] in

theorem exists_tail_embBlock {φ : Semiflow X}
    {blocks : β → Set X} {emb : ι → β}
    (hJoin : ∀ b : β, ∀ x ∈ blocks b,
      ∃ i : ι, x ∈ blocks (emb i) ∧ blocks (emb i) ⊆ blocks b)
    (hInv : ∀ b : β, φ.Invariant (blocks b))
    {γ : ℝ → X} (horb : φ.CompleteOrbit γ) {b : β} {T₀ : ℝ}
    (hb : ∀ s, T₀ ≤ s → γ s ∈ blocks b) :
    ∃ i : ι, blocks (emb i) ⊆ blocks b ∧
      ∀ s, T₀ ≤ s → γ s ∈ blocks (emb i) := by
  obtain ⟨i, hmem, hsub⟩ := hJoin b (γ T₀) (hb T₀ le_rfl)
  exact ⟨i, hsub, fun s hs => horb.forward_mem (hInv (emb i)) hs hmem⟩

theorem exists_range_embBlock {φ : Semiflow X}
    {blocks : β → Set X} {emb : ι → β}
    (hJoin : ∀ b : β, ∀ x ∈ blocks b,
      ∃ i : ι, x ∈ blocks (emb i) ∧ blocks (emb i) ⊆ blocks b)
    (hInv : ∀ b : β, φ.Invariant (blocks b))
    {γ : ℝ → X} (horb : φ.CompleteOrbit γ) {b : β} {T₀ : ℝ}
    (hb : ∀ s, s ≤ T₀ → γ s ∈ blocks b) :
    ∃ i : ι, blocks (emb i) ⊆ blocks b ∧ ∀ s : ℝ, γ s ∈ blocks (emb i) := by
  classical
  by_contra hcon
  push Not at hcon

  have hav : ∀ i : ι, ∃ T : ℝ, blocks (emb i) ⊆ blocks b →
      ∀ s, s ≤ T → γ s ∉ blocks (emb i) := by
    intro i
    by_cases hib : blocks (emb i) ⊆ blocks b
    · obtain ⟨s₀, hs₀⟩ := hcon i hib
      exact ⟨s₀, fun _ s hs hmem =>
        hs₀ (horb.forward_mem (hInv (emb i)) hs hmem)⟩
    · exact ⟨0, fun h => absurd h hib⟩
  choose T hT using hav
  haveI : Nonempty ι := by
    obtain ⟨i, -, -⟩ := hJoin b (γ T₀) (hb T₀ le_rfl)
    exact ⟨i⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min T
  have hs₁T₀ : min (T i₀) T₀ - 1 ≤ T₀ := by
    have := min_le_right (T i₀) T₀; linarith
  obtain ⟨i₁, hmem₁, hsub₁⟩ := hJoin b (γ (min (T i₀) T₀ - 1))
    (hb _ hs₁T₀)
  have hs₁T : min (T i₀) T₀ - 1 ≤ T i₁ := by
    have h1 := min_le_left (T i₀) T₀
    have h2 := hi₀ i₁
    linarith
  exact absurd hmem₁ (hT i₁ hsub₁ _ hs₁T)

theorem exists_cellMem_subset
    {blocks : β → Set X} {emb : ι → β} {cover : ι → β} {cells : ι → Set X}
    (hJoin : ∀ b : β, ∀ x ∈ blocks b,
      ∃ i : ι, x ∈ blocks (emb i) ∧ blocks (emb i) ⊆ blocks b)
    (hcover : ∀ i : ι, blocks (cover i) ⊂ blocks (emb i))
    (hcellsSup : ∀ i : ι, blocks (emb i) \ blocks (cover i) ⊆ cells i)
    {x : X} (i : ι) (hmem : x ∈ blocks (emb i)) :
    ∃ j : ι, blocks (emb j) ⊆ blocks (emb i) ∧
      x ∈ blocks (emb j) ∧ x ∈ cells j := by
  classical
  have hwf : WellFounded (fun i' j : ι => blocks (emb i') ⊂ blocks (emb j)) := by
    haveI : IsTrans ι (fun i' j : ι => blocks (emb i') ⊂ blocks (emb j)) :=
      ⟨fun _ _ _ h1 h2 => h1.trans h2⟩
    haveI : Std.Irrefl (fun i' j : ι => blocks (emb i') ⊂ blocks (emb j)) :=
      ⟨fun _ h => ssubset_irrefl _ h⟩
    exact Finite.wellFounded_of_trans_of_irrefl _
  have key := hwf.induction
    (C := fun i₀ : ι => x ∈ blocks (emb i₀) →
      ∃ j : ι, blocks (emb j) ⊆ blocks (emb i₀) ∧
        x ∈ blocks (emb j) ∧ x ∈ cells j)
    i (by
      intro i₀ IH hmem₀
      by_cases hc : x ∈ blocks (cover i₀)
      · obtain ⟨i', hmem', hsub'⟩ := hJoin (cover i₀) x hc
        have hlt : blocks (emb i') ⊂ blocks (emb i₀) :=
          hsub'.trans_ssubset (hcover i₀)
        obtain ⟨j, hjsub, hjmem, hjcell⟩ := IH i' hlt hmem'
        exact ⟨j, hjsub.trans hlt.subset, hjmem, hjcell⟩
      · exact ⟨i₀, subset_rfl, hmem₀, hcellsSup i₀ ⟨hmem₀, hc⟩⟩)
  exact key hmem

variable [PartialOrder ι] [TopologicalSpace X]

theorem eventualMember_interval (φ : Semiflow X) (D : Set X)
    (blocks : β → Set X) (emb : ι → β) (cover : ι → β) (bD : β)
    (cells : ι → Set X)
    (hbD : D ⊆ blocks bD)
    (hJoin : ∀ b : β, ∀ x ∈ blocks b,
      ∃ i : ι, x ∈ blocks (emb i) ∧ blocks (emb i) ⊆ blocks b)
    (hcover : ∀ i : ι, blocks (cover i) ⊂ blocks (emb i))
    (hcellsSup : ∀ i : ι, blocks (emb i) \ blocks (cover i) ⊆ cells i)
    (horder : ∀ i j : ι, blocks (emb i) ⊆ blocks (emb j) → i ≤ j)
    (hclosed : ∀ i : ι, IsClosed (blocks (emb i)))
    (hInv : ∀ b : β, φ.Invariant (blocks b))
    (hMeet : ∀ a b : β, ∃ c : β, blocks c ⊆ blocks a ∩ blocks b ∧
      ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
        ∀ s t : ℝ, (∀ u, s ≤ u → u ≤ t → γ u ∈ blocks a ∩ blocks b) →
          ∀ u, s ≤ u → u ≤ t → γ u ∈ blocks c)
    (hAbsorbOmega : ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
      ∀ b : β, (omegaSet γ ∩ blocks b).Nonempty →
        ∃ T : ℝ, ∀ t, T ≤ t → γ t ∈ blocks b)
    (hAbsorbAlpha : ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
      ∀ b : β, (alphaSet γ ∩ blocks b).Nonempty →
        ∃ T : ℝ, ∀ t, t ≤ T → γ t ∈ blocks b) :
    ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
      ∃ bα bω : ι, bω ≤ bα ∧
        alphaSet γ ⊆ cells bα ∧ omegaSet γ ⊆ cells bω ∧
        ∀ t : ℝ, ∃ i, bω ≤ i ∧ i ≤ bα ∧ γ t ∈ cells i := by
  intro γ horb hr
  classical
  have hγD : ∀ t : ℝ, γ t ∈ D := fun t => hr ⟨t, rfl⟩

  set TJ : Set ι := {i | ∃ T : ℝ, ∀ s, T ≤ s → γ s ∈ blocks (emb i)}
    with hTJdef
  set RJ : Set ι := {i | ∀ s : ℝ, γ s ∈ blocks (emb i)} with hRJdef
  have hRJ_TJ : RJ ⊆ TJ := fun i hi => ⟨0, fun s _ => hi s⟩
  have hTJne : TJ.Nonempty := by
    obtain ⟨i, -, hitail⟩ := exists_tail_embBlock hJoin hInv horb
      (b := bD) (T₀ := 0) (fun s _ => hbD (hγD s))
    exact ⟨i, 0, hitail⟩
  have hTJdir : ∀ a ∈ TJ, ∀ b ∈ TJ, ∃ c ∈ TJ,
      blocks (emb c) ⊆ blocks (emb a) ∧ blocks (emb c) ⊆ blocks (emb b) := by
    rintro a ⟨Ta, hTa⟩ b ⟨Tb, hTb⟩
    obtain ⟨m, hmsub, hmcl⟩ := hMeet (emb a) (emb b)
    have htailm : ∀ s, max Ta Tb ≤ s → γ s ∈ blocks m := by
      intro s hs
      refine hmcl γ horb hr (max Ta Tb) s ?_ s hs le_rfl
      intro u hu _
      exact ⟨hTa u (le_trans (le_max_left _ _) hu),
             hTb u (le_trans (le_max_right _ _) hu)⟩
    obtain ⟨c, hcsub, hctail⟩ := exists_tail_embBlock hJoin hInv horb htailm
    exact ⟨c, ⟨max Ta Tb, hctail⟩,
      (hcsub.trans hmsub).trans Set.inter_subset_left,
      (hcsub.trans hmsub).trans Set.inter_subset_right⟩

  obtain ⟨iω, hiωTJ, hiωmin⟩ := exists_forall_rel_of_directedOn
    (r := fun i j : ι => blocks (emb i) ⊆ blocks (emb j))
    (fun h1 h2 => h1.trans h2) hTJne hTJdir
  obtain ⟨Tω, hTω⟩ := hiωTJ

  have hRJne : RJ.Nonempty := by
    obtain ⟨i, -, hirange⟩ := exists_range_embBlock hJoin hInv horb
      (b := bD) (T₀ := 0) (fun s _ => hbD (hγD s))
    exact ⟨i, hirange⟩
  have hRJdir : ∀ a ∈ RJ, ∀ b ∈ RJ, ∃ c ∈ RJ,
      blocks (emb c) ⊆ blocks (emb a) ∧ blocks (emb c) ⊆ blocks (emb b) := by
    intro a ha b hb
    obtain ⟨m, hmsub, hmcl⟩ := hMeet (emb a) (emb b)
    have hrangem : ∀ s : ℝ, γ s ∈ blocks m := by
      intro s
      refine hmcl γ horb hr s s ?_ s le_rfl le_rfl
      intro u hu hu'
      obtain rfl : u = s := le_antisymm hu' hu
      exact ⟨ha _, hb _⟩
    obtain ⟨c, hcsub, hcrange⟩ := exists_range_embBlock hJoin hInv horb
      (b := m) (T₀ := 0) (fun s _ => hrangem s)
    exact ⟨c, hcrange,
      (hcsub.trans hmsub).trans Set.inter_subset_left,
      (hcsub.trans hmsub).trans Set.inter_subset_right⟩
  obtain ⟨iα, hiαRJ, hiαmin⟩ := exists_forall_rel_of_directedOn
    (r := fun i j : ι => blocks (emb i) ⊆ blocks (emb j))
    (fun h1 h2 => h1.trans h2) hRJne hRJdir

  have hωcell : omegaSet γ ⊆ cells iω := by
    intro y hy
    have hyJB : y ∈ blocks (emb iω) := by
      have hwin : y ∈ closure (γ '' Set.Ici Tω) := Set.mem_iInter.mp hy Tω
      refine closure_minimal ?_ (hclosed iω) hwin
      rintro _ ⟨s, hs, rfl⟩
      exact hTω s hs
    have hycov : y ∉ blocks (cover iω) := by
      intro hyc
      obtain ⟨T', hT'⟩ := hAbsorbOmega γ horb hr (cover iω) ⟨y, hy, hyc⟩
      obtain ⟨i', hi'sub, hi'tail⟩ :=
        exists_tail_embBlock hJoin hInv horb hT'
      have hcon : blocks (emb iω) ⊆ blocks (cover iω) :=
        (hiωmin i' ⟨T', hi'tail⟩).trans hi'sub
      exact absurd hcon (hcover iω).not_subset
    exact hcellsSup iω ⟨hyJB, hycov⟩

  have hαcell : alphaSet γ ⊆ cells iα := by
    intro y hy
    have hyJB : y ∈ blocks (emb iα) := by
      have hwin : y ∈ closure (γ '' Set.Iic 0) := Set.mem_iInter.mp hy 0
      refine closure_minimal ?_ (hclosed iα) hwin
      rintro _ ⟨s, -, rfl⟩
      exact hiαRJ s
    have hycov : y ∉ blocks (cover iα) := by
      intro hyc
      obtain ⟨T', hT'⟩ := hAbsorbAlpha γ horb hr (cover iα) ⟨y, hy, hyc⟩
      obtain ⟨i', hi'sub, hi'range⟩ :=
        exists_range_embBlock hJoin hInv horb hT'
      have hcon : blocks (emb iα) ⊆ blocks (cover iα) :=
        (hiαmin i' hi'range).trans hi'sub
      exact absurd hcon (hcover iα).not_subset
    exact hcellsSup iα ⟨hyJB, hycov⟩

  refine ⟨iα, iω, horder _ _ (hiωmin iα (hRJ_TJ hiαRJ)), hαcell, hωcell, ?_⟩
  intro t
  obtain ⟨j, hjsub, hjmem, hjcell⟩ :=
    exists_cellMem_subset hJoin hcover hcellsSup iα (hiαRJ t)
  have hjTJ : j ∈ TJ :=
    ⟨t, fun s hs => horb.forward_mem (hInv (emb j)) hs hjmem⟩
  exact ⟨j, horder _ _ (hiωmin j hjTJ), horder _ _ hjsub, hjcell⟩

end EventualMember

section Combined

variable {Vtx ι β : Type*} [PseudoMetricSpace X] [T2Space X]
  [PartialOrder Vtx] [PartialOrder ι] [Finite ι]

theorem qMorseDischarge_sound_eventualMember (φ : Semiflow X) (D : Set X)
    (ρ : Vtx → Set X) (cells : ι → Set X) (hmap : ι → Option Vtx)
    (blocks : β → Set X) (emb : ι → β) (cover : ι → β) (bD : β)
    (hD : IsCompact D)
    (hflow : ∀ t, Continuous (φ.flow t))
    (hcells : ∀ i, IsCompact (cells i))
    (hContain : ∀ i v, hmap i = some v → cells i ⊆ ρ v)
    (hOverlap : ∀ v w, v ≠ w →
      φ.HasTransitCert
        (fiberUnion cells hmap v ∩ fiberUnion cells hmap w))
    (hCell : ∀ x ∈ D, ChainRecurrentIn φ D x → ∃ i, x ∈ φ.MaxInv (cells i))
    (hTransitCert : ∀ i, hmap i = none → φ.HasTransitCert (cells i))
    (hConv : ∀ i j k v, i ≤ j → j ≤ k →
      hmap i = some v → hmap k = some v → hmap j = some v)
    (hMono : ∀ i j v w, i ≤ j →
      hmap i = some v → hmap j = some w → v ≤ w)
    (hbD : D ⊆ blocks bD)
    (hJoin : ∀ b : β, ∀ x ∈ blocks b,
      ∃ i : ι, x ∈ blocks (emb i) ∧ blocks (emb i) ⊆ blocks b)
    (hcover : ∀ i : ι, blocks (cover i) ⊂ blocks (emb i))
    (hcellsSup : ∀ i : ι, blocks (emb i) \ blocks (cover i) ⊆ cells i)
    (horder : ∀ i j : ι, blocks (emb i) ⊆ blocks (emb j) → i ≤ j)
    (hclosed : ∀ i : ι, IsClosed (blocks (emb i)))
    (hInv : ∀ b : β, φ.Invariant (blocks b))
    (hMeet : ∀ a b : β, ∃ c : β, blocks c ⊆ blocks a ∩ blocks b ∧
      ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
        ∀ s t : ℝ, (∀ u, s ≤ u → u ≤ t → γ u ∈ blocks a ∩ blocks b) →
          ∀ u, s ≤ u → u ≤ t → γ u ∈ blocks c)
    (hAbsorbOmega : ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
      ∀ b : β, (omegaSet γ ∩ blocks b).Nonempty →
        ∃ T : ℝ, ∀ t, T ≤ t → γ t ∈ blocks b)
    (hAbsorbAlpha : ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
      ∀ b : β, (alphaSet γ ∩ blocks b).Nonempty →
        ∃ T : ℝ, ∀ t, t ≤ T → γ t ∈ blocks b) :
    MorseSat φ D ρ :=
  qMorseDischarge_sound_orderAssembled φ D ρ cells hmap hD hflow hcells
    hContain hOverlap hCell hTransitCert hConv hMono
    (eventualMember_interval φ D blocks emb cover bD cells hbD hJoin
      hcover hcellsSup horder hclosed hInv hMeet hAbsorbOmega hAbsorbAlpha)

end Combined

end Semiflow
end Qtsl

#print axioms Qtsl.Semiflow.CompleteOrbit.forward_mem
#print axioms Qtsl.Semiflow.exists_forall_rel_of_directedOn
#print axioms Qtsl.Semiflow.exists_tail_embBlock
#print axioms Qtsl.Semiflow.exists_range_embBlock
#print axioms Qtsl.Semiflow.exists_cellMem_subset
#print axioms Qtsl.Semiflow.eventualMember_interval
#print axioms Qtsl.Semiflow.qMorseDischarge_sound_eventualMember

end PPLC
