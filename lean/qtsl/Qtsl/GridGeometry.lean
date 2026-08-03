import Qtsl.Discharge
import Qtsl.MeanValue

/-!
# Grid geometry for the facet-row certificates

The grid-geometry side conditions of the facet-row development: the
local wedge test (arena membership plus nonnegativity of the active
facet observables implies membership in the block) and block-in-arena
containment, mechanized as recomputable geometry over the rational
grid rather than trusted as schema declarations.
-/

namespace PPLC
namespace Qtsl

open scoped NNReal
open Set Topology

structure Grid (d : ℕ) where
  n : Fin d → ℕ
  line : ∀ k : Fin d, Fin (n k + 1) → ℝ
  mono : ∀ k, StrictMono (line k)

namespace Grid

variable {d : ℕ} (G : Grid d)

abbrev CellIdx : Type := ∀ k : Fin d, Fin (G.n k)

def Cell (c : G.CellIdx) : Set (Fin d → ℝ) :=
  {x | ∀ k, G.line k (c k).castSucc ≤ x k ∧ x k ≤ G.line k (c k).succ}

theorem mem_cell_iff {c : G.CellIdx} {y : Fin d → ℝ} :
    y ∈ G.Cell c ↔ ∀ k, G.line k (c k).castSucc ≤ y k ∧ y k ≤ G.line k (c k).succ :=
  Iff.rfl

def arena : Set (Fin d → ℝ) :=
  {x | ∀ k, G.line k 0 ≤ x k ∧ x k ≤ G.line k (Fin.last (G.n k))}

theorem mem_arena_iff {y : Fin d → ℝ} :
    y ∈ G.arena ↔ ∀ k, G.line k 0 ≤ y k ∧ y k ≤ G.line k (Fin.last (G.n k)) :=
  Iff.rfl

def blockRegion (B : Finset G.CellIdx) : Set (Fin d → ℝ) :=
  ⋃ c ∈ B, G.Cell c

theorem mem_blockRegion_iff {B : Finset G.CellIdx} {y : Fin d → ℝ} :
    y ∈ G.blockRegion B ↔ ∃ c ∈ B, y ∈ G.Cell c := by
  simp [blockRegion]

theorem isClosed_cell (c : G.CellIdx) : IsClosed (G.Cell c) := by
  have h : G.Cell c = ⋂ k, (fun x : Fin d → ℝ => x k) ⁻¹'
      Set.Icc (G.line k (c k).castSucc) (G.line k (c k).succ) := by
    ext x
    simp [mem_cell_iff, Set.mem_iInter, Set.mem_Icc]
  rw [h]
  exact isClosed_iInter fun k => isClosed_Icc.preimage (continuous_apply k)

theorem isClosed_arena : IsClosed G.arena := by
  have h : G.arena = ⋂ k, (fun x : Fin d → ℝ => x k) ⁻¹'
      Set.Icc (G.line k 0) (G.line k (Fin.last (G.n k))) := by
    ext x
    simp [mem_arena_iff, Set.mem_iInter, Set.mem_Icc]
  rw [h]
  exact isClosed_iInter fun k => isClosed_Icc.preimage (continuous_apply k)

theorem isClosed_blockRegion (B : Finset G.CellIdx) :
    IsClosed (G.blockRegion B) :=
  Set.Finite.isClosed_biUnion B.finite_toSet fun c _ => G.isClosed_cell c

theorem cell_subset_arena (c : G.CellIdx) : G.Cell c ⊆ G.arena := by
  intro x hx k
  exact ⟨le_trans ((G.mono k).monotone (Fin.zero_le _)) (hx k).1,
    le_trans (hx k).2 ((G.mono k).monotone (Fin.le_last _))⟩

theorem blockRegion_subset_arena (B : Finset G.CellIdx) :
    G.blockRegion B ⊆ G.arena := by
  intro y hy
  obtain ⟨c, -, hyc⟩ := (G.mem_blockRegion_iff).mp hy
  exact G.cell_subset_arena c hyc

abbrev FacetData : Type := G.CellIdx × Fin d × Bool

def IsFacet (B : Finset G.CellIdx) : G.FacetData → Prop
  | (c, k, true) => c ∈ B ∧
      ∃ h : (c k : ℕ) + 1 < G.n k, Function.update c k ⟨(c k : ℕ) + 1, h⟩ ∉ B
  | (c, k, false) => c ∈ B ∧ 0 < (c k : ℕ) ∧
      Function.update c k ⟨(c k : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) (c k).isLt⟩ ∉ B

def facetLine : G.FacetData → ℝ
  | (c, k, true) => G.line k (c k).succ
  | (c, k, false) => G.line k (c k).castSucc

def obs (p : G.FacetData) (y : Fin d → ℝ) : ℝ :=
  if p.2.2 then G.facetLine p - y p.2.1 else y p.2.1 - G.facetLine p

def facetBox (p : G.FacetData) : Set (Fin d → ℝ) :=
  G.Cell p.1 ∩ {y | y p.2.1 = G.facetLine p}

theorem obs_eq_zero_of_mem_facetBox {p : G.FacetData} {x : Fin d → ℝ}
    (h : x ∈ G.facetBox p) : G.obs p x = 0 := by
  have h2 : x p.2.1 = G.facetLine p := h.2
  by_cases hs : p.2.2 <;> simp [obs, hs, h2]

theorem wedge_containment (B : Finset G.CellIdx) (x : Fin d → ℝ)
    (hx : x ∈ G.blockRegion B) :
    ∃ U ∈ 𝓝 x, ∀ y ∈ U, y ∈ G.arena →
      (∀ p : G.FacetData, G.IsFacet B p → x ∈ G.facetBox p → 0 ≤ G.obs p y) →
      y ∈ G.blockRegion B := by
  classical

  set lines : Finset ℝ := insert 1
    ((Finset.univ : Finset (Σ k : Fin d, Fin (G.n k + 1))).image
      fun q => if G.line q.1 q.2 = x q.1 then 1 else |x q.1 - G.line q.1 q.2|)
    with hlines
  have hlne : lines.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  set δ : ℝ := lines.min' hlne with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef, Finset.lt_min'_iff]
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact one_pos
    · obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ha
      by_cases hq : G.line q.1 q.2 = x q.1
      · simp [hq]
      · rw [if_neg hq]
        exact abs_pos.mpr (sub_ne_zero.mpr fun h => hq h.symm)
  have hδle : ∀ (k : Fin d) (j : Fin (G.n k + 1)),
      G.line k j ≠ x k → δ ≤ |x k - G.line k j| := by
    intro k j hj
    refine Finset.min'_le _ _ ?_
    rw [hlines]
    refine Finset.mem_insert_of_mem ?_
    have h := Finset.mem_image_of_mem
      (fun q : Σ k, Fin (G.n k + 1) =>
        if G.line q.1 q.2 = x q.1 then 1 else |x q.1 - G.line q.1 q.2|)
      (Finset.mem_univ (⟨k, j⟩ : Σ k, Fin (G.n k + 1)))
    simpa [if_neg hj] using h

  refine ⟨⋂ k, (fun y : Fin d → ℝ => y k) ⁻¹' Set.Ioo (x k - δ) (x k + δ), ?_, ?_⟩
  · exact Filter.iInter_mem.mpr fun k =>
      (continuous_apply k).continuousAt.preimage_mem_nhds
        (Ioo_mem_nhds (by linarith) (by linarith))
  intro y hyU hyD hactive
  have hclose : ∀ k, x k - δ < y k ∧ y k < x k + δ := by
    intro k
    have h := Set.mem_iInter.mp hyU k
    rw [Set.mem_preimage, Set.mem_Ioo] at h
    exact h

  have hside_lt : ∀ (k : Fin d) (j : Fin (G.n k + 1)),
      x k < G.line k j → y k < G.line k j := by
    intro k j hlt
    have h1 := hδle k j (ne_of_gt hlt)
    have h2 : |x k - G.line k j| = G.line k j - x k := by
      rw [abs_sub_comm]
      exact abs_of_pos (by linarith)
    have h3 := (hclose k).2
    linarith
  have hside_gt : ∀ (k : Fin d) (j : Fin (G.n k + 1)),
      G.line k j < x k → G.line k j < y k := by
    intro k j hlt
    have h1 := hδle k j (ne_of_lt hlt)
    have h2 : |x k - G.line k j| = x k - G.line k j := abs_of_pos (by linarith)
    have h3 := (hclose k).1
    linarith

  set wrong : G.CellIdx → Finset (Fin d) := fun c =>
    Finset.univ.filter fun k =>
      ¬ (G.line k (c k).castSucc ≤ y k ∧ y k ≤ G.line k (c k).succ)
    with hwrongdef
  have hOfEmpty : ∀ c ∈ B, wrong c = ∅ → y ∈ G.blockRegion B := by
    intro c hcB hempty
    refine (G.mem_blockRegion_iff).mpr ⟨c, hcB, ?_⟩
    intro k
    by_contra hbad
    have hk : k ∈ wrong c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩
    simp [hempty] at hk

  suffices H : ∀ (m : ℕ) (c : G.CellIdx), c ∈ B → x ∈ G.Cell c →
      (wrong c).card ≤ m → y ∈ G.blockRegion B by
    obtain ⟨c₀, hc₀, hxc₀⟩ := (G.mem_blockRegion_iff).mp hx
    exact H (wrong c₀).card c₀ hc₀ hxc₀ le_rfl
  intro m
  induction m with
  | zero =>
    intro c hcB hxc hcard
    exact hOfEmpty c hcB (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
  | succ m ih =>
    intro c hcB hxc hcard
    rcases Finset.eq_empty_or_nonempty (wrong c) with hempty | ⟨k, hk⟩
    · exact hOfEmpty c hcB hempty
    have hkw : ¬ (G.line k (c k).castSucc ≤ y k ∧ y k ≤ G.line k (c k).succ) :=
      (Finset.mem_filter.mp hk).2
    rcases lt_or_ge (y k) (G.line k (c k).castSucc) with hlow | hge
    ·

      have hxk : x k = G.line k (c k).castSucc := by
        rcases eq_or_lt_of_le (hxc k).1 with h | h
        · exact h.symm
        · exact absurd (hside_gt k (c k).castSucc h) (by linarith)

      have hpos : 0 < (c k : ℕ) := by
        rcases Nat.eq_zero_or_pos (c k : ℕ) with h0 | h
        · exfalso
          have hcast : (c k).castSucc = (0 : Fin (G.n k + 1)) := by
            apply Fin.ext
            simp [h0]
          have harena := (hyD k).1
          rw [← hcast] at harena
          linarith
        · exact h
      have hlt' : (c k : ℕ) - 1 < G.n k :=
        lt_of_le_of_lt (Nat.sub_le _ _) (c k).isLt
      set c' : G.CellIdx := Function.update c k ⟨(c k : ℕ) - 1, hlt'⟩ with hc'def
      have hc'k : c' k = ⟨(c k : ℕ) - 1, hlt'⟩ := by
        rw [hc'def]
        exact Function.update_self ..
      have hc'j : ∀ j, j ≠ k → c' j = c j := by
        intro j hj
        rw [hc'def]
        exact Function.update_of_ne hj ..

      have hc'B : c' ∈ B := by
        by_contra hnB
        have hfacet : G.IsFacet B (c, k, false) := ⟨hcB, hpos, hnB⟩
        have hxbox : x ∈ G.facetBox (c, k, false) := ⟨hxc, by simpa [facetLine] using hxk⟩
        have hnn := hactive _ hfacet hxbox
        simp [obs, facetLine] at hnn
        linarith

      have hsuccval : ((c' k).succ : ℕ) = (c k : ℕ) := by
        rw [hc'k]
        simp only [Fin.val_succ]
        omega
      have hline_succ : G.line k (c' k).succ = G.line k (c k).castSucc := by
        congr 1
        apply Fin.ext
        simpa using hsuccval
      have hline_cast_lt : G.line k (c' k).castSucc < G.line k (c k).castSucc := by
        rw [← hline_succ]
        exact G.mono k Fin.castSucc_lt_succ

      have hxc' : x ∈ G.Cell c' := by
        intro j
        rcases eq_or_ne j k with rfl | hjk
        · exact ⟨hxk ▸ hline_cast_lt.le, le_of_eq (hxk.trans hline_succ.symm)⟩
        · rw [hc'j j hjk]
          exact hxc j

      have hknot : ¬ (k ∈ wrong c') := by
        intro hkmem
        have hbad := (Finset.mem_filter.mp hkmem).2
        refine hbad ⟨?_, ?_⟩
        · have h := hside_gt k (c' k).castSucc (by rw [hxk]; exact hline_cast_lt)
          exact h.le
        · rw [hline_succ]
          exact hlow.le
      have hsub : wrong c' ⊆ (wrong c).erase k := by
        intro j hj
        have hjmem := (Finset.mem_filter.mp hj).2
        rcases eq_or_ne j k with rfl | hjk
        · exact absurd hj hknot
        · refine Finset.mem_erase.mpr ⟨hjk, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          rwa [hc'j j hjk] at hjmem
      have hcard' : (wrong c').card ≤ m := by
        have h1 : (wrong c').card ≤ ((wrong c).erase k).card := Finset.card_le_card hsub
        have h2 : ((wrong c).erase k).card = (wrong c).card - 1 :=
          Finset.card_erase_of_mem hk
        have h3 : 1 ≤ (wrong c).card := Finset.card_pos.mpr ⟨k, hk⟩
        omega
      exact ih c' hc'B hxc' hcard'
    ·
      have hhigh : G.line k (c k).succ < y k := by
        by_contra hle
        exact hkw ⟨hge, le_of_not_gt hle⟩
      have hxk : x k = G.line k (c k).succ := by
        rcases eq_or_lt_of_le (hxc k).2 with h | h
        · exact h
        · exact absurd (hside_lt k (c k).succ h) (by linarith)

      have hlt' : (c k : ℕ) + 1 < G.n k := by
        rcases Nat.lt_or_ge ((c k : ℕ) + 1) (G.n k) with h | h
        · exact h
        · exfalso
          have hval : (c k : ℕ) + 1 = G.n k := by
            have := (c k).isLt
            omega
          have hsucc : (c k).succ = Fin.last (G.n k) := by
            apply Fin.ext
            simp [hval]
          have harena := (hyD k).2
          rw [← hsucc] at harena
          linarith
      set c' : G.CellIdx := Function.update c k ⟨(c k : ℕ) + 1, hlt'⟩ with hc'def
      have hc'k : c' k = ⟨(c k : ℕ) + 1, hlt'⟩ := by
        rw [hc'def]
        exact Function.update_self ..
      have hc'j : ∀ j, j ≠ k → c' j = c j := by
        intro j hj
        rw [hc'def]
        exact Function.update_of_ne hj ..
      have hc'B : c' ∈ B := by
        by_contra hnB
        have hfacet : G.IsFacet B (c, k, true) := ⟨hcB, hlt', hnB⟩
        have hxbox : x ∈ G.facetBox (c, k, true) := ⟨hxc, by simpa [facetLine] using hxk⟩
        have hnn := hactive _ hfacet hxbox
        simp [obs, facetLine] at hnn
        linarith
      have hcastval : ((c' k).castSucc : ℕ) = ((c k).succ : ℕ) := by
        rw [hc'k]
        simp
      have hline_cast : G.line k (c' k).castSucc = G.line k (c k).succ := by
        congr 1
        apply Fin.ext
        simpa using hcastval
      have hline_succ_gt : G.line k (c k).succ < G.line k (c' k).succ := by
        rw [← hline_cast]
        exact G.mono k Fin.castSucc_lt_succ
      have hxc' : x ∈ G.Cell c' := by
        intro j
        rcases eq_or_ne j k with rfl | hjk
        · exact ⟨le_of_eq (hline_cast.trans hxk.symm), hxk ▸ hline_succ_gt.le⟩
        · rw [hc'j j hjk]
          exact hxc j
      have hknot : ¬ (k ∈ wrong c') := by
        intro hkmem
        have hbad := (Finset.mem_filter.mp hkmem).2
        refine hbad ⟨?_, ?_⟩
        · rw [hline_cast]
          exact hhigh.le
        · have h := hside_lt k (c' k).succ (by rw [hxk]; exact hline_succ_gt)
          exact h.le
      have hsub : wrong c' ⊆ (wrong c).erase k := by
        intro j hj
        have hjmem := (Finset.mem_filter.mp hj).2
        rcases eq_or_ne j k with rfl | hjk
        · exact absurd hj hknot
        · refine Finset.mem_erase.mpr ⟨hjk, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          rwa [hc'j j hjk] at hjmem
      have hcard' : (wrong c').card ≤ m := by
        have h1 : (wrong c').card ≤ ((wrong c).erase k).card := Finset.card_le_card hsub
        have h2 : ((wrong c).erase k).card = (wrong c).card - 1 :=
          Finset.card_erase_of_mem hk
        have h3 : 1 ≤ (wrong c).card := Finset.card_pos.mpr ⟨k, hk⟩
        omega
      exact ih c' hc'B hxc' hcard'

theorem hasFacetRows_of_rows (φ : Semiflow (Fin d → ℝ)) (B : Finset G.CellIdx)
    (ε : G.FacetData → ℝ) (F : G.FacetData → Set (Fin d → ℝ))
    (hε : ∀ p, G.IsFacet B p → 0 < ε p)
    (hF : ∀ p, G.IsFacet B p → ∀ x ∈ G.facetBox p, F p ∈ 𝓝 x)
    (hrow : ∀ p, G.IsFacet B p → ∀ x ∈ F p, ∀ t : ℝ≥0,
      (∀ s ≤ t, φ.flow s x ∈ F p) →
      G.obs p x + ε p * (t : ℝ) ≤ G.obs p (φ.flow t x)) :
    φ.HasFacetRows G.arena (G.blockRegion B) := by
  classical
  refine ⟨Fintype.card {p : G.FacetData // G.IsFacet B p},
    fun i => G.obs ((Fintype.equivFin _).symm i).1,
    fun i => ε ((Fintype.equivFin _).symm i).1,
    fun i => F ((Fintype.equivFin _).symm i).1,
    fun i => hε _ ((Fintype.equivFin _).symm i).2,
    fun i => hrow _ ((Fintype.equivFin _).symm i).2, ?_⟩
  intro x hxfr
  have hxN : x ∈ G.blockRegion B := by
    have h := frontier_subset_closure hxfr
    rwa [(G.isClosed_blockRegion B).closure_eq] at h
  obtain ⟨U, hU, hwedge⟩ := G.wedge_containment B x hxN
  refine ⟨{i | x ∈ G.facetBox ((Fintype.equivFin _).symm i).1}, U, hU, ?_, ?_⟩
  · intro i hi
    exact ⟨G.obs_eq_zero_of_mem_facetBox hi,
      hF _ ((Fintype.equivFin _).symm i).2 x hi⟩
  · intro y hyU hyD hnn
    refine hwedge y hyU hyD ?_
    intro p hp hxp
    have h := hnn ((Fintype.equivFin {p : G.FacetData // G.IsFacet B p}) ⟨p, hp⟩)
      (by simpa using hxp)
    simpa using h

theorem qBlockInv_sound_of_grid (φ : Semiflow (Fin d → ℝ)) (B : Finset G.CellIdx)
    {X0 : Set (Fin d → ℝ)}
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hArena : φ.Invariant G.arena)
    (ε : G.FacetData → ℝ) (F : G.FacetData → Set (Fin d → ℝ))
    (hε : ∀ p, G.IsFacet B p → 0 < ε p)
    (hF : ∀ p, G.IsFacet B p → ∀ x ∈ G.facetBox p, F p ∈ 𝓝 x)
    (hrow : ∀ p, G.IsFacet B p → ∀ x ∈ F p, ∀ t : ℝ≥0,
      (∀ s ≤ t, φ.flow s x ∈ F p) →
      G.obs p x + ε p * (t : ℝ) ≤ G.obs p (φ.flow t x))
    (hInit : X0 ⊆ G.blockRegion B) :
    φ.InvScopeSat (G.blockRegion B) X0 :=
  Semiflow.qBlockInv_sound_of_facetRows (G.isClosed_blockRegion B) htraj
    (G.blockRegion_subset_arena B) hArena
    (G.hasFacetRows_of_rows φ B ε F hε hF hrow) hInit

theorem qBlockInv_sound_of_pointwiseRows (φ : Semiflow (Fin d → ℝ))
    (B : Finset G.CellIdx) {X0 : Set (Fin d → ℝ)}
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hArena : φ.Invariant G.arena)
    (ε : G.FacetData → ℝ) (F : G.FacetData → Set (Fin d → ℝ))
    (W : G.FacetData → (Fin d → ℝ) → ℝ)
    (hε : ∀ p, G.IsFacet B p → 0 < ε p)
    (hF : ∀ p, G.IsFacet B p → ∀ x ∈ G.facetBox p, F p ∈ 𝓝 x)
    (hV : ∀ p, G.IsFacet B p → ContinuousOn (G.obs p) (F p))
    (hW : ∀ p, G.IsFacet B p → φ.FlowDerivOn (G.obs p) (W p) (F p))
    (hrow : ∀ p, G.IsFacet B p → ∀ y ∈ F p, ε p ≤ W p y)
    (hInit : X0 ⊆ G.blockRegion B) :
    φ.InvScopeSat (G.blockRegion B) X0 :=
  G.qBlockInv_sound_of_grid φ B htraj hArena ε F hε hF
    (fun p hp _x _hx _t hconf =>
      Semiflow.integrated_ge_of_flowDeriv_ge htraj (hV p hp) (hW p hp)
        (hrow p hp) hconf)
    hInit

end Grid

namespace Semiflow

variable {X : Type*}

theorem invariant_of_invScopeSat {φ : Semiflow X} {D X0 : Set X}
    (h : φ.InvScopeSat D X0) : φ.Invariant D :=
  h.1

theorem invariant_of_facetRows_univ [TopologicalSpace X] {φ : Semiflow X} {D : Set X}
    (hD : IsClosed D)
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hrows : φ.HasFacetRows Set.univ D) : φ.Invariant D :=
  invariant_of_boundaryDwell hD htraj
    (hrows.boundaryDwell (Set.subset_univ D) (invariant_univ φ) htraj)

end Semiflow

end Qtsl
end PPLC

#print axioms PPLC.Qtsl.Grid.wedge_containment
#print axioms PPLC.Qtsl.Grid.hasFacetRows_of_rows
#print axioms PPLC.Qtsl.Grid.qBlockInv_sound_of_grid
#print axioms PPLC.Qtsl.Grid.qBlockInv_sound_of_pointwiseRows
#print axioms PPLC.Qtsl.Semiflow.invariant_of_invScopeSat
#print axioms PPLC.Qtsl.Semiflow.invariant_of_facetRows_univ
