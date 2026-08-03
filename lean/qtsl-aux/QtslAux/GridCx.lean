import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered

/-! # Cell complexes on boxes: group complexes, leaves, patch trees, and grids

This module builds the combinatorial substrate for piecewise certificates on
axis-aligned boxes in `Fin d → ℝ`.

Main definitions:

* `Box d` and `Box.set`: an axis-aligned box given by lower and upper corner.
* `GroupComplex d B G`: a finite family of closed cells covering the
  coordinates in the group `G ⊆ Fin d` — cells have pairwise disjoint
  interiors, are cylindrical in the coordinates outside `G`, stay inside the
  box on `G`, and cover it; `trivialComplex` is the one-cell instance.
* `Leaf d B`: a partition of the `d` coordinates into `g` groups together
  with one group complex per group; its cells are the intersections of one
  cell per group (`Leaf.cell`), which are closed, interior-disjoint, and
  cover the box (`Leaf.exists_mem_cell`).
* `PatchTree d B`: a binary tree recursively splitting the box along
  coordinate hyperplanes, with leaves carrying `Leaf` complexes; its cells
  again form a closed interior-disjoint cover
  (`PatchTree.interior_disjoint`, `PatchTree.iUnion_cell_eq_set`), and
  `PatchTree.region` collects the cells named by a set of indices.
* `BoxGrid d`: per-axis strictly monotone grid lines; `intervalComplex` and
  `gridLeaf` realize the grid as a leaf whose cells are the grid boxes
  (`gridLeaf_cell`), with `enumCells_gridLeaf_val` computing the mixed-radix
  index of a cell.
* `IsRGS`, `CanonicalPartition`, `rgsEquiv`: restricted growth sequences as
  canonical representatives of coordinate partitions, the equivalence
  between them, and the bridge `CanonicalPartition.toLeaf` /
  `Leaf.Canonical` / `Leaf.toCanonicalPartition` identifying leaves whose
  grouping is canonical (`boxLeaf` and `gridLeaf` are;
  `Leaf.not_canonical_counterexample` shows a leaf that is not).
-/

namespace Qtsl
namespace GridCx

structure Box (d : ℕ) where
  lo : Fin d → ℝ
  hi : Fin d → ℝ

def Box.set {d : ℕ} (B : Box d) : Set (Fin d → ℝ) :=
  {x | ∀ k, B.lo k ≤ x k ∧ x k ≤ B.hi k}

theorem Box.mem_set_iff {d : ℕ} {B : Box d} {x : Fin d → ℝ} :
    x ∈ B.set ↔ ∀ k, B.lo k ≤ x k ∧ x k ≤ B.hi k := Iff.rfl

section InteriorHelpers

variable {d : ℕ}

private theorem coord_band_eq_pi (j : Fin d) (s : Set ℝ) :
    {x : Fin d → ℝ | x j ∈ s}
      = Set.pi Set.univ (fun k => if k = j then s else Set.univ) := by
  ext x
  simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_setOf_eq]
  constructor
  · intro hx k
    by_cases hk : k = j
    · subst hk; simpa using hx
    · simp [hk]
  · intro hx
    have := hx j
    simpa using this

theorem interior_coord_band (j : Fin d) (s : Set ℝ) :
    interior {x : Fin d → ℝ | x j ∈ s} = {x : Fin d → ℝ | x j ∈ interior s} := by
  rw [coord_band_eq_pi, interior_pi_set Set.finite_univ]
  have h : (fun k => interior (if k = j then s else Set.univ))
      = fun k => if k = j then interior s else Set.univ := by
    funext k
    by_cases hk : k = j <;> simp [hk]
  rw [h, ← coord_band_eq_pi]

end InteriorHelpers

structure GroupComplex (d : ℕ) (B : Box d) (G : Finset (Fin d)) where
  ι : Type

  count : ℕ

  enum : ι ≃ Fin count
  cell : ι → Set (Fin d → ℝ)
  isClosed_cell : ∀ i, IsClosed (cell i)
  interior_disjoint : ∀ i i', i ≠ i' →
    Disjoint (interior (cell i)) (interior (cell i'))
  cylinder : ∀ i (x y : Fin d → ℝ),
    (∀ k ∈ G, x k = y k) → x ∈ cell i → y ∈ cell i
  cell_subset : ∀ i (x : Fin d → ℝ),
    x ∈ cell i → ∀ k ∈ G, B.lo k ≤ x k ∧ x k ≤ B.hi k
  covers : ∀ x : Fin d → ℝ,
    (∀ k ∈ G, B.lo k ≤ x k ∧ x k ≤ B.hi k) → ∃ i, x ∈ cell i

instance {d : ℕ} {B : Box d} {G : Finset (Fin d)} (X : GroupComplex d B G) :
    Fintype X.ι :=
  Fintype.ofEquiv _ X.enum.symm

def trivialComplex (d : ℕ) (B : Box d) (G : Finset (Fin d)) :
    GroupComplex d B G where
  ι := Unit
  count := 1
  enum := ⟨fun _ => 0, fun _ => ⟨⟩, fun _ => rfl, fun _ => Subsingleton.elim _ _⟩
  interior_disjoint := fun i i' h => absurd (Subsingleton.elim i i') h
  cell _ := {x | ∀ k ∈ G, B.lo k ≤ x k ∧ x k ≤ B.hi k}
  isClosed_cell := by
    intro _
    have h : {x : Fin d → ℝ | ∀ k ∈ G, B.lo k ≤ x k ∧ x k ≤ B.hi k}
        = ⋂ k ∈ G, ({x | B.lo k ≤ x k} ∩ {x | x k ≤ B.hi k}) := by
      ext x
      simp [Set.mem_iInter]
    rw [h]
    exact isClosed_biInter fun k _ =>
      (isClosed_le continuous_const (continuous_apply k)).inter
        (isClosed_le (continuous_apply k) continuous_const)
  cylinder := by
    intro _ x y hxy hx k hk
    rw [← hxy k hk]
    exact hx k hk
  cell_subset := fun _ _ hx => hx
  covers := fun _ hx => ⟨⟨⟩, hx⟩

structure Leaf (d : ℕ) (B : Box d) where
  g : ℕ
  grp : Fin d → Fin g
  cx : ∀ j : Fin g,
    GroupComplex d B (Finset.univ.filter (fun k => grp k = j))

namespace Leaf

variable {d : ℕ} {B : Box d}

abbrev CellIdx (L : Leaf d B) : Type := ∀ j : Fin L.g, (L.cx j).ι

instance (L : Leaf d B) : Fintype L.CellIdx := Pi.instFintype

def cellCount (L : Leaf d B) : ℕ := ∏ j, (L.cx j).count

def enumCells (L : Leaf d B) : L.CellIdx ≃ Fin L.cellCount :=
  (Equiv.piCongrRight fun j => (L.cx j).enum).trans finPiFinEquiv

def cell (L : Leaf d B) (c : L.CellIdx) : Set (Fin d → ℝ) :=
  ⋂ j : Fin L.g, (L.cx j).cell (c j)

theorem mem_cell_iff {L : Leaf d B} {c : L.CellIdx} {x : Fin d → ℝ} :
    x ∈ L.cell c ↔ ∀ j : Fin L.g, x ∈ (L.cx j).cell (c j) :=
  Set.mem_iInter

theorem isClosed_cell (L : Leaf d B) (c : L.CellIdx) :
    IsClosed (L.cell c) :=
  isClosed_iInter fun j => (L.cx j).isClosed_cell (c j)

theorem interior_disjoint (L : Leaf d B) {c c' : L.CellIdx} (hne : c ≠ c') :
    Disjoint (interior (L.cell c)) (interior (L.cell c')) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  exact ((L.cx j).interior_disjoint _ _ hj).mono
    (interior_mono (Set.iInter_subset _ j))
    (interior_mono (Set.iInter_subset _ j))

theorem cell_subset_set (L : Leaf d B) (c : L.CellIdx) :
    L.cell c ⊆ B.set := by
  intro x hx k
  have hj : x ∈ (L.cx (L.grp k)).cell (c (L.grp k)) :=
    mem_cell_iff.mp hx (L.grp k)
  exact (L.cx (L.grp k)).cell_subset _ x hj k
    (Finset.mem_filter.mpr ⟨Finset.mem_univ k, rfl⟩)

theorem exists_mem_cell (L : Leaf d B) {x : Fin d → ℝ} (hx : x ∈ B.set) :
    ∃ c : L.CellIdx, x ∈ L.cell c := by
  have h : ∀ j : Fin L.g, ∃ i, x ∈ (L.cx j).cell i := by
    intro j
    exact (L.cx j).covers x (fun k _ => hx k)
  choose f hf using h
  exact ⟨f, Set.mem_iInter.mpr hf⟩

def boxLeaf (d : ℕ) (B : Box d) : Leaf d B where
  g := 1
  grp := fun _ => 0
  cx := fun _ => trivialComplex d B _

theorem boxLeaf_cell (c : (boxLeaf d B).CellIdx) :
    (boxLeaf d B).cell c = B.set := by
  ext x
  rw [mem_cell_iff, Box.mem_set_iff]
  constructor
  · intro h k
    exact h (0 : Fin 1) k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, rfl⟩)
  · intro h j k _
    exact h k

end Leaf

inductive PatchTree (d : ℕ) : Box d → Type 1 where
  | leaf {B : Box d} (L : Leaf d B) : PatchTree d B
  | split {B : Box d} (k : Fin d) (c : ℝ)
      (hlo : B.lo k < c) (hhi : c < B.hi k)
      (t₀ : PatchTree d ⟨B.lo, Function.update B.hi k c⟩)
      (t₁ : PatchTree d ⟨Function.update B.lo k c, B.hi⟩) :
      PatchTree d B

namespace PatchTree

variable {d : ℕ} {B : Box d}

@[reducible] def CellIdx : {B : Box d} → PatchTree d B → Type
  | _, .leaf L => L.CellIdx
  | _, .split _ _ _ _ t₀ t₁ => t₀.CellIdx ⊕ t₁.CellIdx

@[reducible] def cell :
    {B : Box d} → (T : PatchTree d B) → T.CellIdx → Set (Fin d → ℝ)
  | _, .leaf L => fun c => L.cell c
  | _, .split _ _ _ _ t₀ t₁ => Sum.elim (fun c => t₀.cell c) (fun c => t₁.cell c)

@[reducible] def cellIdxFintype : {B : Box d} → (T : PatchTree d B) → Fintype T.CellIdx
  | _, .leaf L => inferInstanceAs (Fintype L.CellIdx)
  | _, .split _ _ _ _ t₀ t₁ =>
    letI := t₀.cellIdxFintype
    letI := t₁.cellIdxFintype
    inferInstanceAs (Fintype (t₀.CellIdx ⊕ t₁.CellIdx))

instance {B : Box d} (T : PatchTree d B) : Fintype T.CellIdx :=
  T.cellIdxFintype

def cellCount : {B : Box d} → PatchTree d B → ℕ
  | _, .leaf L => L.cellCount
  | _, .split _ _ _ _ t₀ t₁ => t₀.cellCount + t₁.cellCount

def enumCells : {B : Box d} → (T : PatchTree d B) → T.CellIdx ≃ Fin T.cellCount
  | _, .leaf L => L.enumCells
  | _, .split _ _ _ _ t₀ t₁ =>
    (Equiv.sumCongr t₀.enumCells t₁.enumCells).trans finSumFinEquiv

theorem isClosed_cell :
    ∀ {B : Box d} (T : PatchTree d B) (c : T.CellIdx), IsClosed (T.cell c)
  | _, .leaf L, c => L.isClosed_cell c
  | _, .split _ _ _ _ t₀ t₁, c => by
    cases c with
    | inl c₀ => exact isClosed_cell t₀ c₀
    | inr c₁ => exact isClosed_cell t₁ c₁

theorem set_updateHi_subset (B : Box d) (k : Fin d) {c : ℝ}
    (hc : c ≤ B.hi k) :
    (Box.set ⟨B.lo, Function.update B.hi k c⟩) ⊆ B.set := by
  intro x hx k'
  have h : B.lo k' ≤ x k' ∧ x k' ≤ Function.update B.hi k c k' := hx k'
  refine ⟨h.1, ?_⟩
  rcases eq_or_ne k' k with hk | hk
  · subst hk
    have h₂ : x k' ≤ c := by simpa [Function.update_self] using h.2
    exact h₂.trans hc
  · have h₂ : x k' ≤ B.hi k' := by
      simpa [Function.update_apply, hk] using h.2
    exact h₂

theorem set_updateLo_subset (B : Box d) (k : Fin d) {c : ℝ}
    (hc : B.lo k ≤ c) :
    (Box.set ⟨Function.update B.lo k c, B.hi⟩) ⊆ B.set := by
  intro x hx k'
  have h : Function.update B.lo k c k' ≤ x k' ∧ x k' ≤ B.hi k' := hx k'
  refine ⟨?_, h.2⟩
  rcases eq_or_ne k' k with hk | hk
  · subst hk
    have h₁ : c ≤ x k' := by simpa [Function.update_self] using h.1
    exact hc.trans h₁
  · have h₁ : B.lo k' ≤ x k' := by
      simpa [Function.update_apply, hk] using h.1
    exact h₁

theorem cell_subset_set :
    ∀ {B : Box d} (T : PatchTree d B) (c : T.CellIdx), T.cell c ⊆ B.set
  | _, .leaf L, c => L.cell_subset_set c
  | _, .split _ _ hlo hhi t₀ t₁, c => by
    cases c with
    | inl c₀ =>
      exact (cell_subset_set t₀ c₀).trans (set_updateHi_subset _ _ hhi.le)
    | inr c₁ =>
      exact (cell_subset_set t₁ c₁).trans (set_updateLo_subset _ _ hlo.le)

theorem interior_disjoint :
    ∀ {B : Box d} (T : PatchTree d B) {c c' : T.CellIdx}, c ≠ c' →
      Disjoint (interior (T.cell c)) (interior (T.cell c'))
  | _, .leaf L, _, _, hne => L.interior_disjoint hne
  | _, .split k cval _ _ t₀ t₁, c, c', hne => by
    have h₀ : ∀ c₀ : t₀.CellIdx,
        interior (t₀.cell c₀) ⊆ {x : Fin d → ℝ | x k < cval} := by
      intro c₀
      have hsub : t₀.cell c₀ ⊆ {x : Fin d → ℝ | x k ∈ Set.Iic cval} := by
        intro x hx
        have h2 := (t₀.cell_subset_set c₀ hx k).2
        simpa [Function.update_self] using h2
      have hmono := interior_mono hsub
      rw [interior_coord_band] at hmono
      simpa [interior_Iic] using hmono
    have h₁ : ∀ c₁ : t₁.CellIdx,
        interior (t₁.cell c₁) ⊆ {x : Fin d → ℝ | cval < x k} := by
      intro c₁
      have hsub : t₁.cell c₁ ⊆ {x : Fin d → ℝ | x k ∈ Set.Ici cval} := by
        intro x hx
        have h1 := (t₁.cell_subset_set c₁ hx k).1
        simpa [Function.update_self] using h1
      have hmono := interior_mono hsub
      rw [interior_coord_band] at hmono
      simpa [interior_Ici] using hmono
    have hcross : ∀ (c₀ : t₀.CellIdx) (c₁ : t₁.CellIdx),
        Disjoint (interior (t₀.cell c₀)) (interior (t₁.cell c₁)) := by
      intro c₀ c₁
      rw [Set.disjoint_left]
      intro x hx hx'
      have h1 : x k < cval := h₀ c₀ hx
      have h2 : cval < x k := h₁ c₁ hx'
      exact lt_asymm h1 h2
    cases c with
    | inl c₀ =>
      cases c' with
      | inl c₀' => exact interior_disjoint t₀ fun h => hne (congrArg Sum.inl h)
      | inr c₁ => exact hcross c₀ c₁
    | inr c₁ =>
      cases c' with
      | inl c₀ => exact (hcross c₀ c₁).symm
      | inr c₁' => exact interior_disjoint t₁ fun h => hne (congrArg Sum.inr h)

theorem mem_set_updateHi {B : Box d} {k : Fin d} {c : ℝ} {x : Fin d → ℝ}
    (hx : x ∈ B.set) (hxc : x k ≤ c) :
    x ∈ Box.set ⟨B.lo, Function.update B.hi k c⟩ := by
  intro k'
  refine ⟨(hx k').1, ?_⟩
  rcases eq_or_ne k' k with hk | hk
  · subst hk
    simpa [Function.update_self] using hxc
  · simpa [Function.update_apply, hk] using (hx k').2

theorem mem_set_updateLo {B : Box d} {k : Fin d} {c : ℝ} {x : Fin d → ℝ}
    (hx : x ∈ B.set) (hcx : c ≤ x k) :
    x ∈ Box.set ⟨Function.update B.lo k c, B.hi⟩ := by
  intro k'
  refine ⟨?_, (hx k').2⟩
  rcases eq_or_ne k' k with hk | hk
  · subst hk
    simpa [Function.update_self] using hcx
  · simpa [Function.update_apply, hk] using (hx k').1

theorem exists_mem_cell :
    ∀ {B : Box d} (T : PatchTree d B) {x : Fin d → ℝ},
      x ∈ B.set → ∃ c : T.CellIdx, x ∈ T.cell c
  | _, .leaf L, _, hx => L.exists_mem_cell hx
  | _, .split k c _ _ t₀ t₁, x, hx => by
    rcases le_total (x k) c with hxc | hcx
    · rcases exists_mem_cell t₀ (mem_set_updateHi hx hxc) with ⟨i, hi⟩
      exact ⟨Sum.inl i, hi⟩
    · rcases exists_mem_cell t₁ (mem_set_updateLo hx hcx) with ⟨i, hi⟩
      exact ⟨Sum.inr i, hi⟩

def region (T : PatchTree d B) (S : Set T.CellIdx) : Set (Fin d → ℝ) :=
  ⋃ c ∈ S, T.cell c

theorem mem_region_iff {T : PatchTree d B} {S : Set T.CellIdx}
    {x : Fin d → ℝ} : x ∈ T.region S ↔ ∃ c ∈ S, x ∈ T.cell c := by
  simp only [region, Set.mem_iUnion, exists_prop]

theorem region_subset_set (T : PatchTree d B) (S : Set T.CellIdx) :
    T.region S ⊆ B.set := by
  intro x hx
  rcases mem_region_iff.mp hx with ⟨c, _, hc⟩
  exact T.cell_subset_set c hc

theorem region_univ_eq_set (T : PatchTree d B) :
    T.region Set.univ = B.set := by
  apply Set.Subset.antisymm (T.region_subset_set _)
  intro x hx
  rcases T.exists_mem_cell hx with ⟨c, hc⟩
  exact mem_region_iff.mpr ⟨c, trivial, hc⟩

theorem iUnion_cell_eq_set (T : PatchTree d B) :
    (⋃ c : T.CellIdx, T.cell c) = B.set := by
  have h := T.region_univ_eq_set
  unfold region at h
  rwa [Set.biUnion_univ] at h

theorem boxEmbed (d : ℕ) (B : Box d) :
    (PatchTree.leaf (Leaf.boxLeaf d B)).region Set.univ = B.set :=
  region_univ_eq_set _

theorem image_iUnion_cell (f : (Fin d → ℝ) → (Fin d → ℝ))
    (T : PatchTree d B) :
    ⋃ c : T.CellIdx, f '' T.cell c = f '' B.set := by
  rw [← Set.image_iUnion, T.iUnion_cell_eq_set]

end PatchTree

structure BoxGrid (d : ℕ) where
  n : Fin d → ℕ
  line : ∀ k : Fin d, Fin (n k + 1) → ℝ
  mono : ∀ k, StrictMono (line k)

namespace BoxGrid

variable {d : ℕ} (G : BoxGrid d)

abbrev CellIdx : Type := ∀ k : Fin d, Fin (G.n k)

def Cell (c : G.CellIdx) : Set (Fin d → ℝ) :=
  {x | ∀ k, G.line k (c k).castSucc ≤ x k ∧ x k ≤ G.line k (c k).succ}

def blockRegion (B : Finset G.CellIdx) : Set (Fin d → ℝ) :=
  ⋃ c ∈ B, G.Cell c

def box : Box d where
  lo := fun k => G.line k 0
  hi := fun k => G.line k (Fin.last (G.n k))

theorem exists_interval {m : ℕ} (hm : 0 < m) (l : Fin (m + 1) → ℝ)
    (hl : Monotone l) {t : ℝ} (h0 : l 0 ≤ t) (h1 : t ≤ l (Fin.last m)) :
    ∃ i : Fin m, l i.castSucc ≤ t ∧ t ≤ l i.succ := by
  classical
  have hne : (Finset.univ.filter (fun j' : Fin (m + 1) => l j' ≤ t)).Nonempty :=
    ⟨0, by simp [h0]⟩
  set j := (Finset.univ.filter (fun j' : Fin (m + 1) => l j' ≤ t)).max' hne
    with hj
  have hjt : l j ≤ t := by
    have hmem : j ∈ Finset.univ.filter (fun j' : Fin (m + 1) => l j' ≤ t) := by
      rw [hj]
      exact Finset.max'_mem _ hne
    exact (Finset.mem_filter.mp hmem).2
  by_cases hlast : j = Fin.last m
  ·
    have hmt : l (Fin.last m) ≤ t := hlast ▸ hjt
    have hsucc : (⟨m - 1, Nat.sub_lt hm Nat.one_pos⟩ : Fin m).succ
        = Fin.last m := by
      ext
      show m - 1 + 1 = m
      omega
    refine ⟨⟨m - 1, Nat.sub_lt hm Nat.one_pos⟩, ?_, ?_⟩
    · exact le_trans (hl (Fin.le_last _)) hmt
    · exact le_of_le_of_eq h1 (congrArg l hsucc.symm)
  ·
    have hjlt : j.val < m := by
      have hlt := lt_of_le_of_ne (Fin.le_last j) hlast
      simpa [Fin.lt_def, Fin.val_last] using hlt
    refine ⟨⟨j.val, hjlt⟩, ?_, ?_⟩
    ·
      exact hjt
    · have hnot : ¬ l ⟨j.val + 1, Nat.succ_lt_succ hjlt⟩ ≤ t := by
        intro hle
        have hmem : (⟨j.val + 1, Nat.succ_lt_succ hjlt⟩ : Fin (m + 1))
            ∈ Finset.univ.filter (fun j' : Fin (m + 1) => l j' ≤ t) := by
          simp [hle]
        have hle' := Finset.le_max' _ _ hmem
        rw [← hj] at hle'
        have hle'' : j.val + 1 ≤ j.val := hle'
        omega
      exact (not_le.mp hnot).le

def intervalComplex (hG : ∀ k, 0 < G.n k) (j : Fin d) :
    GroupComplex d G.box (Finset.univ.filter (fun k => k = j)) where
  ι := Fin (G.n j)
  count := G.n j
  enum := Equiv.refl _
  cell i := {x | G.line j i.castSucc ≤ x j ∧ x j ≤ G.line j i.succ}
  isClosed_cell := fun i =>
    (isClosed_le continuous_const (continuous_apply j)).inter
      (isClosed_le (continuous_apply j) continuous_const)
  interior_disjoint := by
    intro i i' hne
    have hband : ∀ i₀ : Fin (G.n j),
        interior {x : Fin d → ℝ |
            G.line j i₀.castSucc ≤ x j ∧ x j ≤ G.line j i₀.succ}
          = {x : Fin d → ℝ |
              x j ∈ Set.Ioo (G.line j i₀.castSucc) (G.line j i₀.succ)} := by
      intro i₀
      have h : {x : Fin d → ℝ |
            G.line j i₀.castSucc ≤ x j ∧ x j ≤ G.line j i₀.succ}
          = {x : Fin d → ℝ |
              x j ∈ Set.Icc (G.line j i₀.castSucc) (G.line j i₀.succ)} := rfl
      rw [h, interior_coord_band, interior_Icc]
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [hband i] at hx
    rw [hband i'] at hx'
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hle : G.line j i.succ ≤ G.line j i'.castSucc :=
        (G.mono j).monotone (Fin.succ_le_castSucc_iff.mpr hlt)
      exact absurd (hx.2.trans_le hle) (not_lt.mpr hx'.1.le)
    · have hle : G.line j i'.succ ≤ G.line j i.castSucc :=
        (G.mono j).monotone (Fin.succ_le_castSucc_iff.mpr hlt)
      exact absurd (hx'.2.trans_le hle) (not_lt.mpr hx.1.le)
  cylinder := by
    intro i x y hxy hx
    have hj : x j = y j :=
      hxy j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, rfl⟩)
    rw [Set.mem_setOf_eq, ← hj]
    exact hx
  cell_subset := by
    intro i x hx k hk
    have hkj : k = j := (Finset.mem_filter.mp hk).2
    subst hkj
    rcases hx with ⟨h₁, h₂⟩
    constructor
    · exact le_trans ((G.mono k).monotone (Fin.zero_le _)) h₁
    · exact le_trans h₂ ((G.mono k).monotone (Fin.le_last _))
  covers := by
    intro x hx
    have hj : G.line j 0 ≤ x j ∧ x j ≤ G.line j (Fin.last (G.n j)) :=
      hx j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, rfl⟩)
    exact exists_interval (hG j) (G.line j) (G.mono j).monotone hj.1 hj.2

def gridLeaf (hG : ∀ k, 0 < G.n k) : Leaf d G.box where
  g := d
  grp := fun k => k
  cx := fun j => G.intervalComplex hG j

theorem gridLeaf_cell (hG : ∀ k, 0 < G.n k)
    (c : (G.gridLeaf hG).CellIdx) :
    (G.gridLeaf hG).cell c = G.Cell c := by
  ext x
  rw [Leaf.mem_cell_iff]
  constructor
  · intro h k
    exact h k
  · intro h j
    exact h j

theorem gridEmbed_region (hG : ∀ k, 0 < G.n k) (S : Finset G.CellIdx) :
    (PatchTree.leaf (G.gridLeaf hG)).region (fun c => c ∈ S)
      = G.blockRegion S := by
  ext x
  rw [PatchTree.mem_region_iff]
  unfold blockRegion
  constructor
  · rintro ⟨c, hcS, hc⟩
    have hc' : x ∈ (G.gridLeaf hG).cell c := hc
    rw [G.gridLeaf_cell hG c] at hc'
    exact Set.mem_iUnion₂.mpr ⟨c, hcS, hc'⟩
  · intro hx
    rcases Set.mem_iUnion₂.mp hx with ⟨c, hcS, hc⟩
    refine ⟨c, hcS, ?_⟩
    show x ∈ (G.gridLeaf hG).cell c
    rw [G.gridLeaf_cell hG c]
    exact hc

theorem enumCells_gridLeaf_val (hG : ∀ k, 0 < G.n k)
    (c : G.CellIdx) :
    (((PatchTree.leaf (G.gridLeaf hG)).enumCells c : Fin _) : ℕ)
      = ∑ k : Fin d, (c k : ℕ) * ∏ k' : Fin k.val,
          G.n (Fin.castLE k.is_lt.le k') := by
  rw [show (PatchTree.leaf (G.gridLeaf hG)).enumCells c
      = finPiFinEquiv
          ((Equiv.piCongrRight fun j => ((G.gridLeaf hG).cx j).enum) c)
    from rfl, finPiFinEquiv_apply]
  rfl

end BoxGrid

section Rgs

def IsRGS {d : ℕ} (s : Fin d → ℕ) : Prop :=
  ∀ k : Fin d, s k ≤ (Finset.univ.filter fun j => j < k).sup fun j => s j + 1

instance {d : ℕ} (s : Fin d → ℕ) : Decidable (IsRGS s) := by
  unfold IsRGS
  infer_instance

structure CanonicalPartition (d : ℕ) where
  g : ℕ
  grp : Fin d → Fin g
  surj : Function.Surjective grp
  rgs : IsRGS fun k => (grp k : ℕ)

theorem IsRGS.attained {d : ℕ} {s : Fin d → ℕ} (h : IsRGS s) {v : ℕ}
    (hv : ∃ k, v ≤ s k) : ∃ k, s k = v := by
  classical
  have hne : (Finset.univ.filter fun k => v ≤ s k).Nonempty := by
    obtain ⟨kw, hkw⟩ := hv
    exact ⟨kw, by simp [hkw]⟩
  set k₀ := (Finset.univ.filter fun k => v ≤ s k).min' hne with hk₀def
  have hk₀mem : k₀ ∈ Finset.univ.filter fun k => v ≤ s k :=
    Finset.min'_mem _ hne
  have hk₀v : v ≤ s k₀ := (Finset.mem_filter.mp hk₀mem).2
  refine ⟨k₀, le_antisymm ?_ hk₀v⟩
  refine (h k₀).trans (Finset.sup_le fun j hj => ?_)
  have hjlt : j < k₀ := (Finset.mem_filter.mp hj).2
  have hjv : s j < v := by
    by_contra hge
    have hmem : j ∈ Finset.univ.filter fun k => v ≤ s k := by
      simp [not_lt.mp hge]
    exact absurd (Finset.min'_le _ _ hmem) (not_le.mpr hjlt)
  omega

def rgsDecode {d : ℕ} (s : Fin d → ℕ) (hs : IsRGS s) :
    CanonicalPartition d where
  g := Finset.univ.sup fun k => s k + 1
  grp k := ⟨s k, by
    have h := Finset.le_sup (f := fun k => s k + 1) (Finset.mem_univ k)
    omega⟩
  surj := by
    intro v
    obtain ⟨v, hv⟩ := v
    have hex : ∃ k, v ≤ s k := by
      obtain ⟨k, -, hk⟩ := Finset.lt_sup_iff.mp hv
      exact ⟨k, Nat.lt_succ_iff.mp hk⟩
    obtain ⟨k, hk⟩ := hs.attained hex
    exact ⟨k, Fin.ext hk⟩
  rgs := hs

theorem CanonicalPartition.ext' {d : ℕ} {P Q : CanonicalPartition d}
    (hg : P.g = Q.g) (hgrp : ∀ k, (P.grp k : ℕ) = (Q.grp k : ℕ)) :
    P = Q := by
  obtain ⟨g₁, grp₁, s₁, r₁⟩ := P
  obtain ⟨g₂, grp₂, s₂, r₂⟩ := Q
  dsimp at hg hgrp
  subst hg
  have hfun : grp₁ = grp₂ := funext fun k => Fin.ext (hgrp k)
  subst hfun
  rfl

def rgsEquiv (d : ℕ) : {s : Fin d → ℕ // IsRGS s} ≃ CanonicalPartition d where
  toFun s := rgsDecode s.1 s.2
  invFun P := ⟨fun k => (P.grp k : ℕ), P.rgs⟩
  left_inv s := by
    apply Subtype.ext
    funext k
    simp [rgsDecode]
  right_inv P := by
    refine CanonicalPartition.ext' ?_ fun k => by simp [rgsDecode]
    apply le_antisymm
    · show (Finset.univ.sup fun k => (P.grp k : ℕ) + 1) ≤ P.g
      exact Finset.sup_le fun k _ => by have := (P.grp k).isLt; omega
    · show P.g ≤ Finset.univ.sup fun k => (P.grp k : ℕ) + 1
      by_cases hg0 : P.g = 0
      · exact le_of_eq_of_le hg0 (Nat.zero_le _)
      · obtain ⟨k, hk⟩ :=
          P.surj ⟨P.g - 1, Nat.sub_lt (Nat.pos_of_ne_zero hg0) Nat.one_pos⟩
        have hval : (P.grp k : ℕ) = P.g - 1 := by rw [hk]
        have hle :=
          Finset.le_sup (f := fun k => (P.grp k : ℕ) + 1) (Finset.mem_univ k)
        omega

end Rgs

section PartitionBridge

def CanonicalPartition.fiber {d : ℕ} (P : CanonicalPartition d)
    (j : Fin P.g) : Finset (Fin d) :=
  Finset.univ.filter fun k => P.grp k = j

theorem CanonicalPartition.fiber_nonempty {d : ℕ}
    (P : CanonicalPartition d) (j : Fin P.g) : (P.fiber j).Nonempty := by
  obtain ⟨k, hk⟩ := P.surj j
  exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩

def CanonicalPartition.toLeaf {d : ℕ} (P : CanonicalPartition d)
    (B : Box d) (cx : ∀ j : Fin P.g,
      GroupComplex d B (Finset.univ.filter fun k => P.grp k = j)) :
    Leaf d B where
  g := P.g
  grp := P.grp
  cx := cx

@[simp] theorem CanonicalPartition.toLeaf_g {d : ℕ}
    (P : CanonicalPartition d) (B : Box d) (cx : ∀ j : Fin P.g,
      GroupComplex d B (Finset.univ.filter fun k => P.grp k = j)) :
    (P.toLeaf B cx).g = P.g := rfl

@[simp] theorem CanonicalPartition.toLeaf_grp {d : ℕ}
    (P : CanonicalPartition d) (B : Box d) (cx : ∀ j : Fin P.g,
      GroupComplex d B (Finset.univ.filter fun k => P.grp k = j)) :
    (P.toLeaf B cx).grp = P.grp := rfl

def Leaf.ofRGS {d : ℕ} (B : Box d) (s : Fin d → ℕ) (hs : IsRGS s)
    (cx : ∀ j : Fin (rgsDecode s hs).g,
      GroupComplex d B
        (Finset.univ.filter fun k => (rgsDecode s hs).grp k = j)) :
    Leaf d B :=
  (rgsDecode s hs).toLeaf B cx

def Leaf.Canonical {d : ℕ} {B : Box d} (L : Leaf d B) : Prop :=
  Function.Surjective L.grp ∧ IsRGS fun k => (L.grp k : ℕ)

theorem CanonicalPartition.toLeaf_canonical {d : ℕ}
    (P : CanonicalPartition d) (B : Box d) (cx : ∀ j : Fin P.g,
      GroupComplex d B (Finset.univ.filter fun k => P.grp k = j)) :
    (P.toLeaf B cx).Canonical :=
  ⟨P.surj, P.rgs⟩

def Leaf.toCanonicalPartition {d : ℕ} {B : Box d} (L : Leaf d B)
    (h : L.Canonical) : CanonicalPartition d :=
  ⟨L.g, L.grp, h.1, h.2⟩

theorem CanonicalPartition.toLeaf_toCanonicalPartition {d : ℕ}
    (P : CanonicalPartition d) (B : Box d) (cx : ∀ j : Fin P.g,
      GroupComplex d B (Finset.univ.filter fun k => P.grp k = j)) :
    (P.toLeaf B cx).toCanonicalPartition (P.toLeaf_canonical B cx) = P :=
  rfl

theorem Leaf.Canonical.fiber_nonempty {d : ℕ} {B : Box d} {L : Leaf d B}
    (h : L.Canonical) (j : Fin L.g) :
    (Finset.univ.filter fun k => L.grp k = j).Nonempty :=
  (L.toCanonicalPartition h).fiber_nonempty j

theorem Leaf.boxLeaf_canonical {d : ℕ} (hd : 0 < d) (B : Box d) :
    (Leaf.boxLeaf d B).Canonical := by
  refine ⟨fun j => ⟨⟨0, hd⟩, ?_⟩, fun k => Nat.zero_le _⟩
  show (0 : Fin 1) = j
  exact Subsingleton.elim _ _

theorem BoxGrid.gridLeaf_canonical {d : ℕ} (G : BoxGrid d)
    (hG : ∀ k, 0 < G.n k) : (G.gridLeaf hG).Canonical := by
  refine ⟨fun j => ⟨j, rfl⟩, ?_⟩
  intro k
  show (k : ℕ) ≤ (Finset.univ.filter fun j => j < k).sup
    fun j : Fin d => (j : ℕ) + 1
  rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | hpos
  · exact le_trans (le_of_eq h0) (Nat.zero_le _)
  · have hk : (k : ℕ) - 1 < d := lt_of_le_of_lt (Nat.sub_le _ _) k.isLt
    have hlt : (⟨(k : ℕ) - 1, hk⟩ : Fin d) < k := by
      show (k : ℕ) - 1 < (k : ℕ)
      omega
    have hmem : (⟨(k : ℕ) - 1, hk⟩ : Fin d) ∈
        Finset.univ.filter fun j : Fin d => j < k :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
    have hle := Finset.le_sup (f := fun j : Fin d => (j : ℕ) + 1) hmem
    refine le_trans ?_ hle
    show (k : ℕ) ≤ (k : ℕ) - 1 + 1
    omega

theorem Leaf.not_canonical_counterexample (B₁ : Box 1) :
    ¬ (Leaf.Canonical
        (⟨2, fun _ => 0, fun _ => trivialComplex 1 B₁ _⟩ : Leaf 1 B₁)) := by
  rintro ⟨hsurj, -⟩
  obtain ⟨k, hk⟩ := hsurj 1
  have h01 : (0 : Fin 2) = 1 := hk
  exact absurd h01 (by decide)

end PartitionBridge

end GridCx
end Qtsl
