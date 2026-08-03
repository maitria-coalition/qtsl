import Pointfree.Valuation.Functor
import Mathlib.Order.Filter.Ultrafilter.Basic

/-! # The escape witness, point-free: witnesses need not be points

The classical escape phenomenon — a sequence of Dirac measures marching
to infinity has no narrow limit — is usually stated with an escaping
sequence of *points*.  Point-free, the phenomenon needs no points at
all: it is the **failure of Scott continuity** for a finitely-additive
valuation, and the witness is a **directed family of opens** (a
hyperspace-flavored object) whose valuation supremum undershoots the
mass of its union.

The valuation is the 0–1 indicator of a free ultrafilter — the
point-free face of a finitely additive `{0,1}`-measure.  Its
modularity is the sealed dagger indicator's modularity
(`daggerInd_modular`) plus the ultrafilter laws for union and
intersection membership; no σ-algebra, no points.  Against the
directed family of all *finite* subsets (union `⊤`, each of valuation
`0` by freeness, mass `1`) Scott continuity fails outright.

Two faces complete the picture:

* the **principal** case is Scott continuous — the ultrafilter
  valuation of `pure a` *is* the Dirac valuation of the frame point of
  `a` — so freeness is exactly the load the refusal carries;
* the escaping Dirac net *does* converge along the free ultrafilter
  itself, to the ultrafilter valuation (`tendsto_dirac_hyperfilter`):
  the mass classical analysis loses to infinity is caught, point-free,
  by the finitely-additive limit object.  σ-additivity (Scott
  continuity, τ-additivity) is precisely what the narrow carrier
  refuses to extend to it.
-/

namespace Pointfree

open Filter TopologicalSpace
open scoped ENNReal Topology

variable {α : Type*}

/-- The frame point of an honest point: membership, as a frame
homomorphism `Set α → Prop` (the `Set` face of the bridge's
`pointHom`). -/
def setPoint (a : α) : FrameHom (Set α) Prop where
  toFun U := a ∈ U
  map_inf' U V := propext ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩
  map_top' := propext ⟨fun _ => trivial, fun _ => Set.mem_univ a⟩
  map_sSup' s := by
    apply propext
    rw [sSup_Prop_eq]
    constructor
    · intro h
      obtain ⟨U, hU, haU⟩ := Set.mem_sUnion.mp (by rwa [← Set.sSup_eq_sUnion])
      exact ⟨a ∈ U, ⟨U, hU, rfl⟩, haU⟩
    · rintro ⟨q, ⟨U, hU, rfl⟩, haU⟩
      rw [Set.sSup_eq_sUnion]
      exact Set.mem_sUnion.mpr ⟨U, hU, haU⟩

@[simp] theorem setPoint_apply (a : α) (U : Set α) :
    setPoint a U = (a ∈ U) := rfl

namespace Valuation

/-- The **ultrafilter valuation**: the 0–1 indicator of membership in
an ultrafilter, as a valuation on the frame `Set α`.  Finitely
additive by the ultrafilter laws; the point-free face of a finitely
additive `{0,1}`-measure. -/
noncomputable def ofUltrafilter (𝒰 : Ultrafilter α) : Valuation (Set α) where
  toFun U := daggerInd 1 (U ∈ 𝒰)
  map_bot' := daggerInd_of_not (by
    rw [Set.bot_eq_empty]
    exact 𝒰.empty_notMem)
  monotone' := fun U V h => daggerInd_mono 1 fun hU => Filter.mem_of_superset hU h
  modular' := fun U V => by
    have h := daggerInd_modular (1 : ℝ≥0∞) (U ∈ 𝒰) (V ∈ 𝒰)
    rwa [show ((U ∈ 𝒰) ∨ (V ∈ 𝒰)) = ((U ⊔ V) ∈ 𝒰) from
        propext (Ultrafilter.union_mem_iff).symm,
      show ((U ∈ 𝒰) ∧ (V ∈ 𝒰)) = ((U ⊓ V) ∈ 𝒰) from
        propext (Filter.inter_mem_iff).symm] at h

@[simp] theorem ofUltrafilter_apply (𝒰 : Ultrafilter α) (U : Set α) :
    ofUltrafilter 𝒰 U = daggerInd 1 (U ∈ 𝒰) := rfl

@[simp] theorem ofUltrafilter_top (𝒰 : Ultrafilter α) :
    ofUltrafilter 𝒰 ⊤ = 1 :=
  daggerInd_of (by rw [Set.top_eq_univ]; exact Filter.univ_mem)

/-- **The principal face**: the ultrafilter valuation of a principal
ultrafilter is the Dirac valuation of the corresponding frame point.
Together with `Valuation.isScottContinuous_dirac`, this makes freeness
the exact load carried by the Scott-continuity refusal below: the
principal case is Scott continuous. -/
theorem ofUltrafilter_pure (a : α) :
    ofUltrafilter (pure a) = dirac (setPoint a) := by
  classical
  ext U
  rw [ofUltrafilter_apply, dirac_apply]
  by_cases h : a ∈ U
  · rw [daggerInd_of (Ultrafilter.mem_pure.mpr h),
      if_pos (show setPoint a U from h)]
  · rw [daggerInd_of_not fun hm => h (Ultrafilter.mem_pure.mp hm),
      if_neg (show ¬ setPoint a U from h)]

theorem isScottContinuous_ofUltrafilter_pure (a : α) :
    (ofUltrafilter (pure a)).IsScottContinuous :=
  ofUltrafilter_pure a ▸ isScottContinuous_dirac (setPoint a)

end Valuation

/-- The probability packaging of the ultrafilter valuation. -/
noncomputable def Prob.ofUltrafilter (𝒰 : Ultrafilter α) : Prob (Set α) :=
  ⟨Valuation.ofUltrafilter 𝒰, Valuation.ofUltrafilter_top 𝒰⟩

/-- **The escape witness, point-free (σ-additivity refusal)**: the free
ultrafilter valuation is not Scott continuous.  The witness is the
directed family of all finite subsets — a family of hyperspace
members, no escaping point sequence: its union is everything (mass
`1`), yet every member has valuation `0` by freeness.  The classical
escape witness (escaping Diracs with no narrow limit) is this
phenomenon's point-shadow. -/
theorem not_isScottContinuous_ofUltrafilter_hyperfilter [Infinite α] :
    ¬ (Valuation.ofUltrafilter (Filter.hyperfilter α)).IsScottContinuous := by
  intro h
  have hne : ({s : Set α | s.Finite}).Nonempty := ⟨∅, Set.finite_empty⟩
  have hdir : DirectedOn (· ≤ ·) {s : Set α | s.Finite} := fun s hs t ht =>
    ⟨s ∪ t, Set.Finite.union hs ht, Set.subset_union_left, Set.subset_union_right⟩
  have hkey := h _ hne hdir
  have hsup : sSup {s : Set α | s.Finite} = (⊤ : Set α) := by
    rw [Set.sSup_eq_sUnion, Set.top_eq_univ]
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_sUnion.mpr ⟨{x}, Set.finite_singleton x, Set.mem_singleton x⟩
  rw [hsup, Valuation.ofUltrafilter_top] at hkey
  have hzero : (⨆ s ∈ {s : Set α | s.Finite},
      Valuation.ofUltrafilter (Filter.hyperfilter α) s) ≤ 0 := by
    refine iSup₂_le fun s hs => ?_
    rw [Valuation.ofUltrafilter_apply,
      Valuation.daggerInd_of_not (Filter.notMem_hyperfilter_of_finite hs)]
  rw [← hkey] at hzero
  simp at hzero

/-- **The escaping mass is caught by the free ultrafilter**: the Dirac
net converges *along the ultrafilter* — in the lower topology of the
probability face — to the ultrafilter valuation.  What classical
analysis loses to infinity, the finitely-additive limit object holds;
Scott continuity is exactly what it lacks. -/
theorem tendsto_dirac_hyperfilter [Infinite α] :
    Tendsto (fun a : α => Prob.dirac (setPoint a))
      (Filter.hyperfilter α : Filter α) (𝓝 (Prob.ofUltrafilter (Filter.hyperfilter α))) := by
  classical
  rw [show (Prob.instTopologicalSpace (Set α) : TopologicalSpace (Prob (Set α)))
      = generateFrom (Prob.lowerGenerators (Set α)) from rfl]
  refine TopologicalSpace.tendsto_nhds_generateFrom_iff.mpr ?_
  rintro S ⟨U, r, rfl⟩ hmem
  -- the limit lies in the half-space: `r < daggerInd 1 (U ∈ 𝒰)`
  have hmem' : r < Valuation.daggerInd 1 (U ∈ Filter.hyperfilter α) := hmem
  by_cases hU : U ∈ Filter.hyperfilter α
  · -- the preimage contains `U` itself, and `U` is an ultrafilter member
    refine Filter.mem_of_superset hU ?_
    intro a haU
    show r < Prob.dirac (setPoint a) U
    rw [show (Prob.dirac (setPoint a) U : ℝ≥0∞) = Valuation.dirac (setPoint a) U from rfl,
      Valuation.dirac_apply, if_pos (show setPoint a U from haU)]
    rw [Valuation.daggerInd_of hU] at hmem'
    exact hmem'
  · -- impossible: the half-space would need `r < 0`
    rw [Valuation.daggerInd_of_not hU] at hmem'
    exact absurd hmem' (by simp)

end Pointfree
