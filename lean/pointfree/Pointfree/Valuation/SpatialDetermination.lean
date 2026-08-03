import Pointfree.Valuation.Determination
import Pointfree.Valuation.Bridge

/-! # The spatial shadow of determination

The frame-general determination theorem
(`Pointfree.Valuation.ext_of_generators`), instantiated at the frame
of opens of an arbitrary topological space: a meet-closed family of
opens whose underlying sets form a topological basis determines
Scott-continuous valuations from generator values.

Against the point-set capacity theorems this strengthens the
frame-level hypothesis class: the landed spatial determination for
Scott-continuous functionals assumes agreement on all *finite joins*
of generators; for valuations, modularity manufactures the finite
joins from single generators.  And against the measure-level π–λ
route it trades the σ-algebra, `BorelSpace`, and countability
hypotheses for Scott continuity — which, by the bridge, every Borel
measure on a second-countable space possesses (τ-additivity).  The
measure-level corollary accordingly concludes agreement of the
*restrictions to opens* (`Measure.toValuation`); recovering equality
of Borel measures from open-agreement is the σ-algebra step, which
belongs to the point-set stack and is not re-proven here.
-/

namespace Pointfree

open scoped ENNReal
open TopologicalSpace

namespace Valuation

variable {X : Type*} [TopologicalSpace X] {κ : Type*} {N : κ → Opens X}

/-- A topological basis join-generates the frame of opens: the
generation hypothesis of the determination theorem, spatially. -/
theorem opens_eq_iSup_of_isTopologicalBasis
    (hB : IsTopologicalBasis (Set.range fun i => (N i : Set X)))
    (U : Opens X) :
    U = ⨆ i ∈ {i | (N i : Set X) ⊆ (U : Set X)}, N i := by
  apply le_antisymm
  · rw [SetLike.le_def]
    intro x hx
    obtain ⟨b, ⟨i, rfl⟩, hxb, hbU⟩ :=
      hB.exists_subset_of_mem_open hx U.isOpen
    have : x ∈ (⨆ i ∈ {i | (N i : Set X) ⊆ (U : Set X)}, N i : Opens X) := by
      simp only [Opens.mem_iSup]
      exact ⟨i, hbU, hxb⟩
    exact this
  · exact iSup₂_le fun i hi => by
      rw [← SetLike.coe_subset_coe]
      exact hi

/-- **Spatial determination from generator values**: on any
topological space, two Scott-continuous valuations on the opens with
finite generator values, agreeing on a meet-closed family whose
underlying sets form a topological basis, are equal.  No countability
and no σ-algebra: Scott continuity does the work the π–λ theorem does
classically. -/
theorem ext_of_isTopologicalBasis
    (hB : IsTopologicalBasis (Set.range fun i => (N i : Set X)))
    (hNinf : ∀ i j, ∃ k, N i ⊓ N j = N k)
    {μ ν : Valuation (Opens X)}
    (hμS : μ.IsScottContinuous) (hνS : ν.IsScottContinuous)
    (hfin : ∀ i, μ (N i) ≠ ∞)
    (h : ∀ i, μ (N i) = ν (N i)) : μ = ν :=
  ext_of_generators hμS hνS hNinf
    (fun U => ⟨{i | (N i : Set X) ⊆ (U : Set X)},
      opens_eq_iSup_of_isTopologicalBasis hB U⟩)
    hfin h

/-- **Separation, spatially**: two distinct Scott-continuous
valuations on the opens with finite generator values are separated by
a single basis member. -/
theorem exists_basis_ne
    (hB : IsTopologicalBasis (Set.range fun i => (N i : Set X)))
    (hNinf : ∀ i j, ∃ k, N i ⊓ N j = N k)
    {μ ν : Valuation (Opens X)}
    (hμS : μ.IsScottContinuous) (hνS : ν.IsScottContinuous)
    (hfin : ∀ i, μ (N i) ≠ ∞)
    (hne : μ ≠ ν) : ∃ i, μ (N i) ≠ ν (N i) :=
  exists_generator_ne hμS hνS hNinf
    (fun U => ⟨{i | (N i : Set X) ⊆ (U : Set X)},
      opens_eq_iSup_of_isTopologicalBasis hB U⟩)
    hfin hne

end Valuation

/-- **The measure-level tie, through the bridge**: on a
second-countable space, two Borel measures with finite basis values
agreeing on a meet-closed topological basis of opens have equal
restrictions to the frame of opens.  Scott continuity is the bridge's
τ-additivity; no π–λ, no `BorelSpace`, no measurable-space structure
on the conclusion — which is deliberately valuation-level (agreement
on every open), the σ-algebra step being the point-set stack's own
business. -/
theorem _root_.MeasureTheory.Measure.toValuation_ext_of_isTopologicalBasis
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopology X] {κ : Type*} {N : κ → Opens X}
    (hB : TopologicalSpace.IsTopologicalBasis (Set.range fun i => (N i : Set X)))
    (hNinf : ∀ i j, ∃ k, N i ⊓ N j = N k)
    {μ ν : MeasureTheory.Measure X}
    (hfin : ∀ i, μ (N i : Set X) ≠ ∞)
    (h : ∀ i, μ (N i : Set X) = ν (N i : Set X)) :
    μ.toValuation = ν.toValuation :=
  Valuation.ext_of_isTopologicalBasis hB hNinf
    (μ.toValuation_isScottContinuous) (ν.toValuation_isScottContinuous)
    (fun i => hfin i) (fun i => h i)

end Pointfree
