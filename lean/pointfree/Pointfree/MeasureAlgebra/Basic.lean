import Pointfree.Valuation.Bridge

/-! # The measure algebra: the null-quotient face of the bridge

The classical presentation of the point-free object: measurable sets
modulo almost-everywhere equality, with the descended mass.  This is
the measure algebra of a measure space in the sense of the classical
treatises (Fremlin, *Measure Theory*, vol. 3: 321A for the abstract
notion, 321H for this quotient construction); the point of building it
*here* is the bridge:

> **τ-additivity — Scott continuity of the restriction to opens — is
> exactly what makes the open-class map order-continuous into the
> quotient.**

`isLUB_ofOpen_sSup` states this: on a second-countable space, for a
finite measure, the null class of a directed union of opens is the
least upper bound of the null classes — the same Fremlin 414O content
as `Measure.toValuation_isScottContinuous`, read on the null-quotient
side.  Null distinctions are quotiented *structurally*, before any
bookkeeping: the classical face carries exactly the information the
valuation face carries, organized as an order.

This module deliberately stops at the partial order: the Boolean
operations descend by the same congruences (`EventuallyEq.union` and
kin) and the completeness of the quotient for finite measures is
classical (Fremlin 322C, 322Ae), but neither is needed to state the
bridge, so both are left to a successor rung along with countable
additivity of the descended mass.
-/

namespace Pointfree

open MeasureTheory TopologicalSpace
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- The almost-everywhere setoid on measurable sets. -/
def aeSetoid (μ : Measure X) : Setoid {s : Set X // MeasurableSet s} where
  r s t := (s : Set X) =ᵐ[μ] (t : Set X)
  iseqv := ⟨fun _ => Filter.EventuallyEq.rfl, Filter.EventuallyEq.symm,
    Filter.EventuallyEq.trans⟩

/-- The **measure algebra** of a measure: measurable sets modulo null
symmetric difference (Fremlin 321H). -/
def MeasureAlgebra (μ : Measure X) : Type _ := Quotient (aeSetoid μ)

namespace MeasureAlgebra

variable {μ : Measure X}

/-- The null class of a measurable set. -/
def mk (μ : Measure X) (s : Set X) (hs : MeasurableSet s) : MeasureAlgebra μ :=
  Quotient.mk (aeSetoid μ) ⟨s, hs⟩

theorem mk_eq_mk {s t : Set X} {hs : MeasurableSet s} {ht : MeasurableSet t} :
    mk μ s hs = mk μ t ht ↔ s =ᵐ[μ] t :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- The descended mass: measure is constant on null classes. -/
def mass : MeasureAlgebra μ → ℝ≥0∞ :=
  Quotient.lift (fun s => μ (s : Set X)) fun _ _ h => measure_congr h

@[simp] theorem mass_mk (s : Set X) (hs : MeasurableSet s) :
    mass (mk μ s hs) = μ s := rfl

/-- Null classes are ordered by almost-everywhere inclusion. -/
instance : LE (MeasureAlgebra μ) :=
  ⟨Quotient.lift₂ (fun s t => (s : Set X) ≤ᵐ[μ] (t : Set X))
    fun _ _ _ _ ha hb =>
      propext ⟨fun H => H.congr ha hb, fun H => H.congr ha.symm hb.symm⟩⟩

theorem mk_le_mk {s t : Set X} {hs : MeasurableSet s} {ht : MeasurableSet t} :
    mk μ s hs ≤ mk μ t ht ↔ s ≤ᵐ[μ] t :=
  Iff.rfl

instance : PartialOrder (MeasureAlgebra μ) where
  le_refl a := Quotient.inductionOn a fun _ => Filter.EventuallyLE.refl _ _
  le_trans a b c := Quotient.inductionOn₃ a b c fun _ _ _ h₁ h₂ =>
    Filter.EventuallyLE.trans h₁ h₂
  le_antisymm a b := Quotient.inductionOn₂ a b fun _ _ h₁ h₂ =>
    Quotient.sound (Filter.EventuallyLE.antisymm h₁ h₂)

/-- The zero class. -/
instance : OrderBot (MeasureAlgebra μ) where
  bot := mk μ ∅ MeasurableSet.empty
  bot_le a := Quotient.inductionOn a fun s =>
    show (∅ : Set X) ≤ᵐ[μ] (s : Set X) from
      ae_le_set.mpr (by rw [Set.empty_sdiff]; exact measure_empty)

theorem bot_def : (⊥ : MeasureAlgebra μ) = mk μ ∅ MeasurableSet.empty := rfl

/-- **Strict positivity by construction** (Fremlin 321A's third clause,
free on the quotient): a class has mass zero exactly when it is the
zero class. -/
theorem mass_eq_zero_iff {a : MeasureAlgebra μ} : mass a = 0 ↔ a = ⊥ := by
  induction a using Quotient.inductionOn with
  | h s =>
    constructor
    · intro h
      exact Quotient.sound (ae_eq_empty.mpr h)
    · intro h
      exact ae_eq_empty.mp (Quotient.exact h)

variable [TopologicalSpace X] [OpensMeasurableSpace X]

/-- The null class of an open set: the map whose order-continuity is
the bridge. -/
def ofOpen (μ : Measure X) (U : Opens X) : MeasureAlgebra μ :=
  mk μ (U : Set X) U.isOpen.measurableSet

theorem ofOpen_mono {U V : Opens X} (h : U ≤ V) :
    ofOpen μ U ≤ ofOpen μ V := by
  refine mk_le_mk.mpr (ae_le_set.mpr ?_)
  rw [Set.sdiff_eq_empty.mpr (SetLike.coe_subset_coe.mpr h)]
  exact measure_empty

/-- **The bridge, on the null-quotient side**: for a finite measure on
a second-countable space, the class of a directed union of opens is
the least upper bound of the classes.  The content is Fremlin 414O —
τ-additivity — consumed through the valuation face
(`Measure.toValuation_isScottContinuous`): Scott continuity of the
restriction to opens and order-continuity of the open-class map are
the same hypothesis read on the two faces of the object. -/
theorem isLUB_ofOpen_sSup [SecondCountableTopology X] [IsFiniteMeasure μ]
    {d : Set (Opens X)} (hd : d.Nonempty) (hdir : DirectedOn (· ≤ ·) d) :
    IsLUB (ofOpen μ '' d) (ofOpen μ (sSup d)) := by
  constructor
  · -- upper bound: each open sits inside the union outright
    rintro _ ⟨U, hU, rfl⟩
    refine mk_le_mk.mpr (ae_le_set.mpr ?_)
    have hsub : ((U : Opens X) : Set X) \ ((sSup d : Opens X) : Set X) = ∅ :=
      Set.sdiff_eq_empty.mpr
        (by rw [Opens.coe_sSup]; exact Set.subset_biUnion_of_mem hU)
    rw [hsub]
    exact measure_empty
  · -- least: τ-additivity, through the valuation face
    intro b hb
    induction b using Quotient.inductionOn with
    | h t =>
      refine mk_le_mk.mpr (ae_le_set.mpr ?_)
      have hub : ∀ U ∈ d, μ ((U : Set X) \ (t : Set X)) = 0 := fun U hU =>
        ae_le_set.mp (mk_le_mk.mp (hb (Set.mem_image_of_mem _ hU)))
      -- Scott continuity of the restriction: the mass of the union is
      -- the supremum of the masses
      have hscott := μ.toValuation_isScottContinuous d hd hdir
      -- every member's mass is carried inside `t`
      have hUt : ∀ U ∈ d, μ (U : Set X) ≤ μ (((sSup d : Opens X) : Set X) ∩ t) := by
        intro U hU
        have hsplit := measure_inter_add_sdiff (μ := μ) (U : Set X) t.2
        rw [hub U hU, add_zero] at hsplit
        rw [← hsplit]
        refine measure_mono (Set.inter_subset_inter_left _ ?_)
        rw [Opens.coe_sSup]
        exact Set.subset_biUnion_of_mem hU
      have hsup : μ (((sSup d : Opens X) : Set X))
          ≤ μ (((sSup d : Opens X) : Set X) ∩ t) := by
        rw [show μ (((sSup d : Opens X) : Set X))
            = μ.toValuation (sSup d) from rfl, hscott]
        exact iSup₂_le hUt
      have hsplit := measure_inter_add_sdiff (μ := μ)
        (((sSup d : Opens X) : Set X)) t.2
      have hcancel : μ (((sSup d : Opens X) : Set X) ∩ t)
            + μ (((sSup d : Opens X) : Set X) \ t)
          ≤ μ (((sSup d : Opens X) : Set X) ∩ t) + 0 := by
        rw [add_zero, hsplit]
        exact hsup
      exact le_antisymm
        ((ENNReal.add_le_add_iff_left (measure_ne_top μ _)).mp hcancel)
        zero_le

end MeasureAlgebra

end Pointfree
