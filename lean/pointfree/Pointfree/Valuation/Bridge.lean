import Pointfree.Valuation.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Sets.Opens

/-! # The bridge: Borel measures restrict to valuations

Restricting a Borel measure to the frame of opens yields a valuation —
strictness is `measure_empty`, monotonicity is `measure_mono`, and
modularity is exactly `measure_union_add_inter`.  This is the classical
face of the point-free stochastics tower, and the two sides exchange
theorems through it in both directions.

**Scott continuity is τ-additivity.**  The restriction is Scott
continuous precisely when the measure is τ-additive (directed unions of
opens are approximated from inside); on a second-countable space
*every* measure is τ-additive — the directed cover reduces to a
countable subcover (Lindelöf), which a countably additive measure
follows along a monotone chain.  This is Fremlin's 414O ("if X is a
hereditarily Lindelöf space then every measure on X is τ-additive",
*Measure Theory*, vol. 4), whose two-line proof is the same reduction;
second countability is this development's route to hereditarily Lindelöf.
Without a countability or regularity hypothesis, τ-additivity is
genuinely false for Borel measures (the Dieudonné measure on the
ordinal space `[0, ω₁]` is the classical witness, Fremlin 411Q), so the
hypothesis on this theorem is honest load, not convenience: the mutant
battery checks that dropping it breaks the proof at the Lindelöf step.

The Dirac bridge closes the square: the restriction of the classical
Dirac measure at a point is the point-free Dirac valuation of the
corresponding frame point.
-/

namespace Pointfree

open MeasureTheory TopologicalSpace
open scoped ENNReal

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The restriction of a Borel measure to the frame of opens, as a
valuation: modularity is `measure_union_add_inter`. -/
def _root_.MeasureTheory.Measure.toValuation (μ : Measure X) : Valuation (Opens X) where
  toFun U := μ U
  map_bot' := by
    rw [Opens.coe_bot]
    exact measure_empty
  monotone' := fun U V h => measure_mono (SetLike.coe_subset_coe.mpr h)
  modular' := fun U V => by
    rw [Opens.coe_sup, Opens.coe_inf]
    exact (measure_union_add_inter (μ := μ) (U : Set X)
      (V.isOpen.measurableSet)).symm

@[simp] theorem _root_.MeasureTheory.Measure.toValuation_apply
    (μ : Measure X) (U : Opens X) : μ.toValuation U = μ (U : Set X) := rfl

theorem _root_.MeasureTheory.Measure.toValuation_top (μ : Measure X) :
    μ.toValuation ⊤ = μ Set.univ := by
  rw [Measure.toValuation_apply, Opens.coe_top]

/-- A measure of total mass at most one restricts to a subprobability
valuation. -/
def _root_.MeasureTheory.Measure.toSubProb (μ : Measure X) (h : μ Set.univ ≤ 1) :
    SubProb (Opens X) :=
  ⟨μ.toValuation, by rw [Measure.toValuation_top]; exact h⟩

/-- A probability measure restricts to a probability valuation. -/
def _root_.MeasureTheory.Measure.toProb (μ : Measure X) [IsProbabilityMeasure μ] :
    Prob (Opens X) :=
  ⟨μ.toValuation, by rw [Measure.toValuation_top]; exact measure_univ⟩

/-! ## τ-additivity: Scott continuity on second-countable spaces -/

/-- **Every Borel measure on a second-countable space is τ-additive**,
point-free form: its restriction to opens is Scott continuous.  The
directed open cover reduces to a countable subcover (Lindelöf), and the
countable subfamily upgrades to a monotone chain inside the directed
family, along which countable additivity follows.

The countability hypothesis is honest load: for general topological
spaces τ-additivity fails (Dieudonné's measure on `[0, ω₁]`,
Fremlin 411Q). -/
theorem _root_.MeasureTheory.Measure.toValuation_isScottContinuous
    [SecondCountableTopology X] (μ : Measure X) :
    μ.toValuation.IsScottContinuous := by
  intro d hd hdir
  rw [Measure.toValuation_apply,
    show ((sSup d : Opens X) : Set X) = ⋃ U ∈ d, (U : Set X) from Opens.coe_sSup]
  apply le_antisymm
  · -- the hard leg: reduce to a countable subcover, then a chain
    rw [Set.biUnion_eq_iUnion]
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun i : ↥d => (i.1 : Set X)) (fun i => i.1.isOpen)
    rw [← hTU]
    rcases T.eq_empty_or_nonempty with hTe | hTne
    · simp [hTe]
    · obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
      -- the directed family upgrades the countable subfamily to a chain
      have hdir' : ∀ x y : ↥d, ∃ z : ↥d, x.1 ≤ z.1 ∧ y.1 ≤ z.1 := by
        intro x y
        obtain ⟨z, hz, h1, h2⟩ := hdir x.1 x.2 y.1 y.2
        exact ⟨⟨z, hz⟩, h1, h2⟩
      choose ub hub1 hub2 using hdir'
      let g : ℕ → ↥d := fun n => Nat.rec (f 0) (fun n gn => ub gn (f (n + 1))) n
      have hgsucc : ∀ n, g (n + 1) = ub (g n) (f (n + 1)) := fun _ => rfl
      have hgmono : Monotone fun n => ((g n).1 : Set X) := by
        apply monotone_nat_of_le_succ
        intro n
        exact SetLike.coe_subset_coe.mpr (by rw [hgsucc]; exact hub1 _ _)
      have hf_le : ∀ n, ((f n).1 : Set X) ⊆ ((g n).1 : Set X) := by
        intro n
        cases n with
        | zero => exact le_refl _
        | succ n =>
          exact SetLike.coe_subset_coe.mpr (by rw [hgsucc]; exact hub2 _ _)
      calc μ (⋃ i ∈ T, ((i.1 : Opens X) : Set X))
          = μ (⋃ n, ((f n).1 : Set X)) := by
            rw [hf, Set.biUnion_range]
        _ ≤ μ (⋃ n, ((g n).1 : Set X)) :=
            measure_mono (Set.iUnion_mono hf_le)
        _ = ⨆ n, μ ((g n).1 : Set X) := hgmono.measure_iUnion
        _ ≤ ⨆ U ∈ d, μ.toValuation U := by
            refine iSup_le fun n => ?_
            exact le_iSup₂ (f := fun U (_ : U ∈ d) => μ.toValuation U)
              (g n).1 (g n).2
  · -- the easy leg: every member sits inside the union
    refine iSup₂_le fun U hU => measure_mono ?_
    exact Set.subset_biUnion_of_mem hU

/-! ## Naturality: pushforward commutes with restriction -/

/-- The bridge is natural: pushing a measure forward along a continuous
map and restricting to opens is restricting first and transporting
along the frame homomorphism of preimages. -/
theorem _root_.MeasureTheory.Measure.toValuation_map
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) {f : X → Y} (hf : Continuous f) :
    (μ.map f).toValuation = μ.toValuation.map (Opens.comap ⟨f, hf⟩) := by
  ext U
  rw [Measure.toValuation_apply,
    Measure.map_apply hf.measurable (U.isOpen.measurableSet),
    Valuation.map_apply, Measure.toValuation_apply, Opens.coe_comap]
  rfl

/-! ## The Dirac bridge -/

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- The frame point of a topological point: membership, as a frame
homomorphism into `Prop`. -/
def pointHom (x : X) : FrameHom (Opens X) Prop where
  toFun U := x ∈ U
  map_inf' U V := by
    apply propext
    constructor
    · intro h
      rw [← SetLike.mem_coe, Opens.coe_inf] at h
      exact ⟨h.1, h.2⟩
    · rintro ⟨h1, h2⟩
      rw [← SetLike.mem_coe, Opens.coe_inf]
      exact ⟨h1, h2⟩
  map_top' := by
    apply propext
    constructor
    · intro _
      trivial
    · intro _
      rw [← SetLike.mem_coe, Opens.coe_top]
      exact Set.mem_univ x
  map_sSup' s := by
    apply propext
    rw [sSup_Prop_eq]
    constructor
    · intro h
      obtain ⟨U, hU, hxU⟩ := Opens.mem_sSup.mp h
      exact ⟨x ∈ U, ⟨U, hU, rfl⟩, hxU⟩
    · rintro ⟨q, ⟨U, hU, rfl⟩, hxU⟩
      exact Opens.mem_sSup.mpr ⟨U, hU, hxU⟩

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
@[simp]
theorem pointHom_apply (x : X) (U : Opens X) :
    pointHom x U = (x ∈ U) := rfl

/-- **The Dirac bridge**: the classical Dirac measure restricts to the
point-free Dirac valuation of the corresponding frame point. -/
theorem dirac_toValuation (x : X) :
    (Measure.dirac x).toValuation = Valuation.dirac (pointHom x) := by
  classical
  ext U
  rw [Measure.toValuation_apply, Valuation.dirac_apply,
    Measure.dirac_apply' x (U.isOpen.measurableSet)]
  by_cases hx : x ∈ U
  · rw [if_pos (show (pointHom x) U from hx),
      Set.indicator_of_mem (show x ∈ (U : Set X) from hx)]
    rfl
  · rw [if_neg (show ¬ (pointHom x) U from hx),
      Set.indicator_of_notMem (show x ∉ (U : Set X) from hx)]

end Pointfree
