import QtslAux.Imprecise.Containment
import QtslAux.Imprecise.MarginalCompatGeneral
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Containment, not identity: the general stratum

`Containment.lean` proves, at the finite-rational stratum, that the
additive composition law on penalties is more committal than the
least-committal glue of the component credal sets, with equality exactly
on the crisp locus and a strict two-graph witness.  This module states
the containment package at the *general* stratum — arbitrary carriers of
joint models, in particular subprobability measures over Polish spaces —
building on the carrier-agnostic penalty calculus of
`MarginalCompatGeneral`:

1. **Containment** (`sublevel_compositeG_subset_glueSetG`): the
   composite's denotation at every threshold lies inside the glue set —
   the set of joints whose marginals meet every component bound (the
   natural-extension set at that threshold,
   `glueSetG_eq_sublevel_supPenaltyG`).  Consequently a certificate
   established on the glue bounds the composite
   (`certificate_transfer`): the containment direction is the direction
   of soundness.
2. **The crisp locus, exactly** (`ENNRat.add_eq_max_iff`,
   `binaryComposite_eq_glue_iff`): the binary composite agrees with the
   glue at a joint iff the lesser penalty vanishes or the greater is
   `⊤`; a `{0, ⊤}`-valued (crisp) component forces equality everywhere
   (`binaryComposite_eq_glue_of_isCrisp_left`).  Denotations agree at
   every threshold iff the penalties agree (`forall_sublevel_eq_iff`).
3. **Strictness at the general stratum**
   (`binaryComposite_ne_glue`, `sublevel_ssubset_glue_witness`): off the
   crisp locus the containment is strict, witnessed here on the
   one-point carrier — a compact Polish space, so the witness already
   lives at the general stratum.  The semantically loaded instance
   (two single-edge dependency-graph models disagreeing about a shared
   binary variable, with exact-rational comparisons `81 > 80` and
   `729 ≤ 800`) is the finite-stratum witness
   `witness_containment_strict` of `Containment.lean`; finite discrete
   carriers are Polish, so it, too, is a general-stratum witness.
4. **Topological citizenship on measure carriers**
   (`isClosed_glueSetG`, `lowerSemicontinuous_addComposite`,
   `isClosed_pmGlueSet`): for lower semicontinuous component penalties
   and continuous marginal maps the glue set is closed — an intersection
   of preimages of sublevels — and the (ℝ≥0∞-valued) additive composite
   is again lower semicontinuous, so both sides of the containment are
   closed denotations; instantiated at probability-measure carriers with
   pushforward marginals along continuous projections.
-/

namespace Qtsl.Imprecise

open Finset Set
open scoped ENNReal

/-! ## Scalar crisp-locus arithmetic in `ENNRat` -/

/-- Absorption characterization in `ENNRat = WithTop ℚ≥0`:
`a + b = b` iff `a` vanishes or `b` is infinite. -/
theorem ENNRat.add_eq_right_iff (a b : ENNRat) :
    a + b = b ↔ a = 0 ∨ b = ⊤ := by
  constructor
  · intro h
    rcases eq_or_ne b ⊤ with rfl | hb
    · exact Or.inr rfl
    · left
      lift b to ℚ≥0 using hb
      rcases eq_or_ne a ⊤ with rfl | ha
      · exact absurd h (by simp)
      · lift a to ℚ≥0 using ha
        rw [← WithTop.coe_add, WithTop.coe_inj] at h
        have : a + b = 0 + b := by rwa [zero_add]
        exact_mod_cast congrArg WithTop.some (add_right_cancel this)
  · rintro (rfl | rfl)
    · exact zero_add b
    · exact add_top a

/-- The crisp-locus characterization of the t-norm collapse: the additive
law agrees with the glue at a pair of grades iff the lesser penalty is
zero or the greater is `⊤`. -/
theorem ENNRat.add_eq_max_iff (a b : ENNRat) :
    a + b = max a b ↔ min a b = 0 ∨ max a b = ⊤ := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h]
    exact ENNRat.add_eq_right_iff a b
  · rw [max_eq_left h, min_eq_right h, add_comm]
    exact ENNRat.add_eq_right_iff b a

/-! ## The glue set and containment displays -/

section General

variable {J : Type*} {ι : Type*} [Fintype ι] {Mi : ι → Type*}

/-- The glue set at a threshold: joints whose every marginal meets its
component bound.  This is the natural-extension set of the marginal
constraints at that threshold. -/
def glueSetG (m : ∀ i, J → Mi i) (f : ∀ i, Mi i → ENNRat) (F : ENNRat) :
    Set J :=
  {ν | ∀ i, f i (m i ν) ≤ F}

theorem glueSetG_eq_sublevel_supPenaltyG (m : ∀ i, J → Mi i)
    (f : ∀ i, Mi i → ENNRat) (F : ENNRat) :
    glueSetG m f F = {ν | supPenaltyG m f ν ≤ F} := by
  ext ν
  exact (supPenaltyG_le_iff m f ν).symm

/-- **Containment.**  At every threshold, the additive composite's
denotation is contained in the glue: the composition law is more
committal than the least-committal glue of the marginal constraints. -/
theorem sublevel_compositeG_subset_glueSetG (m : ∀ i, J → Mi i)
    (f : ∀ i, Mi i → ENNRat) (F : ENNRat) :
    {ν | compositePenaltyG m f ν ≤ F} ⊆ glueSetG m f F :=
  fun ν h i => sublevel_marginalG m f ν i h

/-- Certificates bound the glue, hence the composite: any property
established for every joint in the glue holds for every joint the
composite admits.  (The containment direction is the direction of
soundness: bounds transfer from the less committal object to the more
committal one, never conversely.) -/
theorem certificate_transfer (m : ∀ i, J → Mi i) (f : ∀ i, Mi i → ENNRat)
    (F : ENNRat) {P : J → Prop} (h : ∀ ν ∈ glueSetG m f F, P ν) :
    ∀ ν, compositePenaltyG m f ν ≤ F → P ν :=
  fun ν hν => h ν (sublevel_compositeG_subset_glueSetG m f F hν)

end General

/-! ## The binary crisp locus -/

section Binary

variable {J Y₁ Y₂ : Type*}

/-- A crisp penalty takes only the values `0` and `⊤` (a wall). -/
def IsCrisp (f : Y₁ → ENNRat) : Prop := ∀ y, f y = 0 ∨ f y = ⊤

/-- The binary additive composite agrees with the glue (the max) exactly
on the pointwise crisp locus. -/
theorem binaryComposite_eq_glue_iff (f₁ : Y₁ → ENNRat) (f₂ : Y₂ → ENNRat)
    (p₁ : J → Y₁) (p₂ : J → Y₂) :
    (∀ ν, f₁ (p₁ ν) + f₂ (p₂ ν) = max (f₁ (p₁ ν)) (f₂ (p₂ ν)))
      ↔ ∀ ν, min (f₁ (p₁ ν)) (f₂ (p₂ ν)) = 0
          ∨ max (f₁ (p₁ ν)) (f₂ (p₂ ν)) = ⊤ :=
  forall_congr' fun ν => ENNRat.add_eq_max_iff _ _

/-- A crisp component forces exactness of the additive law. -/
theorem binaryComposite_eq_glue_of_isCrisp_left {f₁ : Y₁ → ENNRat}
    (h : IsCrisp f₁) (f₂ : Y₂ → ENNRat) (p₁ : J → Y₁) (p₂ : J → Y₂) :
    ∀ ν, f₁ (p₁ ν) + f₂ (p₂ ν) = max (f₁ (p₁ ν)) (f₂ (p₂ ν)) := by
  intro ν
  refine (ENNRat.add_eq_max_iff _ _).mpr ?_
  rcases h (p₁ ν) with h0 | htop
  · left
    rw [h0]
    exact min_eq_left (ENNRat.zero_le' _)
  · right
    rw [htop]
    exact max_eq_left le_top

/-- Two `ENNRat`-valued penalties agree iff their denotations agree at
every threshold. -/
theorem forall_sublevel_eq_iff {g h : J → ENNRat} :
    (∀ F, {ν | g ν ≤ F} = {ν | h ν ≤ F}) ↔ g = h := by
  constructor
  · intro hs
    funext ν
    have h1 : g ν ≤ h ν := by
      have hmem : ν ∈ {ν' | h ν' ≤ h ν} := show h ν ≤ h ν from le_rfl
      rw [← hs (h ν)] at hmem
      exact hmem
    have h2 : h ν ≤ g ν := by
      have hmem : ν ∈ {ν' | g ν' ≤ g ν} := show g ν ≤ g ν from le_rfl
      rw [hs (g ν)] at hmem
      exact hmem
    exact le_antisymm h1 h2
  · rintro rfl _
    rfl

/-! ### Strictness, on a (one-point, hence Polish) general-stratum carrier

The semantically loaded strict witness — two dependency-graph models
disagreeing about a shared binary variable, with the exact-rational
comparisons `81 > 80` and `729 ≤ 800` — is the finite-stratum witness
`witness_containment_strict`; a finite discrete carrier is a compact
Polish space, so it is already a general-stratum witness.  The instance
below is the cheapest inhabitant of the same phenomenon: away from the
crisp locus, the containment is strict even on a one-point carrier. -/

/-- The additive law is *not* the glue at the general stratum: penalties
constantly `1` compose to `2`, while the glue is `1`. -/
theorem binaryComposite_ne_glue :
    (fun ν : Unit => (fun _ : Unit => (1 : ENNRat)) ν
        + (fun _ : Unit => (1 : ENNRat)) ν)
      ≠ fun ν : Unit => max ((fun _ : Unit => (1 : ENNRat)) ν)
          ((fun _ : Unit => (1 : ENNRat)) ν) := by
  intro h
  have h1 := congrFun h ()
  simp only [max_self] at h1
  rcases (ENNRat.add_eq_right_iff 1 1).mp h1 with h0 | htop
  · exact one_ne_zero h0
  · exact (WithTop.one_ne_top) htop

/-- Denotation-level strictness: at threshold `1`, the composite of two
unit penalties denotes the empty set while the glue denotes everything —
a strict inclusion on a compact Polish carrier. -/
theorem sublevel_ssubset_glue_witness :
    {ν : Unit | compositePenaltyG (fun _ : Bool => id)
        (fun _ : Bool => fun _ : Unit => (1 : ENNRat)) ν ≤ 1}
      ⊂ glueSetG (fun _ : Bool => id)
        (fun _ : Bool => fun _ : Unit => (1 : ENNRat)) 1 := by
  constructor
  · exact sublevel_compositeG_subset_glueSetG _ _ _
  · intro hsub
    have hmem : () ∈ glueSetG (fun _ : Bool => id)
        (fun _ : Bool => fun _ : Unit => (1 : ENNRat)) 1 :=
      fun _ => le_rfl
    have hcomp := hsub hmem
    have hval : compositePenaltyG (fun _ : Bool => id)
        (fun _ : Bool => fun _ : Unit => (1 : ENNRat)) () = 1 + 1 := by
      unfold compositePenaltyG
      rw [Fintype.sum_bool]
    rw [Set.mem_setOf_eq, hval] at hcomp
    have h1 : (1 : ENNRat) + 1 = 1 :=
      le_antisymm hcomp le_self_add
    rcases (ENNRat.add_eq_right_iff 1 1).mp h1 with h0 | htop
    · exact one_ne_zero h0
    · exact (WithTop.one_ne_top) htop

end Binary

/-! ## Topological citizenship -/

section Topology

variable {J : Type*} [TopologicalSpace J] {ι : Type*} [Fintype ι]
  {Mi : ι → Type*} [∀ i, TopologicalSpace (Mi i)]

omit [Fintype ι] in
/-- The glue set is closed whenever the component penalties are lower
semicontinuous and the marginal maps are continuous: it is an
intersection of preimages of closed sublevels.  (Lower semicontinuity
into `ENNRat` is purely order-theoretic; no topology on the value space
is consumed.) -/
theorem isClosed_glueSetG {m : ∀ i, J → Mi i} (hm : ∀ i, Continuous (m i))
    {f : ∀ i, Mi i → ENNRat} (hf : ∀ i, LowerSemicontinuous (f i))
    (F : ENNRat) : IsClosed (glueSetG m f F) := by
  have heq : glueSetG m f F = ⋂ i, m i ⁻¹' {p | f i p ≤ F} := by
    ext ν
    simp [glueSetG, Set.mem_iInter]
  rw [heq]
  exact isClosed_iInter fun i => ((hf i).isClosed_preimage F).preimage (hm i)

variable {Y₁ Y₂ : Type*} [TopologicalSpace Y₁] [TopologicalSpace Y₂]

/-- The `ℝ≥0∞`-valued binary additive composite of lower semicontinuous
penalties along continuous marginal maps is lower semicontinuous: both
sides of the containment are honest citizens on the general stratum. -/
theorem lowerSemicontinuous_addComposite {p₁ : J → Y₁} {p₂ : J → Y₂}
    (hp₁ : Continuous p₁) (hp₂ : Continuous p₂) {σ₁ : Y₁ → ℝ≥0∞}
    {σ₂ : Y₂ → ℝ≥0∞} (h₁ : LowerSemicontinuous σ₁)
    (h₂ : LowerSemicontinuous σ₂) :
    LowerSemicontinuous fun ν => σ₁ (p₁ ν) + σ₂ (p₂ ν) :=
  (h₁.comp hp₁).add (h₂.comp hp₂)

/-- The `ℝ≥0∞` containment display: the additive composite's sublevel is
inside the intersection of the marginal sublevels, at every threshold. -/
theorem sublevel_addComposite_subset {p₁ : J → Y₁} {p₂ : J → Y₂}
    (σ₁ : Y₁ → ℝ≥0∞) (σ₂ : Y₂ → ℝ≥0∞) (c : ℝ≥0∞) :
    {ν | σ₁ (p₁ ν) + σ₂ (p₂ ν) ≤ c}
      ⊆ (p₁ ⁻¹' {y | σ₁ y ≤ c}) ∩ (p₂ ⁻¹' {y | σ₂ y ≤ c}) :=
  fun ν h =>
    ⟨le_trans le_self_add (show σ₁ (p₁ ν) + σ₂ (p₂ ν) ≤ c from h),
     le_trans le_add_self (show σ₁ (p₁ ν) + σ₂ (p₂ ν) ≤ c from h)⟩

end Topology

section ProbabilityCarrier

open MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]
variable {Xi : ι → Type*} [∀ i, MeasurableSpace (Xi i)]
  [∀ i, TopologicalSpace (Xi i)] [∀ i, BorelSpace (Xi i)]

omit [Fintype ι] in
/-- Pushforward marginals along continuous projections are narrowly
continuous. -/
theorem continuous_pmMarginal {proj : ∀ i, X → Xi i}
    (hproj : ∀ i, Continuous (proj i)) (i : ι) :
    Continuous (pmMarginal proj (fun i => (hproj i).measurable) i) :=
  ProbabilityMeasure.continuous_map (hproj i)

/-- **Containment on the general stratum, with citizenship.**  On the
probability-measure carrier with pushforward marginals along continuous
projections, the glue set of lower semicontinuous component penalties is
narrowly closed, and the composite's denotation is contained in it at
every threshold. -/
theorem isClosed_pmGlueSet {proj : ∀ i, X → Xi i}
    (hproj : ∀ i, Continuous (proj i))
    {f : ∀ i, ProbabilityMeasure (Xi i) → ENNRat}
    (hf : ∀ i, LowerSemicontinuous (f i)) (F : ENNRat) :
    IsClosed (glueSetG (pmMarginal proj fun i => (hproj i).measurable) f F) :=
  isClosed_glueSetG (continuous_pmMarginal hproj) hf F

theorem sublevel_pmComposite_subset_glue {proj : ∀ i, X → Xi i}
    (hproj : ∀ i, Continuous (proj i))
    (f : ∀ i, ProbabilityMeasure (Xi i) → ENNRat) (F : ENNRat) :
    {ν | pmCompositePenalty proj (fun i => (hproj i).measurable) f ν ≤ F}
      ⊆ glueSetG (pmMarginal proj fun i => (hproj i).measurable) f F :=
  sublevel_compositeG_subset_glueSetG _ f F

end ProbabilityCarrier

end Qtsl.Imprecise
