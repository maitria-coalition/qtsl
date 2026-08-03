import Pointfree.Valuation.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.ENNReal.Real

/-! # Gambles and previsions over a frame

The prevision layer of the point-free stochastics tower: **gambles**
(lower-semicontinuous `ℝ≥0∞`-valued observables, carried in sublevel
presentation) and **previsions** (monotone functionals on gambles),
with the Choquet pairing against valuations, its naturality in frame
homomorphisms, and the superlinear (lower-envelope) class.

* A `Gamble L` is an antitone, right-continuous family
  `U : ℝ≥0∞ → L` of frame elements — the point-free face of the
  sublevel family `t ↦ {h > t}` of a lower-semicontinuous function.
  Right-continuity at `∞` forces `U ∞ = ⊥`, as it must (no observable
  exceeds `∞`).  Gambles add by sublevel convolution, transport
  covariantly along frame homomorphisms, and include the indicators of
  frame elements.
* The **Choquet pairing** `Valuation.pair` integrates the sublevel
  masses (the layer-cake formula, taken as definition).  It is linear
  in the valuation, monotone in both arguments, extends the valuation
  through indicators (`pair_indicator`), and is **natural**:
  `(μ.map φ).pair g = μ.pair (g.map φ)` — definitionally.
* A `Prevision L` is a monotone functional on gambles
  (Goubault-Larrecq's previsions, at the point-free stratum);
  `IsSuperadditive` carves the superlinear (lower/demonic) class, and
  `iInfEnvelope` shows that class closed under lower envelopes — the
  credal reading: a set of previsions presents its worst-case member.
  Every valuation gives a prevision through the pairing
  (`Valuation.toPrevision`), naturally.
* The **body** of a prevision — the subprobability valuations dominating
  it — and the cheap envelope half: `F` is below the lower envelope of
  its body.  The converse (every superlinear Scott-continuous prevision
  *is* the lower envelope of its body — the envelope representation,
  with its double-powerspace refinement) is the analytic theorem of the
  layer and stays cited: Goubault-Larrecq, *Just Previsions* (2026),
  with the compact-carrier discharge conditions; the additivity of the
  pairing in the gamble for modular Scott-continuous valuations (Tix;
  Kirch; Goubault-Larrecq–Jia, *Continuous R-valuations*, ENTICS 2023)
  is the named next rung of this module, deliberately not claimed here.
-/

namespace Pointfree

open scoped ENNReal
open MeasureTheory

variable {L M N : Type*} [Order.Frame L] [Order.Frame M] [Order.Frame N]

/-- A **gamble** over a frame: an `ℝ≥0∞`-indexed antitone,
right-continuous family of frame elements — the sublevel presentation
`t ↦ {h > t}` of a lower-semicontinuous nonnegative observable.
Right-continuity at `∞` forces `U ∞ = ⊥`. -/
structure Gamble (L : Type*) [Order.Frame L] where
  /-- The sublevel family: `U t` is the region where the observable
  exceeds `t`. -/
  U : ℝ≥0∞ → L
  /-- Higher thresholds carve smaller regions. -/
  antitone' : Antitone U
  /-- Right-continuity: each sublevel is the join of the strictly
  higher ones. -/
  right_continuous' : ∀ t, U t = ⨆ s, ⨆ _ : t < s, U s

namespace Gamble

theorem antitone (g : Gamble L) : Antitone g.U := g.antitone'

theorem right_continuous (g : Gamble L) (t : ℝ≥0∞) :
    g.U t = ⨆ s, ⨆ _ : t < s, g.U s := g.right_continuous' t

@[ext] theorem ext {g₁ g₂ : Gamble L} (h : ∀ t, g₁.U t = g₂.U t) : g₁ = g₂ := by
  cases g₁ with | mk U₁ a₁ r₁ =>
  cases g₂ with | mk U₂ a₂ r₂ =>
  have hU : U₁ = U₂ := funext h
  subst hU
  rfl

@[simp] theorem U_top (g : Gamble L) : g.U ∞ = ⊥ := by
  rw [g.right_continuous ∞]
  exact le_antisymm (iSup₂_le fun s hs => absurd hs not_top_lt) bot_le

/-- Gambles are ordered pointwise on sublevel families. -/
instance : PartialOrder (Gamble L) :=
  PartialOrder.lift U fun _ _ h => ext (congrFun h)

theorem le_def {g₁ g₂ : Gamble L} : g₁ ≤ g₂ ↔ ∀ t, g₁.U t ≤ g₂.U t :=
  Iff.rfl

/-! ## Indicator gambles -/

/-- The sublevel family of the indicator observable of a frame element:
`a` below threshold `1`, `⊥` from `1` up.  (Encoded by a
proposition-indexed join, so no decidability enters.) -/
def indicatorFun (a : L) (t : ℝ≥0∞) : L := ⨆ _ : t < 1, a

theorem indicatorFun_of_lt {a : L} {t : ℝ≥0∞} (h : t < 1) :
    indicatorFun a t = a := iSup_pos h

theorem indicatorFun_of_ge {a : L} {t : ℝ≥0∞} (h : ¬ t < 1) :
    indicatorFun a t = ⊥ := iSup_neg h

/-- The indicator gamble of a frame element. -/
def indicator (a : L) : Gamble L where
  U := indicatorFun a
  antitone' := by
    intro s t hst
    by_cases ht : t < 1
    · rw [indicatorFun_of_lt ht, indicatorFun_of_lt (lt_of_le_of_lt hst ht)]
    · rw [indicatorFun_of_ge ht]
      exact bot_le
  right_continuous' := by
    intro t
    by_cases ht : t < 1
    · rw [indicatorFun_of_lt ht]
      obtain ⟨s, hts, hs1⟩ := exists_between ht
      refine le_antisymm (le_iSup₂_of_le s hts ?_) (iSup₂_le fun s' _ => ?_)
      · rw [indicatorFun_of_lt hs1]
      · by_cases hs' : s' < 1
        · rw [indicatorFun_of_lt hs']
        · rw [indicatorFun_of_ge hs']
          exact bot_le
    · rw [indicatorFun_of_ge ht]
      refine le_antisymm bot_le (iSup₂_le fun s hs => ?_)
      rw [indicatorFun_of_ge fun hs1 => ht (hs.trans hs1)]

@[simp] theorem indicator_U (a : L) (t : ℝ≥0∞) :
    (indicator a).U t = indicatorFun a t := rfl

/-! ## Transport along frame homomorphisms -/

/-- Covariant transport of gambles along a frame homomorphism:
post-compose the sublevel family. -/
def map (φ : FrameHom L M) (g : Gamble L) : Gamble M where
  U t := φ (g.U t)
  antitone' := fun s t hst => φ.monotone' (g.antitone hst)
  right_continuous' := by
    intro t
    rw [g.right_continuous t, map_iSup]
    refine iSup_congr fun s => ?_
    rw [map_iSup]

@[simp] theorem map_U (φ : FrameHom L M) (g : Gamble L) (t : ℝ≥0∞) :
    (g.map φ).U t = φ (g.U t) := rfl

theorem map_mono (φ : FrameHom L M) {g₁ g₂ : Gamble L} (h : g₁ ≤ g₂) :
    g₁.map φ ≤ g₂.map φ :=
  le_def.mpr fun t => φ.monotone' (le_def.mp h t)

@[simp] theorem map_id (g : Gamble L) : g.map (FrameHom.id L) = g :=
  ext fun _ => FrameHom.id_apply _

theorem map_comp (φ : FrameHom M N) (ψ : FrameHom L M) (g : Gamble L) :
    (g.map ψ).map φ = g.map (φ.comp ψ) :=
  ext fun _ => (FrameHom.comp_apply φ ψ _).symm

/-! ## Addition: sublevel convolution -/

/-- The sublevel convolution family: the region where a sum of
observables exceeds `t` is covered by the splittings of `t` between
the summands. -/
def convFam (g₁ g₂ : Gamble L) (t : ℝ≥0∞) : L :=
  ⨆ r, ⨆ s, ⨆ _ : r + s = t, g₁.U r ⊓ g₂.U s

theorem convFam_antitone (g₁ g₂ : Gamble L) : Antitone (convFam g₁ g₂) := by
  intro t t' htt'
  refine iSup₂_le fun r s => iSup_le fun hrs => ?_
  have hts : t - min r t ≤ s := by
    rcases le_total r t with hrt | htr
    · rw [min_eq_left hrt]
      have h1 : t ≤ r + s := le_trans htt' (le_of_eq hrs.symm)
      exact tsub_le_iff_right.mpr (by rw [add_comm]; exact h1)
    · rw [min_eq_right htr, tsub_self]
      exact zero_le
  have hsum : min r t + (t - min r t) = t :=
    add_tsub_cancel_of_le (min_le_right r t)
  refine le_iSup₂_of_le (min r t) (t - min r t) (le_iSup_of_le hsum ?_)
  exact inf_le_inf (g₁.antitone (min_le_left r t)) (g₂.antitone hts)

theorem convFam_right_continuous (g₁ g₂ : Gamble L) (t : ℝ≥0∞) :
    convFam g₁ g₂ t = ⨆ s, ⨆ _ : t < s, convFam g₁ g₂ s := by
  refine le_antisymm ?_ (iSup₂_le fun s' hs' => convFam_antitone g₁ g₂ hs'.le)
  refine iSup₂_le fun r s => iSup_le fun hrs => ?_
  rcases eq_or_ne t ∞ with ht | ht
  · subst ht
    rcases ENNReal.add_eq_top.mp hrs with hr | hs
    · rw [hr, U_top, bot_inf_eq]
      exact bot_le
    · rw [hs, U_top, inf_bot_eq]
      exact bot_le
  · have hs_ne : s ≠ ∞ := fun hsi => ht (by rw [← hrs, hsi]; simp)
    rw [g₁.right_continuous r, iSup_inf_eq]
    refine iSup_le fun r' => ?_
    rw [iSup_inf_eq]
    refine iSup_le fun hrr' => ?_
    have hlt : t < r' + s := by
      rw [← hrs]
      exact ENNReal.add_lt_add_right hs_ne hrr'
    refine le_iSup₂_of_le (r' + s) hlt ?_
    exact le_iSup₂_of_le r' s (le_iSup_of_le rfl le_rfl)

/-- Gambles add by sublevel convolution. -/
instance : Add (Gamble L) :=
  ⟨fun g₁ g₂ => ⟨convFam g₁ g₂, convFam_antitone g₁ g₂,
    convFam_right_continuous g₁ g₂⟩⟩

@[simp] theorem add_U (g₁ g₂ : Gamble L) (t : ℝ≥0∞) :
    (g₁ + g₂).U t = convFam g₁ g₂ t := rfl

end Gamble

/-! ## The Choquet pairing -/

namespace Valuation

/-- The **Choquet pairing** of a valuation against a gamble: the
layer-cake integral of the sublevel masses. -/
noncomputable def pair (μ : Valuation L) (g : Gamble L) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioi (0 : ℝ), μ (g.U (ENNReal.ofReal t))

theorem pair_integrand_antitone (μ : Valuation L) (g : Gamble L) :
    Antitone fun t : ℝ => μ (g.U (ENNReal.ofReal t)) := fun _ _ hst =>
  μ.mono (g.antitone (ENNReal.ofReal_le_ofReal hst))

theorem pair_integrand_measurable (μ : Valuation L) (g : Gamble L) :
    Measurable fun t : ℝ => μ (g.U (ENNReal.ofReal t)) :=
  (pair_integrand_antitone μ g).measurable

theorem pair_mono_left {μ ν : Valuation L} (h : μ ≤ ν) (g : Gamble L) :
    μ.pair g ≤ ν.pair g :=
  lintegral_mono fun _ => le_def.mp h _

theorem pair_mono_right (μ : Valuation L) {g₁ g₂ : Gamble L} (h : g₁ ≤ g₂) :
    μ.pair g₁ ≤ μ.pair g₂ :=
  lintegral_mono fun _ => μ.mono (Gamble.le_def.mp h _)

/-- The pairing is additive in the valuation. -/
theorem pair_add (μ ν : Valuation L) (g : Gamble L) :
    (μ + ν).pair g = μ.pair g + ν.pair g := by
  simp only [pair, add_apply]
  exact lintegral_add_left (pair_integrand_measurable μ g) _

/-- The pairing is homogeneous in the valuation. -/
theorem pair_smul (c : ℝ≥0∞) (μ : Valuation L) (g : Gamble L) :
    (c • μ).pair g = c * μ.pair g := by
  simp only [pair, smul_apply]
  exact lintegral_const_mul c (pair_integrand_measurable μ g)

/-- **Naturality of the pairing**: pushing the valuation forward is
transporting the gamble back — definitionally. -/
theorem pair_map (μ : Valuation L) (φ : FrameHom M L) (g : Gamble M) :
    (μ.map φ).pair g = μ.pair (g.map φ) := rfl

/-- Indicator gambles evaluate to the valuation: the pairing extends
the valuation through the layer-cake. -/
theorem pair_indicator (μ : Valuation L) (a : L) :
    μ.pair (Gamble.indicator a) = μ a := by
  have hcongr : Set.EqOn
      (fun t : ℝ => μ ((Gamble.indicator a).U (ENNReal.ofReal t)))
      ((Set.Ioo (0 : ℝ) 1).indicator fun _ => μ a) (Set.Ioi 0) := by
    intro t ht
    simp only [Gamble.indicator_U]
    by_cases h1 : t < 1
    · rw [Gamble.indicatorFun_of_lt (ENNReal.ofReal_lt_one.mpr h1),
        Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨ht, h1⟩)]
    · rw [Gamble.indicatorFun_of_ge fun hc => h1 (ENNReal.ofReal_lt_one.mp hc),
        map_bot, Set.indicator_of_notMem fun hm => h1 hm.2]
  show (∫⁻ t in Set.Ioi (0 : ℝ), μ ((Gamble.indicator a).U (ENNReal.ofReal t)))
      = μ a
  rw [setLIntegral_congr_fun measurableSet_Ioi hcongr,
    lintegral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    Set.inter_eq_self_of_subset_left Set.Ioo_subset_Ioi_self,
    setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]

end Valuation

/-! ## Previsions -/

/-- A **prevision**: a monotone functional on gambles.  (Positive
homogeneity and super/sub-additivity are carved as predicates on top,
following the point-free prevision literature.) -/
structure Prevision (L : Type*) [Order.Frame L] where
  /-- The functional. -/
  toFun : Gamble L → ℝ≥0∞
  /-- Monotonicity in the gamble. -/
  monotone' : Monotone toFun

namespace Prevision

instance : FunLike (Prevision L) (Gamble L) ℝ≥0∞ where
  coe := Prevision.toFun
  coe_injective := by
    rintro ⟨f, _⟩ ⟨g, _⟩ h
    simpa using h

@[ext] theorem ext {F G : Prevision L} (h : ∀ g, F g = G g) : F = G :=
  DFunLike.ext _ _ h

theorem mono (F : Prevision L) : Monotone F := F.monotone'

/-- The superlinear (lower/demonic) class: superadditive previsions. -/
def IsSuperadditive (F : Prevision L) : Prop :=
  ∀ g₁ g₂, F g₁ + F g₂ ≤ F (g₁ + g₂)

/-- Transport of previsions along a frame homomorphism: precompose with
gamble transport.  Same variance as `Valuation.map`. -/
def map (φ : FrameHom M L) (F : Prevision L) : Prevision M where
  toFun g := F (g.map φ)
  monotone' := fun _ _ h => F.mono (Gamble.map_mono φ h)

@[simp] theorem map_apply (φ : FrameHom M L) (F : Prevision L) (g : Gamble M) :
    F.map φ g = F (g.map φ) := rfl

@[simp] theorem map_id (F : Prevision L) : F.map (FrameHom.id L) = F :=
  ext fun g => by simp only [map_apply, Gamble.map_id]

theorem map_comp (φ : FrameHom M L) (ψ : FrameHom N M) (F : Prevision L) :
    (F.map φ).map ψ = F.map (φ.comp ψ) :=
  ext fun g => by
    simp only [map_apply]
    rw [Gamble.map_comp]

end Prevision

/-- Every valuation is a prevision, through the Choquet pairing. -/
noncomputable def Valuation.toPrevision (μ : Valuation L) : Prevision L where
  toFun := μ.pair
  monotone' := fun _ _ h => Valuation.pair_mono_right μ h

@[simp] theorem Valuation.toPrevision_apply (μ : Valuation L) (g : Gamble L) :
    μ.toPrevision g = μ.pair g := rfl

/-- The valuation-to-prevision map is natural: the pairing's naturality,
bundled. -/
theorem Valuation.toPrevision_map (μ : Valuation L) (φ : FrameHom M L) :
    (μ.map φ).toPrevision = μ.toPrevision.map φ :=
  Prevision.ext fun g => Valuation.pair_map μ φ g

namespace Prevision

/-- The lower envelope of a set of previsions: the credal (worst-case)
functional. -/
noncomputable def iInfEnvelope (P : Set (Prevision L)) : Prevision L where
  toFun g := ⨅ F ∈ P, F g
  monotone' := fun _ _ h =>
    le_iInf₂ fun F hF => (iInf₂_le F hF).trans (F.mono h)

@[simp] theorem iInfEnvelope_apply (P : Set (Prevision L)) (g : Gamble L) :
    iInfEnvelope P g = ⨅ F ∈ P, F g := rfl

/-- **The superlinear class is closed under lower envelopes**: the
lower envelope of superadditive previsions is superadditive.  (With
`Valuation.toPrevision`, this is the credal reading: a set of
subprobability valuations presents a worst-case expectation operator
in the superlinear class.) -/
theorem iInfEnvelope_isSuperadditive {P : Set (Prevision L)}
    (hP : ∀ F ∈ P, F.IsSuperadditive) :
    (iInfEnvelope P).IsSuperadditive := by
  intro g₁ g₂
  refine le_iInf₂ fun F hF => ?_
  calc (⨅ G ∈ P, G g₁) + ⨅ G ∈ P, G g₂
      ≤ F g₁ + F g₂ := add_le_add (iInf₂_le F hF) (iInf₂_le F hF)
    _ ≤ F (g₁ + g₂) := hP F hF g₁ g₂

/-- The **body** of a prevision: the subprobability valuations whose
pairing dominates it. -/
def body (F : Prevision L) : Set (SubProb L) :=
  {μ : SubProb L | ∀ g, F g ≤ μ.1.pair g}

/-- The cheap half of the envelope representation: every prevision is
below the lower envelope of its body.  The converse — every
Scott-continuous superlinear prevision *is* the lower envelope of its
body — is the envelope representation theorem of the prevision
literature (with its double-powerspace refinement), cited in the module
docstring and deliberately not claimed here. -/
theorem le_iInfEnvelope_body (F : Prevision L) (g : Gamble L) :
    F g ≤ iInfEnvelope ((fun μ : SubProb L => μ.1.toPrevision) '' F.body) g := by
  rw [iInfEnvelope_apply]
  refine le_iInf₂ fun G hG => ?_
  obtain ⟨μ, hμ, rfl⟩ := hG
  exact hμ g

end Prevision

end Pointfree
