import Qtsl.OdeProfile
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Convex.Basic

/-!
# The Dini profile for switched and hybrid systems

Per-point differentiability is semantically false for switched and
hybrid systems: at a switch instant the observable along a trajectory
has a corner, at a Zeno accumulation one-sided derivatives can fail to
exist, and in sliding regimes the right derivative matches no mode's
field. This module provides the upper-right Dini derivative variant of
the flow-derivative interface and re-derives the integrated bounds at
that generality.
-/

namespace PPLC
namespace Qtsl
namespace Semiflow

open scoped NNReal
open Set Topology

variable {X : Type*}

def FlowDiniLeOn (φ : Semiflow X) (V W : X → ℝ) (C : Set X) : Prop :=
  ∀ x ∈ C, ∀ r, W x < r →
    ∀ᶠ s in 𝓝[>] (0:ℝ), slope (fun u : ℝ => V (φ.flow u.toNNReal x)) 0 s < r

def FlowDiniGeOn (φ : Semiflow X) (V W : X → ℝ) (C : Set X) : Prop :=
  ∀ x ∈ C, ∀ r, r < W x →
    ∀ᶠ s in 𝓝[>] (0:ℝ), r < slope (fun u : ℝ => V (φ.flow u.toNNReal x)) 0 s

theorem FlowDiniLeOn.mono {φ : Semiflow X} {V W : X → ℝ} {C D : Set X}
    (h : φ.FlowDiniLeOn V W D) (hCD : C ⊆ D) : φ.FlowDiniLeOn V W C :=
  fun x hx => h x (hCD hx)

theorem FlowDiniGeOn.mono {φ : Semiflow X} {V W : X → ℝ} {C D : Set X}
    (h : φ.FlowDiniGeOn V W D) (hCD : C ⊆ D) : φ.FlowDiniGeOn V W C :=
  fun x hx => h x (hCD hx)

theorem FlowDerivOn.flowDiniLeOn {φ : Semiflow X} {V W : X → ℝ} {C : Set X}
    (h : φ.FlowDerivOn V W C) : φ.FlowDiniLeOn V W C :=
  fun x hx _ hr => (h x hx).Ioi_of_Ici.limsup_slope_le' (by simp) hr

theorem FlowDiniGeOn.neg {φ : Semiflow X} {V W : X → ℝ} {C : Set X}
    (h : φ.FlowDiniGeOn V W C) :
    φ.FlowDiniLeOn (fun z => -V z) (fun z => -W z) C := by
  intro x hx r hr
  have hr' : -r < W x := by linarith
  filter_upwards [h x hx (-r) hr'] with s hs
  have hneg : slope (fun u : ℝ => -(V (φ.flow u.toNNReal x))) 0 s
      = -slope (fun u : ℝ => V (φ.flow u.toNNReal x)) 0 s := by
    simp only [slope_def_field]
    ring
  have h2 : -slope (fun u : ℝ => V (φ.flow u.toNNReal x)) 0 s < r := by
    linarith
  simpa [hneg] using h2

theorem FlowDiniLeOn.frequently_slope_lt {φ : Semiflow X} {V W : X → ℝ}
    {C : Set X} (hW : φ.FlowDiniLeOn V W C) {x : X} {s r : ℝ} (hs : 0 ≤ s)
    (hyC : φ.flow s.toNNReal x ∈ C) (hr : W (φ.flow s.toNNReal x) < r) :
    ∃ᶠ z in 𝓝[>] s, slope (fun u : ℝ => V (φ.flow u.toNNReal x)) s z < r := by
  set y := φ.flow s.toNNReal x with hy
  have hbase : ∀ᶠ v in 𝓝[>] (0:ℝ),
      slope (fun u : ℝ => V (φ.flow u.toNNReal y)) 0 v < r := hW y hyC r hr
  have hmap : Filter.Tendsto (fun v : ℝ => s + v) (𝓝[>] (0:ℝ)) (𝓝[>] s) := by
    have h1 : Filter.Tendsto (fun v : ℝ => s + v) (𝓝[>] (0:ℝ)) (𝓝 s) := by
      have h0 : Filter.Tendsto (fun v : ℝ => s + v) (𝓝 (0:ℝ)) (𝓝 (s + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      simpa using h0.mono_left nhdsWithin_le_nhds
    have h2 : ∀ᶠ v in 𝓝[>] (0:ℝ), s + v ∈ Set.Ioi s := by
      filter_upwards [eventually_mem_nhdsWithin] with v hv
      exact lt_add_of_pos_right s hv
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1 h2
  have hfreq0 : ∃ᶠ v in 𝓝[>] (0:ℝ),
      slope (fun u : ℝ => V (φ.flow u.toNNReal x)) s (s + v) < r := by
    refine ((hbase.and eventually_mem_nhdsWithin).frequently).mono ?_
    rintro v ⟨hv, hv0⟩
    have hvpos : (0:ℝ) < v := hv0
    have hsplit : (s + v).toNNReal = s.toNNReal + v.toNNReal := by
      rw [← Real.toNNReal_add hs hvpos.le]
    have hkey : V (φ.flow (s + v).toNNReal x) = V (φ.flow v.toNNReal y) := by
      rw [hsplit, hy, φ.flow_add]
    have hgs : V (φ.flow s.toNNReal x) = V y := by rw [hy]
    have hv' := hv
    rw [slope_def_field, sub_zero] at hv'
    have hg0 : V (φ.flow (0:ℝ).toNNReal y) = V y := by
      simp [Real.toNNReal_zero, φ.flow_zero]
    rw [hg0] at hv'
    rw [slope_def_field, hkey, hgs, add_sub_cancel_left]
    exact hv'
  exact (Filter.frequently_map.mpr hfreq0).filter_mono hmap

section Bridge

variable [TopologicalSpace X]

theorem integrated_le_of_flowDiniLe {φ : Semiflow X} {C : Set X}
    {V W : X → ℝ} {c : ℝ}
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hV : ContinuousOn V C)
    (hW : φ.FlowDiniLeOn V W C)
    (hrow : ∀ y ∈ C, W y ≤ c)
    {x : X} {t : ℝ≥0} (hconf : ∀ s ≤ t, φ.flow s x ∈ C) :
    V (φ.flow t x) ≤ V x + c * t := by
  set g : ℝ → ℝ := fun u => V (φ.flow u.toNNReal x) with hg
  have htraj' : Continuous fun u : ℝ => φ.flow u.toNNReal x :=
    (htraj x).comp continuous_real_toNNReal
  have hmapsC : ∀ u ∈ Set.Icc (0 : ℝ) (t : ℝ), φ.flow u.toNNReal x ∈ C :=
    fun u hu => hconf _ (Real.toNNReal_le_iff_le_coe.mpr hu.2)
  have hcont : ContinuousOn g (Set.Icc 0 (t : ℝ)) :=
    hV.comp htraj'.continuousOn hmapsC
  set B : ℝ → ℝ := fun u => g 0 + c * u with hB
  have hBc : ContinuousOn B (Set.Icc 0 (t : ℝ)) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  have hB' : ∀ u ∈ Set.Ico (0 : ℝ) (t : ℝ),
      HasDerivWithinAt B ((fun _ : ℝ => c) u) (Set.Ici u) u := by
    intro u _
    show HasDerivWithinAt B c (Set.Ici u) u
    rw [hB]
    have h1 := ((hasDerivWithinAt_id u (Set.Ici u)).const_mul c).const_add (g 0)
    simpa only [id_eq, mul_one] using h1
  have hbound : ∀ u ∈ Set.Ico (0 : ℝ) (t : ℝ), ∀ r, (fun _ : ℝ => c) u < r →
      ∃ᶠ z in 𝓝[>] u, slope g u z < r := by
    intro u hu r hr
    have huC := hmapsC u ⟨hu.1, hu.2.le⟩
    exact hW.frequently_slope_lt hu.1 huC
      (lt_of_le_of_lt (hrow _ huC) hr)
  have hfence := image_le_of_liminf_slope_right_le_deriv_boundary
    (f := g) (a := 0) (b := (t : ℝ)) (B := B) (B' := fun _ : ℝ => c)
    hcont (by simp [hB]) hBc hB' hbound
  have hend := hfence ⟨t.coe_nonneg, le_refl (t : ℝ)⟩
  have hg0 : g 0 = V x := by simp [hg, φ.flow_zero]
  have hgt : g (t : ℝ) = V (φ.flow t x) := by simp [hg]
  simp only [hB] at hend
  rw [hg0, hgt] at hend
  exact hend

theorem integrated_ge_of_flowDiniGe {φ : Semiflow X} {C : Set X}
    {V W : X → ℝ} {c : ℝ}
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hV : ContinuousOn V C)
    (hW : φ.FlowDiniGeOn V W C)
    (hrow : ∀ y ∈ C, c ≤ W y)
    {x : X} {t : ℝ≥0} (hconf : ∀ s ≤ t, φ.flow s x ∈ C) :
    V x + c * t ≤ V (φ.flow t x) := by
  have h := integrated_le_of_flowDiniLe (V := fun z => -V z)
    (W := fun z => -W z) (c := -c) htraj hV.neg hW.neg
    (fun y hy => neg_le_neg (hrow y hy)) hconf
  simp only [neg_mul] at h
  linarith

end Bridge

section DiniFaces

variable [TopologicalSpace X]

theorem hasTransitCert_of_dini_rows {φ : Semiflow X} {C : Set X}
    {V W : X → ℝ} {ε : ℝ}
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hε : 0 < ε) (hV : ContinuousOn V C) (hbdd : BddBelow (V '' C))
    (hW : φ.FlowDiniLeOn V W C) (hrow : ∀ y ∈ C, W y ≤ -ε) :
    φ.HasTransitCert C := by
  refine ⟨V, ε, hε, hbdd, fun x hx t hconf => ?_⟩
  have h := integrated_le_of_flowDiniLe htraj hV hW hrow hconf
  simpa [neg_mul, sub_eq_add_neg] using h

theorem hasTransitCert_of_dini_rows_isCompact {φ : Semiflow X} {C : Set X}
    {V W : X → ℝ} {ε : ℝ}
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hC : IsCompact C) (hε : 0 < ε) (hV : ContinuousOn V C)
    (hW : φ.FlowDiniLeOn V W C) (hrow : ∀ y ∈ C, W y ≤ -ε) :
    φ.HasTransitCert C :=
  hasTransitCert_of_dini_rows htraj hε hV (hC.bddBelow_image hV) hW hrow

theorem hasFacetRows_of_dini_rows {φ : Semiflow X} {D N : Set X}
    {n : ℕ} {ℓ : Fin n → X → ℝ} {ε : Fin n → ℝ} {F : Fin n → Set X}
    (W : Fin n → X → ℝ)
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hε : ∀ i, 0 < ε i)
    (hℓ : ∀ i, ContinuousOn (ℓ i) (F i))
    (hW : ∀ i, φ.FlowDiniGeOn (ℓ i) (W i) (F i))
    (hrow : ∀ i, ∀ y ∈ F i, ε i ≤ W i y)
    (hlocal : ∀ x ∈ frontier N, ∃ (A : Set (Fin n)) (U : Set X), U ∈ 𝓝 x ∧
      (∀ i ∈ A, ℓ i x = 0 ∧ F i ∈ 𝓝 x) ∧
      ∀ y ∈ U, y ∈ D → (∀ i ∈ A, 0 ≤ ℓ i y) → y ∈ N) :
    φ.HasFacetRows D N :=
  ⟨n, ℓ, ε, F, hε,
    fun i _ _ _ hconf =>
      integrated_ge_of_flowDiniGe htraj (hℓ i) (hW i) (hrow i) hconf,
    hlocal⟩

end DiniFaces

theorem hasCrossingCert_of_dini {φ : Semiflow X} {O : Set X}
    {V W : X → ℝ} {c : ℝ}
    (hlevel : ∀ x ∈ O, V x = c) (hW : φ.FlowDiniLeOn V W O)
    (hneg : ∀ x ∈ O, W x < 0) :
    φ.HasCrossingCert O := by
  refine ⟨V, c, hlevel, fun x hx => ?_⟩
  have hev := hW x hx 0 (hneg x hx)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hupos : (0:ℝ) < u := hu
  refine ⟨(u / 2).toNNReal, Real.toNNReal_pos.mpr (by linarith), ?_⟩
  intro s hs hsle
  have hs' : (0:ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hsu : (s : ℝ) ≤ u / 2 := by
    have h1 : ((s : ℝ≥0) : ℝ) ≤ (((u / 2).toNNReal : ℝ≥0) : ℝ) := by
      exact_mod_cast hsle
    rwa [Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ u / 2)] at h1
  have hmem : (s : ℝ) ∈ Set.Ioo (0:ℝ) u := ⟨hs', by linarith⟩
  have hslope := hsub hmem
  simp only [Set.mem_setOf_eq, slope_def_field, sub_zero, Real.toNNReal_coe,
    Real.toNNReal_zero] at hslope
  rw [φ.flow_zero, hlevel x hx] at hslope
  have hnum : V (φ.flow s x) - c < 0 := by
    by_contra hcon
    exact absurd hslope (not_lt.mpr (div_nonneg (not_lt.mp hcon) hs'.le))
  linarith

section SwitchedOde

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

def SolvesSwitchedODEOn (φ : Semiflow E) (f : ι → E → E) (R : ι → Set E)
    (C : Set E) : Prop :=
  ∀ x ∈ C, ∃ i, x ∈ R i ∧
    HasDerivWithinAt (fun s : ℝ => φ.flow s.toNNReal x) (f i x) (Set.Ici 0) 0

theorem SolvesODEOn.solvesSwitchedODEOn {φ : Semiflow E} {f : E → E}
    {C : Set E} (h : φ.SolvesODEOn f C) :
    φ.SolvesSwitchedODEOn (fun _ : Unit => f) (fun _ => Set.univ) C :=
  fun x hx => ⟨(), Set.mem_univ x, h x hx⟩

theorem flowDiniLeOn_of_switched {φ : Semiflow E} {f : ι → E → E}
    {R : ι → Set E} {C : Set E} {V : E → ℝ} {DV : E → E →L[ℝ] ℝ} {W : E → ℝ}
    (hode : φ.SolvesSwitchedODEOn f R C)
    (hV : ∀ x ∈ C, HasFDerivAt V (DV x) x)
    (hrow : ∀ i, ∀ y ∈ C ∩ R i, DV y (f i y) ≤ W y) :
    φ.FlowDiniLeOn V W C := by
  intro x hx r hr
  obtain ⟨i, hxR, hd⟩ := hode x hx
  have hcomp : HasDerivWithinAt (fun s : ℝ => V (φ.flow s.toNNReal x))
      (DV x (f i x)) (Set.Ici 0) 0 :=
    (hV x hx).comp_hasDerivWithinAt_of_eq (0 : ℝ) hd
      (by simp [Real.toNNReal_zero, φ.flow_zero])
  exact hcomp.Ioi_of_Ici.limsup_slope_le' (by simp)
    (lt_of_le_of_lt (hrow i x ⟨hx, hxR⟩) hr)

theorem flowDiniGeOn_of_switched {φ : Semiflow E} {f : ι → E → E}
    {R : ι → Set E} {C : Set E} {V : E → ℝ} {DV : E → E →L[ℝ] ℝ} {W : E → ℝ}
    (hode : φ.SolvesSwitchedODEOn f R C)
    (hV : ∀ x ∈ C, HasFDerivAt V (DV x) x)
    (hrow : ∀ i, ∀ y ∈ C ∩ R i, W y ≤ DV y (f i y)) :
    φ.FlowDiniGeOn V W C := by
  intro x hx r hr
  obtain ⟨i, hxR, hd⟩ := hode x hx
  have hcomp : HasDerivWithinAt (fun s : ℝ => V (φ.flow s.toNNReal x))
      (DV x (f i x)) (Set.Ici 0) 0 :=
    (hV x hx).comp_hasDerivWithinAt_of_eq (0 : ℝ) hd
      (by simp [Real.toNNReal_zero, φ.flow_zero])
  have htend := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl 0)).mp
    hcomp.Ioi_of_Ici
  exact htend.eventually (eventually_gt_nhds
    (lt_of_lt_of_le hr (hrow i x ⟨hx, hxR⟩)))

theorem hasTransitCert_of_switched_rows {φ : Semiflow E} {C : Set E}
    {f : ι → E → E} {R : ι → Set E} {V : E → ℝ} {DV : E → E →L[ℝ] ℝ} {ε : ℝ}
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hC : IsCompact C) (hε : 0 < ε)
    (hode : φ.SolvesSwitchedODEOn f R C)
    (hV : ∀ x ∈ C, HasFDerivAt V (DV x) x)
    (hrow : ∀ i, ∀ y ∈ C ∩ R i, DV y (f i y) ≤ -ε) :
    φ.HasTransitCert C :=
  hasTransitCert_of_dini_rows_isCompact htraj hC hε
    (fun x hx => (hV x hx).continuousAt.continuousWithinAt)
    (flowDiniLeOn_of_switched (W := fun _ => -ε) hode hV hrow)
    (fun _ _ => le_refl _)

theorem hasCrossingCert_of_switched {φ : Semiflow E} {O : Set E}
    {f : ι → E → E} {R : ι → Set E} {V : E → ℝ} {DV : E → E →L[ℝ] ℝ}
    {c ε : ℝ} (hε : 0 < ε)
    (hlevel : ∀ x ∈ O, V x = c)
    (hode : φ.SolvesSwitchedODEOn f R O)
    (hV : ∀ x ∈ O, HasFDerivAt V (DV x) x)
    (hrow : ∀ i, ∀ y ∈ O ∩ R i, DV y (f i y) ≤ -ε) :
    φ.HasCrossingCert O :=
  hasCrossingCert_of_dini hlevel
    (flowDiniLeOn_of_switched (W := fun _ => -ε) hode hV hrow)
    (fun _ _ => neg_lt_zero.mpr hε)

theorem hasFacetRows_of_switched_rows {φ : Semiflow E} {D N : Set E}
    {n : ℕ} {ℓ : Fin n → E → ℝ} {ε : Fin n → ℝ} {F : Fin n → Set E}
    {f : ι → E → E} {R : ι → Set E} (Dℓ : Fin n → E → E →L[ℝ] ℝ)
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hε : ∀ i, 0 < ε i)
    (hode : ∀ i, φ.SolvesSwitchedODEOn f R (F i))
    (hDℓ : ∀ i, ∀ x ∈ F i, HasFDerivAt (ℓ i) (Dℓ i x) x)
    (hrow : ∀ i j, ∀ y ∈ F i ∩ R j, ε i ≤ Dℓ i y (f j y))
    (hlocal : ∀ x ∈ frontier N, ∃ (A : Set (Fin n)) (U : Set E), U ∈ 𝓝 x ∧
      (∀ i ∈ A, ℓ i x = 0 ∧ F i ∈ 𝓝 x) ∧
      ∀ y ∈ U, y ∈ D → (∀ i ∈ A, 0 ≤ ℓ i y) → y ∈ N) :
    φ.HasFacetRows D N :=
  hasFacetRows_of_dini_rows (fun i _ => ε i) htraj hε
    (fun i x hx => (hDℓ i x hx).continuousAt.continuousWithinAt)
    (fun i => flowDiniGeOn_of_switched (W := fun _ => ε i) (hode i) (hDℓ i)
      (fun j y hy => hrow i j y hy))
    (fun _ _ _ => le_refl _) hlocal

end SwitchedOde

section AcIntegrated

open MeasureTheory

theorem le_add_of_absolutelyContinuous_of_ae_deriv_le {g : ℝ → ℝ}
    {b c : ℝ} (hb : 0 ≤ b)
    (hAC : AbsolutelyContinuousOnInterval g 0 b)
    (hae : ∀ᵐ u ∂volume, u ∈ Set.Icc (0:ℝ) b →
      DifferentiableAt ℝ g u → deriv g u ≤ c) :
    g b ≤ g 0 + c * b := by
  have hint : IntervalIntegrable (deriv g) volume 0 b :=
    hAC.intervalIntegrable_deriv
  have heq : ∫ u in (0:ℝ)..b, deriv g u = g b - g 0 :=
    hAC.integral_deriv_eq_sub
  have hdiff := hAC.ae_differentiableAt
  simp only [Set.uIcc_of_le hb] at hdiff
  have hle : deriv g ≤ᵐ[volume.restrict (Set.Icc (0:ℝ) b)] fun _ => c := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hae, hdiff] with u h1 h2 hu
    exact h1 hu (h2 hu)
  have hmono := intervalIntegral.integral_mono_ae_restrict hb hint
    intervalIntegrable_const hle
  rw [heq, intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hcb : (b - 0) * c = c * b := by ring
  rw [hcb] at hmono
  linarith

theorem integrated_le_of_acWindow {φ : Semiflow X} {V : X → ℝ} {c : ℝ}
    {x : X} {t : ℝ≥0}
    (hAC : AbsolutelyContinuousOnInterval
      (fun u : ℝ => V (φ.flow u.toNNReal x)) 0 t)
    (hae : ∀ᵐ u ∂volume, u ∈ Set.Icc (0:ℝ) (t:ℝ) →
      DifferentiableAt ℝ (fun u : ℝ => V (φ.flow u.toNNReal x)) u →
      deriv (fun u : ℝ => V (φ.flow u.toNNReal x)) u ≤ c) :
    V (φ.flow t x) ≤ V x + c * t := by
  have h := le_add_of_absolutelyContinuous_of_ae_deriv_le
    t.coe_nonneg hAC hae
  simpa [Real.toNNReal_coe, Real.toNNReal_zero, φ.flow_zero] using h

theorem hasTransitCert_of_ac {φ : Semiflow X} {C : Set X} {V : X → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hbdd : BddBelow (V '' C))
    (hwin : ∀ x ∈ C, ∀ t : ℝ≥0, (∀ s ≤ t, φ.flow s x ∈ C) →
      AbsolutelyContinuousOnInterval
        (fun u : ℝ => V (φ.flow u.toNNReal x)) 0 t ∧
      ∀ᵐ u ∂volume, u ∈ Set.Icc (0:ℝ) (t:ℝ) →
        DifferentiableAt ℝ (fun u : ℝ => V (φ.flow u.toNNReal x)) u →
        deriv (fun u : ℝ => V (φ.flow u.toNNReal x)) u ≤ -ε) :
    φ.HasTransitCert C := by
  refine ⟨V, ε, hε, hbdd, fun x hx t hconf => ?_⟩
  obtain ⟨hAC, hae⟩ := hwin x hx t hconf
  have h := integrated_le_of_acWindow hAC hae
  simpa [neg_mul, sub_eq_add_neg] using h

end AcIntegrated

section Filippov

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

theorem le_on_convexHull {L : E →L[ℝ] ℝ} {S : Set E} {c : ℝ}
    (h : ∀ v ∈ S, L v ≤ c) : ∀ v ∈ convexHull ℝ S, L v ≤ c :=
  fun _ hv => convexHull_min h
    (convex_halfSpace_le ⟨fun a b => L.map_add a b,
      fun r a => L.map_smul r a⟩ c) hv

def SolvesFilippovOn (φ : Semiflow E) (f : ι → E → E) (inc : E → Set ι)
    (C : Set E) : Prop :=
  ∀ x ∈ C, ∀ t : ℝ≥0, (∀ s ≤ t, φ.flow s x ∈ C) →
    (∃ K : ℝ≥0, LipschitzOnWith K
      (fun u : ℝ => φ.flow u.toNNReal x) (Set.Icc 0 (t:ℝ))) ∧
    ∀ᵐ u ∂volume, u ∈ Set.Icc (0:ℝ) (t:ℝ) →
      ∃ v ∈ convexHull ℝ
        ((fun i => f i (φ.flow u.toNNReal x)) '' inc (φ.flow u.toNNReal x)),
        HasDerivAt (fun w : ℝ => φ.flow w.toNNReal x) v u

theorem hasTransitCert_of_filippov_rows {φ : Semiflow E} {C : Set E}
    {f : ι → E → E} {inc : E → Set ι} {V : E → ℝ} {DV : E → E →L[ℝ] ℝ}
    {KV : ℝ≥0} {ε : ℝ} (hε : 0 < ε) (hbdd : BddBelow (V '' C))
    (hVLip : LipschitzOnWith KV V C)
    (hV : ∀ y ∈ C, HasFDerivAt V (DV y) y)
    (hode : φ.SolvesFilippovOn f inc C)
    (hrow : ∀ y ∈ C, ∀ i ∈ inc y, DV y (f i y) ≤ -ε) :
    φ.HasTransitCert C := by
  refine hasTransitCert_of_ac hε hbdd (fun x hx t hconf => ?_)
  obtain ⟨⟨K, hLip⟩, hae⟩ := hode x hx t hconf
  have hmapsC : Set.MapsTo (fun u : ℝ => φ.flow u.toNNReal x)
      (Set.Icc 0 (t:ℝ)) C :=
    fun u hu => hconf _ (Real.toNNReal_le_iff_le_coe.mpr hu.2)
  constructor
  ·
    have hcomp : LipschitzOnWith (KV * K)
        (fun u : ℝ => V (φ.flow u.toNNReal x)) (Set.uIcc (0:ℝ) (t:ℝ)) := by
      rw [Set.uIcc_of_le t.coe_nonneg]
      exact hVLip.comp hLip hmapsC
    exact hcomp.absolutelyContinuousOnInterval
  · filter_upwards [hae] with u himp hu _
    obtain ⟨v, hvhull, hvderiv⟩ := himp hu
    have hyC : φ.flow u.toNNReal x ∈ C := hmapsC hu
    have hchain : HasDerivAt (fun w : ℝ => V (φ.flow w.toNNReal x))
        (DV (φ.flow u.toNNReal x) v) u :=
      (hV _ hyC).comp_hasDerivAt u hvderiv
    rw [hchain.deriv]
    refine le_on_convexHull ?_ v hvhull
    rintro w ⟨i, hi, rfl⟩
    exact hrow _ hyC i hi

end Filippov

end Semiflow
end Qtsl

#print axioms Qtsl.Semiflow.FlowDiniLeOn.mono
#print axioms Qtsl.Semiflow.FlowDiniGeOn.mono
#print axioms Qtsl.Semiflow.FlowDerivOn.flowDiniLeOn
#print axioms Qtsl.Semiflow.FlowDiniGeOn.neg
#print axioms Qtsl.Semiflow.FlowDiniLeOn.frequently_slope_lt
#print axioms Qtsl.Semiflow.integrated_le_of_flowDiniLe
#print axioms Qtsl.Semiflow.integrated_ge_of_flowDiniGe
#print axioms Qtsl.Semiflow.hasTransitCert_of_dini_rows
#print axioms Qtsl.Semiflow.hasTransitCert_of_dini_rows_isCompact
#print axioms Qtsl.Semiflow.hasFacetRows_of_dini_rows
#print axioms Qtsl.Semiflow.hasCrossingCert_of_dini
#print axioms Qtsl.Semiflow.SolvesODEOn.solvesSwitchedODEOn
#print axioms Qtsl.Semiflow.flowDiniLeOn_of_switched
#print axioms Qtsl.Semiflow.flowDiniGeOn_of_switched
#print axioms Qtsl.Semiflow.hasTransitCert_of_switched_rows
#print axioms Qtsl.Semiflow.hasCrossingCert_of_switched
#print axioms Qtsl.Semiflow.hasFacetRows_of_switched_rows
#print axioms Qtsl.Semiflow.le_add_of_absolutelyContinuous_of_ae_deriv_le
#print axioms Qtsl.Semiflow.integrated_le_of_acWindow
#print axioms Qtsl.Semiflow.hasTransitCert_of_ac
#print axioms Qtsl.Semiflow.le_on_convexHull
#print axioms Qtsl.Semiflow.hasTransitCert_of_filippov_rows

end PPLC
