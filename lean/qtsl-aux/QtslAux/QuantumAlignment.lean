/-
Copyright (c) 2026 The maitria coalition. All rights reserved.
Released under Apache 2.0 / MIT dual license.
-/
import QtslAux.QuantumStrictness

/-! # Alignment: norm-additivity is a common ray

The strictness module characterized mass preservation as
`NonCancelling`, unpacked (`nonCancelling_iff`) into merged blocks
SILENT plus cross blocks NORM-ADDITIVE. The second conjunct is an
ℓ¹/triangle equality stated analytically; this module proves its
geometric form and threads it back through the characterization:

* **The scalar common-ray lemma** (`norm_sum_eq_sum_norm_iff`): a
  finite family of complex numbers sums with additive norms iff all
  entries lie on a common ray — one unit direction `u`, each entry its
  own magnitude times `u`. Zeros ride any ray (`0 = 0·u`), so the
  statement needs no nonzero side conditions and no pairwise
  `SameRay` transitivity care: the witness is global. Proved by the
  Cauchy–Schwarz face for a unit direction (`re_conj_mul_le_norm` /
  `eq_norm_mul_of_re_conj_mul_eq`), no strict-convexity machinery.

* **The block predicate** (`CrossAligned`): the `(c, c')` block's Gram
  entries lie on a common ray — physically, the block carries ONE
  global interference phase. `crossBlock_norm_additive_iff`: a cross
  block's contribution attains its ledger iff it is aligned.

* **The characterization, geometric form**
  (`nonCancelling_iff_aligned`, `offDiagMass_pushforward_eq_iff_aligned`):
  a coarse-graining preserves the off-diagonal mass iff every merged
  block is silent AND every cross block sits on a common ray. Strict
  iff some interference is erased or some block's phases disagree
  (`offDiagMass_pushforward_lt_iff_aligned`).

* **The aligned instance**: the landed `alignMeasure` equality witness
  is convicted of common-ray alignment through the new iff, backward
  (`alignMeasure_crossAligned`) — no new arithmetic; its ray is `u = 1`.

* **The de-phased witness — strictness through misalignment alone**:
  `dephaseMeasure` (branch vectors `(3/10, 0)`, `(0, (16/25)i)`,
  `(3/10, 12/25)` at the state `(1, 0)` — `alignMeasure`'s geometry
  with branch 1 rotated a quarter turn, normalization restored on the
  nose) has its merged pair ORTHOGONAL (`gram 0 1 = 0`) and both
  coarse cross entries NONZERO (`9/100 ± (192/625)i` — no exact
  cancellation), yet its off-diagonal mass drops strictly under the
  landed `mergeCoarse` (`dephaseMeasure_offDiagMass_pushforward_lt`):
  the cross block's two entries sit on the rays `1` and `i`, and
  partial (phase) cancellation is already loss. NEITHER landed
  sufficient condition (`offDiagMass_pushforward_lt_of_merged_pair`,
  `offDiagMass_pushforward_lt_of_cancellation`) has a witness on this
  specimen — the corner only the common-ray characterization reaches.
  The witness suite now spans the landscape: `mergeMeasure` (exact
  cancellation — strict), `alignMeasure` (common ray — equality),
  `dephaseMeasure` (partial cancellation — strict), all on the same
  site, the same merge, the same 3-4-5 total weight.

Scope fences inherited: finite index types, matrix grade, toy grade at
the witnesses; the physical reading is interpretation, not new claims.
Presentational note, recorded once: the `‖u‖ = 1` conjunct in the
common-ray form is redundant (a nonzero entry forces it; the all-zero
block satisfies norm-additivity for any `u`) — kept because a ray IS a
unit direction, at zero proof cost. -/

namespace Qtsl

namespace QuantumAlignment

open Matrix DiamondSite QuantumRecords QuantumDForm QuantumTransport
  QuantumCoarseGraining QuantumDiamondMeasure QuantumTower
  QuantumStrictness
open scoped ComplexOrder

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
  [DecidableEq κ]

/-! ## The scalar common-ray lemma -/

/-- The Cauchy–Schwarz face for a unit direction: the `u`-component of
`z` is at most its magnitude. -/
theorem re_conj_mul_le_norm (u z : ℂ) (hu : ‖u‖ = 1) :
    ((starRingEnd ℂ) u * z).re ≤ ‖z‖ :=
  (Complex.re_le_norm _).trans_eq
    (by rw [norm_mul, Complex.norm_conj, hu, one_mul])

/-- The equality face: attaining the magnitude puts the point on the
ray — `conj u * z` is forced real, nonnegative, of full magnitude. -/
theorem eq_norm_mul_of_re_conj_mul_eq {u z : ℂ} (hu : ‖u‖ = 1)
    (h : ((starRingEnd ℂ) u * z).re = ‖z‖) : z = (‖z‖ : ℂ) * u := by
  have hw : ‖(starRingEnd ℂ) u * z‖ = ‖z‖ := by
    rw [norm_mul, Complex.norm_conj, hu, one_mul]
  have him : ((starRingEnd ℂ) u * z).im = 0 := by
    have hsq := Complex.sq_norm ((starRingEnd ℂ) u * z)
    rw [Complex.normSq_apply, hw, h, sq] at hsq
    have h0 : ((starRingEnd ℂ) u * z).im * ((starRingEnd ℂ) u * z).im
        = 0 := by linarith
    exact mul_self_eq_zero.mp h0
  have hwval : (starRingEnd ℂ) u * z = (‖z‖ : ℂ) :=
    Complex.ext (by rw [h, Complex.ofReal_re])
      (by rw [him, Complex.ofReal_im])
  have hu1 : u * (starRingEnd ℂ) u = 1 := by
    rw [Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, hu, one_pow]
  calc z = (u * (starRingEnd ℂ) u) * z := by rw [hu1, one_mul]
    _ = u * ((starRingEnd ℂ) u * z) := by ring
    _ = u * (‖z‖ : ℂ) := by rw [hwval]
    _ = (‖z‖ : ℂ) * u := mul_comm _ _

/-- **Norm-additivity ⟺ common ray**: a finite family of complex
numbers sums with additive norms iff all entries lie on a common ray
from the origin — one unit direction, each entry its own magnitude
times it. Zeros ride any ray, so no nonzero side conditions. -/
theorem norm_sum_eq_sum_norm_iff {α : Type*} (s : Finset α) (z : α → ℂ) :
    ‖∑ i ∈ s, z i‖ = ∑ i ∈ s, ‖z i‖
      ↔ ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ i ∈ s, z i = (‖z i‖ : ℂ) * u := by
  constructor
  · intro h
    by_cases hs : (∑ i ∈ s, z i) = 0
    · refine ⟨1, norm_one, fun i hi => ?_⟩
      have h0 : ∑ i ∈ s, ‖z i‖ = 0 := by rw [← h, hs, norm_zero]
      have hz : ‖z i‖ = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
          norm_nonneg (z j)).mp h0 i hi
      rw [norm_eq_zero.mp hz]
      simp
    · have hSne : ((‖∑ i ∈ s, z i‖ : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast norm_ne_zero_iff.mpr hs
      have hu : ‖((‖∑ i ∈ s, z i‖ : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, z i‖ = 1 := by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _)]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hs)
      refine ⟨_, hu, ?_⟩
      have hconj : (starRingEnd ℂ)
            (((‖∑ i ∈ s, z i‖ : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, z i) * ∑ i ∈ s, z i
          = ((‖∑ i ∈ s, z i‖ : ℝ) : ℂ) := by
        rw [map_mul, map_inv₀, Complex.conj_ofReal, mul_assoc,
          ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
          sq, Complex.ofReal_mul, inv_mul_cancel_left₀ hSne]
      have hkey : ∑ i ∈ s, ((starRingEnd ℂ)
            (((‖∑ i ∈ s, z i‖ : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, z i) * z i).re
          = ∑ i ∈ s, ‖z i‖ := by
        calc ∑ i ∈ s, ((starRingEnd ℂ)
              (((‖∑ i ∈ s, z i‖ : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, z i) * z i).re
            = ((starRingEnd ℂ)
                (((‖∑ i ∈ s, z i‖ : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, z i)
                  * ∑ i ∈ s, z i).re := by
              rw [← Complex.re_sum, ← Finset.mul_sum]
          _ = ‖∑ i ∈ s, z i‖ := by rw [hconj, Complex.ofReal_re]
          _ = ∑ i ∈ s, ‖z i‖ := h
      have heq := (Finset.sum_eq_sum_iff_of_le
        (fun i _ => re_conj_mul_le_norm _ (z i) hu)).mp hkey
      exact fun i hi => eq_norm_mul_of_re_conj_mul_eq hu (heq i hi)
  · rintro ⟨u, hu, hz⟩
    have hsum : ∑ i ∈ s, z i = ((∑ i ∈ s, ‖z i‖ : ℝ) : ℂ) * u := by
      rw [Complex.ofReal_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl hz
    rw [hsum, norm_mul, hu, mul_one, Complex.norm_of_nonneg
      (Finset.sum_nonneg fun i _ => norm_nonneg (z i))]

/-! ## The block predicate and the characterization -/

/-- **The common-ray predicate**: the `(c, c')` block's Gram entries
lie on a common ray — there is one unit direction `u` with every entry
its own magnitude times `u`. Physically: the block carries a single
global interference phase, so the coarse entry is the block's ℓ¹ mass
times that phase — a lossless re-indexing. (The `‖u‖ = 1` conjunct is
redundant — forced by any nonzero entry, free for silent blocks — and
kept because a ray is a unit direction.) -/
def CrossAligned (f : ι → κ) (Q : QuantumMeasure ι) (c c' : κ) : Prop :=
  ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ a ∈ fiber f c, ∀ b ∈ fiber f c',
    Q.gram a b = (‖Q.gram a b‖ : ℂ) * u

/-- **A cross block attains its ledger iff it is aligned**: the
norm-additivity conjunct of `nonCancelling_iff`, in geometric form. -/
theorem crossBlock_norm_additive_iff (f : ι → κ) (Q : QuantumMeasure ι)
    {c c' : κ} (hcc : c ≠ c') :
    ‖(Q.pushforward f).gram c c'‖ = blockMass f Q c c'
      ↔ CrossAligned f Q c c' := by
  rw [pushforward_gram, blockMass_of_ne f Q hcc]
  simp only [QuantumMeasure.eventForm]
  have h1 : (∑ a ∈ fiber f c, ∑ b ∈ fiber f c', Q.gram a b)
      = ∑ p ∈ fiber f c ×ˢ fiber f c', Q.gram p.1 p.2 :=
    (Finset.sum_product' _ _ _).symm
  have h2 : (∑ a ∈ fiber f c, ∑ b ∈ fiber f c', ‖Q.gram a b‖)
      = ∑ p ∈ fiber f c ×ˢ fiber f c', ‖Q.gram p.1 p.2‖ :=
    (Finset.sum_product' _ _ _).symm
  rw [h1, h2, norm_sum_eq_sum_norm_iff]
  constructor
  · rintro ⟨u, hu, hz⟩
    exact ⟨u, hu, fun a ha b hb =>
      hz (a, b) (Finset.mem_product.mpr ⟨ha, hb⟩)⟩
  · rintro ⟨u, hu, hz⟩
    exact ⟨u, hu, fun p hp =>
      hz p.1 (Finset.mem_product.mp hp).1 p.2
        (Finset.mem_product.mp hp).2⟩

/-- **The honest unpacking, geometric form**: non-cancellation is
merged silence plus a common ray on every cross block. -/
theorem nonCancelling_iff_aligned (f : ι → κ) (Q : QuantumMeasure ι) :
    NonCancelling f Q ↔
      (∀ a b : ι, f a = f b → a ≠ b → Q.gram a b = 0) ∧
      (∀ c c' : κ, c ≠ c' → CrossAligned f Q c c') := by
  rw [nonCancelling_iff]
  refine and_congr_right fun _ => forall₂_congr fun c c' => ?_
  refine imp_congr_right fun hcc => ?_
  rw [← blockMass_of_ne f Q hcc]
  exact crossBlock_norm_additive_iff f Q hcc

/-- **The characterization, geometric form**: a coarse-graining
preserves the off-diagonal mass iff every merged block is silent and
every cross block sits on a common ray. -/
theorem offDiagMass_pushforward_eq_iff_aligned (f : ι → κ)
    (Q : QuantumMeasure ι) :
    (Q.pushforward f).offDiagMass = Q.offDiagMass ↔
      (∀ a b : ι, f a = f b → a ≠ b → Q.gram a b = 0) ∧
      (∀ c c' : κ, c ≠ c' → CrossAligned f Q c c') :=
  (offDiagMass_pushforward_eq_iff f Q).trans
    (nonCancelling_iff_aligned f Q)

/-- **The strict face, geometric form**: the mass drops strictly iff
some interference is erased into a merged alternative or some cross
block's phases disagree. -/
theorem offDiagMass_pushforward_lt_iff_aligned (f : ι → κ)
    (Q : QuantumMeasure ι) :
    (Q.pushforward f).offDiagMass < Q.offDiagMass ↔
      ¬ ((∀ a b : ι, f a = f b → a ≠ b → Q.gram a b = 0) ∧
        (∀ c c' : κ, c ≠ c' → CrossAligned f Q c c')) :=
  (offDiagMass_pushforward_lt_iff f Q).trans
    (not_congr (nonCancelling_iff_aligned f Q))

/-! ## The aligned instance -/

/-- The landed equality witness, convicted of common-ray alignment
through the new characterization, backward — zero new arithmetic. Its
ray is `u = 1`: both cross entries (`9/100`, `16/100`) are positive
reals. -/
theorem alignMeasure_crossAligned :
    CrossAligned mergeCoarse alignMeasure 0 1 :=
  ((nonCancelling_iff_aligned mergeCoarse alignMeasure).mp
    alignMeasure_nonCancelling).2 0 1 (by decide)

/-! ## The de-phased witness: strictness through misalignment alone

Branch 1 of the align witness, rotated a quarter turn; branch 2
re-mixed so the total is again a unit-weight state:
`∑v = (3/5, 12/25 + (16/25)i)`, `‖∑v‖² = 9/25 + 400/625 = 1`. The
merged pair stays orthogonal, no cross block cancels exactly — the
strict drop is pure phase disagreement, the corner neither landed
sufficient condition reaches. -/

/-- The de-phased class operators (first columns are the branch
vectors `(3/10, 0)`, `(0, (16/25)i)`, `(3/10, 12/25)`). -/
noncomputable def dephaseFamily : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![3/10, 0; 0, 0], !![0, 0; (16/25) * Complex.I, 0],
    !![3/10, 0; 12/25, 0]]

/-- The de-phased state. -/
noncomputable def dephaseState : Fin 2 → ℂ := ![1, 0]

/-- Unit total weight (the quarter-turn preserves the 3-4-5
normalization: `9/25 + (144 + 256)/625 = 1`). -/
private theorem dephaseNorm :
    ∑ α, ∑ β, decoherenceFunctional dephaseFamily dephaseState α β
      = 1 := by
  simp only [Fin.sum_univ_three, decoherenceFunctional, dephaseFamily,
    dephaseState, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  norm_num [Matrix.mulVec, Matrix.mul_apply, dotProduct,
    Fin.sum_univ_two, Pi.star_apply, Complex.star_def, map_div₀,
    map_mul, map_ofNat, Complex.conj_I, Complex.ext_iff,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- The de-phased quantum measure on `Fin 3`. -/
noncomputable def dephaseMeasure : QuantumMeasure (Fin 3) :=
  QuantumMeasure.ofPresentation dephaseFamily dephaseState dephaseNorm

private theorem dephaseMeasure_gram_01 : dephaseMeasure.gram 0 1 = 0 := by
  show decoherenceFunctional dephaseFamily dephaseState 0 1 = 0
  norm_num [decoherenceFunctional, dephaseFamily, dephaseState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_mul, map_ofNat,
    Complex.conj_I, Complex.ext_iff, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

private theorem dephaseMeasure_gram_10 : dephaseMeasure.gram 1 0 = 0 := by
  show decoherenceFunctional dephaseFamily dephaseState 1 0 = 0
  norm_num [decoherenceFunctional, dephaseFamily, dephaseState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_mul, map_ofNat,
    Complex.conj_I, Complex.ext_iff, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

private theorem dephaseMeasure_gram_02 :
    dephaseMeasure.gram 0 2 = 9 / 100 := by
  show decoherenceFunctional dephaseFamily dephaseState 0 2 = 9 / 100
  norm_num [decoherenceFunctional, dephaseFamily, dephaseState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_mul, map_ofNat,
    Complex.conj_I, Complex.ext_iff, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]

private theorem dephaseMeasure_gram_20 :
    dephaseMeasure.gram 2 0 = 9 / 100 := by
  show decoherenceFunctional dephaseFamily dephaseState 2 0 = 9 / 100
  norm_num [decoherenceFunctional, dephaseFamily, dephaseState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_mul, map_ofNat,
    Complex.conj_I, Complex.ext_iff, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]

/-- The misalignment's face: the `(1, 2)` overlap is a quarter turn
off the `(0, 2)` overlap's ray — `(192/625)i` against `9/100`. -/
theorem dephaseMeasure_gram_12 :
    dephaseMeasure.gram 1 2 = (192 / 625) * Complex.I := by
  show decoherenceFunctional dephaseFamily dephaseState 1 2
    = (192 / 625) * Complex.I
  norm_num [decoherenceFunctional, dephaseFamily, dephaseState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_mul, map_ofNat,
    Complex.conj_I, Complex.ext_iff, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]

private theorem dephaseMeasure_gram_21 :
    dephaseMeasure.gram 2 1 = -((192 / 625) * Complex.I) := by
  show decoherenceFunctional dephaseFamily dephaseState 2 1
    = -((192 / 625) * Complex.I)
  norm_num [decoherenceFunctional, dephaseFamily, dephaseState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_mul, map_ofNat,
    Complex.conj_I, Complex.ext_iff, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]

/-- The de-phased measure genuinely interferes: the `(0, 2)` overlap
is `9/100 ≠ 0`. -/
theorem dephaseMeasure_not_isDiagonal : ¬ dephaseMeasure.IsDiagonal :=
  fun h => by
    have hc := h (show (0 : Fin 3) ≠ 2 by decide)
    rw [dephaseMeasure_gram_02] at hc
    norm_num at hc

/-- **The cross block is misaligned**: its two entries sit on the rays
`1` and `i`; a common ray would need `u = 1` and `u = I` at once. No
norm is ever evaluated against an unknown — both magnitudes reduce to
real literals and the ray witnesses cancel out. -/
theorem dephaseMeasure_not_crossAligned :
    ¬ CrossAligned mergeCoarse dephaseMeasure 0 1 := by
  rintro ⟨u, hu, h⟩
  have h02 := h 0 (by decide) 2 (by decide)
  have h12 := h 1 (by decide) 2 (by decide)
  rw [dephaseMeasure_gram_02] at h02
  rw [dephaseMeasure_gram_12] at h12
  rw [show (9 / 100 : ℂ) = ((9 / 100 : ℝ) : ℂ) by
    norm_num [Complex.ofReal_div]] at h02
  rw [show (192 / 625 : ℂ) = ((192 / 625 : ℝ) : ℂ) by
    norm_num [Complex.ofReal_div]] at h12
  rw [Complex.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 100)] at h02
  rw [norm_mul, Complex.norm_I, mul_one,
    Complex.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 192 / 625)] at h12
  have h9 : ((9 / 100 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by norm_num : (9 / 100 : ℝ) ≠ 0)
  have h192 : ((192 / 625 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by norm_num : (192 / 625 : ℝ) ≠ 0)
  have hu1 : u = 1 := mul_left_cancel₀ h9
    (h02.symm.trans (mul_one _).symm)
  have hIu : Complex.I = u := mul_left_cancel₀ h192 h12
  rw [hu1] at hIu
  norm_num [Complex.ext_iff] at hIu

/-- The de-phased merge is NOT non-cancelling — through the geometric
characterization: its `(0, 1)` cross block is off the common ray. -/
theorem dephaseMeasure_not_nonCancelling :
    ¬ NonCancelling mergeCoarse dephaseMeasure := fun hnc =>
  dephaseMeasure_not_crossAligned
    (((nonCancelling_iff_aligned mergeCoarse dephaseMeasure).mp
      hnc).2 0 1 (by decide))

/-- **Misalignment forces strictness**: the de-phased measure's
off-diagonal mass drops strictly under the landed merge — pure phase
disagreement, with the merged pair orthogonal and no exact
cancellation anywhere (see the two `≠ 0` rows below). -/
theorem dephaseMeasure_offDiagMass_pushforward_lt :
    (dephaseMeasure.pushforward mergeCoarse).offDiagMass
      < dephaseMeasure.offDiagMass :=
  (offDiagMass_pushforward_lt_iff mergeCoarse dephaseMeasure).mpr
    dephaseMeasure_not_nonCancelling

/-- **No exact cancellation, `(0, 1)` face**: the coarse cross entry
is `9/100 + (192/625)i ≠ 0` — so the landed cancellation mechanism
(`offDiagMass_pushforward_lt_of_cancellation`) has no witness here;
with the merged pair silent (`gram 0 1 = 0`, the site's only merged
pair), the merged-pair mechanism has none either. The strict drop
above is invisible to both landed sufficient conditions. -/
theorem dephaseMeasure_pushforward_gram_01_ne_zero :
    (dephaseMeasure.pushforward mergeCoarse).gram 0 1 ≠ 0 := by
  intro h0
  rw [pushforward_gram] at h0
  simp only [QuantumMeasure.eventForm, fiber, Finset.sum_filter,
    Fin.sum_univ_three] at h0
  norm_num [mergeCoarse, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, dephaseMeasure_gram_02,
    dephaseMeasure_gram_12, Complex.ext_iff] at h0

/-- **No exact cancellation, `(1, 0)` face**: the conjugate cross
entry is `9/100 − (192/625)i ≠ 0` — the site's only two cross blocks
both refuse the exact-cancellation hypothesis. -/
theorem dephaseMeasure_pushforward_gram_10_ne_zero :
    (dephaseMeasure.pushforward mergeCoarse).gram 1 0 ≠ 0 := by
  intro h0
  rw [pushforward_gram] at h0
  simp only [QuantumMeasure.eventForm, fiber, Finset.sum_filter,
    Fin.sum_univ_three] at h0
  norm_num [mergeCoarse, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, dephaseMeasure_gram_20,
    dephaseMeasure_gram_21, Complex.ext_iff] at h0

end QuantumAlignment

end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumAlignment.re_conj_mul_le_norm
#print axioms Qtsl.QuantumAlignment.eq_norm_mul_of_re_conj_mul_eq
#print axioms Qtsl.QuantumAlignment.norm_sum_eq_sum_norm_iff
#print axioms Qtsl.QuantumAlignment.crossBlock_norm_additive_iff
#print axioms Qtsl.QuantumAlignment.nonCancelling_iff_aligned
#print axioms Qtsl.QuantumAlignment.offDiagMass_pushforward_eq_iff_aligned
#print axioms Qtsl.QuantumAlignment.offDiagMass_pushforward_lt_iff_aligned
#print axioms Qtsl.QuantumAlignment.alignMeasure_crossAligned
#print axioms Qtsl.QuantumAlignment.dephaseMeasure_gram_12
#print axioms Qtsl.QuantumAlignment.dephaseMeasure_not_isDiagonal
#print axioms Qtsl.QuantumAlignment.dephaseMeasure_not_crossAligned
#print axioms Qtsl.QuantumAlignment.dephaseMeasure_not_nonCancelling
#print axioms Qtsl.QuantumAlignment.dephaseMeasure_offDiagMass_pushforward_lt
#print axioms Qtsl.QuantumAlignment.dephaseMeasure_pushforward_gram_01_ne_zero
#print axioms Qtsl.QuantumAlignment.dephaseMeasure_pushforward_gram_10_ne_zero
