/-
Copyright (c) 2026 The maitria coalition. All rights reserved.
Released under Apache 2.0 / MIT dual license.
-/
import QtslAux.QuantumAlignment

/-! # Spectral strictness: when the interference spectrum strictly shrinks

The tower module landed the set-level antitone statement —
`interferenceSpectrum_pushforward_subset`, "coarse-graining never mints
interference values" — and the strictness/alignment modules
characterized the OTHER antitone invariant, the off-diagonal mass. This
module characterizes when the spectrum inclusion is STRICT, and shows
the two strictness notions are fully independent.

* **The saturation vocabulary** (`Saturated`): an event is saturated
  (fiber-closed) for a merge when it never splits a fiber. Saturated
  events are exactly the preimages of coarse events
  (`saturated_fiberEvent`, `fiberEvent_image_of_saturated`) — exactly
  the questions the coarse observer can still ask.

* **The membership characterization**
  (`mem_interferenceSpectrum_pushforward` /
  `interferenceSpectrum_pushforward_eq`): the coarse spectrum is the
  fine spectrum through saturated pairs — a coarse value is exactly a
  fine interference value attained at a disjoint pair of fiber-closed
  events.

* **The ⊊-characterization**
  (`interferenceSpectrum_pushforward_ssubset_iff`): the spectrum
  strictly shrinks iff some exhibited interference value is attained
  by NO saturated disjoint pair. The quantifier over ALL saturated
  pairs is the honest form: a value's particular witness can die (its
  events split fibers) while the value persists through a DIFFERENT,
  fiber-closed pair — witness-death is adjudicated value-wide, never
  pair-locally. Injective (padding) merges preserve the spectrum on
  the nose (`interferenceSpectrum_pushforward_of_injective`): under
  them every event is saturated.

* **The independence table**, on ONE site with ONE merge (the landed
  `Fin 3` / `mergeCoarse` witness family), completing the 2×2:

  |                   | spectrum preserved      | spectrum ⊊              |
  |-------------------|-------------------------|-------------------------|
  | **mass preserved**| injective / diagonal    | `alignMeasure`          |
  | **mass ⊊**        | `dephaseMeasure`        | `mergeMeasure` (landed) |

  - `alignMeasure` preserves its off-diagonal mass on the nose (landed
    `alignMeasure_offDiagMass_pushforward_eq`), yet its spectrum
    strictly shrinks (`alignMeasure_interferenceSpectrum_pushforward_ssubset`:
    the value `9/50`, exhibited at `({0}, {2})`, is attained by no
    coarse pair — the coarse spectrum is `{0, 1/2}`). **Mass equality
    does not imply spectrum equality.**
  - `dephaseMeasure` drops its mass strictly (landed
    `dephaseMeasure_offDiagMass_pushforward_lt`, partial cancellation),
    yet its spectrum is exactly preserved
    (`dephaseMeasure_interferenceSpectrum_pushforward_eq`: every fine
    value is `0` or `9/50`, and `9/50` is re-attained at the coarse
    pair `({0}, {1})` through the phase-rotated coarse entry). **Strict
    mass drop does not imply spectrum shrinkage.**

  Mass is blind to WHICH values carry it; the spectrum is blind to HOW
  MUCH mass a value carries. Neither antitone invariant refines the
  other: a tower rung can be Lyapunov-strict yet spectrum-lazy
  (dephase) or Lyapunov-lazy yet spectrum-strict (align).

* **The multiplicity subtlety, kernel-checked**: the dephase witness
  `({0}, {2})` of `9/50` is NOT saturated
  (`mergeCoarse_singleton_not_saturated` — `{0}` splits the fiber
  `{0, 1}`), yet its value survives coarse-graining; the align witness
  of the SAME shape dies value-and-all (saturating it changes `9/50`
  to `1/2` by picking up the within-fiber partner). "Every witness
  merges-or-cancels away" is honest only when "witness" ranges over
  every pair attaining the value.

Scope fences inherited from the record tier: finite index types,
matrix grade, toy grade at the witnesses; the physical reading (the
spectrum = the set of distinguishable interference phenomena; the
coarse spectrum = the fine landscape seen through fiber-closed
questions) is interpretation, not new claims. -/

namespace Qtsl

namespace QuantumSpectrum

open Matrix DiamondSite QuantumRecords QuantumDForm QuantumTransport
  QuantumCoarseGraining QuantumDiamondMeasure QuantumTower
  QuantumStrictness QuantumAlignment

universe u

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
  [DecidableEq κ]

/-! ## The saturation vocabulary -/

/-- **Saturated (fiber-closed) events**: `A` never splits a fiber of
`f` — whenever it contains one fine alternative it contains every
alternative the merge identifies with it. Saturated events are exactly
the preimages of coarse events (`saturated_fiberEvent` and
`fiberEvent_image_of_saturated` are the two directions): the questions
the coarse observer can still ask. -/
def Saturated (f : ι → κ) (A : Finset ι) : Prop :=
  ∀ ⦃a b : ι⦄, f a = f b → a ∈ A → b ∈ A

omit [Fintype κ] [DecidableEq ι] in
/-- Preimages of coarse events are saturated. -/
theorem saturated_fiberEvent (f : ι → κ) (A : Finset κ) :
    Saturated f (fiberEvent f A) := by
  intro a b hab ha
  rw [mem_fiberEvent] at ha ⊢
  exact hab ▸ ha

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- Under an injective (padding) merge every event is saturated:
nothing merges, so nothing splits. -/
theorem saturated_of_injective {f : ι → κ}
    (hf : Function.Injective f) (A : Finset ι) : Saturated f A :=
  fun _ _ hab ha => hf hab ▸ ha

omit [Fintype κ] [DecidableEq ι] in
/-- A saturated event is the preimage of its own image: saturation is
exactly "being a coarse question". -/
theorem fiberEvent_image_of_saturated {f : ι → κ} {A : Finset ι}
    (hA : Saturated f A) : fiberEvent f (A.image f) = A := by
  ext a
  rw [mem_fiberEvent, Finset.mem_image]
  constructor
  · rintro ⟨b, hb, hba⟩
    exact hA hba hb
  · intro ha
    exact ⟨a, ha, rfl⟩

omit [Fintype ι] [Fintype κ] [DecidableEq ι] in
/-- Disjointness pushes forward along images when ONE side is
saturated: a shared coarse atom would pull a fine alternative of `A`
into `B` through `B`'s fiber-closure. -/
theorem disjoint_image_of_saturated {f : ι → κ} {A B : Finset ι}
    (hAB : Disjoint A B) (hB : Saturated f B) :
    Disjoint (A.image f) (B.image f) := by
  rw [Finset.disjoint_left]
  rintro c hcA hcB
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hcA
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hcB
  exact Finset.disjoint_left.mp hAB ha (hB hba hb)

/-! ## Generic plumbing: empty pairs interfere trivially -/

/-- Interference against the empty event vanishes (left). -/
theorem interference_empty_left (Q : QuantumMeasure ι) (B : Finset ι) :
    Q.interference ∅ B = 0 := by
  simp [QuantumMeasure.interference, QuantumMeasure.sorkinMeasure,
    QuantumMeasure.eventForm]

/-- Interference against the empty event vanishes (right). -/
theorem interference_empty_right (Q : QuantumMeasure ι) (A : Finset ι) :
    Q.interference A ∅ = 0 := by
  simp [QuantumMeasure.interference, QuantumMeasure.sorkinMeasure,
    QuantumMeasure.eventForm]

/-! ## The membership characterization -/

/-- **The coarse spectrum is the fine spectrum through saturated
pairs**: a value lies in the merged measure's interference spectrum
iff the FINE measure attains it at a disjoint pair of fiber-closed
events. Forward: take preimages. Backward: take images — the value
transfers because a saturated event is the preimage of its own image,
and disjointness transfers through one side's saturation. -/
theorem mem_interferenceSpectrum_pushforward (f : ι → κ)
    (Q : QuantumMeasure ι) {z : ℂ} :
    z ∈ (Q.pushforward f).interferenceSpectrum ↔
      ∃ A B : Finset ι, Disjoint A B ∧ Saturated f A ∧ Saturated f B ∧
        Q.interference A B = z := by
  constructor
  · rintro ⟨A, B, hAB, rfl⟩
    exact ⟨fiberEvent f A, fiberEvent f B, fiberEvent_disjoint f hAB,
      saturated_fiberEvent f A, saturated_fiberEvent f B,
      (pushforward_interference f Q A B).symm⟩
  · rintro ⟨A, B, hAB, hA, hB, rfl⟩
    refine ⟨A.image f, B.image f,
      disjoint_image_of_saturated hAB hB, ?_⟩
    rw [pushforward_interference, fiberEvent_image_of_saturated hA,
      fiberEvent_image_of_saturated hB]

/-- The set-level form of the membership characterization. -/
theorem interferenceSpectrum_pushforward_eq (f : ι → κ)
    (Q : QuantumMeasure ι) :
    (Q.pushforward f).interferenceSpectrum =
      {z | ∃ A B : Finset ι, Disjoint A B ∧ Saturated f A ∧
        Saturated f B ∧ Q.interference A B = z} :=
  Set.ext fun _ => mem_interferenceSpectrum_pushforward f Q

/-! ## The ⊊-characterization -/

/-- **When the spectrum strictly shrinks**: the merged measure's
interference spectrum is a STRICT subset of the fine one iff some
exhibited interference value is attained by NO saturated disjoint
pair. The universal quantifier over saturated pairs is the honest
form of "every witness of the value merges-or-cancels away": a
particular witness dying (splitting a fiber, its value shifting under
saturation) never kills the value by itself — the value dies only
when every fiber-closed pair misses it. The module's two instances
realize both outcomes on one site. -/
theorem interferenceSpectrum_pushforward_ssubset_iff (f : ι → κ)
    (Q : QuantumMeasure ι) :
    (Q.pushforward f).interferenceSpectrum ⊂ Q.interferenceSpectrum ↔
      ∃ A B : Finset ι, Disjoint A B ∧ ∀ A' B' : Finset ι,
        Disjoint A' B' → Saturated f A' → Saturated f B' →
          Q.interference A' B' ≠ Q.interference A B := by
  rw [Set.ssubset_iff_of_subset
    (interferenceSpectrum_pushforward_subset f Q)]
  constructor
  · rintro ⟨z, hzfine, hzcoarse⟩
    obtain ⟨A, B, hAB, rfl⟩ := hzfine
    exact ⟨A, B, hAB, fun A' B' h1 h2 h3 heq =>
      hzcoarse ((mem_interferenceSpectrum_pushforward f Q).mpr
        ⟨A', B', h1, h2, h3, heq⟩)⟩
  · rintro ⟨A, B, hAB, hall⟩
    refine ⟨Q.interference A B, ⟨A, B, hAB, rfl⟩, fun hz => ?_⟩
    obtain ⟨A', B', h1, h2, h3, heq⟩ :=
      (mem_interferenceSpectrum_pushforward f Q).mp hz
    exact hall A' B' h1 h2 h3 heq

/-- **Padding merges preserve the spectrum on the nose**: under an
injective merge every event is saturated, so every fine witness is
already a coarse one — the spectrum face of the lazy-rung padding
row. -/
theorem interferenceSpectrum_pushforward_of_injective (f : ι → κ)
    (Q : QuantumMeasure ι) (hf : Function.Injective f) :
    (Q.pushforward f).interferenceSpectrum = Q.interferenceSpectrum := by
  refine Set.Subset.antisymm
    (interferenceSpectrum_pushforward_subset f Q) ?_
  rintro z ⟨A, B, hAB, rfl⟩
  exact (mem_interferenceSpectrum_pushforward f Q).mpr
    ⟨A, B, hAB, saturated_of_injective hf A,
      saturated_of_injective hf B, rfl⟩

/-- **The tower-facing face**: rung `n` of a refinement tower strictly
shrinks the interference spectrum iff some stage-`n` interference
value is attained by no pair saturated for the step merge. -/
theorem interferenceSpectrum_stageMeasure_succ_ssubset_iff
    {X : ℕ → Type u} [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    (Q : QuantumMeasure (X 0)) (step : ∀ n, X n → X (n + 1)) (n : ℕ) :
    (stageMeasure Q step (n + 1)).interferenceSpectrum ⊂
        (stageMeasure Q step n).interferenceSpectrum ↔
      ∃ A B : Finset (X n), Disjoint A B ∧ ∀ A' B' : Finset (X n),
        Disjoint A' B' → Saturated (step n) A' → Saturated (step n) B' →
          (stageMeasure Q step n).interference A' B' ≠
            (stageMeasure Q step n).interference A B :=
  interferenceSpectrum_pushforward_ssubset_iff (step n)
    (stageMeasure Q step n)

/-! ## The align instance: mass preserved, spectrum strictly shrinks

The landed equality witness (`alignMeasure_offDiagMass_pushforward_eq`
— a genuine merge preserving the off-diagonal mass on the nose) LOSES
spectrum values: its fine spectrum is `{0, 9/50, 8/25, 1/2}`, its
coarse spectrum `{0, 1/2}`. Mass equality does not imply spectrum
equality. (Value rows re-derived locally, the lane's precedent for the
strictness module's private rows.) -/

private theorem alignMeasure_gram_02 :
    alignMeasure.gram 0 2 = 9 / 100 := by
  show decoherenceFunctional alignFamily alignState 0 2 = 9 / 100
  norm_num [decoherenceFunctional, alignFamily, alignState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_ofNat,
    Complex.ext_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two]

private theorem alignMeasure_gram_20 :
    alignMeasure.gram 2 0 = 9 / 100 := by
  show decoherenceFunctional alignFamily alignState 2 0 = 9 / 100
  norm_num [decoherenceFunctional, alignFamily, alignState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_ofNat,
    Complex.ext_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two]

private theorem alignMeasure_gram_12 :
    alignMeasure.gram 1 2 = 16 / 100 := by
  show decoherenceFunctional alignFamily alignState 1 2 = 16 / 100
  norm_num [decoherenceFunctional, alignFamily, alignState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_ofNat,
    Complex.ext_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two]

private theorem alignMeasure_gram_21 :
    alignMeasure.gram 2 1 = 16 / 100 := by
  show decoherenceFunctional alignFamily alignState 2 1 = 16 / 100
  norm_num [decoherenceFunctional, alignFamily, alignState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_ofNat,
    Complex.ext_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two]

private theorem alignCoarse_gram_01 :
    (alignMeasure.pushforward mergeCoarse).gram 0 1 = 1 / 4 := by
  rw [pushforward_gram]
  simp only [QuantumMeasure.eventForm, fiber, Finset.sum_filter,
    Fin.sum_univ_three]
  norm_num [mergeCoarse, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, alignMeasure_gram_02,
    alignMeasure_gram_12]

private theorem alignCoarse_gram_10 :
    (alignMeasure.pushforward mergeCoarse).gram 1 0 = 1 / 4 := by
  rw [pushforward_gram]
  simp only [QuantumMeasure.eventForm, fiber, Finset.sum_filter,
    Fin.sum_univ_three]
  norm_num [mergeCoarse, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, alignMeasure_gram_20,
    alignMeasure_gram_21]

/-- The value that dies: the fine pair `({0}, {2})` exhibits the
interference value `9/50` (its two cross entries, hermitian). -/
theorem alignMeasure_interference_zero_two :
    alignMeasure.interference {0} {2} = 9 / 50 := by
  rw [alignMeasure.interference_eq
    (show Disjoint ({0} : Finset (Fin 3)) {2} by decide)]
  simp only [QuantumMeasure.eventForm, Finset.sum_singleton]
  rw [alignMeasure_gram_02, alignMeasure_gram_20]
  norm_num

/-- Shape enumeration for two-point events, decide-free (membership
case split + extensionality). -/
private theorem finset_fin_two_cases (C : Finset (Fin 2)) :
    C = ∅ ∨ C = {0} ∨ C = {1} ∨ C = {0, 1} := by
  by_cases h0 : (0 : Fin 2) ∈ C <;> by_cases h1 : (1 : Fin 2) ∈ C
  · exact Or.inr (Or.inr (Or.inr (Finset.ext fun x => by
      fin_cases x <;> simp [h0, h1])))
  · exact Or.inr (Or.inl (Finset.ext fun x => by
      fin_cases x <;> simp [h0, h1]))
  · exact Or.inr (Or.inr (Or.inl (Finset.ext fun x => by
      fin_cases x <;> simp [h0, h1])))
  · exact Or.inl (Finset.ext fun x => by fin_cases x <;> simp [h0, h1])

set_option maxHeartbeats 800000 in
/-- The coarse value classification: on the merged (two-point) site,
every disjoint pair's interference is `0` or `1/2` — in particular
never `9/50`. -/
theorem alignMeasure_pushforward_interference_cases
    (A B : Finset (Fin 2)) (h : Disjoint A B) :
    (alignMeasure.pushforward mergeCoarse).interference A B = 0 ∨
      (alignMeasure.pushforward mergeCoarse).interference A B = 1 / 2 := by
  rcases finset_fin_two_cases A with rfl | rfl | rfl | rfl <;>
    rcases finset_fin_two_cases B with rfl | rfl | rfl | rfl <;>
      first
        | (exfalso; revert h; decide)
        | (rw [(alignMeasure.pushforward mergeCoarse).interference_eq h]
           simp only [QuantumMeasure.eventForm, Finset.sum_empty,
             Finset.sum_const_zero, Finset.sum_singleton,
             alignCoarse_gram_01, alignCoarse_gram_10]
           norm_num)

/-- **Mass equality does not imply spectrum equality**: the landed
equality witness — a genuine non-injective merge of a genuinely
quantum measure preserving the off-diagonal mass on the nose
(`alignMeasure_offDiagMass_pushforward_eq`) — nevertheless STRICTLY
shrinks the interference spectrum: the value `9/50` is exhibited fine
(`({0}, {2})`) and attained by no coarse pair (`{0, 1/2}` is the whole
coarse landscape). Saturating the witness changes its value (`9/50 →
1/2`, picking up the within-fiber partner `8/25`): merged away, in
the ⊊-characterization's sense. -/
theorem alignMeasure_interferenceSpectrum_pushforward_ssubset :
    (alignMeasure.pushforward mergeCoarse).interferenceSpectrum ⊂
      alignMeasure.interferenceSpectrum := by
  refine ⟨interferenceSpectrum_pushforward_subset mergeCoarse
    alignMeasure, fun hsub => ?_⟩
  have h950 : (9 / 50 : ℂ) ∈
      (alignMeasure.pushforward mergeCoarse).interferenceSpectrum :=
    hsub ⟨{0}, {2}, by decide, alignMeasure_interference_zero_two⟩
  obtain ⟨A, B, hAB, hval⟩ := h950
  rcases alignMeasure_pushforward_interference_cases A B hAB with
    h0 | hhalf
  · rw [hval] at h0
    norm_num at h0
  · rw [hval] at hhalf
    norm_num at hhalf

/-! ## The dephase instance: mass strictly drops, spectrum preserved

The landed partial-cancellation witness
(`dephaseMeasure_offDiagMass_pushforward_lt` — strict mass drop
through pure phase misalignment) loses NO spectrum values: its
Re-profile puts every disjoint pair's interference in `{0, 9/50}`, and
`9/50` is re-attained at the coarse pair `({0}, {1})` through the
phase-rotated coarse entry `9/100 + (192/625)i`. Strict mass drop does
not imply spectrum shrinkage. -/

private theorem dephaseMeasure_gram_01 :
    dephaseMeasure.gram 0 1 = 0 := by
  show decoherenceFunctional dephaseFamily dephaseState 0 1 = 0
  norm_num [decoherenceFunctional, dephaseFamily, dephaseState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_mul, map_ofNat,
    Complex.conj_I, Complex.ext_iff, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

private theorem dephaseMeasure_gram_10 :
    dephaseMeasure.gram 1 0 = 0 := by
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

private theorem dephaseMeasure_gram_21 :
    dephaseMeasure.gram 2 1 = -((192 / 625) * Complex.I) := by
  show decoherenceFunctional dephaseFamily dephaseState 2 1
    = -((192 / 625) * Complex.I)
  norm_num [decoherenceFunctional, dephaseFamily, dephaseState,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_div₀, map_mul, map_ofNat,
    Complex.conj_I, Complex.ext_iff, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]

private theorem dephaseCoarse_gram_01 :
    (dephaseMeasure.pushforward mergeCoarse).gram 0 1
      = 9 / 100 + (192 / 625) * Complex.I := by
  rw [pushforward_gram]
  simp only [QuantumMeasure.eventForm, fiber, Finset.sum_filter,
    Fin.sum_univ_three]
  norm_num [mergeCoarse, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, dephaseMeasure_gram_02,
    dephaseMeasure_gram_12, Complex.ext_iff]

private theorem dephaseCoarse_gram_10 :
    (dephaseMeasure.pushforward mergeCoarse).gram 1 0
      = 9 / 100 - (192 / 625) * Complex.I := by
  rw [pushforward_gram]
  simp only [QuantumMeasure.eventForm, fiber, Finset.sum_filter,
    Fin.sum_univ_three]
  norm_num [mergeCoarse, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, dephaseMeasure_gram_20,
    dephaseMeasure_gram_21, Complex.ext_iff]

/-- Shape enumeration for three-point events, decide-free (membership
case split + extensionality). -/
private theorem finset_fin_three_cases (C : Finset (Fin 3)) :
    C = ∅ ∨ C = {0} ∨ C = {1} ∨ C = {2} ∨ C = {0, 1} ∨ C = {0, 2} ∨
      C = {1, 2} ∨ C = {0, 1, 2} := by
  by_cases h0 : (0 : Fin 3) ∈ C <;> by_cases h1 : (1 : Fin 3) ∈ C <;>
    by_cases h2 : (2 : Fin 3) ∈ C
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Finset.ext fun x => by fin_cases x <;> simp [h0, h1, h2])))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (Finset.ext fun x => by fin_cases x <;> simp [h0, h1, h2])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (Finset.ext fun x => by fin_cases x <;> simp [h0, h1, h2]))))))
  · exact Or.inr (Or.inl
      (Finset.ext fun x => by fin_cases x <;> simp [h0, h1, h2]))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (Finset.ext fun x => by fin_cases x <;> simp [h0, h1, h2])))))))
  · exact Or.inr (Or.inr (Or.inl
      (Finset.ext fun x => by fin_cases x <;> simp [h0, h1, h2])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (Finset.ext fun x => by fin_cases x <;> simp [h0, h1, h2]))))
  · exact Or.inl (Finset.ext fun x => by fin_cases x <;> simp [h0, h1, h2])

set_option maxHeartbeats 6400000 in
/-- The fine value classification: every disjoint pair's interference
is `0` or `9/50` — the Re-profile has a single nonzero entry pair
(`(0, 2)`), so the value depends only on whether the split separates
`0` from `2`; the `i`-bearing `(1, 2)` overlap enters every
interference hermitianly and cancels. -/
theorem dephaseMeasure_interference_cases (A B : Finset (Fin 3))
    (h : Disjoint A B) :
    dephaseMeasure.interference A B = 0 ∨
      dephaseMeasure.interference A B = 9 / 50 := by
  rcases finset_fin_three_cases A with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases finset_fin_three_cases B with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  first
    | (exfalso; revert h; decide)
    | (rw [dephaseMeasure.interference_eq h]
       simp only [QuantumMeasure.eventForm, Finset.sum_empty,
         Finset.sum_const_zero,
         Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide),
         Finset.sum_pair (show (0 : Fin 3) ≠ 2 by decide),
         Finset.sum_pair (show (1 : Fin 3) ≠ 2 by decide),
         Finset.sum_singleton, dephaseMeasure_gram_01,
         dephaseMeasure_gram_10, dephaseMeasure_gram_02,
         dephaseMeasure_gram_20, dephaseMeasure_gram_12,
         dephaseMeasure_gram_21]
       norm_num [Complex.ext_iff])

/-- The coarse re-attainment witness: the coarse pair `({0}, {1})`
attains `9/50` — the hermitian sum of the two phase-rotated coarse
entries, their `i`-parts cancelling. -/
theorem dephaseMeasure_pushforward_interference_zero_one :
    (dephaseMeasure.pushforward mergeCoarse).interference {0} {1}
      = 9 / 50 := by
  rw [(dephaseMeasure.pushforward mergeCoarse).interference_eq
    (show Disjoint ({0} : Finset (Fin 2)) {1} by decide)]
  simp only [QuantumMeasure.eventForm, Finset.sum_singleton]
  rw [dephaseCoarse_gram_01, dephaseCoarse_gram_10]
  ring

/-- **Strict mass drop does not imply spectrum shrinkage**: the landed
partial-cancellation witness — strict off-diagonal mass drop through
pure phase misalignment
(`dephaseMeasure_offDiagMass_pushforward_lt`) — preserves its
interference spectrum EXACTLY: every fine value is `0` or `9/50`
(`dephaseMeasure_interference_cases`), and both are coarse-attained.
The two antitone invariants of the tower order its rungs
differently. -/
theorem dephaseMeasure_interferenceSpectrum_pushforward_eq :
    (dephaseMeasure.pushforward mergeCoarse).interferenceSpectrum =
      dephaseMeasure.interferenceSpectrum := by
  refine Set.Subset.antisymm
    (interferenceSpectrum_pushforward_subset mergeCoarse
      dephaseMeasure) ?_
  rintro z ⟨A, B, hAB, rfl⟩
  rcases dephaseMeasure_interference_cases A B hAB with h0 | h950
  · rw [h0]
    exact zero_mem_interferenceSpectrum _
  · rw [h950]
    exact ⟨{0}, {1}, by decide,
      dephaseMeasure_pushforward_interference_zero_one⟩

/-- The dying witness whose value survives: the fine pair
`({0}, {2})` exhibits `9/50`… -/
theorem dephaseMeasure_interference_zero_two :
    dephaseMeasure.interference {0} {2} = 9 / 50 := by
  rw [dephaseMeasure.interference_eq
    (show Disjoint ({0} : Finset (Fin 3)) {2} by decide)]
  simp only [QuantumMeasure.eventForm, Finset.sum_singleton]
  rw [dephaseMeasure_gram_02, dephaseMeasure_gram_20]
  norm_num

/-- …and is NOT saturated (`{0}` splits the merged fiber `{0, 1}`):
the witness dies under coarse-graining, while its value persists
through the saturated pair `({0, 1}, {2})`-class questions
(`dephaseMeasure_pushforward_interference_zero_one`). The
⊊-characterization's quantifier over ALL saturated pairs — rather
than over the witnesses one holds — is exactly this specimen's
lesson. -/
theorem mergeCoarse_singleton_not_saturated :
    ¬ Saturated mergeCoarse ({0} : Finset (Fin 3)) := fun h =>
  absurd (h (a := 0) (b := 1) (by decide) (by decide)) (by decide)

end QuantumSpectrum

end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumSpectrum.saturated_fiberEvent
#print axioms Qtsl.QuantumSpectrum.saturated_of_injective
#print axioms Qtsl.QuantumSpectrum.fiberEvent_image_of_saturated
#print axioms Qtsl.QuantumSpectrum.disjoint_image_of_saturated
#print axioms Qtsl.QuantumSpectrum.interference_empty_left
#print axioms Qtsl.QuantumSpectrum.interference_empty_right
#print axioms Qtsl.QuantumSpectrum.mem_interferenceSpectrum_pushforward
#print axioms Qtsl.QuantumSpectrum.interferenceSpectrum_pushforward_eq
#print axioms Qtsl.QuantumSpectrum.interferenceSpectrum_pushforward_ssubset_iff
#print axioms Qtsl.QuantumSpectrum.interferenceSpectrum_pushforward_of_injective
#print axioms Qtsl.QuantumSpectrum.interferenceSpectrum_stageMeasure_succ_ssubset_iff
#print axioms Qtsl.QuantumSpectrum.alignMeasure_interference_zero_two
#print axioms Qtsl.QuantumSpectrum.alignMeasure_pushforward_interference_cases
#print axioms Qtsl.QuantumSpectrum.alignMeasure_interferenceSpectrum_pushforward_ssubset
#print axioms Qtsl.QuantumSpectrum.dephaseMeasure_interference_cases
#print axioms Qtsl.QuantumSpectrum.dephaseMeasure_pushforward_interference_zero_one
#print axioms Qtsl.QuantumSpectrum.dephaseMeasure_interferenceSpectrum_pushforward_eq
#print axioms Qtsl.QuantumSpectrum.dephaseMeasure_interference_zero_two
#print axioms Qtsl.QuantumSpectrum.mergeCoarse_singleton_not_saturated
