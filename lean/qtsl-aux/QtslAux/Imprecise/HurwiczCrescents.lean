import QtslAux.Imprecise.PenaltyEnvelope
import QtslAux.Imprecise.Compose
import Mathlib.Data.Set.Lattice

/-! # Hurwicz superlevels are infinitary unions of crescents

The Hurwicz criterion `hurwicz α M f = α·upperE + (1−α)·lowerE` is neither
an upper nor a lower envelope, so its superlevel classes do not live at
either polarity alone.  What they are is an **infinitary disjunction**: the
superlevel `{f | lo ≤ H_α(f)}` is the union, over the *splitting segment*
`{(a,b) | lo ≤ α·a + (1−α)·b}` (the admissible chords), of **crescents**
`{a ≤ upperE} ∩ {b ≤ lowerE}` — each crescent one ∃-polarized escape face
at `a` and one ∀-polarized floor face at `b`.  This module mechanizes the
decomposition and its honest finitary complement:

* `hurwicz_ge_iff_exists_chord` / `hurwiczSuperlevel_eq_iUnion_crescents` —
  **the decomposition**: pointwise, the attained pair
  `(upperE f, lowerE f)` is itself an admissible chord, so the superlevel is
  *exactly* the union of crescents; at this ℚ-valued finite stratum the
  dense subfamily of rational chords is the whole index.  In the σ-algebra
  reading, closedness of the superlevel class becomes a corollary of the
  index structure (a compactly-indexed directed union of closed crescents)
  rather than an assumption on the class.
* `le_hurwicz_of_chord` — **the certificate-pair rule**: a floor certificate
  at `b`, an escape certificate at `a`, and the chord check discharge the
  Hurwicz threshold.  A certificate pair *is* a choice of disjunct; that the
  two extreme chords suffice at the root of a composition is linearity
  (`rootHurwicz_eq_mix` in `Imprecise.Compose`), and that the optimal chord
  *re-chooses* under composition is the tower failure witnessed in
  `Imprecise.TowerWitness` — transport across composition is pointwise in
  the chord index, not uniform.
* `finite_chords_strict` — **no finite subfamily of chords yields the
  class**: for `0 < α < 1` and any finite admissible chord family, a
  two-point model sits on the Hurwicz line beyond every listed escape face,
  satisfying the threshold while escaping every listed crescent (its floor
  face fails).  The between-the-chords witness: finite unions of quadrants
  cannot cover a half-plane bounded by a strictly sloped line.  So the
  disjunction is irreducibly infinitary, and any finitely-presented
  certificate layer for Hurwicz thresholds must carry the chord as *data*
  (the certificate-pair rule), never enumerate the class.
-/

namespace Qtsl.Imprecise

open Finset

section Crescents

variable {X : Type*} [Fintype X] {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **The certificate-pair rule**: a floor certificate at `b`, an escape
certificate at `a`, and the chord check discharge the Hurwicz threshold.
A certificate pair is a choice of disjunct in the crescent decomposition. -/
theorem le_hurwicz_of_chord {α lo a b : ℚ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {M : ι → FinPMF X} {f : X → ℚ}
    (hchord : lo ≤ α * a + (1 - α) * b)
    (ha : a ≤ upperE M f) (hb : b ≤ lowerE M f) :
    lo ≤ hurwicz α M f := by
  have h1 := mul_le_mul_of_nonneg_left ha hα0
  have h2 := mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℚ) ≤ 1 - α)
  simp only [hurwicz]
  linarith

/-- **The pointwise decomposition**: the Hurwicz threshold holds iff some
admissible chord's crescent contains the gamble.  Forward: the attained
pair `(upperE f, lowerE f)` is itself an admissible chord. -/
theorem hurwicz_ge_iff_exists_chord (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (M : ι → FinPMF X) (f : X → ℚ) (lo : ℚ) :
    lo ≤ hurwicz α M f
      ↔ ∃ a b : ℚ, lo ≤ α * a + (1 - α) * b
          ∧ a ≤ upperE M f ∧ b ≤ lowerE M f := by
  constructor
  · intro h
    exact ⟨upperE M f, lowerE M f, by simpa [hurwicz] using h, le_rfl, le_rfl⟩
  · rintro ⟨a, b, hchord, ha, hb⟩
    exact le_hurwicz_of_chord hα0 hα1 hchord ha hb

/-- **The set-level decomposition**: the Hurwicz superlevel class is the
union of crescents over the splitting segment — an infinitary disjunction,
each disjunct one escape face (∃-polarity) and one floor face (∀-polarity). -/
theorem hurwiczSuperlevel_eq_iUnion_crescents (α : ℚ) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (M : ι → FinPMF X) (lo : ℚ) :
    {f : X → ℚ | lo ≤ hurwicz α M f}
      = ⋃ p : {q : ℚ × ℚ // lo ≤ α * q.1 + (1 - α) * q.2},
          ({f : X → ℚ | p.val.1 ≤ upperE M f}
            ∩ {f : X → ℚ | p.val.2 ≤ lowerE M f}) := by
  ext f
  constructor
  · intro h
    refine Set.mem_iUnion.mpr
      ⟨⟨(upperE M f, lowerE M f), by simpa [hurwicz] using h⟩, ?_, ?_⟩
    · show upperE M f ≤ upperE M f
      exact le_rfl
    · show lowerE M f ≤ lowerE M f
      exact le_rfl
  · intro h
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp h
    obtain ⟨hp1, hp2⟩ := hp
    have ha : p.val.1 ≤ upperE M f := hp1
    have hb : p.val.2 ≤ lowerE M f := hp2
    exact le_hurwicz_of_chord hα0 hα1 p.property ha hb

end Crescents

section FiniteStrictness

/-- **No finite subfamily of chords yields the class**: for a genuinely
mixed attitude (`0 < α < 1`) and any finite family of admissible chords, a
two-point model on the Hurwicz line beyond every listed escape face
satisfies the threshold while escaping every listed crescent.  The
disjunction over the splitting segment is irreducibly infinitary. -/
theorem finite_chords_strict {α lo : ℚ} (hα0 : 0 < α) (hα1 : α < 1)
    (S : Finset (ℚ × ℚ)) (hS : ∀ p ∈ S, lo ≤ α * p.1 + (1 - α) * p.2) :
    ∃ (M : Bool → FinPMF Bool) (f : Bool → ℚ),
      lo ≤ hurwicz α M f ∧
        ∀ p ∈ S, ¬(p.2 ≤ lowerE M f ∧ p.1 ≤ upperE M f) := by
  have h1α : (0 : ℚ) < 1 - α := by linarith
  have h1α' : (1 : ℚ) - α ≠ 0 := ne_of_gt h1α
  set A : ℚ := 1 + |lo| + S.sum (fun p => |p.1|) with hA_def
  set B : ℚ := (lo - α * A) / (1 - α) with hB_def
  have hsum : (0 : ℚ) ≤ S.sum (fun p => |p.1|) :=
    Finset.sum_nonneg fun p _ => abs_nonneg _
  have hA_lo : lo ≤ A := by
    have habs := le_abs_self lo
    have := abs_nonneg lo
    linarith
  have hlin : (1 - α) * B = lo - α * A := by
    rw [hB_def, mul_comm, div_mul_cancel₀ _ h1α']
  have hchord : α * A + (1 - α) * B = lo := by linarith
  have hAB : B ≤ A := by nlinarith [hlin, hA_lo, h1α]
  have hup : upperE (fun b : Bool => FinPMF.dirac b)
      (fun b => bif b then A else B) = A := by
    apply le_antisymm
    · refine upperE_le fun b => ?_
      rw [FinPMF.exp_dirac]
      cases b
      · simpa using hAB
      · simp
    · have := exp_le_upperE (fun b : Bool => FinPMF.dirac b)
        (fun b => bif b then A else B) true
      rwa [FinPMF.exp_dirac] at this
  have hlow : lowerE (fun b : Bool => FinPMF.dirac b)
      (fun b => bif b then A else B) = B := by
    apply le_antisymm
    · have := lowerE_le_exp (fun b : Bool => FinPMF.dirac b)
        (fun b => bif b then A else B) false
      rwa [FinPMF.exp_dirac] at this
    · refine le_lowerE fun b => ?_
      rw [FinPMF.exp_dirac]
      cases b
      · simp
      · simpa using hAB
  refine ⟨fun b => FinPMF.dirac b, fun b => bif b then A else B, ?_, ?_⟩
  · simp only [hurwicz, hup, hlow]
    linarith
  · rintro p hp ⟨hbf, -⟩
    rw [hlow] at hbf
    have hmem := Finset.single_le_sum
      (f := fun q : ℚ × ℚ => |q.1|) (fun q _ => abs_nonneg _) hp
    have hpa : p.1 + 1 ≤ A := by
      have := le_abs_self p.1
      have := abs_nonneg lo
      linarith
    have hchord_p := hS p hp
    have hstep : (1 - α) * p.2 ≤ (1 - α) * B :=
      mul_le_mul_of_nonneg_left hbf (le_of_lt h1α)
    have hmul : α * (p.1 + 1) ≤ α * A :=
      mul_le_mul_of_nonneg_left hpa (le_of_lt hα0)
    nlinarith [hchord, hchord_p, hstep, hmul, hα0]

end FiniteStrictness

end Qtsl.Imprecise
