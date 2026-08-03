/-
Copyright (c) 2026 The maitria coalition. All rights reserved.
Released under Apache 2.0 / MIT dual license.
-/
import QtslAux.QuantumConverse

/-! # The completeness tier: GMH's `∑ R = 1` located exactly at
exhaustiveness

The landed converse module mapped the record landscape below
exhaustiveness and deliberately fenced GMH's strong-decoherence
additions (gr-qc/9509054): record *permanence* (still unclaimed here —
it needs dynamics) and **completeness** `∑_α R_α = 1`. This module
sharpens the completeness half of that fence into theorems. The answer,
kernel-checked at toy grade: **completeness is exhaustiveness** —

* complete correlated records force the family exhaustive at the state
  (`complete_records_force_exhaustive`: `(∑ C)ψ = (∑ R)ψ = ψ` — no
  hermiticity, no orthogonality, no medium decoherence consumed);
* completeness + orthogonality force idempotence
  (`complete_orthogonal_records_idem`: `R = R·∑R = R²`) — the
  projective tier is free inside the complete tier, so "complete but
  not projective" is an empty cell, by theorem and without
  hermiticity;
* consequently complete records kill the converse's gap parameter at
  every atom (`complete_records_force_weight_overlap`: overlap =
  branch weight, via the landed idempotence obstruction);
* conversely, under exhaustiveness any projective record family
  UPGRADES to a complete one
  (`projective_records_complete_of_exhaustive`) by dumping the
  remainder projector `1 − ∑ R` onto one marked atom — Hermitian,
  idempotent, annihilating every family member, and killing the state
  exactly because the family is exhaustive; hence
  `medium_implies_complete_records_of_exhaustive`: GMH's full strong
  record package (minus permanence), where their standing hypothesis
  holds;
* crown (`complete_records_iff_exhaustive`): given medium decoherence,
  **complete records exist iff the family is exhaustive at the
  state**. GMH's exhaustiveness was never a convenience — it is
  precisely what their record shape's completeness demand costs.
  (Idempotence is deliberately absent from the iff's record shape: it
  is forced back by `complete_orthogonal_records_idem`.)

At D-form grade, what strengthens: the presentation's normalization
hypothesis becomes a THEOREM (`complete_records_norm`: `∑∑ D =
⟪Σψ, Σψ⟫ = ⟪ψ, ψ⟫ = 1` for a unit state under complete records), so
`ofPresentation` fires hypothesis-free and conservativity packages
with it (`complete_records_conservativity`);
`zMeasure_norm_from_completeness` re-derives the D-form module's
hand-computed normalization through the abstract route, as an artifact
pair.

The strong-package cell table on the toys (medium decoherence holds on
every row; "records" is the landed generalized shape):

| family (state)            | records | projective | complete | locus |
|---|---|---|---|---|
| `controlledSwitch` `Ψ`    | ✓ (landed) | ✗ (landed) | ✗ (`controlledSwitch_no_complete_records`) | overlap defect `1 ≠ 1/2`; non-exhaustive |
| `soloFamily` `(3/5,4/5)`  | ✓ | ✓ (`soloFamily_projective_records`) | ✗ (`soloFamily_no_complete_records`) | non-exhaustive; defect `0` |
| `![Pz0,Pz1]` `(3/5,4/5)`  | ✓ | ✓ (landed) | ✓ (`zPair_complete_projective_records`) | — (exhaustive: the full GMH regime) |
| projective ✗, complete ✓  | — | — | — | EMPTY by `complete_orthogonal_records_idem` |

The two components of GMH's strong package fail SEPARATELY and in both
orders on the toys: projectivity dies at the overlap defect while
generalized records survive (controlled switch, landed), and
completeness dies at exhaustiveness while projective records survive
(`soloFamily`, the one-atom witness).

Scope fences, honestly: matrix grade, finite index, pure states —
"kernel-checked at toy grade", never the operator-algebra theorem.
Record permanence (gr-qc/9509054's other addition) remains unclaimed:
it quantifies over time evolution, which the toy grade does not
host. -/

namespace Qtsl

namespace QuantumCompleteness

open Matrix QuantumRecords QuantumDescent QuantumOuterStorey QuantumDForm
  QuantumConverse

variable {d : Type*} [Fintype d] {ι : Type*}

/-! ## Completeness forces exhaustiveness -/

section Forcing

variable [Fintype ι] [DecidableEq d]

/-- **Complete correlated records force exhaustiveness at the state**:
`(∑ C)ψ = ∑ (C_α ψ) = ∑ (R_α ψ) = (∑ R)ψ = ψ`. Note what is NOT
consumed: hermiticity, orthogonality, medium decoherence — completeness
and correlation alone already pin the family to GMH's standing
hypothesis. -/
theorem complete_records_force_exhaustive (C R : ι → Matrix d d ℂ)
    (ψ : d → ℂ)
    (hrec : ∀ α, C α *ᵥ ψ = R α *ᵥ ψ) (hcomp : ∑ α, R α = 1) :
    (∑ α, C α) *ᵥ ψ = ψ := by
  rw [Matrix.sum_mulVec]
  calc ∑ α, C α *ᵥ ψ
      = ∑ α, R α *ᵥ ψ := Finset.sum_congr rfl fun α _ => hrec α
    _ = (∑ α, R α) *ᵥ ψ := (Matrix.sum_mulVec _ _ _).symm
    _ = ψ := by rw [hcomp, Matrix.one_mulVec]

/-- **Completeness + orthogonality force idempotence**:
`R_α = R_α · ∑ R_β = R_α · R_α`. No hermiticity consumed. The
"complete but not projective" cell of the strong-package table is
empty by this theorem: inside the complete tier, the projective tier
is free. -/
theorem complete_orthogonal_records_idem (R : ι → Matrix d d ℂ)
    (horth : ∀ α β, α ≠ β → R α * R β = 0) (hcomp : ∑ α, R α = 1) :
    ∀ α, R α * R α = R α := by
  intro α
  symm
  calc R α
      = R α * 1 := (mul_one _).symm
    _ = R α * ∑ β, R β := by rw [hcomp]
    _ = ∑ β, R α * R β := by rw [Finset.mul_sum]
    _ = R α * R α := Finset.sum_eq_single_of_mem α (Finset.mem_univ α)
        fun β _ hβ => horth α β (Ne.symm hβ)

/-- **Complete records kill the overlap defect at every atom**: the
converse module's gap parameter `⟪ψ, C_α ψ⟫ − D(α,α)` vanishes under
completeness — idempotence is forced
(`complete_orthogonal_records_idem`), and the landed idempotence
obstruction does the rest. -/
theorem complete_records_force_weight_overlap (C R : ι → Matrix d d ℂ)
    (ψ : d → ℂ)
    (hherm : ∀ α, (R α).IsHermitian)
    (horth : ∀ α β, α ≠ β → R α * R β = 0) (hcomp : ∑ α, R α = 1)
    (hrec : ∀ α, C α *ᵥ ψ = R α *ᵥ ψ) (α : ι) :
    branchOverlap C ψ α = decoherenceFunctional C ψ α α :=
  projective_records_force_weight_overlap C R ψ hherm
    (complete_orthogonal_records_idem R horth hcomp) hrec α

/-! ## The D-form strengthening: normalization becomes a theorem -/

/-- **Under complete records, the presentation normalizes itself**: for
a unit state, `∑∑ D(α,β) = ⟪Σψ, Σψ⟫ = ⟪ψ, ψ⟫ = 1`. The `ofPresentation`
hypothesis of the D-form module is discharged rather than assumed —
what GMH's strong package buys at measure grade. -/
theorem complete_records_norm (C R : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1)
    (hrec : ∀ α, C α *ᵥ ψ = R α *ᵥ ψ) (hcomp : ∑ α, R α = 1) :
    ∑ α, ∑ β, decoherenceFunctional C ψ α β = 1 := by
  have hsum : ∑ β, C β *ᵥ ψ = ψ := by
    rw [← Matrix.sum_mulVec]
    exact complete_records_force_exhaustive C R ψ hrec hcomp
  calc ∑ α, ∑ β, decoherenceFunctional C ψ α β
      = ∑ α, star ψ ⬝ᵥ (C α *ᵥ ψ) := by
        refine Finset.sum_congr rfl fun α _ => ?_
        simp only [decoherenceFunctional]
        rw [← sum_dotProduct, ← star_sum, hsum]
    _ = star ψ ⬝ᵥ ∑ α, C α *ᵥ ψ := by rw [dotProduct_sum]
    _ = 1 := by rw [hsum, hψ]

/-- Conservativity with the normalization hypothesis discharged: a
complete record family on a unit state makes its presentation a
quantum measure for free, and that measure is classical. -/
theorem complete_records_conservativity [DecidableEq ι]
    (C R : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1)
    (hherm : ∀ α, (R α).IsHermitian)
    (horth : ∀ α β, α ≠ β → R α * R β = 0)
    (hrec : ∀ α, C α *ᵥ ψ = R α *ᵥ ψ) (hcomp : ∑ α, R α = 1) :
    ∃ (p : ι → ℝ) (hp : ∀ α, 0 ≤ p α) (hs : ∑ α, p α = 1),
      QuantumMeasure.ofPresentation C ψ
        (complete_records_norm C R ψ hψ hrec hcomp)
      = QuantumMeasure.classical p hp hs :=
  QuantumMeasure.records_conservativity _ hherm horth hrec

end Forcing

/-! ## The completion: exhaustiveness manufactures completeness

The remainder projector `1 − ∑ R` of a projective, mutually orthogonal
family is Hermitian, idempotent, annihilates every family member, and
— exactly when the family is exhaustive at the state — kills the state.
Dumping it onto one marked atom completes the family without breaking
any conjunct. -/

section Completion

variable [Fintype ι] [DecidableEq d]

/-- The remainder projector of a family: what is left of the identity
after the family's total. -/
private noncomputable def remainderProjector (R : ι → Matrix d d ℂ) :
    Matrix d d ℂ :=
  1 - ∑ γ, R γ

omit [DecidableEq d] in
private theorem sum_mul_single (R : ι → Matrix d d ℂ)
    (hidem : ∀ α, R α * R α = R α)
    (horth : ∀ α β, α ≠ β → R α * R β = 0) (β : ι) :
    (∑ γ, R γ) * R β = R β := by
  rw [Finset.sum_mul,
    Finset.sum_eq_single_of_mem β (Finset.mem_univ β)
      fun γ _ hγ => horth γ β hγ]
  exact hidem β

omit [DecidableEq d] in
private theorem single_mul_sum (R : ι → Matrix d d ℂ)
    (hidem : ∀ α, R α * R α = R α)
    (horth : ∀ α β, α ≠ β → R α * R β = 0) (β : ι) :
    R β * ∑ γ, R γ = R β := by
  rw [Finset.mul_sum,
    Finset.sum_eq_single_of_mem β (Finset.mem_univ β)
      fun γ _ hγ => horth β γ (Ne.symm hγ)]
  exact hidem β

private theorem remainderProjector_mul (R : ι → Matrix d d ℂ)
    (hidem : ∀ α, R α * R α = R α)
    (horth : ∀ α β, α ≠ β → R α * R β = 0) (β : ι) :
    remainderProjector R * R β = 0 := by
  unfold remainderProjector
  rw [sub_mul, one_mul, sum_mul_single R hidem horth β, sub_self]

private theorem mul_remainderProjector (R : ι → Matrix d d ℂ)
    (hidem : ∀ α, R α * R α = R α)
    (horth : ∀ α β, α ≠ β → R α * R β = 0) (β : ι) :
    R β * remainderProjector R = 0 := by
  unfold remainderProjector
  rw [mul_sub, mul_one, single_mul_sum R hidem horth β, sub_self]

private theorem remainderProjector_idem (R : ι → Matrix d d ℂ)
    (hidem : ∀ α, R α * R α = R α)
    (horth : ∀ α β, α ≠ β → R α * R β = 0) :
    remainderProjector R * remainderProjector R = remainderProjector R := by
  have hS : (∑ γ, R γ) * ∑ γ, R γ = ∑ γ, R γ := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun γ _ => single_mul_sum R hidem horth γ
  unfold remainderProjector
  rw [sub_mul, one_mul, mul_sub, mul_one, hS, sub_self, sub_zero]

omit [Fintype d] in
private theorem remainderProjector_isHermitian (R : ι → Matrix d d ℂ)
    (hherm : ∀ α, (R α).IsHermitian) :
    (remainderProjector R).IsHermitian := by
  have hs : (∑ γ, R γ).IsHermitian := by
    show (∑ γ, R γ)ᴴ = ∑ γ, R γ
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun γ _ => (hherm γ).eq
  exact Matrix.isHermitian_one.sub hs

private theorem remainderProjector_mulVec (C R : ι → Matrix d d ℂ)
    (ψ : d → ℂ)
    (hexh : (∑ α, C α) *ᵥ ψ = ψ) (hrec : ∀ α, C α *ᵥ ψ = R α *ᵥ ψ) :
    remainderProjector R *ᵥ ψ = 0 := by
  have hS : (∑ γ, R γ) *ᵥ ψ = ψ := by
    rw [Matrix.sum_mulVec]
    calc ∑ γ, R γ *ᵥ ψ
        = ∑ γ, C γ *ᵥ ψ := Finset.sum_congr rfl fun γ _ => (hrec γ).symm
      _ = (∑ γ, C γ) *ᵥ ψ := (Matrix.sum_mulVec _ _ _).symm
      _ = ψ := hexh
  unfold remainderProjector
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hS, sub_self]

/-- **The completion**: under exhaustiveness, any projective record
family upgrades to a COMPLETE one — dump the remainder projector onto
one marked atom. Every conjunct survives: the remainder is Hermitian,
idempotent, annihilates each family member, and kills the state
(exhaustiveness is consumed exactly there, and is witnessed
non-droppable by `soloFamily_no_complete_records` below). -/
theorem projective_records_complete_of_exhaustive [DecidableEq ι]
    [Nonempty ι] (C R : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hexh : (∑ α, C α) *ᵥ ψ = ψ)
    (hherm : ∀ α, (R α).IsHermitian)
    (hidem : ∀ α, R α * R α = R α)
    (horth : ∀ α β, α ≠ β → R α * R β = 0)
    (hrec : ∀ α, C α *ᵥ ψ = R α *ᵥ ψ) :
    ∃ R' : ι → Matrix d d ℂ,
      (∀ α, (R' α).IsHermitian) ∧
      (∀ α, R' α * R' α = R' α) ∧
      (∀ α β, α ≠ β → R' α * R' β = 0) ∧
      (∑ α, R' α = 1) ∧
      (∀ α, C α *ᵥ ψ = R' α *ᵥ ψ) := by
  refine ⟨fun α => R α + if α = Classical.arbitrary ι
      then remainderProjector R else 0,
    fun α => ?_, fun α => ?_, fun α β hαβ => ?_, ?_, fun α => ?_⟩
  · -- Hermitian
    by_cases hα : α = Classical.arbitrary ι
    · simp only [if_pos hα]
      exact (hherm α).add (remainderProjector_isHermitian R hherm)
    · simp only [if_neg hα, add_zero]
      exact hherm α
  · -- idempotent
    by_cases hα : α = Classical.arbitrary ι
    · simp only [if_pos hα]
      rw [add_mul, mul_add, mul_add, hidem α,
        mul_remainderProjector R hidem horth α,
        remainderProjector_mul R hidem horth α,
        remainderProjector_idem R hidem horth]
      abel
    · simp only [if_neg hα, add_zero]
      exact hidem α
  · -- mutually orthogonal
    by_cases hα : α = Classical.arbitrary ι <;>
      by_cases hβ : β = Classical.arbitrary ι
    · exact absurd (hα.trans hβ.symm) hαβ
    · simp only [if_pos hα, if_neg hβ, add_zero, add_mul]
      rw [horth α β hαβ, remainderProjector_mul R hidem horth β, add_zero]
    · simp only [if_neg hα, if_pos hβ, add_zero, mul_add]
      rw [horth α β hαβ, mul_remainderProjector R hidem horth α, add_zero]
    · simp only [if_neg hα, if_neg hβ, add_zero]
      exact horth α β hαβ
  · -- complete
    rw [Finset.sum_add_distrib,
      Fintype.sum_ite_eq' (Classical.arbitrary ι)
        fun _ => remainderProjector R]
    unfold remainderProjector
    abel
  · -- correlated
    by_cases hα : α = Classical.arbitrary ι
    · simp only [if_pos hα]
      rw [Matrix.add_mulVec,
        remainderProjector_mulVec C R ψ hexh hrec, add_zero]
      exact hrec α
    · simp only [if_neg hα, add_zero]
      exact hrec α

/-- **GMH's full strong record package (minus permanence), where their
standing hypothesis holds**: medium decoherence + exhaustiveness
manufacture a Hermitian, idempotent, mutually orthogonal, COMPLETE,
correlated record family — the landed projective converse, completed
through the remainder projector. -/
theorem medium_implies_complete_records_of_exhaustive [DecidableEq ι]
    [Nonempty ι] (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hexh : (∑ α, C α) *ᵥ ψ = ψ) (hmed : MediumDecoherent C ψ) :
    ∃ R : ι → Matrix d d ℂ,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α, R α * R α = R α) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∑ α, R α = 1) ∧
      (∀ α, C α *ᵥ ψ = R α *ᵥ ψ) := by
  obtain ⟨R, hherm, hidem, horth, hrec⟩ :=
    medium_implies_projective_records_of_exhaustive C ψ hexh hmed
  exact projective_records_complete_of_exhaustive C R ψ hexh
    hherm hidem horth hrec

/-- **The crown: completeness is exhaustiveness.** Given medium
decoherence, a complete record family exists iff the family is
exhaustive at the state. Idempotence is deliberately absent from the
record shape on the left — it is forced back by
`complete_orthogonal_records_idem` (and the witness produced by the
reverse direction carries it anyway). GMH's exhaustiveness hypothesis
was never a convenience: it is exactly what `∑ R = 1` costs. -/
theorem complete_records_iff_exhaustive [DecidableEq ι] [Nonempty ι]
    (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hmed : MediumDecoherent C ψ) :
    (∃ R : ι → Matrix d d ℂ,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∑ α, R α = 1) ∧
      (∀ α, C α *ᵥ ψ = R α *ᵥ ψ)) ↔ (∑ α, C α) *ᵥ ψ = ψ := by
  constructor
  · rintro ⟨R, -, -, hcomp, hrec⟩
    exact complete_records_force_exhaustive C R ψ hrec hcomp
  · intro hexh
    obtain ⟨R, hherm, _hidem, horth, hcomp, hrec⟩ :=
      medium_implies_complete_records_of_exhaustive C ψ hexh hmed
    exact ⟨R, hherm, horth, hcomp, hrec⟩

end Completion

/-! ## Witnesses: the strong package's two conjuncts fail separately -/

section Toys

/-- **The controlled switch admits no complete record family** — the
refutation demands neither hermiticity nor orthogonality nor
idempotence: completeness + correlation alone force exhaustiveness,
which the landed `controlledSwitch_not_exhaustive` refutes. Against
the landed `controlledSwitch_records` (generalized records exist) and
`controlledSwitch_no_projective_records` (defect kills projectivity):
the strong package's two components fail SEPARATELY on this toy, each
with its own obstruction. -/
theorem controlledSwitch_no_complete_records :
    ¬ ∃ R : SwitchOrder → TwoQubits,
        (∑ α, R α = 1) ∧
        (∀ α, controlledSwitch α *ᵥ switchState = R α *ᵥ switchState) := by
  rintro ⟨R, hcomp, hrec⟩
  exact controlledSwitch_not_exhaustive
    (complete_records_force_exhaustive controlledSwitch R switchState
      hrec hcomp)

/-- The z-pair is exhaustive on the 3-4-5 state (the landed D-form
witness family, its exhaustiveness now a named lemma). -/
theorem zPair_exhaustive :
    (∑ α, ![Pz0, Pz1] α) *ᵥ ![(3/5 : ℂ), 4/5] = ![(3/5 : ℂ), 4/5] := by
  funext i
  simp only [Fin.sum_univ_two]
  fin_cases i <;>
    norm_num [Pz0, Pz1, Matrix.add_mulVec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

/-- The z-pair is medium-decoherent on the 3-4-5 state. -/
theorem zPair_mediumDecoherent :
    MediumDecoherent ![Pz0, Pz1] ![(3/5 : ℂ), 4/5] := by
  intro α β hαβ
  fin_cases α <;> fin_cases β <;>
    first
      | exact absurd rfl hαβ
      | (simp only [decoherenceFunctional]
         norm_num [Pz0, Pz1, Matrix.mulVec, dotProduct,
           Fin.sum_univ_two, Pi.star_apply, Complex.star_def,
           map_div₀, map_ofNat, Complex.ext_iff, Complex.add_re,
           Complex.add_im, Complex.mul_re, Complex.mul_im,
           Complex.div_re, Complex.div_im, Complex.normSq_apply])

/-- **The full GMH regime, exercised end-to-end**: on the exhaustive
z-pair, the completed converse manufactures the entire strong record
package — Hermitian, idempotent, orthogonal, complete, correlated. -/
theorem zPair_complete_projective_records :
    ∃ R : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α, R α * R α = R α) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∑ α, R α = 1) ∧
      (∀ α, ![Pz0, Pz1] α *ᵥ ![(3/5 : ℂ), 4/5]
        = R α *ᵥ ![(3/5 : ℂ), 4/5]) :=
  medium_implies_complete_records_of_exhaustive _ _
    zPair_exhaustive zPair_mediumDecoherent

/-- The 3-4-5 state is a unit vector: `9/25 + 16/25 = 1`. -/
theorem zState_unit :
    star ![(3/5 : ℂ), 4/5] ⬝ᵥ ![(3/5 : ℂ), 4/5] = 1 := by
  norm_num [dotProduct, Fin.sum_univ_two, Pi.star_apply,
    Complex.star_def, map_div₀, map_ofNat, Complex.ext_iff,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im, Complex.normSq_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

private theorem Pz0_add_Pz1 : Pz0 + Pz1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pz0, Pz1]

/-- **The artifact pair**: the D-form module's hand-computed
normalization (`zMeasure_norm`, private there), re-derived through the
abstract route — the z-projectors are their own complete record family
on a unit state, so `complete_records_norm` yields the total weight
with no matrix arithmetic. -/
theorem zMeasure_norm_from_completeness :
    ∑ α, ∑ β,
      decoherenceFunctional ![Pz0, Pz1] ![(3/5 : ℂ), 4/5] α β = 1 := by
  refine complete_records_norm ![Pz0, Pz1] ![Pz0, Pz1] _ zState_unit
    (fun α => rfl) ?_
  rw [Fin.sum_univ_two]
  exact Pz0_add_Pz1

/-! ### The one-atom witness: projective records without complete ones

`soloFamily` isolates the completion theorem's exhaustiveness
hypothesis: a single projector on a state it does not fix. Projective
records exist (the projector is its own record family — orthogonality
vacuous on one atom); complete records do not, because the family is
not exhaustive. The (projective ✓, complete ✗) cell is inhabited. -/

/-- The one-atom family: `Pz0` alone, on the 3-4-5 state. -/
noncomputable def soloFamily : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ := ![Pz0]

private theorem Pz0_idem : Pz0 * Pz0 = Pz0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pz0, Matrix.mul_apply, Fin.sum_univ_two]

/-- The solo family carries the full projective record shape (its own
projector; orthogonality vacuous on one atom). -/
theorem soloFamily_projective_records :
    ∃ R : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α, R α * R α = R α) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∀ α, soloFamily α *ᵥ ![(3/5 : ℂ), 4/5]
        = R α *ᵥ ![(3/5 : ℂ), 4/5]) := by
  refine ⟨![Pz0], fun α => ?_, fun α => ?_,
    fun α β hαβ => absurd (Subsingleton.elim α β) hαβ, fun α => rfl⟩
  · fin_cases α
    exact Pz0_isHermitian
  · fin_cases α
    exact Pz0_idem

/-- The solo family is not exhaustive: `Pz0` kills the second
coordinate of the 3-4-5 state (`0 ≠ 4/5`). -/
theorem soloFamily_not_exhaustive :
    (∑ α, soloFamily α) *ᵥ ![(3/5 : ℂ), 4/5] ≠ ![(3/5 : ℂ), 4/5] := by
  intro h
  have h1 := congrFun h 1
  simp only [soloFamily, Fin.sum_univ_one] at h1
  norm_num [Pz0, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Complex.ext_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at h1

/-- **Projective records are not enough for completeness**: the solo
family has them, yet admits no complete record family — the completion
theorem's exhaustiveness hypothesis is witnessed non-droppable
(refutation, house style: hermiticity/orthogonality/idempotence not
even demanded). -/
theorem soloFamily_no_complete_records :
    ¬ ∃ R : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ,
        (∑ α, R α = 1) ∧
        (∀ α, soloFamily α *ᵥ ![(3/5 : ℂ), 4/5]
          = R α *ᵥ ![(3/5 : ℂ), 4/5]) := by
  rintro ⟨R, hcomp, hrec⟩
  exact soloFamily_not_exhaustive
    (complete_records_force_exhaustive soloFamily R _ hrec hcomp)

end Toys

end QuantumCompleteness

end Qtsl

-- Axiom receipts (expected: exactly [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumCompleteness.complete_records_force_exhaustive
#print axioms Qtsl.QuantumCompleteness.complete_orthogonal_records_idem
#print axioms Qtsl.QuantumCompleteness.complete_records_force_weight_overlap
#print axioms Qtsl.QuantumCompleteness.complete_records_norm
#print axioms Qtsl.QuantumCompleteness.complete_records_conservativity
#print axioms Qtsl.QuantumCompleteness.projective_records_complete_of_exhaustive
#print axioms Qtsl.QuantumCompleteness.medium_implies_complete_records_of_exhaustive
#print axioms Qtsl.QuantumCompleteness.complete_records_iff_exhaustive
#print axioms Qtsl.QuantumCompleteness.controlledSwitch_no_complete_records
#print axioms Qtsl.QuantumCompleteness.zPair_exhaustive
#print axioms Qtsl.QuantumCompleteness.zPair_mediumDecoherent
#print axioms Qtsl.QuantumCompleteness.zPair_complete_projective_records
#print axioms Qtsl.QuantumCompleteness.zState_unit
#print axioms Qtsl.QuantumCompleteness.zMeasure_norm_from_completeness
#print axioms Qtsl.QuantumCompleteness.soloFamily_projective_records
#print axioms Qtsl.QuantumCompleteness.soloFamily_not_exhaustive
#print axioms Qtsl.QuantumCompleteness.soloFamily_no_complete_records
