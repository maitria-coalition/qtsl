/-
Copyright (c) 2026 The maitria coalition. All rights reserved.
Released under Apache 2.0 / MIT dual license.
-/
import QtslAux.QuantumConverse

/-! # The record–medium–weak hierarchy: one strict chain over arbitrary
class-operator families

Assembly of the landed record kinematics into a single kernel-checked
package: over arbitrary finite-dimensional class-operator families (any
index type, any finite dimension, pure state),

  record-supported ⊊ medium-decoherent ⊊ weakly consistent

(`records_medium_weak_strict_hierarchy`). On standard pure exhaustive
families the first inclusion is an equivalence, not a strict one —
medium decoherence carries automatic records, and in Gell-Mann–Hartle's
own projective shape (`medium_implies_projective_records_of_exhaustive`,
restated below as the companion pair) — so the strictness of the first
inclusion lives only in the enlarged, possibly sub-exhaustive, domain of
arbitrary class-operator families. The chain and its companion are one
artifact deliberately: quoting the strict inclusion without the
exhaustive-case equivalence would misstate where the gap lives.

Ingredients, all landed and cited rather than re-proven:

* inclusion 1 — `records_imply_medium` (Gell-Mann–Hartle 1993,
  Phys. Rev. D 47, 3345), wrapped as `RecordSupported.mediumDecoherent`
  on the named predicate;
* inclusion 2 — `MediumDecoherent.weaklyConsistent` (diagonal ⟹
  Griffiths condition);
* gap 1 — `phaseFamily` (medium-decoherent, no record family:
  `phaseFamily_mediumDecoherent` + `phaseFamily_no_records`);
* gap 2 — `zyFamily` (weakly consistent, not medium-decoherent: the
  landed `exists_weaklyConsistent_without_records` rules out records;
  here the sharper not-medium fact is proven for the same family,
  `zyFamily_not_mediumDecoherent` — `D((0,0),(1,0)) = i/2` has nonzero
  imaginary part, which weak consistency tolerates and medium
  decoherence refuses).

Scope fences (inherited from the ingredient modules): matrix grade
(`Matrix d d ℂ`), finite dimension, pure global states. Completeness
(`∑ R = 1`) and record permanence (gr-qc/9509054's strong-decoherence
additions) are not claimed anywhere in this module. -- [classical]
-/

namespace Qtsl

namespace QuantumHierarchy

open Matrix QuantumRecords QuantumConverse

universe u v

variable {d : Type u} [Fintype d] {ι : Type v}

/-- A class-operator family at a pure state is **record-supported** when
some family of mutually orthogonal Hermitian record observables is
correlated with it at the state (`C_α ψ = R_α ψ`) — the
generalized-record shape of Gell-Mann–Hartle 1993 (Phys. Rev. D 47,
3345), with hypotheses exactly as consumed by the landed
`records_imply_medium`. Defined for arbitrary class-operator families:
no exhaustiveness, no projectivity of the `C α`, arbitrary index type. -/
def RecordSupported (C : ι → Matrix d d ℂ) (ψ : d → ℂ) : Prop :=
  ∃ R : ι → Matrix d d ℂ,
    (∀ α, (R α).IsHermitian) ∧
    (∀ α β, α ≠ β → R α * R β = 0) ∧
    (∀ α, C α *ᵥ ψ = R α *ᵥ ψ)

/-- **Inclusion 1**: record-supported families are medium decoherent —
the landed `records_imply_medium`, read on the named predicate. Holds
over arbitrary class-operator families. -/
theorem RecordSupported.mediumDecoherent {C : ι → Matrix d d ℂ}
    {ψ : d → ℂ} (h : RecordSupported C ψ) : MediumDecoherent C ψ := by
  obtain ⟨R, hherm, horth, hrec⟩ := h
  exact records_imply_medium C R ψ hherm horth hrec

/-- **Gap-1 strictness witness**: the phase family is not
record-supported — a fortiori from the landed `phaseFamily_no_records`,
whose negation refuses even the weaker Hermitian-and-correlated pair
(orthogonality not demanded). With `phaseFamily_mediumDecoherent`, the
first inclusion is strict on arbitrary class-operator families. -/
theorem phaseFamily_not_recordSupported :
    ¬ RecordSupported phaseFamily ![1, 1] := by
  rintro ⟨R, hherm, -, hrec⟩
  exact phaseFamily_no_records ⟨R, hherm, hrec⟩

/-- The z-then-y family is weakly consistent: every off-diagonal
interference term is purely imaginary. (The first half of the landed
`exists_weaklyConsistent_without_records`, exposed for the named
witness family.) -/
theorem zyFamily_weaklyConsistent : WeaklyConsistent zyFamily ![1, 1] := by
  intro α β hne
  obtain ⟨a₁, b₁⟩ := α
  obtain ⟨a₂, b₂⟩ := β
  simp only [decoherenceFunctional, zyFamily]
  fin_cases a₁ <;> fin_cases b₁ <;> fin_cases a₂ <;> fin_cases b₂ <;>
    first
      | exact (hne rfl).elim
      | norm_num [Yp, Ym, Pz0, Pz1, Matrix.mulVec, Matrix.mul_apply, dotProduct,
    Fin.sum_univ_two, Pi.star_apply, Complex.star_def, map_div₀, map_neg,
    map_one, map_ofNat, Complex.conj_I, Complex.ext_iff, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im, Complex.I_re, Complex.I_im, Complex.normSq_apply]

/-- **Gap-2 strictness witness**: the z-then-y family is not medium
decoherent — `D((0,0),(1,0)) = i/2 ≠ 0` (purely imaginary: exactly what
weak consistency tolerates and medium decoherence refuses). The landed
`exists_weaklyConsistent_without_records` rules out records for this
family; this is the sharper fact for the same witness, so the second
inclusion is strict with no new family needed. -/
theorem zyFamily_not_mediumDecoherent :
    ¬ MediumDecoherent zyFamily ![1, 1] := by
  intro h
  have hcontra := h (0, 0) (1, 0) (by decide)
  simp only [decoherenceFunctional, zyFamily] at hcontra
  norm_num [Yp, Ym, Pz0, Pz1, Matrix.mulVec, Matrix.mul_apply, dotProduct,
    Fin.sum_univ_two, Pi.star_apply, Complex.star_def, map_div₀, map_neg,
    map_one, map_ofNat, Complex.conj_I, Complex.ext_iff, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im, Complex.I_re, Complex.I_im, Complex.normSq_apply] at hcontra

/-- **The strict chain, one package**: over arbitrary finite-dimensional
class-operator families, record-supported ⊊ medium-decoherent ⊊ weakly
consistent. On standard pure exhaustive families the first inclusion is
an equivalence (`recordSupported_iff_mediumDecoherent_of_exhaustive` —
records are automatic there, in projective shape), so its strictness
lives only in the enlarged, possibly sub-exhaustive, domain quantified
here. Four conjuncts: the two inclusions, universally over arbitrary
families; the two strictness witnesses (`phaseFamily`: medium without
record support; `zyFamily`: weak consistency without medium
decoherence), each a landed concrete two-dimensional family. -/
theorem records_medium_weak_strict_hierarchy :
    (∀ {d : Type u} {ι : Type v} [Fintype d]
        (C : ι → Matrix d d ℂ) (ψ : d → ℂ),
        RecordSupported C ψ → MediumDecoherent C ψ)
  ∧ (∀ {d : Type u} {ι : Type v} [Fintype d]
        (C : ι → Matrix d d ℂ) (ψ : d → ℂ),
        MediumDecoherent C ψ → WeaklyConsistent C ψ)
  ∧ (∃ (C : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (ψ : Fin 2 → ℂ),
        MediumDecoherent C ψ ∧ ¬ RecordSupported C ψ)
  ∧ (∃ (C : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (ψ : Fin 2 → ℂ),
        WeaklyConsistent C ψ ∧ ¬ MediumDecoherent C ψ) :=
  ⟨fun _C _ψ h => h.mediumDecoherent,
   fun _C _ψ h => h.weaklyConsistent,
   ⟨phaseFamily, ![1, 1], phaseFamily_mediumDecoherent,
     phaseFamily_not_recordSupported⟩,
   ⟨zyFamily, ![1, 1], zyFamily_weaklyConsistent,
     zyFamily_not_mediumDecoherent⟩⟩

/-! ## The automatic-records companion

On exhaustive families the first link of the chain collapses to an
equivalence: medium decoherence manufactures its own records, and in
the projective shape at that. Stated adjacent to the chain on purpose —
the strict inclusion and the exhaustive-case equivalence are two halves
of one honest statement about where the gap between record support and
medium decoherence does and does not live. -/

/-- **Automatic projective records on exhaustive families** — the
landed `medium_implies_projective_records_of_exhaustive`
(Gell-Mann–Hartle's eq. 4.11 record shape: orthogonal projections
correlated with the class operators), restated beside the chain. For
exhaustive class-operator families, medium decoherence is never
record-free: the gap-1 witness of
`records_medium_weak_strict_hierarchy` is necessarily non-exhaustive
(`phaseFamily_not_exhaustive`). Completeness (`∑ R = 1`) and permanence
remain unclaimed. -/
theorem projectiveRecords_of_mediumDecoherent_of_exhaustive [Fintype ι]
    (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hexh : (∑ α, C α) *ᵥ ψ = ψ) (hmed : MediumDecoherent C ψ) :
    ∃ R : ι → Matrix d d ℂ,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α, R α * R α = R α) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∀ α, C α *ᵥ ψ = R α *ᵥ ψ) :=
  medium_implies_projective_records_of_exhaustive C ψ hexh hmed

/-- **The exhaustive-case equivalence**: on exhaustive class-operator
families at a pure state, record support and medium decoherence
coincide at the formal grade. Forward is inclusion 1 of the chain;
backward drops the idempotence conjunct of the automatic projective
records. This equivalence is exactly why the chain's first strictness
witness must live outside the exhaustive domain. -/
theorem recordSupported_iff_mediumDecoherent_of_exhaustive [Fintype ι]
    (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hexh : (∑ α, C α) *ᵥ ψ = ψ) :
    RecordSupported C ψ ↔ MediumDecoherent C ψ := by
  constructor
  · exact RecordSupported.mediumDecoherent
  · intro hmed
    obtain ⟨R, hherm, _hidem, horth, hrec⟩ :=
      projectiveRecords_of_mediumDecoherent_of_exhaustive C ψ hexh hmed
    exact ⟨R, hherm, horth, hrec⟩

/-- The companion's exhaustiveness hypothesis is load-bearing: without
it the equivalence is false, and the chain's own gap-1 witness refutes
the unhypothesized statement (`phaseFamily` is medium-decoherent yet
not record-supported). The strict chain and the exhaustive-case
equivalence are consistent precisely because the equivalence never
leaves the exhaustive domain. -/
theorem companion_exhaustiveness_load_bearing :
    ¬ (∀ (C : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (ψ : Fin 2 → ℂ),
        RecordSupported C ψ ↔ MediumDecoherent C ψ) := fun h =>
  phaseFamily_not_recordSupported
    ((h phaseFamily ![1, 1]).mpr phaseFamily_mediumDecoherent)

end QuantumHierarchy

end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumHierarchy.RecordSupported.mediumDecoherent
#print axioms Qtsl.QuantumHierarchy.phaseFamily_not_recordSupported
#print axioms Qtsl.QuantumHierarchy.zyFamily_weaklyConsistent
#print axioms Qtsl.QuantumHierarchy.zyFamily_not_mediumDecoherent
#print axioms Qtsl.QuantumHierarchy.records_medium_weak_strict_hierarchy
#print axioms Qtsl.QuantumHierarchy.projectiveRecords_of_mediumDecoherent_of_exhaustive
#print axioms Qtsl.QuantumHierarchy.recordSupported_iff_mediumDecoherent_of_exhaustive
#print axioms Qtsl.QuantumHierarchy.companion_exhaustiveness_load_bearing
