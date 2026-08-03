/-
Copyright (c) 2026 The maitria coalition. All rights reserved.
Released under Apache 2.0 / MIT dual license.
-/
import QtslAux.QuantumDForm

/-! # The Gell-Mann–Hartle converse, completed on the two-fibre toy:
the reconstruction theorem's hypothesis landscape below exhaustiveness

`QtslAux.QuantumRecords` proved both directions of the GMH records
identity (gr-qc/9210010 §IV, eq. 4.11): `records_imply_medium`
(index-generic) and `medium_implies_records_of_exhaustive` (pure
states, exhaustive families, branch projectors). GMH's own families
are exhaustive by construction and their records are *projections*;
the two-fibre toy of `QtslAux.QuantumOuterStorey` (`SwitchOrder`) is
neither — its two atoms select one outcome pair from a four-outcome
fine family, which is why that probe fenced record-existence out of
scope there. This module maps the
converse's exact hypothesis landscape below exhaustiveness, and fires
it on the switch index itself.

Everything is governed by one scalar per atom, the **state–branch
overlap** `branchOverlap C ψ α = ⟪ψ, C_α ψ⟫`:

* records force every overlap **real**
  (`records_force_real_overlap` — invisible in GMH's setting, where
  exhaustiveness forces the overlap to equal the branch weight);
* projective (GMH-shaped) records force overlap = branch weight
  exactly (`projective_records_force_weight_overlap`);
* medium decoherence + real overlaps + (zero branch ∨ nonzero
  overlap) **reconstructs** records
  (`medium_implies_records_of_real_overlap`), strictly generalizing
  the landed exhaustive converse on two axes: no exhaustiveness, and
  no `[Fintype ι]` (the reconstruction is pointwise);
* the landed converse is subsumed (`records_of_exhaustive_via_overlap`
  via `exhaustive_overlap_eq_weight`), and upgrades to the projection
  record shape GMH actually construct
  (`medium_implies_projective_records_of_exhaustive`, via
  `branchProjector_idem`).

The failure strata, each witnessed kernel-checked (with the landed
coherent switch as stratum zero):

| family (state) | medium | records | projective | failure locus |
|---|---|---|---|---|
| `switchFamily` `(1,1)`      | ✗ | ✗ | ✗ | interference `D₀₁ = 1/2` (landed) |
| `phaseFamily` `(1,1)`       | ✓ | ✗ | ✗ | phase: overlap `= i` |
| `roomFamily` `(1,0)`        | ✓ | ✗ | ✗ | room: overlap `0` on a nonzero branch |
| `controlledSwitch` `Ψ`      | ✓ | **✓** | ✗ | defect: overlap `1 ≠ 1/2` weight |
| `![Pz0,Pz1]` `(3/5,4/5)`    | ✓ | ✓ | ✓ | — (exhaustive: the GMH regime) |

The controlled-switch row is the payoff pair: records EXIST
(`controlledSwitch_records` — manufactured non-exhaustively, repairing
the probe's fence: exhaustiveness was sufficient, never necessary),
yet NO projective record family exists
(`controlledSwitch_no_projective_records`) — the medium-vs-strong gap
of gr-qc/9509054 witnessed on the two-fibre toy, located at the overlap
defect `overlap − weight = 1 − 1/2`. And the crown: on BOTH fibres of
the toy, *which-order records exist iff the order index's quantum
measure is diagonal* (`controlled_records_iff_isDiagonal`,
`switch_records_iff_isDiagonal`) — the GMH biconditional completed at
D-form grade, populated oppositely at the two fibres.

Scope fences, honestly: matrix grade, finite index, pure states —
"kernel-checked at toy grade", never the operator-algebra theorem.
GMH's full strong-decoherence package (gr-qc/9509054: record
*permanence*, completeness `∑ R = 1`) is not claimed; the projective
tier here is idempotence added to the landed record shape. The
`overlap = 0` stratum's exact geometry (in higher dimension a
zero-overlap branch CAN carry records, given spectral room) is out of
toy scope: the nonvanishing hypothesis is the clean sufficient
boundary, witnessed non-droppable in `d = 2`. -/

namespace Qtsl

namespace QuantumConverse

open Matrix QuantumRecords QuantumDescent QuantumOuterStorey QuantumDForm
open scoped ComplexOrder Kronecker

variable {d : Type*} [Fintype d] {ι : Type*}

/-! ## The overlap, and the two obstructions -/

/-- The state–branch overlap `⟪ψ, C_α ψ⟫` — the one scalar per atom
that governs the converse's hypothesis landscape at toy grade. Under
exhaustiveness it equals the branch weight
(`exhaustive_overlap_eq_weight`); below exhaustiveness it is free, and
its phase and its vanishing are exactly the two ways the converse
dies. -/
noncomputable def branchOverlap (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (α : ι) : ℂ :=
  star ψ ⬝ᵥ (C α *ᵥ ψ)

/-- **The Hermiticity obstruction**: a record family (Hermitian,
correlated — orthogonality not even consumed) forces every
state–branch overlap to be real: `⟪ψ, C_α ψ⟫ = ⟪ψ, R_α ψ⟫` is the
expectation of a Hermitian observable. In GMH's exhaustive setting
this is invisible (overlaps are branch weights, nonnegative); below
exhaustiveness it is the first load-bearing wall. -/
theorem records_force_real_overlap (C R : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hherm : ∀ α, (R α).IsHermitian)
    (hrec : ∀ α, C α *ᵥ ψ = R α *ᵥ ψ) (α : ι) :
    (branchOverlap C ψ α).im = 0 := by
  have h : star (star ψ ⬝ᵥ (R α *ᵥ ψ)) = star ψ ⬝ᵥ (R α *ᵥ ψ) := by
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec,
      ← Matrix.dotProduct_mulVec, (hherm α).eq]
  have h' : star (branchOverlap C ψ α) = branchOverlap C ψ α := by
    unfold branchOverlap
    rw [hrec α]
    exact h
  rw [Complex.star_def] at h'
  exact Complex.conj_eq_iff_im.mp h'

/-- **The idempotence obstruction**: a *projective* record family (the
record shape GMH construct in gr-qc/9210010 eq. 4.11) forces the
state–branch overlap to equal the branch weight exactly:
`⟪ψ, R ψ⟫ = ⟪ψ, R R ψ⟫ = ⟪R ψ, R ψ⟫`. The medium-vs-strong gap at toy
grade is the failure of this identity — the overlap defect. -/
theorem projective_records_force_weight_overlap
    (C R : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hherm : ∀ α, (R α).IsHermitian)
    (hidem : ∀ α, R α * R α = R α)
    (hrec : ∀ α, C α *ᵥ ψ = R α *ᵥ ψ) (α : ι) :
    branchOverlap C ψ α = decoherenceFunctional C ψ α α := by
  show star ψ ⬝ᵥ (C α *ᵥ ψ) = star (C α *ᵥ ψ) ⬝ᵥ (C α *ᵥ ψ)
  rw [hrec α]
  conv_lhs => rw [← hidem α, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  conv_rhs => rw [Matrix.star_mulVec, (hherm α).eq]

/-! ## The reconstruction -/

open scoped Classical in
/-- The reconstructed record at `α`: `QuantumRecords`' `branchProjector` with
the normalizer moved from the branch weight `⟪v, v⟫` to the overlap
`⟪ψ, v⟫` — zero when the branch is zero. At exhaustive families the
two normalizers coincide (`exhaustive_overlap_eq_weight`), so this is
the strict generalization of the branch-projector construction. -/
noncomputable def overlapRecord (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (α : ι) : Matrix d d ℂ :=
  if C α *ᵥ ψ = 0 then 0
  else (branchOverlap C ψ α)⁻¹ •
    Matrix.vecMulVec (C α *ᵥ ψ) (star (C α *ᵥ ψ))

/-- Hermiticity of the reconstructed record — consumes realness of the
overlap at the coefficient. -/
theorem overlapRecord_isHermitian (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (α : ι) (hre : (branchOverlap C ψ α).im = 0) :
    (overlapRecord C ψ α).IsHermitian := by
  unfold overlapRecord
  split
  · exact Matrix.isHermitian_zero
  · have hstar : star ((branchOverlap C ψ α)⁻¹)
        = (branchOverlap C ψ α)⁻¹ := by
      rw [star_inv₀, Complex.star_def, Complex.conj_eq_iff_im.mpr hre]
    show _ᴴ = _
    rw [Matrix.conjTranspose_smul, hstar,
      (vecMulVec_star_self_isHermitian _).eq]

/-- Mutual annihilation of the reconstructed records — consumes medium
decoherence (the hypothesis is the raw off-diagonal vanishing
`⟪C_α ψ, C_β ψ⟫ = 0`, definitionally `decoherenceFunctional C ψ β α =
0`). -/
theorem overlapRecord_orthogonal (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    {α β : ι} (hvw : star (C α *ᵥ ψ) ⬝ᵥ (C β *ᵥ ψ) = 0) :
    overlapRecord C ψ α * overlapRecord C ψ β = 0 := by
  unfold overlapRecord
  split
  · simp
  · split
    · simp
    · rw [Matrix.smul_mul, Matrix.mul_smul,
        Matrix.vecMulVec_mul_vecMulVec, hvw]
      simp

/-- Correlation of the reconstructed record with the class operator —
consumes realness (the flip `⟪v, ψ⟫ = star ⟪ψ, v⟫ = ⟪ψ, v⟫`) and the
nonvanishing disjunction (the `⟪ψ,v⟫⁻¹ ⟪ψ,v⟫ = 1` cancellation). -/
theorem overlapRecord_correlated (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (α : ι) (hre : (branchOverlap C ψ α).im = 0)
    (hnz : C α *ᵥ ψ = 0 ∨ branchOverlap C ψ α ≠ 0) :
    overlapRecord C ψ α *ᵥ ψ = C α *ᵥ ψ := by
  unfold overlapRecord
  split
  · rename_i hv
    rw [hv]
    simp
  · rename_i hv
    have hω : branchOverlap C ψ α ≠ 0 := hnz.resolve_left hv
    have hsw : star (C α *ᵥ ψ) ⬝ᵥ ψ = branchOverlap C ψ α := by
      rw [Matrix.star_dotProduct]
      show star (branchOverlap C ψ α) = branchOverlap C ψ α
      rw [Complex.star_def, Complex.conj_eq_iff_im]
      exact hre
    rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hsw,
      op_smul_eq_smul, smul_smul, inv_mul_cancel₀ hω, one_smul]

/-- **The reconstruction theorem** (the GMH converse below
exhaustiveness): medium decoherence, real overlaps, and the
nonvanishing disjunction manufacture a record family. Note the two
generalization axes over the landed
`medium_implies_records_of_exhaustive`: no exhaustiveness hypothesis,
and no `[Fintype ι]` — the reconstruction is pointwise. Each
hypothesis is witnessed load-bearing below (`phaseFamily_no_records`:
realness; `roomFamily_no_records`: nonvanishing; the landed
`switch_no_records`: medium itself). -/
theorem medium_implies_records_of_real_overlap
    (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hmed : MediumDecoherent C ψ)
    (hre : ∀ α, (branchOverlap C ψ α).im = 0)
    (hnz : ∀ α, C α *ᵥ ψ = 0 ∨ branchOverlap C ψ α ≠ 0) :
    ∃ R : ι → Matrix d d ℂ,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∀ α, C α *ᵥ ψ = R α *ᵥ ψ) :=
  ⟨overlapRecord C ψ,
    fun α => overlapRecord_isHermitian C ψ α (hre α),
    fun α β hαβ => overlapRecord_orthogonal C ψ (hmed β α hαβ.symm),
    fun α => (overlapRecord_correlated C ψ α (hre α) (hnz α)).symm⟩

/-! ## Subsumption: exhaustiveness is the special case, and upgrades
to the projection shape -/

/-- Under exhaustiveness (and medium decoherence) the overlap IS the
branch weight — the computation that makes the Hermiticity obstruction
invisible in GMH's setting, and the landed converse a special case of
the reconstruction theorem. -/
theorem exhaustive_overlap_eq_weight [Fintype ι]
    (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hexh : (∑ α, C α) *ᵥ ψ = ψ) (hmed : MediumDecoherent C ψ)
    (α : ι) :
    branchOverlap C ψ α = decoherenceFunctional C ψ α α := by
  have hψ : ψ = ∑ β, C β *ᵥ ψ := by rw [← Matrix.sum_mulVec, hexh]
  show star ψ ⬝ᵥ (C α *ᵥ ψ) = decoherenceFunctional C ψ α α
  nth_rewrite 1 [hψ]
  rw [star_sum, sum_dotProduct]
  exact Finset.sum_eq_single_of_mem α (Finset.mem_univ _)
    fun β _ hne => hmed α β hne.symm

/-- The landed exhaustive converse, re-derived through the
reconstruction theorem: exhaustiveness implies both overlap
hypotheses (weights are self-inner-products — real, and nonzero
exactly off the zero branches). Kernel-checks the subsumption;
`controlledSwitch_not_exhaustive` below witnesses its strictness. -/
theorem records_of_exhaustive_via_overlap [Fintype ι]
    (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hexh : (∑ α, C α) *ᵥ ψ = ψ) (hmed : MediumDecoherent C ψ) :
    ∃ R : ι → Matrix d d ℂ,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∀ α, C α *ᵥ ψ = R α *ᵥ ψ) := by
  refine medium_implies_records_of_real_overlap C ψ hmed
    (fun α => ?_) (fun α => ?_)
  · rw [exhaustive_overlap_eq_weight C ψ hexh hmed α]
    have h : (0 : ℂ) ≤ star (C α *ᵥ ψ) ⬝ᵥ (C α *ᵥ ψ) :=
      dotProduct_star_self_nonneg _
    show (star (C α *ᵥ ψ) ⬝ᵥ (C α *ᵥ ψ)).im = 0
    simpa using ((Complex.le_def.mp h).2).symm
  · by_cases hv : C α *ᵥ ψ = 0
    · exact Or.inl hv
    · refine Or.inr ?_
      rw [exhaustive_overlap_eq_weight C ψ hexh hmed α]
      show star (C α *ᵥ ψ) ⬝ᵥ (C α *ᵥ ψ) ≠ 0
      rwa [Ne, dotProduct_star_self_eq_zero]

/-- Branch projectors are idempotent — the missing conjunct that
upgrades the landed converse's records to the projection shape of
GMH's eq. 4.11. -/
theorem branchProjector_idem (v : d → ℂ) :
    branchProjector v * branchProjector v = branchProjector v := by
  unfold branchProjector
  split
  · simp
  · rename_i hv
    have hc : star v ⬝ᵥ v ≠ 0 := by
      rwa [Ne, dotProduct_star_self_eq_zero]
    rw [Matrix.smul_mul, Matrix.mul_smul,
      Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul, smul_smul,
      smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]

/-- **Medium decoherence constructs projective records, under
exhaustiveness** — the landed converse at GMH's own record shape
(orthogonal *projections* correlated with the class operators,
gr-qc/9210010 eq. 4.11): where their standing hypothesis holds, the
strong record shape comes back for free. Completeness (`∑ R = 1`) and
permanence (gr-qc/9509054's additions) remain unclaimed. -/
theorem medium_implies_projective_records_of_exhaustive [Fintype ι]
    (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hexh : (∑ α, C α) *ᵥ ψ = ψ)
    (hmed : MediumDecoherent C ψ) :
    ∃ R : ι → Matrix d d ℂ,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α, R α * R α = R α) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∀ α, C α *ᵥ ψ = R α *ᵥ ψ) := by
  refine ⟨fun α => branchProjector (C α *ᵥ ψ),
    fun α => branchProjector_isHermitian _,
    fun α => branchProjector_idem _,
    fun α β hαβ => branchProjector_orthogonal (hmed β α hαβ.symm),
    fun α => ?_⟩
  refine (branchProjector_mulVec_of _ _ ?_).symm
  have hψ : ψ = ∑ β, C β *ᵥ ψ := by rw [← Matrix.sum_mulVec, hexh]
  calc star (C α *ᵥ ψ) ⬝ᵥ ψ
      = ∑ β, star (C α *ᵥ ψ) ⬝ᵥ (C β *ᵥ ψ) := by
        nth_rewrite 2 [hψ]
        rw [dotProduct_sum]
    _ = star (C α *ᵥ ψ) ⬝ᵥ (C α *ᵥ ψ) :=
        Finset.sum_eq_single_of_mem α (Finset.mem_univ _)
          fun β _ hne => hmed β α hne

/-! ## The phase stratum: medium decoherence with an imaginary
overlap — no records at all -/

/-- The phase family: `i·|0⟩⟨0|` and `|1⟩⟨1|` on the state `(1,1)`.
Branches `(i,0)` and `(0,1)` — orthogonal (medium-decoherent), both
overlaps nonzero (`i` and `1`), but the first is imaginary. -/
noncomputable def phaseFamily : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![Complex.I, 0; 0, 0], !![0, 0; 0, 1]]

theorem phaseFamily_mediumDecoherent :
    MediumDecoherent phaseFamily ![1, 1] := by
  intro α β hαβ
  fin_cases α <;> fin_cases β <;>
    first
      | exact absurd rfl hαβ
      | (simp only [decoherenceFunctional, phaseFamily]
         norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
           Pi.star_apply, Complex.star_def, map_one, Complex.conj_I,
           Complex.ext_iff, Complex.add_re, Complex.add_im,
           Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im])

/-- The phase witness: the first overlap is `i` — imaginary part
`1`. -/
theorem phaseFamily_overlap_im :
    (branchOverlap phaseFamily ![1, 1] 0).im = 1 := by
  simp only [branchOverlap, phaseFamily]
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.star_apply,
    Complex.star_def, map_one, Complex.add_im, Complex.mul_im,
    Complex.mul_re, Complex.I_re, Complex.I_im]

/-- Both overlaps are nonzero — the phase family satisfies every
hypothesis of the reconstruction theorem EXCEPT realness (the m1
mutant's semantic witness: dropping realness would make the mutated
theorem apply here, contradicting `phaseFamily_no_records`). -/
theorem phaseFamily_overlaps_ne_zero (α : Fin 2) :
    branchOverlap phaseFamily ![1, 1] α ≠ 0 := by
  fin_cases α <;>
    (simp only [branchOverlap, phaseFamily]
     norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
       Pi.star_apply, Complex.star_def, map_one, Complex.ext_iff,
       Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
       Complex.I_re, Complex.I_im])

/-- The phase family is not exhaustive at its state — as it must be,
since exhaustiveness forces real overlaps. -/
theorem phaseFamily_not_exhaustive :
    (∑ α, phaseFamily α) *ᵥ ![1, 1] ≠ ![(1 : ℂ), 1] := by
  intro h
  have h0 := congrFun h 0
  simp only [phaseFamily, Fin.sum_univ_two] at h0
  norm_num [Matrix.add_mulVec, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Complex.ext_iff, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at h0

/-- **Medium decoherence does not reconstruct records** — the phase
stratum: the negation does not even demand orthogonality (strictly
stronger than refusing the standard record triple), because the
Hermiticity obstruction alone kills it: any Hermitian correlated
family would force the overlap `i` to be real. -/
theorem phaseFamily_no_records :
    ¬ ∃ R : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ,
        (∀ α, (R α).IsHermitian) ∧
        (∀ α, phaseFamily α *ᵥ ![1, 1] = R α *ᵥ ![1, 1]) := by
  rintro ⟨R, hherm, hrec⟩
  have h := records_force_real_overlap phaseFamily R ![1, 1] hherm hrec 0
  rw [phaseFamily_overlap_im] at h
  exact one_ne_zero h

/-! ## The room stratum: medium decoherence with real overlaps —
still no records, when a zero overlap sits on a nonzero branch -/

/-- The room family: `|1⟩⟨0|` and `|0⟩⟨0|` on the state `(1,0)`.
Branches `(0,1)` and `(1,0) = ψ` — orthogonal, overlaps `0` and `1`
(all real), but the zero overlap sits on a nonzero branch and `d = 2`
has no room for a record of it. -/
noncomputable def roomFamily : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 0; 1, 0], !![1, 0; 0, 0]]

theorem roomFamily_mediumDecoherent :
    MediumDecoherent roomFamily ![1, 0] := by
  intro α β hαβ
  fin_cases α <;> fin_cases β <;>
    first
      | exact absurd rfl hαβ
      | (simp only [decoherenceFunctional, roomFamily]
         norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
           Pi.star_apply, Complex.star_def, map_one, Complex.ext_iff,
           Complex.add_re, Complex.add_im, Complex.mul_re,
           Complex.mul_im])

/-- Every overlap of the room family is real — the phase obstruction
is silent here; what fails is nonvanishing (the m2 mutant's semantic
witness). -/
theorem roomFamily_overlap_im (α : Fin 2) :
    (branchOverlap roomFamily ![1, 0] α).im = 0 := by
  fin_cases α <;>
    (simp only [branchOverlap, roomFamily]
     norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
       Pi.star_apply, Complex.star_def, map_one, Complex.add_im,
       Complex.mul_im, Complex.mul_re])

/-- **Real overlaps are still not enough** — the room stratum: the
negation does not even demand Hermiticity, because orthogonality and
correlation alone collide: `R₁ ψ = ψ` (the second branch IS the
state), so `0 = (R₀ R₁) ψ = R₀ ψ = (0,1) ≠ 0`. In higher dimension a
zero-overlap branch can carry records (spectral room); in `d = 2`
there is none — the nonvanishing disjunction is the clean sufficient
boundary, witnessed non-droppable. -/
theorem roomFamily_no_records :
    ¬ ∃ R : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ,
        (∀ α β, α ≠ β → R α * R β = 0) ∧
        (∀ α, roomFamily α *ᵥ ![1, 0] = R α *ᵥ ![1, 0]) := by
  rintro ⟨R, horth, hrec⟩
  have h1 : R 1 *ᵥ ![(1 : ℂ), 0] = ![(1 : ℂ), 0] := by
    rw [← hrec 1]
    funext i
    fin_cases i <;>
      norm_num [roomFamily, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h0 : R 0 *ᵥ ![(1 : ℂ), 0] = ![(0 : ℂ), 1] := by
    rw [← hrec 0]
    funext i
    fin_cases i <;>
      norm_num [roomFamily, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hcol : (R 0 * R 1) *ᵥ ![(1 : ℂ), 0] = 0 := by
    rw [horth 0 1 (by decide), Matrix.zero_mulVec]
  rw [← Matrix.mulVec_mulVec, h1, h0] at hcol
  have h := congrFun hcol 1
  norm_num [Complex.ext_iff] at h

/-! ## The controlled switch, completed: records without
exhaustiveness, and the medium-vs-strong gap -/

private theorem sum_over_switchOrder {M : Type*} [AddCommMonoid M]
    (f : SwitchOrder → M) :
    ∑ x, f x = f .zThenX + f .xThenZ := by
  have h : (Finset.univ : Finset SwitchOrder)
      = {SwitchOrder.zThenX, SwitchOrder.xThenZ} := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The `zThenX` overlap of the controlled switch is `1` — real,
nonzero, and (the gap parameter) NOT equal to its branch weight
`1/2`. -/
theorem controlledSwitch_overlap_zThenX :
    branchOverlap controlledSwitch switchState .zThenX = 1 := by
  simp only [branchOverlap, controlledSwitch]
  norm_num [switchState, Qx0, Pz0, Matrix.mulVec, Matrix.mul_apply,
    dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Pi.star_apply, Complex.star_def, map_div₀,
    map_one, Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im]

/-- The `xThenZ` overlap of the controlled switch is `1` — real and
nonzero (and here equal to its branch weight: the overlap defect
lives entirely at `zThenX`). -/
theorem controlledSwitch_overlap_xThenZ :
    branchOverlap controlledSwitch switchState .xThenZ = 1 := by
  simp only [branchOverlap, controlledSwitch]
  norm_num [switchState, Qx0, Pz0, Pz1, Matrix.mulVec, Matrix.mul_apply,
    dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Pi.star_apply, Complex.star_def, map_div₀,
    map_one, Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im]

/-- The `zThenX` branch weight is `1/2` — against the overlap `1`,
the kernel-visible overlap defect. -/
theorem controlledSwitch_weight_zThenX :
    decoherenceFunctional controlledSwitch switchState
      .zThenX .zThenX = 1 / 2 := by
  simp only [decoherenceFunctional, controlledSwitch]
  norm_num [switchState, Qx0, Pz0, Matrix.mulVec, Matrix.mul_apply,
    dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Pi.star_apply, Complex.star_def, map_div₀,
    map_one, Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im]

/-- The controlled switch is NOT exhaustive at its state (coordinate
`(1,1)`: `0 ≠ 1`) — so the landed exhaustive converse cannot fire
here, and the reconstruction below is genuinely new reach. -/
theorem controlledSwitch_not_exhaustive :
    (∑ α, controlledSwitch α) *ᵥ switchState ≠ switchState := by
  intro h
  rw [sum_over_switchOrder] at h
  have h11 := congrFun h ((1 : Fin 2), (1 : Fin 2))
  simp only [controlledSwitch] at h11
  norm_num [switchState, Qx0, Pz0, Pz1, Matrix.add_mulVec,
    Matrix.mulVec, Matrix.mul_apply, dotProduct,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Pi.add_apply, Complex.ext_iff] at h11

private theorem controlledSwitch_overlaps_real (α : SwitchOrder) :
    (branchOverlap controlledSwitch switchState α).im = 0 := by
  cases α
  · rw [controlledSwitch_overlap_zThenX]
    norm_num
  · rw [controlledSwitch_overlap_xThenZ]
    norm_num

private theorem controlledSwitch_overlaps_cond (α : SwitchOrder) :
    controlledSwitch α *ᵥ switchState = 0 ∨
      branchOverlap controlledSwitch switchState α ≠ 0 := by
  cases α
  · exact Or.inr (by rw [controlledSwitch_overlap_zThenX]; norm_num)
  · exact Or.inr (by rw [controlledSwitch_overlap_xThenZ]; norm_num)

/-- **The which-order records exist** — manufactured by the
reconstruction theorem on a non-exhaustive family: the outer-storey
probe's fence ("record-existence via the converse needs exhaustive
families")
is repaired — exhaustiveness was sufficient, never necessary; real
nonzero overlaps are what the controlled switch actually has. -/
theorem controlledSwitch_records :
    ∃ R : SwitchOrder → TwoQubits,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∀ α, controlledSwitch α *ᵥ switchState = R α *ᵥ switchState) :=
  medium_implies_records_of_real_overlap _ _
    controlledSwitch_mediumDecoherent
    controlledSwitch_overlaps_real controlledSwitch_overlaps_cond

/-- **No projective record family exists for the controlled switch**
— the medium-vs-strong gap witnessed on the two-fibre toy: the idempotence
obstruction demands overlap = weight, and at `zThenX` the defect is
`1 ≠ 1/2`. Generalized records exist (`controlledSwitch_records`);
GMH-shaped ones do not. The gap between medium decoherence and the
strong regime is, at toy grade, exactly the overlap defect —
which exhaustiveness would force to vanish. -/
theorem controlledSwitch_no_projective_records :
    ¬ ∃ R : SwitchOrder → TwoQubits,
        (∀ α, (R α).IsHermitian) ∧
        (∀ α, R α * R α = R α) ∧
        (∀ α, controlledSwitch α *ᵥ switchState = R α *ᵥ switchState) := by
  rintro ⟨R, hherm, hidem, hrec⟩
  have h := projective_records_force_weight_overlap controlledSwitch R
    switchState hherm hidem hrec .zThenX
  rw [controlledSwitch_overlap_zThenX,
    controlledSwitch_weight_zThenX] at h
  norm_num at h

/-! ## The crown: the GMH biconditional at D-form grade, on both
fibres of the toy -/

/-- Records force the D-form diagonal — `records_imply_medium` read
through the landed `controlledMeasure` gram. -/
theorem controlled_records_to_isDiagonal
    (h : ∃ R : SwitchOrder → TwoQubits,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∀ α, controlledSwitch α *ᵥ switchState = R α *ᵥ switchState)) :
    controlledMeasure.IsDiagonal := by
  obtain ⟨R, hherm, horth, hrec⟩ := h
  intro α β hαβ
  rw [controlledMeasure_gram,
    records_imply_medium controlledSwitch R switchState hherm horth
      hrec α β hαβ, mul_zero]

/-- **Diagonality of the D-form reconstructs the records**: from the
quantum measure's diagonal verdict alone (the scale `2/3` cancelled),
medium decoherence returns, and the reconstruction theorem
manufactures the which-order record family. The D-form vocabulary was
the missing piece: the converse is now statable — and true — at
measure grade. -/
theorem controlled_isDiagonal_to_records
    (hd : controlledMeasure.IsDiagonal) :
    ∃ R : SwitchOrder → TwoQubits,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∀ α, controlledSwitch α *ᵥ switchState = R α *ᵥ switchState) := by
  have hmed : MediumDecoherent controlledSwitch switchState := by
    intro α β hαβ
    have h := hd hαβ
    rw [controlledMeasure_gram] at h
    rcases mul_eq_zero.mp h with h23 | hD
    · rw [Complex.ofReal_eq_zero] at h23
      norm_num at h23
    · exact hD
  exact medium_implies_records_of_real_overlap _ _ hmed
    controlledSwitch_overlaps_real controlledSwitch_overlaps_cond

/-- **The GMH biconditional at D-form grade, controlled fibre**:
which-order records exist iff the order index's quantum measure is
diagonal. Both directions carry real proof paths
(`controlled_records_to_isDiagonal`,
`controlled_isDiagonal_to_records`); on this fibre both sides hold. -/
theorem controlled_records_iff_isDiagonal :
    (∃ R : SwitchOrder → TwoQubits,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∀ α, controlledSwitch α *ᵥ switchState = R α *ᵥ switchState)) ↔
    controlledMeasure.IsDiagonal :=
  ⟨controlled_records_to_isDiagonal, controlled_isDiagonal_to_records⟩

/-- **The GMH biconditional at D-form grade, coherent fibre**: the
same equivalence, populated oppositely — no records
(`switch_no_records`, landed) and no diagonality
(`switchMeasure_not_isDiagonal`, landed). One biconditional, two
fibres: records ⟺ diagonality across the whole two-fibre toy. -/
theorem switch_records_iff_isDiagonal :
    (∃ R : SwitchOrder → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∀ α, switchFamily α *ᵥ ![1, 1] = R α *ᵥ ![1, 1])) ↔
    switchMeasure.IsDiagonal :=
  iff_of_false switch_no_records switchMeasure_not_isDiagonal

/-! ## The exhaustive contrast point -/

/-- Where GMH's standing hypothesis holds, the full projective shape
returns: the D-form's recorded presentation (`zMeasure`'s family, the
z-projectors on the 3-4-5 state) is exhaustive, and the upgraded
converse manufactures projective records. -/
theorem zPair_projective_records :
    ∃ R : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α, R α * R α = R α) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∀ α, ![Pz0, Pz1] α *ᵥ ![(3 / 5 : ℂ), 4 / 5]
        = R α *ᵥ ![(3 / 5 : ℂ), 4 / 5]) := by
  refine medium_implies_projective_records_of_exhaustive _ _ ?_ ?_
  · funext i
    simp only [Fin.sum_univ_two]
    fin_cases i <;>
      norm_num [Pz0, Pz1, Matrix.add_mulVec, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
  · intro α β hαβ
    fin_cases α <;> fin_cases β <;>
      first
        | exact absurd rfl hαβ
        | (simp only [decoherenceFunctional]
           norm_num [Pz0, Pz1, Matrix.mulVec, dotProduct,
             Fin.sum_univ_two, Pi.star_apply, Complex.star_def,
             map_div₀, map_ofNat, Complex.ext_iff, Complex.add_re,
             Complex.add_im, Complex.mul_re, Complex.mul_im,
             Complex.div_re, Complex.div_im, Complex.normSq_apply])

end QuantumConverse

end Qtsl

-- Axiom receipts (expected: exactly [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumConverse.records_force_real_overlap
#print axioms Qtsl.QuantumConverse.projective_records_force_weight_overlap
#print axioms Qtsl.QuantumConverse.overlapRecord_isHermitian
#print axioms Qtsl.QuantumConverse.overlapRecord_orthogonal
#print axioms Qtsl.QuantumConverse.overlapRecord_correlated
#print axioms Qtsl.QuantumConverse.medium_implies_records_of_real_overlap
#print axioms Qtsl.QuantumConverse.exhaustive_overlap_eq_weight
#print axioms Qtsl.QuantumConverse.records_of_exhaustive_via_overlap
#print axioms Qtsl.QuantumConverse.branchProjector_idem
#print axioms Qtsl.QuantumConverse.medium_implies_projective_records_of_exhaustive
#print axioms Qtsl.QuantumConverse.phaseFamily_mediumDecoherent
#print axioms Qtsl.QuantumConverse.phaseFamily_overlap_im
#print axioms Qtsl.QuantumConverse.phaseFamily_overlaps_ne_zero
#print axioms Qtsl.QuantumConverse.phaseFamily_not_exhaustive
#print axioms Qtsl.QuantumConverse.phaseFamily_no_records
#print axioms Qtsl.QuantumConverse.roomFamily_mediumDecoherent
#print axioms Qtsl.QuantumConverse.roomFamily_overlap_im
#print axioms Qtsl.QuantumConverse.roomFamily_no_records
#print axioms Qtsl.QuantumConverse.controlledSwitch_overlap_zThenX
#print axioms Qtsl.QuantumConverse.controlledSwitch_overlap_xThenZ
#print axioms Qtsl.QuantumConverse.controlledSwitch_weight_zThenX
#print axioms Qtsl.QuantumConverse.controlledSwitch_not_exhaustive
#print axioms Qtsl.QuantumConverse.controlledSwitch_records
#print axioms Qtsl.QuantumConverse.controlledSwitch_no_projective_records
#print axioms Qtsl.QuantumConverse.controlled_records_to_isDiagonal
#print axioms Qtsl.QuantumConverse.controlled_isDiagonal_to_records
#print axioms Qtsl.QuantumConverse.controlled_records_iff_isDiagonal
#print axioms Qtsl.QuantumConverse.switch_records_iff_isDiagonal
#print axioms Qtsl.QuantumConverse.zPair_projective_records
