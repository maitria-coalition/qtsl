/-
Copyright (c) 2026 The maitria coalition. All rights reserved.
Released under Apache 2.0 / MIT dual license.
-/
import QtslAux.QuantumApproxConsistency
import QtslAux.QuantumConsistentSets

/-! # The approximate history-count cap (the Donald obstruction, quantified)

Dowker–Kent flag, at the conjecture locus of "On the Consistent Histories
Approach to Quantum Mechanics" (J. Stat. Phys. 82 (1996) 1575,
gr-qc/9412067), a phenomenon that forces the "generic" clause of their
approximate-vs-exact consistency conjecture: "Given a pure initial density
matrix in a space of dimension `n`, one can construct examples in which an
approximately consistent set with no approximately consistent non-trivial
fine graining contains more than `n` non-trivial histories, and so cannot
possibly be approximated by an exactly consistent set." Their footnote:
"We thank Matthew Donald, to whom this point is due." No construction is
given in the paper; the quantitative bound governing the phenomenon is
McElwaine's (PRA 53, 2021 (1996), quant-ph/9506034: for the medium
Dowker–Halliwell criterion, at most `d(1-ε²)/(1-dε²)` non-null histories
when `ε² ≤ 1/(d+1)`), obtained there by zonal-spherical-harmonic methods.

This module machine-checks the phenomenon's *impossibility half* — the
necessity direction — over arbitrary class-operator families, by the
elementary frame (Welch-type) argument, with no spectral theory:

* **`welch_sq_of_nonnull` / `nonnull_card_welch`** — for any family that is
  `ε`-approximately medium decoherent (`ApproxMediumDecoherent`) with `M`
  non-null histories in dimension `d`: `M - d ≤ ε² · d · (M - 1)` — the
  division-free contrapositive of the kissing bound
  (`ε² ≥ (M-d)/(d(M-1))`), valid unconditionally.
* **`donaldStratum_card_le`** — the **Donald stratum is empty below the
  kissing threshold**: at `ε · d < 1`, every `ε`-approximately consistent
  family has at most `d` non-null histories. Uniform in `M` (the per-`M`
  threshold `(M-d)/(d(M-1))` is increasing in `M`; the binding case is
  `M = d + 1`). This is the boundary condition any genericity notion for
  the Dowker–Kent conjecture must respect, and below the threshold it is
  vacuously satisfiable: there is nothing to carve.
* **`qubit_floor`** — the sharpest instance: a qubit family (`d = 2`) with
  three or more non-null histories is `ε`-approximately medium decoherent
  only at `ε ≥ 1/2`. The floor is attained: the qubit trine (three
  equiangular branch vectors, pairwise normalized overlap `1/2`) is
  `ε`-consistent at exactly `ε = 1/2` — the saturating exhibit belongs to
  the quantitative-instance development and is deliberately not rebuilt
  here.
* **`mediumDecoherent_nonnull_card_le`** — the `ε = 0` face: an exactly
  medium-decoherent family has at most `d` non-null histories — the
  family-level counting core of Dowker–Kent's Lemma 1, here by a second
  mechanism (the frame bound) independent of the orthogonality/linear-
  independence route used for `dkConsistent_card_nonzero_le`.
* **`DKApproxConsistent`** — the instantiation on Dowker–Kent's own domain
  (`QuantumConsistentSets`): `ε`-approximate consistency of a DK set, its
  `ε = 0` bridge to `DKConsistent`, and the cap corollaries for DK
  histories — the objects a formal statement of the Dowker–Kent conjecture
  consumes for its genericity clause.

The engine is the completing-the-square/frame computation: for non-null
branch vectors `v_α` with weights `c_α = 1/‖v_α‖²`, the matrix
`T i j = ∑ α c_α v_α(i) conj (v_α(j))` has `∑ᵢ (T i i).re = M` and
`∑ᵢⱼ |T i j|² = ∑_{αβ} c_α c_β |D(α,β)|²`; Cauchy–Schwarz over the `d`
diagonal slots plus the criterion bound on the off-diagonal Gram entries
yields `M² ≤ d(M + ε² M(M-1))`. -- [classical]
-/

namespace Qtsl

namespace QuantumApproxCap

open Matrix ComplexConjugate
open QuantumRecords QuantumApproxConsistency
open scoped ComplexOrder

variable {d : Type*} [Fintype d] {ι : Type*}

/-! ## Diagonal facts: branch weights are real, positive iff non-null -/

/-- The diagonal of the decoherence functional is real: its imaginary part
vanishes (it is `⟨C_α ψ, C_α ψ⟩`). -/
theorem diagonal_im_zero (C : ι → Matrix d d ℂ) (ψ : d → ℂ) (α : ι) :
    (decoherenceFunctional C ψ α α).im = 0 := by
  have h : (0 : ℂ) ≤ star (C α *ᵥ ψ) ⬝ᵥ (C α *ᵥ ψ) :=
    dotProduct_star_self_nonneg _
  have him := (Complex.le_def.mp h).2
  simpa [decoherenceFunctional] using him.symm

/-- The branch weight as a sum of coordinate `normSq`s. -/
theorem diagonal_re_eq_sum_normSq (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (α : ι) :
    (decoherenceFunctional C ψ α α).re
      = ∑ i : d, Complex.normSq ((C α *ᵥ ψ) i) := by
  have h : decoherenceFunctional C ψ α α
      = ((∑ i : d, Complex.normSq ((C α *ᵥ ψ) i) : ℝ) : ℂ) := by
    simp only [decoherenceFunctional, dotProduct, Pi.star_apply,
      Complex.star_def]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, Complex.mul_conj]
  rw [h, Complex.ofReal_re]

/-- A branch weight is positive iff the branch vector is nonzero — the
family-level face of "non-zero probability". -/
theorem diagonal_re_pos_iff (C : ι → Matrix d d ℂ) (ψ : d → ℂ) (α : ι) :
    0 < (decoherenceFunctional C ψ α α).re ↔ C α *ᵥ ψ ≠ 0 := by
  constructor
  · intro hpos h0
    have hz : decoherenceFunctional C ψ α α = 0 := by
      simp only [decoherenceFunctional, h0, star_zero, zero_dotProduct]
    rw [hz] at hpos
    simp at hpos
  · intro hv
    rcases lt_or_eq_of_le (diagonal_re_nonneg C ψ α) with hlt | heq
    · exact hlt
    · exfalso
      apply hv
      have hz : decoherenceFunctional C ψ α α = 0 :=
        Complex.ext (by simpa using heq.symm)
          (by simpa using diagonal_im_zero C ψ α)
      rw [← dotProduct_star_self_eq_zero (v := C α *ᵥ ψ)]
      simpa [decoherenceFunctional] using hz

/-- `normSq` is the squared norm. -/
private theorem normSq_eq_sq_norm (z : ℂ) : Complex.normSq z = ‖z‖ ^ 2 := by
  have h1 : ((Complex.normSq z : ℝ) : ℂ) = z * conj z :=
    (Complex.mul_conj z).symm
  have h2 : ‖z * conj z‖ = ‖z‖ ^ 2 := by
    rw [norm_mul, RCLike.norm_conj, sq]
  have h3 : ‖((Complex.normSq z : ℝ) : ℂ)‖ = ‖z‖ ^ 2 := by rw [h1]; exact h2
  rwa [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Complex.normSq_nonneg z)] at h3

/-! ## The Gram expansion (the frame computation's engine identity) -/

/-- Cauchy–Schwarz over a finite index with the cardinality constant:
`(∑ f)² ≤ card · ∑ f²`. Proven by expanding `∑ᵢⱼ (fᵢ - fⱼ)² ≥ 0`. -/
private theorem sq_sum_le_card_mul_sum_sq' {γ : Type*} [Fintype γ]
    (f : γ → ℝ) :
    (∑ i : γ, f i) ^ 2 ≤ (Fintype.card γ : ℝ) * ∑ i : γ, f i ^ 2 := by
  have key : (0 : ℝ) ≤ ∑ i : γ, ∑ j : γ, (f i - f j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have expand : ∑ i : γ, ∑ j : γ, (f i - f j) ^ 2
      = 2 * ((Fintype.card γ : ℝ) * ∑ i : γ, f i ^ 2)
        - 2 * (∑ i : γ, f i) ^ 2 := by
    have h1 : ∀ i : γ, ∑ j : γ, (f i - f j) ^ 2
        = (Fintype.card γ : ℝ) * f i ^ 2
          - 2 * f i * (∑ j : γ, f j) + ∑ j : γ, f j ^ 2 := by
      intro i
      rw [Finset.sum_congr rfl fun j _ =>
        (by ring : (f i - f j) ^ 2 = f i ^ 2 - 2 * f i * f j + f j ^ 2)]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, ← Finset.mul_sum, Finset.card_univ,
        nsmul_eq_mul]
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  have key' : (0 : ℝ)
      ≤ 2 * ((Fintype.card γ : ℝ) * ∑ i : γ, f i ^ 2)
        - 2 * (∑ i : γ, f i) ^ 2 := expand ▸ key
  linarith

/-- Reordering a fourfold sum: the outer pair moves inside. -/
private theorem sum_swap₄ {γ : Type*} [Fintype γ] [Fintype ι]
    (f : ι → ι → γ → γ → ℂ) :
    ∑ i : γ, ∑ j : γ, ∑ α : ι, ∑ β : ι, f α β i j
      = ∑ α : ι, ∑ β : ι, ∑ i : γ, ∑ j : γ, f α β i j := by
  calc ∑ i : γ, ∑ j : γ, ∑ α : ι, ∑ β : ι, f α β i j
      = ∑ i : γ, ∑ α : ι, ∑ j : γ, ∑ β : ι, f α β i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ α : ι, ∑ i : γ, ∑ j : γ, ∑ β : ι, f α β i j := Finset.sum_comm
    _ = ∑ α : ι, ∑ i : γ, ∑ β : ι, ∑ j : γ, f α β i j :=
        Finset.sum_congr rfl fun α _ =>
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ α : ι, ∑ β : ι, ∑ i : γ, ∑ j : γ, f α β i j :=
        Finset.sum_congr rfl fun α _ => Finset.sum_comm

/-- The decoherence functional as a coordinate sum, first slot
unconjugated: `D(α,β) = ∑ᵢ v_α(i) · conj (v_β(i))`. -/
theorem decoherenceFunctional_eq_sum (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (α β : ι) :
    decoherenceFunctional C ψ α β
      = ∑ i : d, (C α *ᵥ ψ) i * conj ((C β *ᵥ ψ) i) := by
  simp only [decoherenceFunctional, dotProduct, Pi.star_apply,
    Complex.star_def]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The conjugated decoherence functional as a coordinate sum. -/
theorem conj_decoherenceFunctional_eq_sum (C : ι → Matrix d d ℂ)
    (ψ : d → ℂ) (α β : ι) :
    conj (decoherenceFunctional C ψ α β)
      = ∑ j : d, conj ((C α *ᵥ ψ) j) * (C β *ᵥ ψ) j := by
  rw [← Complex.star_def, ← decoherenceFunctional_conj]
  simp only [decoherenceFunctional, dotProduct, Pi.star_apply,
    Complex.star_def]

/-- One pair's worth of the Gram expansion, factored back into
decoherence-functional entries. -/
private theorem pair_factor (C : ι → Matrix d d ℂ) (ψ : d → ℂ) (c : ι → ℝ)
    (α β : ι) :
    ∑ i : d, ∑ j : d,
        (((c α : ℂ) * (C α *ᵥ ψ) i * conj ((C α *ᵥ ψ) j))
          * ((c β : ℂ) * conj ((C β *ᵥ ψ) i) * (C β *ᵥ ψ) j))
      = (c α : ℂ) * (c β : ℂ)
          * (decoherenceFunctional C ψ α β
              * conj (decoherenceFunctional C ψ α β)) := by
  calc ∑ i : d, ∑ j : d,
        (((c α : ℂ) * (C α *ᵥ ψ) i * conj ((C α *ᵥ ψ) j))
          * ((c β : ℂ) * conj ((C β *ᵥ ψ) i) * (C β *ᵥ ψ) j))
      = ∑ i : d, ∑ j : d,
          ((c α : ℂ) * (c β : ℂ))
            * (((C α *ᵥ ψ) i * conj ((C β *ᵥ ψ) i))
                * (conj ((C α *ᵥ ψ) j) * (C β *ᵥ ψ) j)) :=
        Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by ring
    _ = ((c α : ℂ) * (c β : ℂ))
          * ∑ i : d, ∑ j : d,
              ((C α *ᵥ ψ) i * conj ((C β *ᵥ ψ) i))
                * (conj ((C α *ᵥ ψ) j) * (C β *ᵥ ψ) j) := by
        simp only [← Finset.mul_sum]
    _ = ((c α : ℂ) * (c β : ℂ))
          * ((∑ i : d, (C α *ᵥ ψ) i * conj ((C β *ᵥ ψ) i))
              * (∑ j : d, conj ((C α *ᵥ ψ) j) * (C β *ᵥ ψ) j)) := by
        rw [← Finset.sum_mul_sum]
    _ = (c α : ℂ) * (c β : ℂ)
          * (decoherenceFunctional C ψ α β
              * conj (decoherenceFunctional C ψ α β)) := by
        rw [← decoherenceFunctional_eq_sum,
          ← conj_decoherenceFunctional_eq_sum]

/-- **The Gram expansion**: the total `normSq`-mass of the weighted frame
matrix `T i j = ∑ α c_α v_α(i) conj (v_α(j))` equals the weighted
`normSq`-mass of the decoherence functional. The conjugation on the second
slot is load-bearing: on real families the unconjugated identity would
also hold, which is exactly why this locus is the complex-slice mutant. -/
theorem gram_expansion [Fintype ι] (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (c : ι → ℝ) :
    ∑ i : d, ∑ j : d,
        Complex.normSq (∑ α : ι, (c α : ℂ) * (C α *ᵥ ψ) i
          * conj ((C α *ᵥ ψ) j))
      = ∑ α : ι, ∑ β : ι,
          c α * c β * Complex.normSq (decoherenceFunctional C ψ α β) := by
  have hconj_sum : ∀ i j : d,
      conj (∑ α : ι, (c α : ℂ) * (C α *ᵥ ψ) i * conj ((C α *ᵥ ψ) j))
        = ∑ β : ι, (c β : ℂ) * conj ((C β *ᵥ ψ) i) * (C β *ᵥ ψ) j := by
    intro i j
    rw [map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.mul_conj]
  calc ∑ i : d, ∑ j : d,
        ((∑ α : ι, (c α : ℂ) * (C α *ᵥ ψ) i * conj ((C α *ᵥ ψ) j))
          * conj (∑ α : ι, (c α : ℂ) * (C α *ᵥ ψ) i
              * conj ((C α *ᵥ ψ) j)))
      = ∑ i : d, ∑ j : d, ∑ α : ι, ∑ β : ι,
          (((c α : ℂ) * (C α *ᵥ ψ) i * conj ((C α *ᵥ ψ) j))
            * ((c β : ℂ) * conj ((C β *ᵥ ψ) i) * (C β *ᵥ ψ) j)) := by
        refine Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => ?_
        rw [hconj_sum i j, Finset.sum_mul_sum]
    _ = ∑ α : ι, ∑ β : ι, ∑ i : d, ∑ j : d,
          (((c α : ℂ) * (C α *ᵥ ψ) i * conj ((C α *ᵥ ψ) j))
            * ((c β : ℂ) * conj ((C β *ᵥ ψ) i) * (C β *ᵥ ψ) j)) :=
        sum_swap₄ _
    _ = ∑ α : ι, ∑ β : ι, (c α : ℂ) * (c β : ℂ)
          * (decoherenceFunctional C ψ α β
              * conj (decoherenceFunctional C ψ α β)) :=
        Finset.sum_congr rfl fun α _ =>
          Finset.sum_congr rfl fun β _ => pair_factor C ψ c α β

/-! ## The approximate cap (Welch-type necessity) -/

/-- **The frame bound, square form**: an `ε`-approximately medium
decoherent family of `M` non-null histories in dimension `d` satisfies
`M² ≤ d · (M + ε² · M(M-1))` — the necessity direction of the kissing
bound, by the elementary frame argument. No sign hypothesis on `ε` is
needed (squaring the criterion only uses `‖D‖ ≥ 0`). -/
theorem welch_sq_of_nonnull [Fintype ι] {ε : ℝ}
    {C : ι → Matrix d d ℂ} {ψ : d → ℂ}
    (hnn : ∀ α, C α *ᵥ ψ ≠ 0) (h : ApproxMediumDecoherent ε C ψ) :
    (Fintype.card ι : ℝ) ^ 2
      ≤ (Fintype.card d : ℝ)
        * (Fintype.card ι
            + ε ^ 2 * (Fintype.card ι * ((Fintype.card ι : ℝ) - 1))) := by
  classical
  have hp : ∀ α, 0 < (decoherenceFunctional C ψ α α).re := fun α =>
    (diagonal_re_pos_iff C ψ α).mpr (hnn α)
  set c : ι → ℝ := fun α => ((decoherenceFunctional C ψ α α).re)⁻¹
    with hc_def
  have hc : ∀ α, 0 ≤ c α := fun α => by
    simp only [hc_def]
    exact inv_nonneg.mpr (hp α).le
  have hcp : ∀ α, c α * (decoherenceFunctional C ψ α α).re = 1 := fun α => by
    simp only [hc_def]
    exact inv_mul_cancel₀ (hp α).ne'
  -- the frame matrix's diagonal entries are real casts
  have hTdiag : ∀ i : d,
      (∑ α : ι, (c α : ℂ) * (C α *ᵥ ψ) i * conj ((C α *ᵥ ψ) i))
        = ((∑ α : ι, c α * Complex.normSq ((C α *ᵥ ψ) i) : ℝ) : ℂ) := by
    intro i
    push_cast
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [mul_assoc, Complex.mul_conj]
  -- 1. the trace is M
  have htrace : ∑ i : d, ∑ α : ι, c α * Complex.normSq ((C α *ᵥ ψ) i)
      = (Fintype.card ι : ℝ) := by
    rw [Finset.sum_comm]
    have hone : ∀ α : ι,
        ∑ i : d, c α * Complex.normSq ((C α *ᵥ ψ) i) = 1 := by
      intro α
      rw [← Finset.mul_sum, ← diagonal_re_eq_sum_normSq]
      exact hcp α
    rw [Finset.sum_congr rfl fun α _ => hone α]
    simp [Finset.card_univ]
  -- 2. per-slot: (trace entry)² ≤ ∑ⱼ normSq (T i j)
  have hdiag : ∀ i : d,
      (∑ α : ι, c α * Complex.normSq ((C α *ᵥ ψ) i)) ^ 2
        ≤ ∑ j : d, Complex.normSq (∑ α : ι, (c α : ℂ) * (C α *ᵥ ψ) i
            * conj ((C α *ᵥ ψ) j)) := by
    intro i
    have h1 : (∑ α : ι, c α * Complex.normSq ((C α *ᵥ ψ) i)) ^ 2
        = Complex.normSq (∑ α : ι, (c α : ℂ) * (C α *ᵥ ψ) i
            * conj ((C α *ᵥ ψ) i)) := by
      rw [hTdiag i, Complex.normSq_ofReal, sq]
    rw [h1]
    exact Finset.single_le_sum
      (f := fun j : d => Complex.normSq (∑ α : ι, (c α : ℂ) * (C α *ᵥ ψ) i
        * conj ((C α *ᵥ ψ) j)))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  -- 3. the criterion bounds the Gram mass
  have hbound : ∑ α : ι, ∑ β : ι,
      c α * c β * Complex.normSq (decoherenceFunctional C ψ α β)
        ≤ (Fintype.card ι : ℝ)
          + ε ^ 2 * (Fintype.card ι * ((Fintype.card ι : ℝ) - 1)) := by
    have hsplit : ∀ α : ι,
        ∑ β : ι, c α * c β
            * Complex.normSq (decoherenceFunctional C ψ α β)
          = c α * c α * Complex.normSq (decoherenceFunctional C ψ α α)
            + ∑ β ∈ Finset.univ.erase α,
                c α * c β
                  * Complex.normSq (decoherenceFunctional C ψ α β) :=
      fun α => (Finset.add_sum_erase _ _ (Finset.mem_univ α)).symm
    have hdiagval : ∀ α : ι,
        c α * c α * Complex.normSq (decoherenceFunctional C ψ α α)
          = 1 := by
      intro α
      have hnsq : Complex.normSq (decoherenceFunctional C ψ α α)
          = (decoherenceFunctional C ψ α α).re
            * (decoherenceFunctional C ψ α α).re := by
        rw [Complex.normSq_apply, diagonal_im_zero, mul_zero, add_zero]
      rw [hnsq]
      linear_combination
        (c α * (decoherenceFunctional C ψ α α).re + 1) * hcp α
    have hoff : ∀ α : ι, ∀ β ∈ Finset.univ.erase α,
        c α * c β * Complex.normSq (decoherenceFunctional C ψ α β)
          ≤ ε ^ 2 := by
      intro α β hβ
      have hne : α ≠ β := (Finset.ne_of_mem_erase hβ).symm
      have hcrit := h α β hne
      have hsq : ‖decoherenceFunctional C ψ α β‖ ^ 2
          ≤ (ε * Real.sqrt ((decoherenceFunctional C ψ α α).re
              * (decoherenceFunctional C ψ β β).re)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hcrit 2
      rw [mul_pow, Real.sq_sqrt (mul_nonneg (hp α).le (hp β).le)] at hsq
      have hns : Complex.normSq (decoherenceFunctional C ψ α β)
          ≤ ε ^ 2 * ((decoherenceFunctional C ψ α α).re
              * (decoherenceFunctional C ψ β β).re) := by
        calc Complex.normSq (decoherenceFunctional C ψ α β)
            = ‖decoherenceFunctional C ψ α β‖ ^ 2 :=
              normSq_eq_sq_norm _
          _ ≤ ε ^ 2 * ((decoherenceFunctional C ψ α α).re
                * (decoherenceFunctional C ψ β β).re) := hsq
      calc c α * c β * Complex.normSq (decoherenceFunctional C ψ α β)
          ≤ c α * c β
              * (ε ^ 2 * ((decoherenceFunctional C ψ α α).re
                  * (decoherenceFunctional C ψ β β).re)) :=
            mul_le_mul_of_nonneg_left hns (mul_nonneg (hc α) (hc β))
        _ = ε ^ 2 := by
            linear_combination
              (ε ^ 2 * (c β * (decoherenceFunctional C ψ β β).re))
                  * hcp α
                + ε ^ 2 * hcp β
    have hoffsum : ∀ α : ι,
        ∑ β ∈ Finset.univ.erase α,
            c α * c β * Complex.normSq (decoherenceFunctional C ψ α β)
          ≤ ((Fintype.card ι : ℝ) - 1) * ε ^ 2 := by
      intro α
      calc ∑ β ∈ Finset.univ.erase α,
            c α * c β * Complex.normSq (decoherenceFunctional C ψ α β)
          ≤ ∑ _β ∈ Finset.univ.erase α, ε ^ 2 :=
            Finset.sum_le_sum (hoff α)
        _ = ((Finset.univ.erase α).card : ℝ) * ε ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((Fintype.card ι : ℝ) - 1) * ε ^ 2 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ α),
              Finset.card_univ]
            have hpos : 1 ≤ Fintype.card ι :=
              Fintype.card_pos_iff.mpr ⟨α⟩
            push_cast [Nat.cast_sub hpos]
            ring_nf
    calc ∑ α : ι, ∑ β : ι,
          c α * c β * Complex.normSq (decoherenceFunctional C ψ α β)
        = ∑ α : ι,
            (c α * c α * Complex.normSq (decoherenceFunctional C ψ α α)
              + ∑ β ∈ Finset.univ.erase α,
                  c α * c β
                    * Complex.normSq (decoherenceFunctional C ψ α β)) :=
          Finset.sum_congr rfl fun α _ => hsplit α
      _ ≤ ∑ _α : ι, (1 + ((Fintype.card ι : ℝ) - 1) * ε ^ 2) := by
          refine Finset.sum_le_sum fun α _ => ?_
          rw [hdiagval α]
          linarith [hoffsum α]
      _ = (Fintype.card ι : ℝ)
            + ε ^ 2 * (Fintype.card ι * ((Fintype.card ι : ℝ) - 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
          ring
  -- assemble
  calc (Fintype.card ι : ℝ) ^ 2
      = (∑ i : d, ∑ α : ι, c α * Complex.normSq ((C α *ᵥ ψ) i)) ^ 2 := by
        rw [htrace]
    _ ≤ (Fintype.card d : ℝ)
          * ∑ i : d,
              (∑ α : ι, c α * Complex.normSq ((C α *ᵥ ψ) i)) ^ 2 :=
        sq_sum_le_card_mul_sum_sq' _
    _ ≤ (Fintype.card d : ℝ)
          * ∑ i : d, ∑ j : d,
              Complex.normSq (∑ α : ι, (c α : ℂ) * (C α *ᵥ ψ) i
                * conj ((C α *ᵥ ψ) j)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum fun i _ => hdiag i
    _ = (Fintype.card d : ℝ)
          * ∑ α : ι, ∑ β : ι,
              c α * c β
                * Complex.normSq (decoherenceFunctional C ψ α β) := by
        rw [gram_expansion]
    _ ≤ (Fintype.card d : ℝ)
          * ((Fintype.card ι : ℝ)
              + ε ^ 2
                * (Fintype.card ι * ((Fintype.card ι : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)

/-- **The frame bound, linear form**: with at least one history,
`M - d ≤ ε² · d · (M - 1)` — the division-free contrapositive of the
kissing bound `ε² ≥ (M-d)/(d(M-1))`. -/
theorem welch_of_nonnull [Fintype ι] [Nonempty ι] {ε : ℝ}
    {C : ι → Matrix d d ℂ} {ψ : d → ℂ}
    (hnn : ∀ α, C α *ᵥ ψ ≠ 0) (h : ApproxMediumDecoherent ε C ψ) :
    (Fintype.card ι : ℝ) - Fintype.card d
      ≤ ε ^ 2 * Fintype.card d * ((Fintype.card ι : ℝ) - 1) := by
  have hsq := welch_sq_of_nonnull hnn h
  have hM : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hM0 : (0 : ℝ) < (Fintype.card ι : ℝ) := lt_of_lt_of_le one_pos hM
  have key : (Fintype.card ι : ℝ)
      * ((Fintype.card ι : ℝ) - Fintype.card d)
        ≤ (Fintype.card ι : ℝ)
          * (ε ^ 2 * Fintype.card d * ((Fintype.card ι : ℝ) - 1)) := by
    nlinarith [hsq]
  exact le_of_mul_le_mul_left key hM0

open scoped Classical in
/-- **The kissing-bound inversion, non-null-count form**: for any family
(no non-nullity hypothesis), with `M ≥ 1` the number of non-null
histories, `M - d ≤ ε² · d · (M - 1)`. -/
theorem nonnull_card_welch [Fintype ι] {ε : ℝ}
    {C : ι → Matrix d d ℂ} {ψ : d → ℂ} (h : ApproxMediumDecoherent ε C ψ)
    (hM : 1 ≤ ((Finset.univ : Finset ι).filter
      fun α => C α *ᵥ ψ ≠ 0).card) :
    ((((Finset.univ : Finset ι).filter
        fun α => C α *ᵥ ψ ≠ 0).card : ℝ)) - Fintype.card d
      ≤ ε ^ 2 * Fintype.card d
        * ((((Finset.univ : Finset ι).filter
            fun α => C α *ᵥ ψ ≠ 0).card : ℝ) - 1) := by
  have hne : ((Finset.univ : Finset ι).filter
      fun α => C α *ᵥ ψ ≠ 0).Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le one_pos hM)
  obtain ⟨α₀, hα₀⟩ := hne
  have hα₀' : C α₀ *ᵥ ψ ≠ 0 := (Finset.mem_filter.mp hα₀).2
  haveI : Nonempty {α : ι // C α *ᵥ ψ ≠ 0} := ⟨⟨α₀, hα₀'⟩⟩
  have h' : ApproxMediumDecoherent ε
      (fun a : {α : ι // C α *ᵥ ψ ≠ 0} => C a.val) ψ := by
    intro a b hab
    exact h a.val b.val fun hv => hab (Subtype.ext hv)
  have hnn' : ∀ a : {α : ι // C α *ᵥ ψ ≠ 0},
      (fun a : {α : ι // C α *ᵥ ψ ≠ 0} => C a.val) a *ᵥ ψ ≠ 0 :=
    fun a => a.2
  have hres := welch_of_nonnull hnn' h'
  rwa [Fintype.card_subtype] at hres

open scoped Classical in
/-- **The Donald stratum is empty below the kissing threshold**: at
`ε · d < 1`, an `ε`-approximately medium decoherent family has at most
`d` non-null histories. Dowker–Kent's flagged phenomenon (sets with more
than `d` non-trivial histories that "cannot possibly be approximated";
their footnote credits the point to Matthew Donald) therefore cannot
occur below `ε = 1/d`, so the genericity carve their conjecture needs is
vacuously satisfiable there. Uniform in the history count — the binding
case is `M = d + 1`. -/
theorem donaldStratum_card_le [Fintype ι] {ε : ℝ} (hε : 0 ≤ ε)
    {C : ι → Matrix d d ℂ} {ψ : d → ℂ}
    (hεd : ε * Fintype.card d < 1) (h : ApproxMediumDecoherent ε C ψ) :
    ((Finset.univ : Finset ι).filter fun α => C α *ᵥ ψ ≠ 0).card
      ≤ Fintype.card d := by
  by_contra hgt
  push Not at hgt
  rcases Nat.eq_zero_or_pos (Fintype.card d) with hn0 | hn1
  · -- dimension 0: every branch vector is 0, the filter is empty
    haveI : IsEmpty d := Fintype.card_eq_zero_iff.mp hn0
    have hzero : ∀ α : ι, C α *ᵥ ψ = 0 := fun α =>
      funext fun i => (IsEmpty.false i).elim
    have hempty : ((Finset.univ : Finset ι).filter
        fun α => C α *ᵥ ψ ≠ 0) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun _ _ => not_not.mpr (hzero _)
    rw [hempty] at hgt
    simp at hgt
  · -- dimension ≥ 1
    have hM1 : 1 ≤ ((Finset.univ : Finset ι).filter
        fun α => C α *ᵥ ψ ≠ 0).card := le_trans hn1 (Nat.le_of_lt hgt)
    have hkey := nonnull_card_welch h hM1
    have hMn : (Fintype.card d : ℝ) + 1
        ≤ ((((Finset.univ : Finset ι).filter
            fun α => C α *ᵥ ψ ≠ 0).card : ℝ)) := by
      exact_mod_cast hgt
    have hn1' : (1 : ℝ) ≤ (Fintype.card d : ℝ) := by exact_mod_cast hn1
    have hεn : 0 ≤ ε * (Fintype.card d : ℝ) :=
      mul_nonneg hε (Nat.cast_nonneg _)
    have hsq : (ε * (Fintype.card d : ℝ)) ^ 2 < 1 := by
      nlinarith [hεd, hεn]
    have hM1' : (0 : ℝ)
        < ((((Finset.univ : Finset ι).filter
            fun α => C α *ᵥ ψ ≠ 0).card : ℝ)) - 1 := by linarith
    have hprod : (0 : ℝ)
        ≤ ((Fintype.card d : ℝ) - 1)
          * (((((Finset.univ : Finset ι).filter
              fun α => C α *ᵥ ψ ≠ 0).card : ℝ))
            - (Fintype.card d : ℝ) - 1) :=
      mul_nonneg (sub_nonneg.mpr hn1') (by linarith)
    nlinarith [hkey, hMn, hn1', hsq, hM1', hprod,
      mul_le_mul_of_nonneg_left hkey
        (Nat.cast_nonneg (α := ℝ) (Fintype.card d)),
      mul_lt_mul_of_pos_right hsq hM1']

open scoped Classical in
/-- **The qubit floor**: a family on a two-dimensional space with three or
more non-null histories is `ε`-approximately medium decoherent only at
`ε ≥ 1/2`. The floor is attained by the qubit trine (pairwise normalized
overlaps `1/2`), so the constant is sharp. -/
theorem qubit_floor [Fintype ι] {ε : ℝ} (hε : 0 ≤ ε)
    {C : ι → Matrix d d ℂ} {ψ : d → ℂ} (hd : Fintype.card d = 2)
    (h : ApproxMediumDecoherent ε C ψ)
    (h3 : 3 ≤ ((Finset.univ : Finset ι).filter
      fun α => C α *ᵥ ψ ≠ 0).card) :
    1 / 2 ≤ ε := by
  by_contra hlt
  push Not at hlt
  have hεd : ε * (Fintype.card d : ℝ) < 1 := by
    rw [hd]
    push_cast
    linarith
  have hcap := donaldStratum_card_le hε hεd h
  rw [hd] at hcap
  omega

open scoped Classical in
/-- The `ε = 0` face: an exactly medium-decoherent family has at most `d`
non-null histories — the family-level counting core of Dowker–Kent's
Lemma 1, obtained here from the frame bound (a mechanism independent of
the orthogonality/linear-independence route). -/
theorem mediumDecoherent_nonnull_card_le [Fintype ι]
    {C : ι → Matrix d d ℂ} {ψ : d → ℂ} (h : MediumDecoherent C ψ) :
    ((Finset.univ : Finset ι).filter fun α => C α *ᵥ ψ ≠ 0).card
      ≤ Fintype.card d :=
  donaldStratum_card_le le_rfl (by simp)
    (h.approxMediumDecoherent le_rfl)

/-! ## Instantiation on Dowker–Kent's own domain -/

section DKDomain

open QuantumConsistentSets

variable [DecidableEq d]

/-- **`ε`-approximate Dowker–Kent consistency**: the induced class-operator
family of a DK set is `ε`-approximately medium decoherent. The `ε = 0`
face is `DKConsistent` on the nose (`dkApproxConsistent_zero_iff`). -/
def DKApproxConsistent (ε : ℝ) (L : List (ProjectiveDecomposition d))
    (ψ : d → ℂ) : Prop :=
  ApproxMediumDecoherent ε (classOp L) ψ

/-- At `ε = 0`, approximate DK consistency is DK consistency. -/
theorem dkApproxConsistent_zero_iff (L : List (ProjectiveDecomposition d))
    (ψ : d → ℂ) :
    DKApproxConsistent 0 L ψ ↔ DKConsistent L ψ :=
  approxMediumDecoherent_zero_iff (classOp L) ψ

/-- Exact DK consistency is `ε`-approximate DK consistency at every
`ε ≥ 0`. -/
theorem DKConsistent.dkApproxConsistent {ε : ℝ} (hε : 0 ≤ ε)
    {L : List (ProjectiveDecomposition d)} {ψ : d → ℂ}
    (h : DKConsistent L ψ) : DKApproxConsistent ε L ψ :=
  MediumDecoherent.approxMediumDecoherent hε h

open scoped Classical in
/-- The Donald-stratum emptiness on Dowker–Kent's domain: below the
kissing threshold `ε · d < 1`, an `ε`-approximately consistent DK set has
at most `d` histories of non-zero probability. -/
theorem dkApproxConsistent_nonnull_card_le {ε : ℝ} (hε : 0 ≤ ε)
    (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ)
    (hεd : ε * Fintype.card d < 1) (h : DKApproxConsistent ε L ψ) :
    ((Finset.univ : Finset (History L)).filter
      fun h => branch L ψ h ≠ 0).card ≤ Fintype.card d :=
  donaldStratum_card_le hε hεd h

open scoped Classical in
/-- The qubit floor on Dowker–Kent's domain: a qubit DK set with three or
more histories of non-zero probability is `ε`-approximately consistent
only at `ε ≥ 1/2`. -/
theorem dkApproxConsistent_qubit_floor {ε : ℝ} (hε : 0 ≤ ε)
    (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ)
    (hd : Fintype.card d = 2) (h : DKApproxConsistent ε L ψ)
    (h3 : 3 ≤ ((Finset.univ : Finset (History L)).filter
      fun h => branch L ψ h ≠ 0).card) :
    1 / 2 ≤ ε :=
  qubit_floor hε hd h h3

end DKDomain

end QuantumApproxCap

end Qtsl
