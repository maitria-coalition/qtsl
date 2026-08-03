import Mathlib.Analysis.InnerProductSpace.PiL2
import QtslAux.QuantumRecords

/-! # Approximate medium decoherence (ε-consistency, the Dowker–Kent vocabulary)

Definitions ABOUT the vocabulary of Dowker–Kent's 1996 approximate-vs-exact
consistency conjecture (J. Stat. Phys. 82, 1575; gr-qc/9412067): what it means
for a family of class operators to be *approximately* consistent to order
`ε`, on the substrate of `QtslAux.QuantumRecords` (`decoherenceFunctional`,
`MediumDecoherent`). Nothing here claims progress on the conjecture itself;
these are its load-bearing nouns, made precise.

**Criterion adoption.** Dowker–Kent never fix a criterion ("satisfies
equations \decohgmh approximately"); adjudicating against McElwaine's
analysis (PRA 53, 2021 (1996), quant-ph/9506034 — the reference DK
themselves cite at the conjecture) selects the **medium Dowker–Halliwell
criterion** with McElwaine's `≤` repair,

  `‖D(α,β)‖ ≤ ε · √(D(α,α).re · D(β,β).re)   ∀ α ≠ β`,

whose `ε = 0` face is exactly `MediumDecoherent` — Dowker–Kent's own
consistency equations — and whose normalization gives it range `[0,1]`:
by Cauchy–Schwarz on the branch-vector Gram matrix, *every* family is
`ε`-consistent at `ε ≥ 1` (`approxMediumDecoherent_of_one_le`), with no
non-nullity or exhaustiveness hypothesis (that unconditionality is what the
`≤` repair buys: a null history's row of `D` vanishes identically). The
rejected bare criterion `‖D(α,β)‖ ≤ ε` is kept as a named contrast
(`ApproxMediumDecoherentAbs`): McElwaine's Theorem 6 exhibits, in every
dimension `≥ 2`, families satisfying it at any `ε > 0` with arbitrarily
large probability-sum-rule violation, so it cannot serve as the
conjecture's vocabulary; its `ε = 0` face still agrees
(`approxMediumDecoherentAbs_zero_iff`) — criterion choice is invisible at
the exact point and separates only at `ε > 0`.

**Sanity battery** (the preregistered acceptance tests, frozen before
this module was written): the `ε = 0` definitional bridge
(`approxMediumDecoherent_zero_iff`), monotonicity in `ε`
(`ApproxMediumDecoherent.mono`), exact-implies-approximate at every
`ε ≥ 0` (`MediumDecoherent.approxMediumDecoherent`), and the `ε ≥ 1`
vacuity theorem above. -- [classical]
-/

namespace Qtsl

namespace QuantumApproxConsistency

open Matrix
open QuantumRecords

variable {d : Type*} [Fintype d] {ι : Type*}

/-! ## The Gram entries as inner products, and Cauchy–Schwarz -/

/-- The decoherence functional is the Euclidean inner product of branch
vectors: `D(α,β) = ⟪C_β ψ, C_α ψ⟫` (conjugate-linear in the first slot,
matching the `star`-side of `decoherenceFunctional`). -/
theorem decoherenceFunctional_eq_inner (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (α β : ι) :
    decoherenceFunctional C ψ α β
      = inner ℂ (WithLp.toLp 2 (C β *ᵥ ψ)) (WithLp.toLp 2 (C α *ᵥ ψ)) := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [decoherenceFunctional]
  rw [dotProduct_comm]

/-- The diagonal of the decoherence functional is the squared norm of the
branch vector — the branch weight, manifestly real and nonnegative. -/
theorem decoherenceFunctional_diag_re (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (γ : ι) :
    (decoherenceFunctional C ψ γ γ).re
      = ‖(WithLp.toLp 2 (C γ *ᵥ ψ) : EuclideanSpace ℂ d)‖ ^ 2 := by
  rw [decoherenceFunctional_eq_inner, norm_sq_eq_re_inner (𝕜 := ℂ),
    RCLike.re_to_complex]

/-- **Cauchy–Schwarz for the decoherence functional**: every off-diagonal
entry is bounded by the geometric mean of its diagonal neighbors. This is
the fact that makes the (medium) Dowker–Halliwell criterion a normalized —
range `[0,1]` — measure of interference. -/
theorem norm_decoherenceFunctional_le (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (α β : ι) :
    ‖decoherenceFunctional C ψ α β‖
      ≤ Real.sqrt ((decoherenceFunctional C ψ α α).re
          * (decoherenceFunctional C ψ β β).re) := by
  rw [decoherenceFunctional_eq_inner, decoherenceFunctional_diag_re,
    decoherenceFunctional_diag_re, ← mul_pow,
    Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans_eq (mul_comm _ _)

/-! ## The two criteria -/

/-- **`ε`-approximate medium decoherence** — the adopted criterion (medium
Dowker–Halliwell, with the `≤` repair): every off-diagonal entry of the
decoherence functional is at most `ε` times the geometric mean of the
corresponding branch weights. `ε = 0` is `MediumDecoherent` on the nose
(`approxMediumDecoherent_zero_iff`); `ε ≥ 1` holds vacuously
(`approxMediumDecoherent_of_one_le`). Adoption grounds against the
alternatives: McElwaine's analysis (quant-ph/9506034). -/
def ApproxMediumDecoherent (ε : ℝ) (C : ι → Matrix d d ℂ) (ψ : d → ℂ) :
    Prop :=
  ∀ α β, α ≠ β →
    ‖decoherenceFunctional C ψ α β‖
      ≤ ε * Real.sqrt ((decoherenceFunctional C ψ α α).re
          * (decoherenceFunctional C ψ β β).re)

/-- The **bare** (absolute) criterion `‖D(α,β)‖ ≤ ε` — the *rejected*
candidate, kept as a named contrast object: McElwaine (PRA 53, 2021,
Theorem 6) shows it fails to control probability-sum-rule violations at
any fixed `ε > 0`, and it is neither scale-covariant nor branch-stable.
It shares the `ε = 0` face with the adopted criterion
(`approxMediumDecoherentAbs_zero_iff`). -/
def ApproxMediumDecoherentAbs (ε : ℝ) (C : ι → Matrix d d ℂ) (ψ : d → ℂ) :
    Prop :=
  ∀ α β, α ≠ β → ‖decoherenceFunctional C ψ α β‖ ≤ ε

/-! ## The sanity battery (preregistered) -/

/-- **T1, the definitional bridge**: `ε = 0` approximate consistency *is*
medium decoherence. -/
theorem approxMediumDecoherent_zero_iff (C : ι → Matrix d d ℂ) (ψ : d → ℂ) :
    ApproxMediumDecoherent 0 C ψ ↔ MediumDecoherent C ψ := by
  constructor
  · intro h α β hαβ
    have h0 := h α β hαβ
    rw [zero_mul] at h0
    exact norm_le_zero_iff.mp h0
  · intro h α β hαβ
    rw [h α β hαβ, norm_zero, zero_mul]

/-- **T2, monotonicity**: approximate consistency relaxes as `ε` grows. -/
theorem ApproxMediumDecoherent.mono {ε ε' : ℝ} {C : ι → Matrix d d ℂ}
    {ψ : d → ℂ} (hεε' : ε ≤ ε') (h : ApproxMediumDecoherent ε C ψ) :
    ApproxMediumDecoherent ε' C ψ := fun α β hαβ =>
  (h α β hαβ).trans
    (mul_le_mul_of_nonneg_right hεε' (Real.sqrt_nonneg _))

/-- **T3, exact ⇒ approximate**: a medium-decoherent family is
`ε`-approximately medium decoherent at every `ε ≥ 0`. -/
theorem _root_.Qtsl.QuantumRecords.MediumDecoherent.approxMediumDecoherent
    {C : ι → Matrix d d ℂ} {ψ : d → ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : MediumDecoherent C ψ) : ApproxMediumDecoherent ε C ψ := by
  intro α β hαβ
  rw [h α β hαβ, norm_zero]
  exact mul_nonneg hε (Real.sqrt_nonneg _)

/-- **T4, the normalization behaves**: at `ε ≥ 1` *every* family is
`ε`-approximately medium decoherent — Cauchy–Schwarz makes the criterion's
natural range `[0,1]`. No non-nullity or exhaustiveness hypothesis:
McElwaine's `≤` repair handles null histories (whose `D`-rows vanish
identically). This theorem is what the bare criterion cannot have —
a preregistered separation point: an absolute bound has no top
element. -/
theorem approxMediumDecoherent_of_one_le {ε : ℝ} (hε : 1 ≤ ε)
    (C : ι → Matrix d d ℂ) (ψ : d → ℂ) : ApproxMediumDecoherent ε C ψ := by
  intro α β _
  calc ‖decoherenceFunctional C ψ α β‖
      ≤ Real.sqrt ((decoherenceFunctional C ψ α α).re
          * (decoherenceFunctional C ψ β β).re) :=
        norm_decoherenceFunctional_le C ψ α β
    _ = 1 * Real.sqrt ((decoherenceFunctional C ψ α α).re
          * (decoherenceFunctional C ψ β β).re) := (one_mul _).symm
    _ ≤ ε * Real.sqrt ((decoherenceFunctional C ψ α α).re
          * (decoherenceFunctional C ψ β β).re) :=
        mul_le_mul_of_nonneg_right hε (Real.sqrt_nonneg _)

/-- **T5, the shared `ε = 0` face**: the bare criterion at `ε = 0` also
recovers medium decoherence — criterion choice is invisible at the exact
point and separates only at `ε > 0`, which is why the adjudication
is about the approximate regime. -/
theorem approxMediumDecoherentAbs_zero_iff (C : ι → Matrix d d ℂ)
    (ψ : d → ℂ) :
    ApproxMediumDecoherentAbs 0 C ψ ↔ MediumDecoherent C ψ := by
  constructor
  · intro h α β hαβ
    exact norm_le_zero_iff.mp (h α β hαβ)
  · intro h α β hαβ
    rw [h α β hαβ, norm_zero]

/-- The adopted criterion implies the bare one whenever the branch weights
are bounded by `1` (in particular on any subfamily of a normalized set):
the geometric-mean factor is then at most `1`. Recorded as the one honest
bridge between the two criteria — in general there is none, which is the
content of the adjudication. -/
theorem ApproxMediumDecoherent.abs_of_diag_le_one {ε : ℝ} (hε : 0 ≤ ε)
    {C : ι → Matrix d d ℂ} {ψ : d → ℂ}
    (hdiag : ∀ γ, (decoherenceFunctional C ψ γ γ).re ≤ 1)
    (h : ApproxMediumDecoherent ε C ψ) :
    ApproxMediumDecoherentAbs ε C ψ := by
  intro α β hαβ
  refine (h α β hαβ).trans ?_
  have hsqrt : Real.sqrt ((decoherenceFunctional C ψ α α).re
      * (decoherenceFunctional C ψ β β).re) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    refine Real.sqrt_le_sqrt ?_
    calc (decoherenceFunctional C ψ α α).re
          * (decoherenceFunctional C ψ β β).re
        ≤ 1 * 1 := by
          exact mul_le_mul (hdiag α) (hdiag β)
            (diagonal_re_nonneg C ψ β) zero_le_one
      _ = 1 := one_mul 1
  calc ε * Real.sqrt ((decoherenceFunctional C ψ α α).re
        * (decoherenceFunctional C ψ β β).re)
      ≤ ε * 1 := mul_le_mul_of_nonneg_left hsqrt hε
    _ = ε := mul_one ε

end QuantumApproxConsistency

end Qtsl
