import Mathlib.Analysis.CStarAlgebra.Matrix
import QtslAux.QuantumApproxConsistency

/-! # Quantitative instances of the approximate-to-exact passage

Concrete **instances** — not a proof of any conjecture — of the passage from
approximate to exact medium decoherence, in the vocabulary of
`QtslAux.QuantumApproxConsistency` (the medium Dowker–Halliwell criterion
with McElwaine's `≤` repair): families that are `ε`-approximately medium
decoherent but not exactly so, together with an exactly medium-decoherent
family nearby, the distance bounded by an explicit constant times `ε`.
This exhibits, at instance grade, the *inclusion direction* posed by
Dowker–Kent (J. Stat. Phys. 82, 1575 (1996), gr-qc/9412067): approximately
consistent sets contain exactly consistent sets in their neighbourhood.
Only that one direction is exhibited; the converse inclusion fails in DH
normalization near null histories and is not claimed.

**The metric, declared.** Distances below are stated directly on the
class-operator family, as `∑ α, ‖C α - E α‖` in the **L2 operator norm**
(`Matrix.Norms.L2Operator` scoped instances) — the shape of Dowker–Kent's
metric (a sum of aligned per-cell operator-norm differences), taken at the
class-operator stratum as an interim metric while the projective-
decomposition structure and its `dkDist` are still in flight (see the
workshop phase-2 spec accompanying `QuantumApproxConsistency`).

**Instance 1 (the symmetric leak family, `A = 1` at the sharp `ε`).**
An exhaustive two-history qubit family of positive diagonal operators,
`C₀ = (1+b)⁻¹·diag(1,b)`, `C₁ = (1+b)⁻¹·diag(b,1)` at the state `(1,1)`:
for every `b ∈ (0,1)` it is `ε`-approximately medium decoherent with
`ε = 2b/(1+b²)` — and this is *sharp* (`symmetricLeakFamily_approx_sharp`:
no smaller criterion value admits it), so the exhibited `ε` is the exact
DH ratio, not an inflation — while the exactly medium-decoherent pointer
family `(Pz0, Pz1)` sits at distance exactly `2b/(1+b) ≤ 1 · ε`. As `b`
ranges over `(0,1)` the sharp `ε` covers all of `(0,1)`: the passage is
witnessed with constant `A = 1` at every criterion value below the
vacuity threshold.

**Instance 2 (the qubit trine, `A = 2` at the kissing floor).** Three
rank-one projectors onto equiangular qubit directions, at the state
`(1,0)`: approximately medium decoherent at `ε = 1/2` and at no smaller
value (`trineFamily_approx_sharp`) — `1/2` is McElwaine's kissing-bound
floor for three non-null histories in dimension two, and the trine
saturates it — with an exactly medium-decoherent family at distance
`1 = 2 · ε` (two of its three branches null, as the dimension cap
forces).

**Why these families are not projective history sets.** In dimension two,
any history family built from projective decompositions whose (effective)
final decomposition has rank pattern `(1,1)` is *rigid*: branch vectors
sharing the final outcome lie in one rank-one range, hence are parallel,
so their DH ratio is `1` unless a branch is null — `ε`-approximate medium
decoherence at any `ε < 1` then forces exact medium decoherence (the
approximate and exact varieties coincide below the vacuity threshold).
Non-degenerate qubit instances therefore must be non-projective, as both
instances here are. The theorem `approx_implies_exact_of_rank_one_final`
below is this rigidity statement at its natural generality: any dimension,
any family of earlier-time operators (hence any number of earlier times),
any orthonormal rank-one final decomposition. -- [classical]
-/

namespace Qtsl

namespace QuantumApproxExactInstance

open Matrix
open QuantumRecords
open QuantumApproxConsistency
open scoped Matrix.Norms.L2Operator

/-! ## Norm and arithmetic helpers -/

/-- The sup norm of a two-entry vector is the max of the entry norms. -/
theorem pi_norm_pair (x y : ℂ) : ‖![x, y]‖ = max ‖x‖ ‖y‖ := by
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg
      (le_max_iff.mpr (Or.inl (norm_nonneg x)))).mpr fun i => ?_
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (norm_le_pi_norm ![x, y] 0) (norm_le_pi_norm ![x, y] 1)

/-- `Pz0` is the diagonal matrix `diag(1, 0)`. -/
theorem pz0_eq_diagonal : Pz0 = Matrix.diagonal ![1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pz0, Matrix.diagonal_apply]

/-- `Pz1` is the diagonal matrix `diag(0, 1)`. -/
theorem pz1_eq_diagonal : Pz1 = Matrix.diagonal ![0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pz1, Matrix.diagonal_apply]

/-- `√3 · √3 = 3`, at the complex level. -/
theorem sqrt3_mul_self : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  norm_num

/-- `(√3)² = 3`, at the complex level. -/
theorem sqrt3_sq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
  rw [sq]; exact sqrt3_mul_self

/-- Reduce one Dowker–Halliwell criterion cell to real arithmetic: when
the three decoherence-functional entries of a pair are (coercions of)
explicit reals, the criterion inequality follows from its real shadow.
Stated `exact`-application-style so it applies up to definitional
unfolding of the indices (robust under `fin_cases`). -/
private theorem criterion_of_values {d ι : Type*} [Fintype d]
    {C : ι → Matrix d d ℂ} {ψ : d → ℂ} {α β : ι} {x u v ε : ℝ}
    (hD : decoherenceFunctional C ψ α β = ((x : ℝ) : ℂ))
    (hu : decoherenceFunctional C ψ α α = ((u : ℝ) : ℂ))
    (hv : decoherenceFunctional C ψ β β = ((v : ℝ) : ℂ))
    (hbound : |x| ≤ ε * Real.sqrt (u * v)) :
    ‖decoherenceFunctional C ψ α β‖
      ≤ ε * Real.sqrt ((decoherenceFunctional C ψ α α).re
          * (decoherenceFunctional C ψ β β).re) := by
  rw [hD, hu, hv]
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  exact hbound

/-! ## Instance 1: the symmetric leak family -/

/-- The symmetric leak family: an exhaustive two-history family of positive
diagonal operators on the qubit, leaking weight symmetrically between the
two pointer states. Deliberately *not* a projective family — see the
module docstring: no qubit projective family witnesses a non-degenerate
instance. -/
noncomputable def symmetricLeakFamily (b : ℝ) :
    Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![Matrix.diagonal ![(((1 + b)⁻¹ : ℝ) : ℂ), ((b * (1 + b)⁻¹ : ℝ) : ℂ)],
    Matrix.diagonal ![((b * (1 + b)⁻¹ : ℝ) : ℂ), (((1 + b)⁻¹ : ℝ) : ℂ)]]

/-- The exact pointer family: the `z`-basis projectors. -/
noncomputable def pointerFamily : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![Pz0, Pz1]

/-- The leak family is exhaustive: its members sum to the identity. -/
theorem symmetricLeakFamily_sum_eq_one {b : ℝ} (hb : 0 ≤ b) :
    symmetricLeakFamily b 0 + symmetricLeakFamily b 1 = 1 := by
  have hb1 : (1 : ℝ) + b ≠ 0 := by positivity
  have hb1c : (1 : ℂ) + (b : ℂ) ≠ 0 := by exact_mod_cast hb1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricLeakFamily, Matrix.add_apply, Matrix.diagonal_apply,
      Matrix.one_apply] <;>
    (push_cast; field_simp; try ring)

/-- Branch vector of the leak family's first history at the state `(1,1)`. -/
theorem symmetricLeakFamily_mulVec_zero (b : ℝ) :
    symmetricLeakFamily b 0 *ᵥ ![1, 1]
      = ![(((1 + b)⁻¹ : ℝ) : ℂ), ((b * (1 + b)⁻¹ : ℝ) : ℂ)] := by
  funext i
  fin_cases i <;> simp [symmetricLeakFamily, Matrix.mulVec_diagonal]

/-- Branch vector of the leak family's second history at the state `(1,1)`. -/
theorem symmetricLeakFamily_mulVec_one (b : ℝ) :
    symmetricLeakFamily b 1 *ᵥ ![1, 1]
      = ![((b * (1 + b)⁻¹ : ℝ) : ℂ), (((1 + b)⁻¹ : ℝ) : ℂ)] := by
  funext i
  fin_cases i <;> simp [symmetricLeakFamily, Matrix.mulVec_diagonal]

/-- The `(0,1)` decoherence-functional entry of the leak family. -/
theorem symmetricLeakFamily_D_off (b : ℝ) :
    decoherenceFunctional (symmetricLeakFamily b) ![1, 1] 0 1
      = ((2 * b * ((1 + b)⁻¹) ^ 2 : ℝ) : ℂ) := by
  simp only [decoherenceFunctional, symmetricLeakFamily_mulVec_zero,
    symmetricLeakFamily_mulVec_one]
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

/-- The `(1,0)` decoherence-functional entry of the leak family. -/
theorem symmetricLeakFamily_D_off' (b : ℝ) :
    decoherenceFunctional (symmetricLeakFamily b) ![1, 1] 1 0
      = ((2 * b * ((1 + b)⁻¹) ^ 2 : ℝ) : ℂ) := by
  rw [decoherenceFunctional_conj, symmetricLeakFamily_D_off]
  simp [Complex.star_def, Complex.conj_ofReal]

/-- The first diagonal decoherence-functional entry of the leak family. -/
theorem symmetricLeakFamily_D_zero (b : ℝ) :
    decoherenceFunctional (symmetricLeakFamily b) ![1, 1] 0 0
      = (((1 + b ^ 2) * ((1 + b)⁻¹) ^ 2 : ℝ) : ℂ) := by
  simp only [decoherenceFunctional, symmetricLeakFamily_mulVec_zero]
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

/-- The second diagonal decoherence-functional entry of the leak family. -/
theorem symmetricLeakFamily_D_one (b : ℝ) :
    decoherenceFunctional (symmetricLeakFamily b) ![1, 1] 1 1
      = (((1 + b ^ 2) * ((1 + b)⁻¹) ^ 2 : ℝ) : ℂ) := by
  simp only [decoherenceFunctional, symmetricLeakFamily_mulVec_one]
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

/-- The leak family is `ε`-approximately medium decoherent at
`ε = 2b/(1+b²)`. (In fact the criterion holds with equality — see
`symmetricLeakFamily_approx_sharp` for the matching lower bound.) -/
theorem symmetricLeakFamily_approxMediumDecoherent {b : ℝ} (hb : 0 ≤ b) :
    ApproxMediumDecoherent (2 * b / (1 + b ^ 2))
      (symmetricLeakFamily b) ![1, 1] := by
  have hb1 : (0 : ℝ) < 1 + b := by positivity
  have hb2 : (0 : ℝ) < 1 + b ^ 2 := by positivity
  have hbound : |2 * b * ((1 + b)⁻¹) ^ 2|
      ≤ (2 * b / (1 + b ^ 2))
        * Real.sqrt (((1 + b ^ 2) * ((1 + b)⁻¹) ^ 2)
            * ((1 + b ^ 2) * ((1 + b)⁻¹) ^ 2)) := by
    rw [Real.sqrt_mul_self
        (by positivity : (0:ℝ) ≤ (1 + b ^ 2) * ((1 + b)⁻¹) ^ 2),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * b * ((1 + b)⁻¹) ^ 2)]
    refine le_of_eq ?_
    field_simp
    try ring
  intro α β hαβ
  fin_cases α <;> fin_cases β
  · exact absurd rfl hαβ
  · exact criterion_of_values (symmetricLeakFamily_D_off b)
      (symmetricLeakFamily_D_zero b) (symmetricLeakFamily_D_one b) hbound
  · exact criterion_of_values (symmetricLeakFamily_D_off' b)
      (symmetricLeakFamily_D_one b) (symmetricLeakFamily_D_zero b) hbound
  · exact absurd rfl hαβ

/-- Sharpness: no criterion value below `2b/(1+b²)` admits the leak
family — the exhibited `ε` is the exact DH ratio, not an inflation. -/
theorem symmetricLeakFamily_approx_sharp {b : ℝ} (hb : 0 < b) {ε : ℝ}
    (h : ApproxMediumDecoherent ε (symmetricLeakFamily b) ![1, 1]) :
    2 * b / (1 + b ^ 2) ≤ ε := by
  have hb2 : (0 : ℝ) < 1 + b ^ 2 := by positivity
  have hs2 : (0 : ℝ) < ((1 + b)⁻¹) ^ 2 := by positivity
  have h01 := h 0 1 (by decide)
  rw [symmetricLeakFamily_D_off, symmetricLeakFamily_D_zero,
    symmetricLeakFamily_D_one] at h01
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at h01
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * b * ((1 + b)⁻¹) ^ 2),
    Real.sqrt_mul_self
      (by positivity : (0:ℝ) ≤ (1 + b ^ 2) * ((1 + b)⁻¹) ^ 2)] at h01
  rw [div_le_iff₀ hb2]
  nlinarith [h01, hs2]

/-- The leak family is *not* exactly medium decoherent for `b > 0`: the
exhibited approximate family is genuinely distinct from every exact one. -/
theorem symmetricLeakFamily_not_mediumDecoherent {b : ℝ} (hb : 0 < b) :
    ¬ MediumDecoherent (symmetricLeakFamily b) ![1, 1] := by
  intro h
  have h01 := h 0 1 (by decide)
  rw [symmetricLeakFamily_D_off, Complex.ofReal_eq_zero] at h01
  have hpos : (0:ℝ) < 2 * b * ((1 + b)⁻¹) ^ 2 := by positivity
  linarith

/-- The pointer family is exactly medium decoherent at the state `(1,1)`. -/
theorem pointerFamily_mediumDecoherent :
    MediumDecoherent pointerFamily ![1, 1] := by
  intro α β hαβ
  fin_cases α <;> fin_cases β <;>
    first
      | exact absurd rfl hαβ
      | (simp only [decoherenceFunctional, pointerFamily]
         norm_num [Pz0, Pz1, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
           Pi.star_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
           Matrix.head_cons])

/-- The distance from the leak family to the exact pointer family, in the
interim (summed L2 operator norm) metric: exactly `2b/(1+b)`. -/
theorem symmetricLeakFamily_dist {b : ℝ} (hb : 0 ≤ b) :
    ∑ α, ‖symmetricLeakFamily b α - pointerFamily α‖ = 2 * b / (1 + b) := by
  have hb1 : (1 : ℝ) + b ≠ 0 := by positivity
  have hb1c : (1 : ℂ) + (b : ℂ) ≠ 0 := by exact_mod_cast hb1
  have hbs : (0 : ℝ) ≤ b * (1 + b)⁻¹ := by positivity
  have h0 : symmetricLeakFamily b 0 - pointerFamily 0
      = Matrix.diagonal
          ![((-(b * (1 + b)⁻¹) : ℝ) : ℂ), ((b * (1 + b)⁻¹ : ℝ) : ℂ)] := by
    show symmetricLeakFamily b 0 - Pz0 = _
    rw [pz0_eq_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symmetricLeakFamily, Matrix.sub_apply, Matrix.diagonal_apply] <;>
      (push_cast; field_simp; try ring)
  have h1 : symmetricLeakFamily b 1 - pointerFamily 1
      = Matrix.diagonal
          ![((b * (1 + b)⁻¹ : ℝ) : ℂ), ((-(b * (1 + b)⁻¹) : ℝ) : ℂ)] := by
    show symmetricLeakFamily b 1 - Pz1 = _
    rw [pz1_eq_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symmetricLeakFamily, Matrix.sub_apply, Matrix.diagonal_apply] <;>
      (push_cast; field_simp; try ring)
  rw [Fin.sum_univ_two, h0, h1, Matrix.l2_opNorm_diagonal,
    Matrix.l2_opNorm_diagonal, pi_norm_pair, pi_norm_pair]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg hbs, max_self]
  field_simp
  ring

/-- **The quantitative instance, packaged** (the inclusion direction of the
Dowker–Kent approximate-vs-exact relationship, at instance grade, with the
explicit constant `A = 1`): for every `b ∈ (0,1)`, the symmetric leak
family is `ε`-approximately medium decoherent at `ε = 2b/(1+b²)` (its
sharp criterion value), is not exactly medium decoherent, and the exactly
medium-decoherent pointer family sits within interim-metric distance
`1 · ε` of it. As `b` ranges over `(0,1)`, the sharp `ε` covers all of
`(0,1)`. Only this inclusion direction is exhibited; nothing here is, or
is claimed to be, a proof of the Dowker–Kent conjecture. -/
theorem approxToExact_instance_symmetricLeak {b : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) :
    ApproxMediumDecoherent (2 * b / (1 + b ^ 2))
        (symmetricLeakFamily b) ![1, 1]
    ∧ ¬ MediumDecoherent (symmetricLeakFamily b) ![1, 1]
    ∧ MediumDecoherent pointerFamily ![1, 1]
    ∧ ∑ α, ‖symmetricLeakFamily b α - pointerFamily α‖
        ≤ 1 * (2 * b / (1 + b ^ 2)) := by
  refine ⟨symmetricLeakFamily_approxMediumDecoherent hb0.le,
    symmetricLeakFamily_not_mediumDecoherent hb0,
    pointerFamily_mediumDecoherent, ?_⟩
  rw [symmetricLeakFamily_dist hb0.le, one_mul]
  have hbb : (0 : ℝ) < 1 + b := by positivity
  have hb2 : (0 : ℝ) < 1 + b ^ 2 := by positivity
  rw [div_le_div_iff₀ hbb hb2]
  nlinarith [hb0, hb1]

/-! ## Instance 2: the qubit trine -/

/-- The qubit trine: rank-one projectors onto the three equiangular
directions `(1,0)`, `(-1/2, ±√3/2)`. Three non-null histories in
dimension two — more than the exact-decoherence cap — with pairwise DH
ratio exactly `1/2`, McElwaine's kissing-bound floor for `M = 3`,
`d = 2`. -/
noncomputable def trineFamily : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![Pz0,
    !![((1/4 : ℝ) : ℂ), ((-(Real.sqrt 3)/4 : ℝ) : ℂ);
       ((-(Real.sqrt 3)/4 : ℝ) : ℂ), ((3/4 : ℝ) : ℂ)],
    !![((1/4 : ℝ) : ℂ), ((Real.sqrt 3/4 : ℝ) : ℂ);
       ((Real.sqrt 3/4 : ℝ) : ℂ), ((3/4 : ℝ) : ℂ)]]

/-- The exact witness for the trine: the pointer projectors, with the two
branches beyond the dimension cap gone null (`Pz1` annihilates the state
`(1,0)`). -/
noncomputable def trineExactWitness : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![Pz0, Pz1, Pz1]

/-- First trine branch vector at the state `(1,0)`. -/
theorem trineFamily_mulVec_zero :
    trineFamily 0 *ᵥ ![1, 0] = ![(1 : ℂ), 0] := by
  funext i
  fin_cases i <;>
    simp [trineFamily, Pz0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Second trine branch vector at the state `(1,0)`. -/
theorem trineFamily_mulVec_one :
    trineFamily 1 *ᵥ ![1, 0]
      = ![((1/4 : ℝ) : ℂ), ((-(Real.sqrt 3)/4 : ℝ) : ℂ)] := by
  funext i
  fin_cases i <;>
    simp [trineFamily, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Third trine branch vector at the state `(1,0)`. -/
theorem trineFamily_mulVec_two :
    trineFamily 2 *ᵥ ![1, 0]
      = ![((1/4 : ℝ) : ℂ), ((Real.sqrt 3/4 : ℝ) : ℂ)] := by
  funext i
  fin_cases i <;>
    simp [trineFamily, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

section TrineD

private lemma trine_D_00 :
    decoherenceFunctional trineFamily ![1, 0] 0 0 = ((1 : ℝ) : ℂ) := by
  simp only [decoherenceFunctional, trineFamily_mulVec_zero]
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.star_def, map_one, map_zero]
  push_cast
  ring

private lemma trine_D_11 :
    decoherenceFunctional trineFamily ![1, 0] 1 1 = ((1/4 : ℝ) : ℂ) := by
  simp only [decoherenceFunctional, trineFamily_mulVec_one]
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  linear_combination (1/16 : ℂ) * sqrt3_sq

private lemma trine_D_22 :
    decoherenceFunctional trineFamily ![1, 0] 2 2 = ((1/4 : ℝ) : ℂ) := by
  simp only [decoherenceFunctional, trineFamily_mulVec_two]
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  linear_combination (1/16 : ℂ) * sqrt3_sq

private lemma trine_D_01 :
    decoherenceFunctional trineFamily ![1, 0] 0 1 = ((1/4 : ℝ) : ℂ) := by
  simp only [decoherenceFunctional, trineFamily_mulVec_zero,
    trineFamily_mulVec_one]
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

private lemma trine_D_10 :
    decoherenceFunctional trineFamily ![1, 0] 1 0 = ((1/4 : ℝ) : ℂ) := by
  simp only [decoherenceFunctional, trineFamily_mulVec_zero,
    trineFamily_mulVec_one]
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.star_def, map_one, map_zero]
  push_cast
  ring

private lemma trine_D_02 :
    decoherenceFunctional trineFamily ![1, 0] 0 2 = ((1/4 : ℝ) : ℂ) := by
  simp only [decoherenceFunctional, trineFamily_mulVec_zero,
    trineFamily_mulVec_two]
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

private lemma trine_D_20 :
    decoherenceFunctional trineFamily ![1, 0] 2 0 = ((1/4 : ℝ) : ℂ) := by
  simp only [decoherenceFunctional, trineFamily_mulVec_zero,
    trineFamily_mulVec_two]
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.star_def, map_one, map_zero]
  push_cast
  ring

private lemma trine_D_12 :
    decoherenceFunctional trineFamily ![1, 0] 1 2 = ((-(1/8) : ℝ) : ℂ) := by
  simp only [decoherenceFunctional, trineFamily_mulVec_one,
    trineFamily_mulVec_two]
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  linear_combination (-1/16 : ℂ) * sqrt3_sq

private lemma trine_D_21 :
    decoherenceFunctional trineFamily ![1, 0] 2 1 = ((-(1/8) : ℝ) : ℂ) := by
  simp only [decoherenceFunctional, trineFamily_mulVec_one,
    trineFamily_mulVec_two]
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  linear_combination (-1/16 : ℂ) * sqrt3_sq

end TrineD

/-- The trine is approximately medium decoherent at `ε = 1/2` — every
off-diagonal pair meets the criterion with equality. -/
theorem trineFamily_approxMediumDecoherent :
    ApproxMediumDecoherent (1/2) trineFamily ![1, 0] := by
  intro α β hαβ
  fin_cases α <;> fin_cases β
  · exact absurd rfl hαβ
  · exact criterion_of_values trine_D_01 trine_D_00 trine_D_11
      (by rw [show ((1:ℝ) * (1/4 : ℝ)) = ((1/2 : ℝ))^2 by norm_num,
            Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (1/2 : ℝ))]
          norm_num)
  · exact criterion_of_values trine_D_02 trine_D_00 trine_D_22
      (by rw [show ((1:ℝ) * (1/4 : ℝ)) = ((1/2 : ℝ))^2 by norm_num,
            Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (1/2 : ℝ))]
          norm_num)
  · exact criterion_of_values trine_D_10 trine_D_11 trine_D_00
      (by rw [show ((1/4 : ℝ) * (1:ℝ)) = ((1/2 : ℝ))^2 by norm_num,
            Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (1/2 : ℝ))]
          norm_num)
  · exact absurd rfl hαβ
  · exact criterion_of_values trine_D_12 trine_D_11 trine_D_22
      (by rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ (1/4 : ℝ))]
          norm_num)
  · exact criterion_of_values trine_D_20 trine_D_22 trine_D_00
      (by rw [show ((1/4 : ℝ) * (1:ℝ)) = ((1/2 : ℝ))^2 by norm_num,
            Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (1/2 : ℝ))]
          norm_num)
  · exact criterion_of_values trine_D_21 trine_D_22 trine_D_11
      (by rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ (1/4 : ℝ))]
          norm_num)
  · exact absurd rfl hαβ

/-- The trine is not exactly medium decoherent. -/
theorem trineFamily_not_mediumDecoherent :
    ¬ MediumDecoherent trineFamily ![1, 0] := by
  intro h
  have h01 := h 0 1 (by decide)
  rw [trine_D_01, Complex.ofReal_eq_zero] at h01
  norm_num at h01

/-- Saturation: the trine admits no criterion value below `1/2` — it sits
exactly at McElwaine's kissing-bound floor for three non-null histories
in dimension two. -/
theorem trineFamily_approx_sharp {ε : ℝ}
    (h : ApproxMediumDecoherent ε trineFamily ![1, 0]) : 1/2 ≤ ε := by
  have h01 := h 0 1 (by decide)
  rw [trine_D_01, trine_D_00, trine_D_11] at h01
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at h01
  rw [show ((1:ℝ) * (1/4 : ℝ)) = ((1/2 : ℝ))^2 by norm_num,
    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (1/2 : ℝ)),
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1/4 : ℝ))] at h01
  linarith

/-- The trine's exact witness is medium decoherent at `(1,0)`: its second
and third branch vectors vanish. -/
theorem trineExactWitness_mediumDecoherent :
    MediumDecoherent trineExactWitness ![1, 0] := by
  intro α β hαβ
  fin_cases α <;> fin_cases β <;>
    first
      | exact absurd rfl hαβ
      | (simp only [decoherenceFunctional, trineExactWitness]
         norm_num [Pz0, Pz1, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
           Pi.star_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
           Matrix.head_cons])

section TrineDist

private lemma trine_diff_one_eq :
    trineFamily 1 - trineExactWitness 1
      = !![((1/4 : ℝ) : ℂ), ((-(Real.sqrt 3)/4 : ℝ) : ℂ);
           ((-(Real.sqrt 3)/4 : ℝ) : ℂ), ((-(1/4) : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [trineFamily, trineExactWitness, Pz1, Matrix.sub_apply]
     try push_cast
     try norm_num)

private lemma trine_diff_two_eq :
    trineFamily 2 - trineExactWitness 2
      = !![((1/4 : ℝ) : ℂ), ((Real.sqrt 3/4 : ℝ) : ℂ);
           ((Real.sqrt 3/4 : ℝ) : ℂ), ((-(1/4) : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [trineFamily, trineExactWitness, Pz1, Matrix.sub_apply]
     try push_cast
     try norm_num)

private lemma trine_diff_one_norm :
    ‖(!![((1/4 : ℝ) : ℂ), ((-(Real.sqrt 3)/4 : ℝ) : ℂ);
         ((-(Real.sqrt 3)/4 : ℝ) : ℂ), ((-(1/4) : ℝ) : ℂ)]
       : Matrix (Fin 2) (Fin 2) ℂ)‖ = 1/2 := by
  set M : Matrix (Fin 2) (Fin 2) ℂ :=
    !![((1/4 : ℝ) : ℂ), ((-(Real.sqrt 3)/4 : ℝ) : ℂ);
       ((-(Real.sqrt 3)/4 : ℝ) : ℂ), ((-(1/4) : ℝ) : ℂ)] with hM
  have hherm : Mᴴ = M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hM, Matrix.conjTranspose_apply]
  have hprod : Mᴴ * M
      = Matrix.diagonal ![((1/4 : ℝ) : ℂ), ((1/4 : ℝ) : ℂ)] := by
    rw [hherm]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [hM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
       try push_cast
       try (first
         | linear_combination (1/16 : ℂ) * sqrt3_sq
         | ring
         | norm_num))
  have h2 : ‖M‖ * ‖M‖ = 1/4 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hprod,
      Matrix.l2_opNorm_diagonal, pi_norm_pair]
    norm_num [Complex.norm_real, Real.norm_eq_abs, max_self]
  have h3 : (‖M‖ - 1/2) * (‖M‖ + 1/2) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · linarith [norm_nonneg M]

private lemma trine_diff_two_norm :
    ‖(!![((1/4 : ℝ) : ℂ), ((Real.sqrt 3/4 : ℝ) : ℂ);
         ((Real.sqrt 3/4 : ℝ) : ℂ), ((-(1/4) : ℝ) : ℂ)]
       : Matrix (Fin 2) (Fin 2) ℂ)‖ = 1/2 := by
  set M : Matrix (Fin 2) (Fin 2) ℂ :=
    !![((1/4 : ℝ) : ℂ), ((Real.sqrt 3/4 : ℝ) : ℂ);
       ((Real.sqrt 3/4 : ℝ) : ℂ), ((-(1/4) : ℝ) : ℂ)] with hM
  have hherm : Mᴴ = M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hM, Matrix.conjTranspose_apply]
  have hprod : Mᴴ * M
      = Matrix.diagonal ![((1/4 : ℝ) : ℂ), ((1/4 : ℝ) : ℂ)] := by
    rw [hherm]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [hM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
       try push_cast
       try (first
         | linear_combination (1/16 : ℂ) * sqrt3_sq
         | ring
         | norm_num))
  have h2 : ‖M‖ * ‖M‖ = 1/4 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hprod,
      Matrix.l2_opNorm_diagonal, pi_norm_pair]
    norm_num [Complex.norm_real, Real.norm_eq_abs, max_self]
  have h3 : (‖M‖ - 1/2) * (‖M‖ + 1/2) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · linarith [norm_nonneg M]

end TrineDist

/-- The distance from the trine to its exact witness in the interim
(summed L2 operator norm) metric: exactly `1 = 2 · (1/2)`. The two moved
cells each move by operator norm `1/2`, computed through the C*-identity
`‖Mᴴ M‖ = ‖M‖²`. -/
theorem trineFamily_dist :
    ∑ α, ‖trineFamily α - trineExactWitness α‖ = 1 := by
  have h0 : trineFamily 0 - trineExactWitness 0 = 0 := by
    simp [trineFamily, trineExactWitness]
  rw [Fin.sum_univ_three, h0, trine_diff_one_eq, trine_diff_two_eq,
    norm_zero, trine_diff_one_norm, trine_diff_two_norm]
  norm_num

/-- **The trine instance, packaged**: approximately medium decoherent at
`ε = 1/2` and at no smaller value (the kissing floor, saturated), not
exactly medium decoherent, with an exactly medium-decoherent family
within `2 · ε`. Instance cargo only; nothing here is, or is claimed to
be, a proof of the Dowker–Kent conjecture. -/
theorem approxToExact_instance_trine :
    ApproxMediumDecoherent (1/2) trineFamily ![1, 0]
    ∧ ¬ MediumDecoherent trineFamily ![1, 0]
    ∧ MediumDecoherent trineExactWitness ![1, 0]
    ∧ ∑ α, ‖trineFamily α - trineExactWitness α‖ ≤ 2 * (1/2) := by
  refine ⟨trineFamily_approxMediumDecoherent,
    trineFamily_not_mediumDecoherent,
    trineExactWitness_mediumDecoherent, ?_⟩
  rw [trineFamily_dist]
  norm_num

/-! ## Rigidity of rank-one-final projective families

Why the instances above had to be non-projective: for history families
whose *final*-time decomposition is rank one along orthonormal directions,
approximate medium decoherence below the vacuity threshold collapses to
exact medium decoherence. Branch vectors sharing the final outcome are
parallel (they live in one rank-one range), so the DH criterion at
`ε < 1` forces one of each such pair null; branch vectors with distinct
final outcomes are orthogonal outright. The earlier-time operators are
arbitrary — in particular arbitrary products of earlier projectors — so
this covers every multi-time projective family over a qubit whose
effective final decomposition has rank pattern `(1,1)`, the setting in
which one might first have looked for approximate-but-not-exact
families. -/

/-- Rank-one matrix acting on a vector: `|x⟩⟨y| z = (y ⬝ᵥ z) x`. -/
private theorem vecMulVec_mulVec_eq {d : Type*} [Fintype d]
    (x y z : d → ℂ) :
    Matrix.vecMulVec x y *ᵥ z = (y ⬝ᵥ z) • x := by
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Rigidity**: a history family whose final decomposition is rank one
along pairwise-orthonormal directions `w` — class operators
`|w_b⟩⟨w_b| · P_a` with the earlier-time operators `P` arbitrary — that
is `ε`-approximately medium decoherent for any `ε < 1` is exactly medium
decoherent. On this class the approximate and exact varieties coincide
below the vacuity threshold (the Dowker–Kent inclusion holds there
degenerately, with `A = 0`); genuinely approximate-but-not-exact families
must escape it, as the instances in this module do. -/
theorem approx_implies_exact_of_rank_one_final
    {d ι κ : Type*} [Fintype d] [DecidableEq κ]
    (P : ι → Matrix d d ℂ) (w : κ → (d → ℂ))
    (hw : ∀ i j, star (w i) ⬝ᵥ w j = if i = j then 1 else 0)
    (ψ : d → ℂ) {ε : ℝ} (hε : ε < 1)
    (h : ApproxMediumDecoherent ε
      (fun ab : ι × κ =>
        Matrix.vecMulVec (w ab.2) (star (w ab.2)) * P ab.1) ψ) :
    MediumDecoherent
      (fun ab : ι × κ =>
        Matrix.vecMulVec (w ab.2) (star (w ab.2)) * P ab.1) ψ := by
  -- the branch-amplitude scalars
  set c : ι × κ → ℂ :=
    fun ab => star (w ab.2) ⬝ᵥ (P ab.1 *ᵥ ψ) with hc
  -- branch vectors are scalar multiples of the final directions
  have hCψ : ∀ ab : ι × κ,
      (Matrix.vecMulVec (w ab.2) (star (w ab.2)) * P ab.1) *ᵥ ψ
        = c ab • w ab.2 := by
    intro ab
    rw [← Matrix.mulVec_mulVec, vecMulVec_mulVec_eq]
  -- the decoherence functional in terms of the scalars
  have hD : ∀ ab ab' : ι × κ,
      decoherenceFunctional
          (fun ab : ι × κ =>
            Matrix.vecMulVec (w ab.2) (star (w ab.2)) * P ab.1) ψ ab ab'
        = (starRingEnd ℂ) (c ab') * c ab
            * (star (w ab'.2) ⬝ᵥ w ab.2) := by
    intro ab ab'
    simp only [decoherenceFunctional, hCψ]
    rw [star_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul, Complex.star_def]
    ring
  -- the diagonal entries
  have hDdiag : ∀ ab : ι × κ,
      decoherenceFunctional
          (fun ab : ι × κ =>
            Matrix.vecMulVec (w ab.2) (star (w ab.2)) * P ab.1) ψ ab ab
        = (starRingEnd ℂ) (c ab) * c ab := by
    intro ab
    rw [hD ab ab, hw, if_pos rfl, mul_one]
  have hdiag_re : ∀ ab : ι × κ,
      ((starRingEnd ℂ) (c ab) * c ab).re = ‖c ab‖ ^ 2 := by
    intro ab
    rw [mul_comm, Complex.mul_conj]
    first
      | rw [Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      | rw [Complex.ofReal_re, Complex.sq_norm]
      | simp [Complex.normSq_eq_norm_sq]
      | simp [Complex.sq_norm]
  intro α β hαβ
  by_cases hb : β.2 = α.2
  · -- same final outcome: the DH bound forces a null branch
    have happrox := h α β hαβ
    rw [hD α β, hDdiag α, hDdiag β, hw, if_pos hb, mul_one] at happrox
    rw [hdiag_re, hdiag_re, norm_mul, RCLike.norm_conj,
      show ‖c α‖ ^ 2 * ‖c β‖ ^ 2 = (‖c α‖ * ‖c β‖) ^ 2 by ring,
      Real.sqrt_sq
        (mul_nonneg (norm_nonneg (c α)) (norm_nonneg (c β)))] at happrox
    have h1 : ‖c α‖ * ‖c β‖ ≤ 0 := by nlinarith [happrox, hε]
    have hzero : ‖c α‖ * ‖c β‖ = 0 :=
      le_antisymm h1 (mul_nonneg (norm_nonneg (c α)) (norm_nonneg (c β)))
    rw [hD α β, hw, if_pos hb, mul_one]
    rcases mul_eq_zero.mp hzero with hα | hβ
    · rw [norm_eq_zero.mp hα, mul_zero]
    · rw [norm_eq_zero.mp hβ, map_zero, zero_mul]
  · -- distinct final outcomes: orthogonality kills the entry outright
    rw [hD α β, hw, if_neg hb, mul_zero]

end QuantumApproxExactInstance

end Qtsl
