/-
Copyright (c) 2026 The maitria coalition. All rights reserved.
Released under Apache 2.0 / MIT dual license.
-/
import QtslAux.QuantumConsistentSets

/-! # Dowker–Kent's Lemma 2, fully quantified: the profligacy of consistent sets

**Naming discipline, first**: this module is a finite-dimensional
mechanization of Dowker–Kent's Lemma 2 (Phys. Rev. Lett. 75 (1995) 3038,
gr-qc/9409037; proof in J. Stat. Phys. 82 (1996) 1575, gr-qc/9412067), at
the append position — the fully quantified theorem, not an instance. The
kernel-checked *instance* of the same construction lives in
`QtslAux.QuantumConsistentSets` (final section) and keeps its own,
deliberately weaker, name.

DK's Lemma 2, verbatim (PRL): "Let S be a set of consistent histories for
which there exists a non-trivial consistent extension. Let S have a pure
initial state ρ, and let H be either finite-dimensional or separable. Then
there exists a continuous family of non-trivial extensions for each history
in S with non-zero probability." (The JSP statement phrases the hypothesis
"that is not maximally extended" — equivalent under their definition of
maximal extension.) Their proof: normalize the nonzero-probability branch
vectors `|h_j⟩ = S_j|ψ⟩/‖S_jψ‖` (orthogonal, by consistency); "Since S is
not maximally extended, r < n", extend to an orthonormal basis with states
`|e_k⟩`; for z₁, z₂ with `z₁*z₁ + z₂*z₂ = 1` set `φ₊ = z₁h_j + z₂*e_k`,
`φ₋ = z₂h_j − z₁*e_k`, `P± = |φ±⟩⟨φ±|`, `P₃ = 1 − P₊ − P₋`,
`τ = {P₊, P₋, P₃}`; appending τ is a non-trivial consistent extension;
"Since there is a consistent extension for every choice of z₁ and z₂, the
lemma holds."

**Deltas versus DK as posed, flagged loudly** (each deliberate):

1. *Finite-dimensional only.* DK also claim separable `H`; this development
   is the finite-dimensional matrix grade throughout (its standing scope
   fence). A weakening of scope.
2. *Append position only.* DK's extensions allow insertion at any interior
   time; the landed vocabulary (and DK's own Lemma 2 construction) appends
   at the latest time. Consequently `MaximallyExtended` here quantifies
   over append extensions only, so the hypothesis `¬ MaximallyExtended` is
   formally STRONGER than DK's. The primary theorem therefore takes the
   intrinsic hypothesis `card {nonzero histories} < dim` — which is DK's
   own working hypothesis (their proof consumes non-maximality only through
   "Since S is not maximally extended, r < n") — with the
   `¬ MaximallyExtended` form as a corollary. Conclusion-side, an append
   extension is a special case of DK's extension: a strengthening.
3. *Arbitrary ψ.* DK's pure state ρ = |ψ⟩⟨ψ| has unit trace; no
   normalization of ψ is assumed here. A mild strengthening (the pure-case
   maximality iff below is where ψ ≠ 0 is genuinely consumed).
4. *"Continuous family"* is cashed exactly at the bar the instance module
   set: a map from ℝ whose members are consistent extensions for ALL
   parameter values (DK's "every choice of z₁ and z₂" — and consistency
   with nontriviality is proven here at all COMPLEX parameters,
   `genRotation_consistent`/`genRotation_nontrivialExtension`, before the
   real slice is taken), non-trivial and splitting THE GIVEN history on the
   open interval `(0, π/2)`, INJECTIVE on that interval, with projector
   entries CONTINUOUS in the parameter. A finite list of extensions would
   satisfy none of this.

**Deliverables.** `exists_unit_dotProduct_orthogonal` (the one genuinely new
interface: below full dimension, a unit vector orthogonal to any given
family — rank–nullity at the `dotProduct` grade);
`genRotation_consistent` (DK's construction consistent at every complex
parameter pair, general base set, general dimension);
`genRotation_nontrivialExtension`; the continuous family
(`dkGeneralFamily`, with injectivity and entrywise continuity);
`dowkerKent_lemma2` (the headline, packaging all clauses);
`dowkerKent_lemma2_of_not_maximallyExtended`; and
`maximallyExtended_iff_card_eq` — DK's pure-case note ("a set is maximally
extended if and only if it has n histories of non-zero probability"), BOTH
directions: the saturation direction is the landed
`maximallyExtended_of_card_eq`; the converse — the direction the instance
module deliberately did not claim — is delivered here by the construction.

The automatic-records fact needs no restatement: every member of every
family produced here is a DK-consistent set, so
`dkConsistent_projective_records` applies verbatim — record existence does
not thin these families either. -/

namespace Qtsl

namespace QuantumProfligacy

open Matrix QuantumRecords QuantumConverse QuantumCompleteness
  QuantumConsistentSets
open scoped ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## Vector-grade helpers -/

omit [DecidableEq d] in
/-- The rank-one operator acts by projection onto its vector:
`|u⟩⟨u| x = ⟨u, x⟩ u`, at the `dotProduct` grade. -/
theorem outer_mulVec (u x : d → ℂ) : outer u *ᵥ x = (star u ⬝ᵥ x) • u := by
  ext i
  simp only [outer, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq d] in
private theorem star_dot_flip {a b : d → ℂ} (h : star a ⬝ᵥ b = 0) :
    star b ⬝ᵥ a = 0 := by
  rw [Matrix.star_dotProduct, h, star_zero]

omit [DecidableEq d] in
/-- Every nonzero vector has a positive real rescaling of unit norm. -/
theorem exists_smul_unit {x : d → ℂ} (hx : x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ star ((c : ℂ) • x) ⬝ᵥ ((c : ℂ) • x) = 1 := by
  have hpos : 0 < star x ⬝ᵥ x := dotProduct_star_self_pos_iff.mpr hx
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hpos
  have hsre : star x ⬝ᵥ x = (((star x ⬝ᵥ x).re : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im]; exact him.symm
  refine ⟨(Real.sqrt (star x ⬝ᵥ x).re)⁻¹,
    inv_pos.mpr (Real.sqrt_pos.mpr hre), ?_⟩
  have hkey : (Real.sqrt (star x ⬝ᵥ x).re)⁻¹
      * ((Real.sqrt (star x ⬝ᵥ x).re)⁻¹ * (star x ⬝ᵥ x).re) = 1 := by
    rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hre.le]
    exact inv_mul_cancel₀ (ne_of_gt hre)
  rw [star_smul, Complex.star_def, Complex.conj_ofReal, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, hsre]
  exact_mod_cast hkey

omit [DecidableEq d] in
/-- **The orthonormal-complement interface** (the one genuinely new brick of
the Lemma 2 mechanization): below full dimension, there is a unit vector
orthogonal to every member of a given family — with NO hypothesis on the
family (rank–nullity gives the generality for free). This is DK's "we can
extend the set of |h_j⟩ to an orthonormal basis by adding states |e_k⟩",
pared to the single complement vector the construction consumes. -/
theorem exists_unit_dotProduct_orthogonal {ι : Type*} [Fintype ι]
    (v : ι → d → ℂ) (hcard : Fintype.card ι < Fintype.card d) :
    ∃ e : d → ℂ, star e ⬝ᵥ e = 1 ∧ ∀ j, star (v j) ⬝ᵥ e = 0 := by
  set M : Matrix ι d ℂ := Matrix.of fun j i => star (v j i) with hM
  have hker : LinearMap.ker M.mulVecLin ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective M.mulVecLin := LinearMap.ker_eq_bot.mp hbot
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
      at hle
    omega
  obtain ⟨e₀, he₀mem, he₀ne⟩ := (Submodule.ne_bot_iff _).mp hker
  have he₀ : ∀ j, star (v j) ⬝ᵥ e₀ = 0 := by
    intro j
    have h0 := congrFun (LinearMap.mem_ker.mp he₀mem) j
    simpa [hM, Matrix.mulVecLin, Matrix.mulVec, dotProduct] using h0
  obtain ⟨c, _, hcu⟩ := exists_smul_unit he₀ne
  refine ⟨(c : ℂ) • e₀, hcu, fun j => ?_⟩
  rw [dotProduct_smul, he₀ j, smul_zero]

open scoped Classical in
/-- A consistent set that is not maximally extended (in the append sense)
has strictly fewer nonzero-probability histories than `dim` — DK's
"Since S is not maximally extended, r < n", assembled from the landed cap
and the landed saturation direction. -/
theorem card_nonzero_lt_of_not_maximallyExtended
    {L : List (ProjectiveDecomposition d)} {ψ : d → ℂ}
    (hcons : DKConsistent L ψ) (hnmax : ¬ MaximallyExtended L ψ) :
    Fintype.card {h : History L // branch L ψ h ≠ 0} < Fintype.card d := by
  rcases lt_or_eq_of_le (dkConsistent_card_nonzero_le L ψ hcons) with h | h
  · exact h
  · exact absurd (maximallyExtended_of_card_eq L ψ hcons h) hnmax

/-! ## The DK rotation at a general orthonormal pair

DK's `φ₊ = z₁|h_j⟩ + z₂*|e_k⟩`, `φ₋ = z₂|h_j⟩ − z₁*|e_k⟩` at a general
orthonormal pair `(u, e)` and general complex parameters — the conjugates
are load-bearing (`genPhiPlus_orth_genPhiMinus` fails without them for
non-real parameters; the real slice would not notice). -/

/-- DK's `|φ₊⟩ = z₁|h_j⟩ + z₂*|e_k⟩` at a general pair. -/
noncomputable def genPhiPlus (u e : d → ℂ) (z₁ z₂ : ℂ) : d → ℂ :=
  z₁ • u + (star z₂) • e

/-- DK's `|φ₋⟩ = z₂|h_j⟩ − z₁*|e_k⟩` at a general pair. -/
noncomputable def genPhiMinus (u e : d → ℂ) (z₁ z₂ : ℂ) : d → ℂ :=
  z₂ • u - (star z₁) • e

section Rotation

variable {u e : d → ℂ} {z₁ z₂ : ℂ}

omit [DecidableEq d] in
theorem genPhiPlus_unit (hu : star u ⬝ᵥ u = 1) (he : star e ⬝ᵥ e = 1)
    (hue : star u ⬝ᵥ e = 0) (hz : star z₁ * z₁ + star z₂ * z₂ = 1) :
    star (genPhiPlus u e z₁ z₂) ⬝ᵥ genPhiPlus u e z₁ z₂ = 1 := by
  have heu : star e ⬝ᵥ u = 0 := star_dot_flip hue
  simp only [genPhiPlus, star_add, star_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, star_star, hu, he, hue,
    heu, mul_one, mul_zero, add_zero, zero_add]
  linear_combination hz

omit [DecidableEq d] in
theorem genPhiMinus_unit (hu : star u ⬝ᵥ u = 1) (he : star e ⬝ᵥ e = 1)
    (hue : star u ⬝ᵥ e = 0) (hz : star z₁ * z₁ + star z₂ * z₂ = 1) :
    star (genPhiMinus u e z₁ z₂) ⬝ᵥ genPhiMinus u e z₁ z₂ = 1 := by
  have heu : star e ⬝ᵥ u = 0 := star_dot_flip hue
  simp only [genPhiMinus, star_sub, star_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, star_star, hu, he, hue,
    heu, mul_one, mul_zero, sub_zero, zero_sub]
  linear_combination hz

omit [DecidableEq d] in
/-- The load-bearing orthogonality — where the conjugate placement in DK's
display earns its keep: needs the pair orthonormal, but NO normalization of
`(z₁, z₂)`. -/
theorem genPhiPlus_orth_genPhiMinus (hu : star u ⬝ᵥ u = 1)
    (he : star e ⬝ᵥ e = 1) (hue : star u ⬝ᵥ e = 0) :
    star (genPhiPlus u e z₁ z₂) ⬝ᵥ genPhiMinus u e z₁ z₂ = 0 := by
  have heu : star e ⬝ᵥ u = 0 := star_dot_flip hue
  simp only [genPhiPlus, genPhiMinus, star_add, star_smul, add_dotProduct,
    dotProduct_sub, dotProduct_smul, smul_dotProduct, smul_eq_mul, star_star,
    hu, he, hue, heu, mul_one, mul_zero]
  ring

/-- The DK rotation `τ = {P₊, P₋, P₃}` at a general orthonormal pair, for
any normalized complex parameter pair — assembled through the landed
`rotationDecomposition`, which discharges all of DK's `\conds` obligations
from the three scalar identities above. -/
@[reducible] noncomputable def genRotation (hu : star u ⬝ᵥ u = 1)
    (he : star e ⬝ᵥ e = 1) (hue : star u ⬝ᵥ e = 0) (z₁ z₂ : ℂ)
    (hz : star z₁ * z₁ + star z₂ * z₂ = 1) : ProjectiveDecomposition d :=
  rotationDecomposition (genPhiPlus u e z₁ z₂) (genPhiMinus u e z₁ z₂)
    (genPhiPlus_unit hu he hue hz) (genPhiMinus_unit hu he hue hz)
    (genPhiPlus_orth_genPhiMinus hu he hue)

omit [DecidableEq d] in
theorem genPhiPlus_ne_zero (hu : star u ⬝ᵥ u = 1) (he : star e ⬝ᵥ e = 1)
    (hue : star u ⬝ᵥ e = 0) (hz : star z₁ * z₁ + star z₂ * z₂ = 1) :
    genPhiPlus u e z₁ z₂ ≠ 0 := by
  intro h
  have h1 := genPhiPlus_unit hu he hue hz
  rw [h, star_zero, zero_dotProduct] at h1
  exact one_ne_zero h1.symm

omit [DecidableEq d] in
theorem genPhiMinus_ne_zero (hu : star u ⬝ᵥ u = 1) (he : star e ⬝ᵥ e = 1)
    (hue : star u ⬝ᵥ e = 0) (hz : star z₁ * z₁ + star z₂ * z₂ = 1) :
    genPhiMinus u e z₁ z₂ ≠ 0 := by
  intro h
  have h1 := genPhiMinus_unit hu he hue hz
  rw [h, star_zero, zero_dotProduct] at h1
  exact one_ne_zero h1.symm

omit [DecidableEq d] in
/-- `⟨φ₊, u⟩ = z₁*` — the target-direction component of the plus state. -/
theorem genPhiPlus_dot_u (hu : star u ⬝ᵥ u = 1) (heu : star e ⬝ᵥ u = 0) :
    star (genPhiPlus u e z₁ z₂) ⬝ᵥ u = star z₁ := by
  simp only [genPhiPlus, star_add, star_smul, add_dotProduct,
    smul_dotProduct, smul_eq_mul, star_star, hu, heu, mul_one, mul_zero,
    add_zero]

omit [DecidableEq d] in
/-- `⟨φ₋, u⟩ = z₂*` — the target-direction component of the minus state. -/
theorem genPhiMinus_dot_u (hu : star u ⬝ᵥ u = 1) (heu : star e ⬝ᵥ u = 0) :
    star (genPhiMinus u e z₁ z₂) ⬝ᵥ u = star z₂ := by
  simp only [genPhiMinus, star_sub, star_smul, sub_dotProduct,
    smul_dotProduct, smul_eq_mul, star_star, hu, heu, mul_one, mul_zero,
    sub_zero]

end Rotation

/-! ## Appending the rotation to a consistent set

Standing data for this section: a DK-consistent set `(L, ψ)`; a target
history `h₀` whose branch vector is `c • u` with `c ≠ 0` and `u` a unit
vector (so the branch is nonzero); and a unit vector `e` orthogonal to
EVERY branch vector of the set (the complement direction — supplied by
`exists_unit_dotProduct_orthogonal` in the headline proof). -/

section Extension

variable {L : List (ProjectiveDecomposition d)} {ψ : d → ℂ} {h₀ : History L}
  {u e : d → ℂ} {c : ℂ} {z₁ z₂ : ℂ}

/-- Consistency makes every OTHER branch orthogonal to the target
direction. -/
theorem branch_dot_u_of_ne (hcons : DKConsistent L ψ) (hc : c ≠ 0)
    (hbu : branch L ψ h₀ = c • u) {g : History L} (hg : g ≠ h₀) :
    star (branch L ψ g) ⬝ᵥ u = 0 := by
  have h0 : decoherenceFunctional (classOp L) ψ h₀ g = 0 :=
    hcons h₀ g (Ne.symm hg)
  rw [decoherenceFunctional_classOp_eq, hbu, dotProduct_smul, smul_eq_mul]
    at h0
  exact (mul_eq_zero.mp h0).resolve_left hc

/-- The complement direction is orthogonal to the target direction (derived,
not assumed: `e ⊥ branch h₀ = c • u` with `c ≠ 0`). -/
theorem u_dot_e (hc : c ≠ 0) (hbu : branch L ψ h₀ = c • u)
    (heb : ∀ g : History L, star (branch L ψ g) ⬝ᵥ e = 0) :
    star u ⬝ᵥ e = 0 := by
  have h0 := heb h₀
  rw [hbu, star_smul, smul_dotProduct, smul_eq_mul] at h0
  exact (mul_eq_zero.mp h0).resolve_left (star_ne_zero.mpr hc)

/-- Every non-target branch is orthogonal to the plus state. -/
theorem branch_dot_genPhiPlus (hcons : DKConsistent L ψ) (hc : c ≠ 0)
    (hbu : branch L ψ h₀ = c • u)
    (heb : ∀ g : History L, star (branch L ψ g) ⬝ᵥ e = 0)
    {g : History L} (hg : g ≠ h₀) :
    star (branch L ψ g) ⬝ᵥ genPhiPlus u e z₁ z₂ = 0 := by
  rw [genPhiPlus, dotProduct_add, dotProduct_smul, dotProduct_smul,
    branch_dot_u_of_ne hcons hc hbu hg, heb g, smul_zero, smul_zero,
    add_zero]

/-- Every non-target branch is orthogonal to the minus state. -/
theorem branch_dot_genPhiMinus (hcons : DKConsistent L ψ) (hc : c ≠ 0)
    (hbu : branch L ψ h₀ = c • u)
    (heb : ∀ g : History L, star (branch L ψ g) ⬝ᵥ e = 0)
    {g : History L} (hg : g ≠ h₀) :
    star (branch L ψ g) ⬝ᵥ genPhiMinus u e z₁ z₂ = 0 := by
  rw [genPhiMinus, dotProduct_sub, dotProduct_smul, dotProduct_smul,
    branch_dot_u_of_ne hcons hc hbu hg, heb g, smul_zero, smul_zero,
    sub_zero]

theorem genPhiPlus_dot_branch (hcons : DKConsistent L ψ) (hc : c ≠ 0)
    (hbu : branch L ψ h₀ = c • u)
    (heb : ∀ g : History L, star (branch L ψ g) ⬝ᵥ e = 0)
    {g : History L} (hg : g ≠ h₀) :
    star (genPhiPlus u e z₁ z₂) ⬝ᵥ branch L ψ g = 0 :=
  star_dot_flip (branch_dot_genPhiPlus hcons hc hbu heb hg)

theorem genPhiMinus_dot_branch (hcons : DKConsistent L ψ) (hc : c ≠ 0)
    (hbu : branch L ψ h₀ = c • u)
    (heb : ∀ g : History L, star (branch L ψ g) ⬝ᵥ e = 0)
    {g : History L} (hg : g ≠ h₀) :
    star (genPhiMinus u e z₁ z₂) ⬝ᵥ branch L ψ g = 0 :=
  star_dot_flip (branch_dot_genPhiMinus hcons hc hbu heb hg)

/-- `P₊` annihilates every non-target branch. -/
theorem outer_genPhiPlus_mulVec_of_ne (hcons : DKConsistent L ψ) (hc : c ≠ 0)
    (hbu : branch L ψ h₀ = c • u)
    (heb : ∀ g : History L, star (branch L ψ g) ⬝ᵥ e = 0)
    {g : History L} (hg : g ≠ h₀) :
    outer (genPhiPlus u e z₁ z₂) *ᵥ branch L ψ g = 0 := by
  rw [outer_mulVec, genPhiPlus_dot_branch hcons hc hbu heb hg, zero_smul]

/-- `P₋` annihilates every non-target branch. -/
theorem outer_genPhiMinus_mulVec_of_ne (hcons : DKConsistent L ψ)
    (hc : c ≠ 0) (hbu : branch L ψ h₀ = c • u)
    (heb : ∀ g : History L, star (branch L ψ g) ⬝ᵥ e = 0)
    {g : History L} (hg : g ≠ h₀) :
    outer (genPhiMinus u e z₁ z₂) *ᵥ branch L ψ g = 0 := by
  rw [outer_mulVec, genPhiMinus_dot_branch hcons hc hbu heb hg, zero_smul]

/-- `P₃` fixes every non-target branch. -/
theorem genP3_mulVec_of_ne (hcons : DKConsistent L ψ) (hc : c ≠ 0)
    (hbu : branch L ψ h₀ = c • u)
    (heb : ∀ g : History L, star (branch L ψ g) ⬝ᵥ e = 0)
    {g : History L} (hg : g ≠ h₀) :
    (1 - outer (genPhiPlus u e z₁ z₂) - outer (genPhiMinus u e z₁ z₂)) *ᵥ
      branch L ψ g = branch L ψ g := by
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    outer_genPhiPlus_mulVec_of_ne hcons hc hbu heb hg,
    outer_genPhiMinus_mulVec_of_ne hcons hc hbu heb hg, sub_zero, sub_zero]

/-- `P₊` sends the target branch to `(c z₁*) • φ₊`. -/
theorem outer_genPhiPlus_mulVec_target (hu : star u ⬝ᵥ u = 1)
    (heu : star e ⬝ᵥ u = 0) (hbu : branch L ψ h₀ = c • u) :
    outer (genPhiPlus u e z₁ z₂) *ᵥ branch L ψ h₀
      = (c * star z₁) • genPhiPlus u e z₁ z₂ := by
  rw [hbu, Matrix.mulVec_smul, outer_mulVec, genPhiPlus_dot_u hu heu,
    smul_smul]

/-- `P₋` sends the target branch to `(c z₂*) • φ₋`. -/
theorem outer_genPhiMinus_mulVec_target (hu : star u ⬝ᵥ u = 1)
    (heu : star e ⬝ᵥ u = 0) (hbu : branch L ψ h₀ = c • u) :
    outer (genPhiMinus u e z₁ z₂) *ᵥ branch L ψ h₀
      = (c * star z₂) • genPhiMinus u e z₁ z₂ := by
  rw [hbu, Matrix.mulVec_smul, outer_mulVec, genPhiMinus_dot_u hu heu,
    smul_smul]

/-- **`P₃` annihilates the target branch**: the rotated pair carries all of
it — `z₁* • φ₊ + z₂* • φ₋ = u` by the normalization `z₁*z₁ + z₂*z₂ = 1`. -/
theorem genP3_mulVec_target (hu : star u ⬝ᵥ u = 1) (heu : star e ⬝ᵥ u = 0)
    (hbu : branch L ψ h₀ = c • u) (hz : star z₁ * z₁ + star z₂ * z₂ = 1) :
    (1 - outer (genPhiPlus u e z₁ z₂) - outer (genPhiMinus u e z₁ z₂)) *ᵥ
      branch L ψ h₀ = 0 := by
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    outer_genPhiPlus_mulVec_target hu heu hbu,
    outer_genPhiMinus_mulVec_target hu heu hbu, hbu, genPhiPlus, genPhiMinus]
  match_scalars
  · linear_combination (-c) * hz
  · ring

/-- **Appending the DK rotation preserves consistency, for EVERY complex
parameter choice** (DK: "there is a consistent extension for every choice
of z₁ and z₂") — at a GENERAL base set and general dimension. Same-base
pairs decohere by the landed `extend_decoherence_same_base`; cross-history
pairs vanish because `P±` annihilate every non-target branch, `P₃`
annihilates the target branch and fixes the others, and the surviving
diagonal case is the base set's own consistency. -/
theorem genRotation_consistent (hcons : DKConsistent L ψ) (hc : c ≠ 0)
    (hbu : branch L ψ h₀ = c • u)
    (heb : ∀ g : History L, star (branch L ψ g) ⬝ᵥ e = 0)
    (hu : star u ⬝ᵥ u = 1) (he : star e ⬝ᵥ e = 1) (hue : star u ⬝ᵥ e = 0)
    (z₁ z₂ : ℂ) (hz : star z₁ * z₁ + star z₂ * z₂ = 1) :
    DKConsistent (genRotation hu he hue z₁ z₂ hz :: L) ψ := by
  have heu : star e ⬝ᵥ u = 0 := star_dot_flip hue
  intro α β hne
  obtain ⟨i, g⟩ := α
  obtain ⟨i', g'⟩ := β
  by_cases hgg : g = g'
  · subst hgg
    exact extend_decoherence_same_base _ L ψ g fun h => hne (by rw [h])
  · by_cases hbg : branch L ψ g = 0
    · exact decoherenceFunctional_zero_of_branch_left _ _ _
        (by rw [branch_cons, hbg, Matrix.mulVec_zero])
    by_cases hbg' : branch L ψ g' = 0
    · exact decoherenceFunctional_zero_of_branch_right _ _ _
        (by rw [branch_cons, hbg', Matrix.mulVec_zero])
    have hsplit : ∀ k : Fin (genRotation hu he hue z₁ z₂ hz).n,
        k = 0 ∨ k = 1 ∨ k = 2 := by
      intro k
      have hk : k.val < 3 := k.isLt
      have hv0 : ((0 : Fin (genRotation hu he hue z₁ z₂ hz).n)).val = 0 := rfl
      have hv1 : ((1 : Fin (genRotation hu he hue z₁ z₂ hz).n)).val = 1 := rfl
      have hv2 : ((2 : Fin (genRotation hu he hue z₁ z₂ hz).n)).val = 2 := rfl
      rcases eq_or_ne k.val 0 with h | h
      · exact Or.inl (Fin.ext (by omega))
      rcases eq_or_ne k.val 1 with h1 | h1
      · exact Or.inr (Or.inl (Fin.ext (by omega)))
      · exact Or.inr (Or.inr (Fin.ext (by omega)))
    -- the outer cells kill every non-target branch
    have houter : ∀ (g₁ : History L), g₁ ≠ h₀ →
        ∀ k : Fin (genRotation hu he hue z₁ z₂ hz).n, k = 0 ∨ k = 1 →
        branch (genRotation hu he hue z₁ z₂ hz :: L) ψ (k, g₁) = 0 := by
      intro g₁ hg₁ k hk01
      rcases hk01 with rfl | rfl
      · rw [branch_cons]
        show outer (genPhiPlus u e z₁ z₂) *ᵥ branch L ψ g₁ = 0
        exact outer_genPhiPlus_mulVec_of_ne hcons hc hbu heb hg₁
      · rw [branch_cons]
        show outer (genPhiMinus u e z₁ z₂) *ᵥ branch L ψ g₁ = 0
        exact outer_genPhiMinus_mulVec_of_ne hcons hc hbu heb hg₁
    -- the third cell kills the target branch
    have hP3target :
        branch (genRotation hu he hue z₁ z₂ hz :: L) ψ (2, h₀) = 0 := by
      rw [branch_cons]
      show (1 - outer (genPhiPlus u e z₁ z₂) - outer (genPhiMinus u e z₁ z₂))
          *ᵥ branch L ψ h₀ = 0
      exact genP3_mulVec_target hu heu hbu hz
    rcases eq_or_ne g h₀ with hgh | hgh
    · -- α rides the target history; β does not
      have hg'h : g' ≠ h₀ := fun h => hgg (hgh.trans h.symm)
      rw [hgh]
      rcases hsplit i with hi | hi | hi
      · rw [hi]
        rcases hsplit i' with hi' | hi' | hi'
        · rw [hi']
          exact decoherenceFunctional_zero_of_branch_right _ _ _
            (houter g' hg'h 0 (Or.inl rfl))
        · rw [hi']
          exact decoherenceFunctional_zero_of_branch_right _ _ _
            (houter g' hg'h 1 (Or.inr rfl))
        · rw [hi', decoherenceFunctional_classOp_eq, branch_cons, branch_cons]
          show star ((1 - outer (genPhiPlus u e z₁ z₂)
              - outer (genPhiMinus u e z₁ z₂)) *ᵥ branch L ψ g')
              ⬝ᵥ (outer (genPhiPlus u e z₁ z₂) *ᵥ branch L ψ h₀) = 0
          rw [genP3_mulVec_of_ne hcons hc hbu heb hg'h,
            outer_genPhiPlus_mulVec_target hu heu hbu, dotProduct_smul,
            branch_dot_genPhiPlus hcons hc hbu heb hg'h, smul_zero]
      · rw [hi]
        rcases hsplit i' with hi' | hi' | hi'
        · rw [hi']
          exact decoherenceFunctional_zero_of_branch_right _ _ _
            (houter g' hg'h 0 (Or.inl rfl))
        · rw [hi']
          exact decoherenceFunctional_zero_of_branch_right _ _ _
            (houter g' hg'h 1 (Or.inr rfl))
        · rw [hi', decoherenceFunctional_classOp_eq, branch_cons, branch_cons]
          show star ((1 - outer (genPhiPlus u e z₁ z₂)
              - outer (genPhiMinus u e z₁ z₂)) *ᵥ branch L ψ g')
              ⬝ᵥ (outer (genPhiMinus u e z₁ z₂) *ᵥ branch L ψ h₀) = 0
          rw [genP3_mulVec_of_ne hcons hc hbu heb hg'h,
            outer_genPhiMinus_mulVec_target hu heu hbu, dotProduct_smul,
            branch_dot_genPhiMinus hcons hc hbu heb hg'h, smul_zero]
      · rw [hi]
        exact decoherenceFunctional_zero_of_branch_left _ _ _ hP3target
    · rcases eq_or_ne g' h₀ with hg'h | hg'h
      · -- β rides the target history; α does not
        rw [hg'h]
        rcases hsplit i' with hi' | hi' | hi'
        · rw [hi']
          rcases hsplit i with hi | hi | hi
          · rw [hi]
            exact decoherenceFunctional_zero_of_branch_left _ _ _
              (houter g hgh 0 (Or.inl rfl))
          · rw [hi]
            exact decoherenceFunctional_zero_of_branch_left _ _ _
              (houter g hgh 1 (Or.inr rfl))
          · rw [hi, decoherenceFunctional_classOp_eq, branch_cons,
              branch_cons]
            show star (outer (genPhiPlus u e z₁ z₂) *ᵥ branch L ψ h₀)
                ⬝ᵥ ((1 - outer (genPhiPlus u e z₁ z₂)
                  - outer (genPhiMinus u e z₁ z₂)) *ᵥ branch L ψ g) = 0
            rw [genP3_mulVec_of_ne hcons hc hbu heb hgh,
              outer_genPhiPlus_mulVec_target hu heu hbu, star_smul,
              smul_dotProduct, genPhiPlus_dot_branch hcons hc hbu heb hgh,
              smul_zero]
        · rw [hi']
          rcases hsplit i with hi | hi | hi
          · rw [hi]
            exact decoherenceFunctional_zero_of_branch_left _ _ _
              (houter g hgh 0 (Or.inl rfl))
          · rw [hi]
            exact decoherenceFunctional_zero_of_branch_left _ _ _
              (houter g hgh 1 (Or.inr rfl))
          · rw [hi, decoherenceFunctional_classOp_eq, branch_cons,
              branch_cons]
            show star (outer (genPhiMinus u e z₁ z₂) *ᵥ branch L ψ h₀)
                ⬝ᵥ ((1 - outer (genPhiPlus u e z₁ z₂)
                  - outer (genPhiMinus u e z₁ z₂)) *ᵥ branch L ψ g) = 0
            rw [genP3_mulVec_of_ne hcons hc hbu heb hgh,
              outer_genPhiMinus_mulVec_target hu heu hbu, star_smul,
              smul_dotProduct, genPhiMinus_dot_branch hcons hc hbu heb hgh,
              smul_zero]
        · rw [hi']
          exact decoherenceFunctional_zero_of_branch_right _ _ _ hP3target
      · -- neither history is the target
        rcases hsplit i with hi | hi | hi
        · rw [hi]
          exact decoherenceFunctional_zero_of_branch_left _ _ _
            (houter g hgh 0 (Or.inl rfl))
        · rw [hi]
          exact decoherenceFunctional_zero_of_branch_left _ _ _
            (houter g hgh 1 (Or.inr rfl))
        · rcases hsplit i' with hi' | hi' | hi'
          · rw [hi']
            exact decoherenceFunctional_zero_of_branch_right _ _ _
              (houter g' hg'h 0 (Or.inl rfl))
          · rw [hi']
            exact decoherenceFunctional_zero_of_branch_right _ _ _
              (houter g' hg'h 1 (Or.inr rfl))
          · rw [hi, hi', decoherenceFunctional_classOp_eq, branch_cons,
              branch_cons]
            show star ((1 - outer (genPhiPlus u e z₁ z₂)
                - outer (genPhiMinus u e z₁ z₂)) *ᵥ branch L ψ g')
                ⬝ᵥ ((1 - outer (genPhiPlus u e z₁ z₂)
                  - outer (genPhiMinus u e z₁ z₂)) *ᵥ branch L ψ g) = 0
            rw [genP3_mulVec_of_ne hcons hc hbu heb hg'h,
              genP3_mulVec_of_ne hcons hc hbu heb hgh]
            exact hcons g g' hgg

/-- **The target history splits**: for both parameters nonzero, both rotated
continuations of `h₀` carry nonzero probability — DK's "The histories in S'
with non-zero probabilities correspond to the states P±|h_j⟩ and the |h_i⟩
for i ≠ j", at the P± half. -/
theorem genRotation_nontrivial_at (hc : c ≠ 0) (hbu : branch L ψ h₀ = c • u)
    (hu : star u ⬝ᵥ u = 1) (he : star e ⬝ᵥ e = 1) (hue : star u ⬝ᵥ e = 0)
    {hz : star z₁ * z₁ + star z₂ * z₂ = 1} (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) :
    branch (genRotation hu he hue z₁ z₂ hz :: L) ψ (0, h₀) ≠ 0 ∧
    branch (genRotation hu he hue z₁ z₂ hz :: L) ψ (1, h₀) ≠ 0 := by
  have heu : star e ⬝ᵥ u = 0 := star_dot_flip hue
  constructor
  · rw [branch_cons]
    show outer (genPhiPlus u e z₁ z₂) *ᵥ branch L ψ h₀ ≠ 0
    rw [outer_genPhiPlus_mulVec_target hu heu hbu]
    exact smul_ne_zero (mul_ne_zero hc (star_ne_zero.mpr hz₁))
      (genPhiPlus_ne_zero hu he hue hz)
  · rw [branch_cons]
    show outer (genPhiMinus u e z₁ z₂) *ᵥ branch L ψ h₀ ≠ 0
    rw [outer_genPhiMinus_mulVec_target hu heu hbu]
    exact smul_ne_zero (mul_ne_zero hc (star_ne_zero.mpr hz₂))
      (genPhiMinus_ne_zero hu he hue hz)

/-- The DK rotation is a non-trivial consistent extension whenever both
parameters are nonzero (DK's implicit genericity, explicit). -/
theorem genRotation_nontrivialExtension (hcons : DKConsistent L ψ)
    (hc : c ≠ 0) (hbu : branch L ψ h₀ = c • u)
    (heb : ∀ g : History L, star (branch L ψ g) ⬝ᵥ e = 0)
    (hu : star u ⬝ᵥ u = 1) (he : star e ⬝ᵥ e = 1) (hue : star u ⬝ᵥ e = 0)
    {hz : star z₁ * z₁ + star z₂ * z₂ = 1} (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) :
    NontrivialExtension (genRotation hu he hue z₁ z₂ hz) L ψ := by
  obtain ⟨hbp, hbm⟩ := genRotation_nontrivial_at hc hbu hu he hue hz₁ hz₂
  refine ⟨genRotation_consistent hcons hc hbu heb hu he hue z₁ z₂ hz,
    fun htriv => ?_⟩
  have h01 := htriv h₀ 0 1 hbp hbm
  have hv := congrArg Fin.val h01
  have hv0 : ((0 : Fin (genRotation hu he hue z₁ z₂ hz).n)).val = 0 := rfl
  have hv1 : ((1 : Fin (genRotation hu he hue z₁ z₂ hz).n)).val = 1 := rfl
  omega

end Extension

/-! ## The continuous family -/

section Family

variable {u e : d → ℂ}

/-- The real-interval slice of the general DK rotation:
`(z₁, z₂) = (cos t, sin t)`. -/
@[reducible] noncomputable def dkGeneralFamily (hu : star u ⬝ᵥ u = 1)
    (he : star e ⬝ᵥ e = 1) (hue : star u ⬝ᵥ e = 0) (t : ℝ) :
    ProjectiveDecomposition d :=
  genRotation hu he hue (Real.cos t) (Real.sin t)
    (by
      have hc : (star (↑(Real.cos t) : ℂ)) = (↑(Real.cos t) : ℂ) :=
        Complex.conj_ofReal _
      have hs : (star (↑(Real.sin t) : ℂ)) = (↑(Real.sin t) : ℂ) :=
        Complex.conj_ofReal _
      rw [hc, hs, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        ← Complex.ofReal_add, ← Complex.ofReal_one, Complex.ofReal_inj]
      linear_combination Real.sin_sq_add_cos_sq t)

variable {L : List (ProjectiveDecomposition d)} {ψ : d → ℂ} {h₀ : History L}
  {c : ℂ}

/-- Every member of the family extends the set consistently — DK's "every
choice of z₁ and z₂", at the real slice. -/
theorem dkGeneralFamily_consistent (hcons : DKConsistent L ψ) (hc : c ≠ 0)
    (hbu : branch L ψ h₀ = c • u)
    (heb : ∀ g : History L, star (branch L ψ g) ⬝ᵥ e = 0)
    (hu : star u ⬝ᵥ u = 1) (he : star e ⬝ᵥ e = 1) (hue : star u ⬝ᵥ e = 0)
    (t : ℝ) : DKConsistent (dkGeneralFamily hu he hue t :: L) ψ :=
  genRotation_consistent hcons hc hbu heb hu he hue _ _ _

/-- Every member with parameter in `(0, π/2)` splits the target history:
a non-trivial consistent extension, with both rotated continuations of `h₀`
nonzero. -/
theorem dkGeneralFamily_nontrivial (hcons : DKConsistent L ψ) (hc : c ≠ 0)
    (hbu : branch L ψ h₀ = c • u)
    (heb : ∀ g : History L, star (branch L ψ g) ⬝ᵥ e = 0)
    (hu : star u ⬝ᵥ u = 1) (he : star e ⬝ᵥ e = 1) (hue : star u ⬝ᵥ e = 0)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 (Real.pi / 2)) :
    NontrivialExtension (dkGeneralFamily hu he hue t) L ψ ∧
    branch (dkGeneralFamily hu he hue t :: L) ψ (0, h₀) ≠ 0 ∧
    branch (dkGeneralFamily hu he hue t :: L) ψ (1, h₀) ≠ 0 := by
  have hcos : ((Real.cos t : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩).ne'
  have hsin : ((Real.sin t : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (Real.sin_pos_of_pos_of_lt_pi ht.1
        (by linarith [Real.pi_pos, ht.2])).ne'
  obtain ⟨hbp, hbm⟩ := genRotation_nontrivial_at hc hbu hu he hue hcos hsin
  exact ⟨genRotation_nontrivialExtension hcons hc hbu heb hu he hue hcos
    hsin, hbp, hbm⟩

/-- The probe entry `⟨u, P₊(t) u⟩ = cos² t` — total on the structure, so
equality of decompositions transports it. -/
private noncomputable def genProbe (u : d → ℂ)
    (τ : ProjectiveDecomposition d) : ℂ :=
  if h : 0 < τ.n then star u ⬝ᵥ (τ.P ⟨0, h⟩ *ᵥ u) else 0

private theorem genProbe_dkGeneralFamily (hu : star u ⬝ᵥ u = 1)
    (he : star e ⬝ᵥ e = 1) (hue : star u ⬝ᵥ e = 0) (t : ℝ) :
    genProbe u (dkGeneralFamily hu he hue t)
      = (Real.cos t : ℂ) * (Real.cos t : ℂ) := by
  have heu : star e ⬝ᵥ u = 0 := star_dot_flip hue
  unfold genProbe
  rw [dif_pos (show 0 < (dkGeneralFamily hu he hue t).n from Nat.succ_pos 2)]
  show star u ⬝ᵥ (outer (genPhiPlus u e (Real.cos t) (Real.sin t)) *ᵥ u) = _
  have hdot : star u ⬝ᵥ genPhiPlus u e ((Real.cos t : ℝ) : ℂ)
      ((Real.sin t : ℝ) : ℂ) = ((Real.cos t : ℝ) : ℂ) := by
    simp only [genPhiPlus, dotProduct_add, dotProduct_smul, hu, hue,
      smul_eq_mul, mul_one, mul_zero, add_zero]
  rw [outer_mulVec, dotProduct_smul, genPhiPlus_dot_u hu heu, smul_eq_mul,
    hdot, Complex.star_def, Complex.conj_ofReal]

/-- **The family is injective on the open interval**: distinct parameters
give distinct decompositions, read off the probe entry via strict
antitonicity of `cos²` there. -/
theorem dkGeneralFamily_injOn (hu : star u ⬝ᵥ u = 1) (he : star e ⬝ᵥ e = 1)
    (hue : star u ⬝ᵥ e = 0) :
    Set.InjOn (dkGeneralFamily hu he hue) (Set.Ioo 0 (Real.pi / 2)) := by
  intro t ht t' ht' heq
  have hprobe := congrArg (genProbe u) heq
  rw [genProbe_dkGeneralFamily hu he hue, genProbe_dkGeneralFamily hu he hue,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj]
    at hprobe
  have hct : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  have hct' : 0 < Real.cos t' :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht'.1, Real.pi_pos], ht'.2⟩
  have hcc : Real.cos t = Real.cos t' := by
    rcases mul_self_eq_mul_self_iff.mp hprobe with h | h
    · exact h
    · nlinarith
  exact Real.strictAntiOn_cos.injOn
    ⟨le_of_lt ht.1, by linarith [Real.pi_pos, ht.2]⟩
    ⟨le_of_lt ht'.1, by linarith [Real.pi_pos, ht'.2]⟩ hcc

/-- The family's projectors, unbundled onto plain matrix-valued functions of
the parameter (definitionally the bundle's `P` field —
`dkGeneralFamily_P_eq`), so continuity statements need no dependent
indices. -/
noncomputable def genFamilyProjectors (u e : d → ℂ) (t : ℝ) :
    Fin 3 → Matrix d d ℂ :=
  ![outer (genPhiPlus u e (Real.cos t) (Real.sin t)),
    outer (genPhiMinus u e (Real.cos t) (Real.sin t)),
    1 - outer (genPhiPlus u e (Real.cos t) (Real.sin t))
      - outer (genPhiMinus u e (Real.cos t) (Real.sin t))]

theorem dkGeneralFamily_P_eq (hu : star u ⬝ᵥ u = 1) (he : star e ⬝ᵥ e = 1)
    (hue : star u ⬝ᵥ e = 0) (t : ℝ) :
    (dkGeneralFamily hu he hue t).P = genFamilyProjectors u e t := rfl

omit [Fintype d] [DecidableEq d] in
private theorem continuous_genPhiPlus_entry (u e : d → ℂ) (a : d) :
    Continuous fun t => genPhiPlus u e (Real.cos t) (Real.sin t) a := by
  simp only [genPhiPlus, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal]
  exact ((Complex.continuous_ofReal.comp Real.continuous_cos).mul
    continuous_const).add
    ((Complex.continuous_ofReal.comp Real.continuous_sin).mul
      continuous_const)

omit [Fintype d] [DecidableEq d] in
private theorem continuous_genPhiMinus_entry (u e : d → ℂ) (a : d) :
    Continuous fun t => genPhiMinus u e (Real.cos t) (Real.sin t) a := by
  simp only [genPhiMinus, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal]
  exact ((Complex.continuous_ofReal.comp Real.continuous_sin).mul
    continuous_const).sub
    ((Complex.continuous_ofReal.comp Real.continuous_cos).mul
      continuous_const)

omit [Fintype d] in
/-- **The family is continuous in its parameter**, entrywise: every entry of
every projector of `dkGeneralFamily t` is a continuous function of `t`. -/
theorem dkGeneralFamily_continuous (u e : d → ℂ) (i : Fin 3) (a b : d) :
    Continuous fun t => genFamilyProjectors u e t i a b := by
  have hp : ∀ a b : d, Continuous fun t =>
      outer (genPhiPlus u e (Real.cos t) (Real.sin t)) a b := by
    intro a b
    simp only [outer, Matrix.vecMulVec_apply, Pi.star_apply]
    exact (continuous_genPhiPlus_entry u e a).mul
      (continuous_genPhiPlus_entry u e b).star
  have hm : ∀ a b : d, Continuous fun t =>
      outer (genPhiMinus u e (Real.cos t) (Real.sin t)) a b := by
    intro a b
    simp only [outer, Matrix.vecMulVec_apply, Pi.star_apply]
    exact (continuous_genPhiMinus_entry u e a).mul
      (continuous_genPhiMinus_entry u e b).star
  fin_cases i
  · exact hp a b
  · exact hm a b
  · exact (continuous_const.sub (hp a b)).sub (hm a b)

end Family

/-! ## The headline -/

open scoped Classical in
/-- **Dowker–Kent's Lemma 2** (PRL 75 (1995) 3038; proof in JSP 82 (1996)
1575), fully quantified at the finite-dimensional matrix grade, at the
append position: for every consistent set with strictly fewer
nonzero-probability histories than `dim` (DK's "r < n" — the intrinsic form
of "not maximally extended"; see `dowkerKent_lemma2_of_not_maximallyExtended`
for that form), for EACH history with nonzero probability there is a
continuous family of non-trivial consistent extensions splitting that very
history: consistent at every parameter, non-trivial on `(0, π/2)` with the
given history acquiring two distinct nonzero continuations, injective on
that interval, and with all projector entries continuous in the parameter
(`Φ` is the unbundled projector map, linked to each member by the `hn`
cast). Deltas versus DK as posed are flagged in the module docstring
(finite-dimensional only; append position; ψ unnormalized; "continuous
family" cashed as this five-clause package). -/
theorem dowkerKent_lemma2 {L : List (ProjectiveDecomposition d)}
    {ψ : d → ℂ} (hcons : DKConsistent L ψ)
    (hcard : Fintype.card {h : History L // branch L ψ h ≠ 0}
      < Fintype.card d)
    (h₀ : History L) (hb₀ : branch L ψ h₀ ≠ 0) :
    ∃ (F : ℝ → ProjectiveDecomposition d) (Φ : ℝ → Fin 3 → Matrix d d ℂ)
      (hn : ∀ t, (F t).n = 3),
      (∀ t, DKConsistent (F t :: L) ψ) ∧
      (∀ t ∈ Set.Ioo 0 (Real.pi / 2),
        NontrivialExtension (F t) L ψ ∧
        ∃ i i' : Fin (F t).n, i ≠ i' ∧
          branch (F t :: L) ψ (i, h₀) ≠ 0 ∧
          branch (F t :: L) ψ (i', h₀) ≠ 0) ∧
      Set.InjOn F (Set.Ioo 0 (Real.pi / 2)) ∧
      (∀ t, (F t).P = Φ t ∘ Fin.cast (hn t)) ∧
      (∀ i a b, Continuous fun t => Φ t i a b) := by
  -- the complement direction: unit, orthogonal to every branch
  obtain ⟨e, he, heK⟩ := exists_unit_dotProduct_orthogonal
    (fun g : {h : History L // branch L ψ h ≠ 0} => branch L ψ g.1) hcard
  have heb : ∀ g : History L, star (branch L ψ g) ⬝ᵥ e = 0 := by
    intro g
    by_cases hbg : branch L ψ g = 0
    · rw [hbg, star_zero, zero_dotProduct]
    · exact heK ⟨g, hbg⟩
  -- the normalized target direction
  obtain ⟨c₀, hc₀, hc₀u⟩ := exists_smul_unit hb₀
  have hc₀c : ((c₀ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc₀)
  set u : d → ℂ := ((c₀ : ℝ) : ℂ) • branch L ψ h₀ with hudef
  have hu : star u ⬝ᵥ u = 1 := hc₀u
  have hcinv : (((c₀ : ℝ) : ℂ))⁻¹ ≠ 0 := inv_ne_zero hc₀c
  have hbu : branch L ψ h₀ = (((c₀ : ℝ) : ℂ))⁻¹ • u := by
    rw [hudef, smul_smul, inv_mul_cancel₀ hc₀c, one_smul]
  have hue : star u ⬝ᵥ e = 0 := u_dot_e hcinv hbu heb
  refine ⟨dkGeneralFamily hu he hue, genFamilyProjectors u e, fun _ => rfl,
    fun t => dkGeneralFamily_consistent hcons hcinv hbu heb hu he hue t,
    ?_, dkGeneralFamily_injOn hu he hue, fun t => rfl,
    fun i a b => dkGeneralFamily_continuous u e i a b⟩
  intro t ht
  obtain ⟨hnt, hbp, hbm⟩ :=
    dkGeneralFamily_nontrivial hcons hcinv hbu heb hu he hue ht
  refine ⟨hnt, 0, 1, ?_, hbp, hbm⟩
  intro h01
  have hv := congrArg Fin.val h01
  have hv0 : ((0 : Fin (dkGeneralFamily hu he hue t).n)).val = 0 := rfl
  have hv1 : ((1 : Fin (dkGeneralFamily hu he hue t).n)).val = 1 := rfl
  omega

open scoped Classical in
/-- Dowker–Kent's Lemma 2, from the extension-vocabulary hypothesis: a
consistent set that is not maximally extended (append sense) admits, for
each nonzero-probability history, the same continuous family. NOTE the
scope flag: `MaximallyExtended` quantifies over append extensions only, so
this hypothesis is formally stronger than DK's insertion-inclusive
non-maximality; the intrinsic `dowkerKent_lemma2` form carries DK's own
working hypothesis. -/
theorem dowkerKent_lemma2_of_not_maximallyExtended
    {L : List (ProjectiveDecomposition d)} {ψ : d → ℂ}
    (hcons : DKConsistent L ψ) (hnmax : ¬ MaximallyExtended L ψ)
    (h₀ : History L) (hb₀ : branch L ψ h₀ ≠ 0) :
    ∃ (F : ℝ → ProjectiveDecomposition d) (Φ : ℝ → Fin 3 → Matrix d d ℂ)
      (hn : ∀ t, (F t).n = 3),
      (∀ t, DKConsistent (F t :: L) ψ) ∧
      (∀ t ∈ Set.Ioo 0 (Real.pi / 2),
        NontrivialExtension (F t) L ψ ∧
        ∃ i i' : Fin (F t).n, i ≠ i' ∧
          branch (F t :: L) ψ (i, h₀) ≠ 0 ∧
          branch (F t :: L) ψ (i', h₀) ≠ 0) ∧
      Set.InjOn F (Set.Ioo 0 (Real.pi / 2)) ∧
      (∀ t, (F t).P = Φ t ∘ Fin.cast (hn t)) ∧
      (∀ i a b, Continuous fun t => Φ t i a b) :=
  dowkerKent_lemma2 hcons
    (card_nonzero_lt_of_not_maximallyExtended hcons hnmax) h₀ hb₀

open scoped Classical in
/-- **DK's pure-case maximality criterion, both directions** ("Note also
that, when ρ is pure, it follows that a set is maximally extended if and
only if it has n histories of non-zero probability"): a consistent set at a
nonzero state is maximally extended (append sense) iff it has exactly `dim`
nonzero-probability histories. The saturation direction is the landed
`maximallyExtended_of_card_eq`; the converse is the Lemma 2 construction.
`ψ ≠ 0` is genuinely necessary — at `ψ = 0` every set is vacuously
maximally extended with zero nonzero histories (this is where DK's "ρ is a
state" carries content). -/
theorem maximallyExtended_iff_card_eq {L : List (ProjectiveDecomposition d)}
    {ψ : d → ℂ} (hψ : ψ ≠ 0) (hcons : DKConsistent L ψ) :
    MaximallyExtended L ψ ↔
      Fintype.card {h : History L // branch L ψ h ≠ 0} = Fintype.card d := by
  constructor
  · intro hmax
    by_contra hne
    have hlt : Fintype.card {h : History L // branch L ψ h ≠ 0}
        < Fintype.card d :=
      lt_of_le_of_ne (dkConsistent_card_nonzero_le L ψ hcons) hne
    have hex : ∃ h₀ : History L, branch L ψ h₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hψ
      have hsum := dkSet_exhaustive_mulVec L ψ
      rw [Matrix.sum_mulVec] at hsum
      rw [← hsum]
      exact Finset.sum_eq_zero fun h _ => hall h
    obtain ⟨h₀, hb₀⟩ := hex
    obtain ⟨F, Φ, hn, hFcons, hFnt, _, _, _⟩ :=
      dowkerKent_lemma2 hcons hlt h₀ hb₀
    have hmem : Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    obtain ⟨hnt, -⟩ := hFnt _ hmem
    exact hnt.2 (hmax _ hnt.1)
  · exact maximallyExtended_of_card_eq L ψ hcons

end QuantumProfligacy

end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumProfligacy.outer_mulVec
#print axioms Qtsl.QuantumProfligacy.exists_smul_unit
#print axioms Qtsl.QuantumProfligacy.exists_unit_dotProduct_orthogonal
#print axioms Qtsl.QuantumProfligacy.card_nonzero_lt_of_not_maximallyExtended
#print axioms Qtsl.QuantumProfligacy.genPhiPlus_orth_genPhiMinus
#print axioms Qtsl.QuantumProfligacy.genP3_mulVec_target
#print axioms Qtsl.QuantumProfligacy.genRotation_consistent
#print axioms Qtsl.QuantumProfligacy.genRotation_nontrivialExtension
#print axioms Qtsl.QuantumProfligacy.dkGeneralFamily_injOn
#print axioms Qtsl.QuantumProfligacy.dkGeneralFamily_continuous
#print axioms Qtsl.QuantumProfligacy.dowkerKent_lemma2
#print axioms Qtsl.QuantumProfligacy.dowkerKent_lemma2_of_not_maximallyExtended
#print axioms Qtsl.QuantumProfligacy.maximallyExtended_iff_card_eq
