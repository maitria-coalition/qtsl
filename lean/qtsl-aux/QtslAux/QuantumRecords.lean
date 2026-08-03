import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Complex.BigOperators
import QtslAux.DiamondTopology

/-! # Records imply consistency (Gell-Mann–Hartle, finite-dimensional)

The quantum tier of the record definitions of the semantic-universe
chapter (`def:su-record`, and its poset-supported generalization
`def:su-record-window`: a record over a window whose *every maximal
chain* is a classical record). Two halves, both at the honest
finite-dimensional stratum (`Matrix d d ℂ`, finite stage supports,
pure global state), plus the probability bookkeeping and concrete
counterexample witnesses for every load-bearing hypothesis.

**Kinematic half — class operators are well-defined.** A history's
class operator `C = P tₙ ⋯ P t₁` multiplies stage observables
latest-first. On a partially ordered stage support the product is
a priori ambiguous: distinct temporal linearizations of the same
support differ by reorderings of causally incomparable (spacelike)
stages. `classOperator_well_defined`: if the assignment commutes at
incomparables — microcausality, the axiom the algebraic-QFT tradition
imposes on spacelike-separated local algebras — then every temporal
linearization yields the same class operator. This is exactly the
structure the every-maximal-chain-classical clause of
`def:su-record-window` contributes at the quantum tier: chains are
rigid (their order is respected by every linearization), and only
antichain-neighbors ever reorder. Instantiated at the free monoid the
same theorem says a chain support has a *unique* linearization
(`chain_linearization_unique`) — the classical collapse, where
`def:su-record-window` degenerates to `def:su-record` on the nose.

**Dynamic half — records force decoherence.** `records_imply_medium`
(Gell-Mann–Hartle 1993, Phys. Rev. D 47, 3345, the easy direction of
their generalized-records identity): mutually orthogonal Hermitian
record observables correlated with the class operators at the state
(`C_α ψ = R_α ψ`) force the decoherence functional
`D(α,β) = ⟨C_β ψ, C_α ψ⟩` diagonal — *medium decoherence*, hence
(`weaklyConsistent_additivity`) additivity of the induced probabilities
over coarse-grainings: records imply consistency. The hypotheses are
deliberately weaker than Gell-Mann–Hartle's projections — Hermitian and
mutually orthogonal suffice for this direction — and the converse
construction (`medium_implies_records_of_exhaustive`) produces genuine
branch projectors, completing their biconditional for pure states:
medium decoherence of an exhaustive family *is* the existence of
generalized records. `perfect_records_imply_medium` is the companion
sufficient condition in Gell-Mann–Hartle's *exact-record*
(projection-cell) convention — `R_β C_α ψ = δ_{αβ} C_α ψ` — an
incomparable hypothesis package with the same conclusion (neither
implies the other; witnesses in its docstring).

**Witnesses (each hypothesis is load-bearing).**
* `exists_orderDependent_without_commutation` — without
  antichain-commutation, class operators are order-dependent: z- and
  x-spin projectors on a two-point antichain multiply differently in
  the two linearizations.
* `records_hypothesis_load_bearing` — without the record-correlation
  hypothesis, diagonality fails: the z-then-x two-stage family on the
  state `(1,1)` has `D((0,0),(1,0)) = 1/2 ≠ 0` (the double-slit
  interference term), even in the presence of a perfectly good
  orthogonal Hermitian family.
* `hermiticity_load_bearing` — without Hermiticity, diagonality fails:
  nilpotent "records" satisfy orthogonality and correlation yet
  interfere. Non-Hermitian records are not observables; the hypothesis
  is physical, not technical.
* `exists_weaklyConsistent_without_records` — **consistency does not
  imply records**: the z-then-y family on `(1,1)` is weakly consistent
  (every off-diagonal `D` purely imaginary — probabilities fully
  additive) yet admits *no* record family at all, since
  `D((0,0),(1,0)) = i/2 ≠ 0` breaks medium decoherence. This is the
  formal-records stratum of the Riedel–Zurek–Zwolak arrow
  (arXiv:1312.0331: decoherence does not imply *accessible* records;
  their finer counterexample concerns environment fragments and is out
  of scope here).

**Scope fences.** Finite supports only (continuum supports are
Isham–Linden territory); fixed stage-assignments (branch-dependent
projections representable by enlarging the stage set, not treated);
pure global states (the mixed case may admit no records at all —
a live research boundary). -- [classical]
-/

namespace Qtsl

namespace QuantumRecords

/-! ## The kinematic half: class operators over a poset support -/

section ClassOperator

variable {X : Type*} {M : Type*} [Monoid M]

/-- The class operator of a stage-assignment `P` along a stage list `L`,
read latest-first (the decoherent-histories convention
`C = P tₙ ⋯ P t₁`). -/
def classOperator (P : X → M) (L : List X) : M := (L.map P).prod

/-- A stage whose value commutes with every value on a prefix bubbles
to the front of the class operator. -/
private theorem prod_map_append_cons (P : X → M) {pre post : List X} {b : X}
    (hpre : ∀ a ∈ pre, Commute (P b) (P a)) :
    ((pre ++ b :: post).map P).prod = P b * ((pre ++ post).map P).prod := by
  have hc : Commute (P b) (pre.map P).prod := by
    refine Commute.list_prod_right _ _ ?_
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact hpre a ha
  simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  rw [← mul_assoc, ← hc.eq, mul_assoc]

variable [PartialOrder X]

private theorem well_defined_aux (P : X → M) :
    ∀ L₂ : List X, L₂.Pairwise (fun a b => ¬ a < b) →
      ∀ L₁ : List X, L₁.Perm L₂ → L₁.Pairwise (fun a b => ¬ a < b) →
        (∀ a ∈ L₁, ∀ b ∈ L₁, ¬ a < b → ¬ b < a → Commute (P a) (P b)) →
        (L₁.map P).prod = (L₂.map P).prod := by
  intro L₂
  induction L₂ with
  | nil =>
    intro _ L₁ hperm _ _
    rw [hperm.eq_nil]
  | cons b tail ih =>
    intro h₂ L₁ hperm h₁ hcomm
    have hb : b ∈ L₁ := hperm.mem_iff.mpr (List.mem_cons_self ..)
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hb
    rw [List.pairwise_append] at h₁
    obtain ⟨hpre_pw, hbpost_pw, hcross⟩ := h₁
    obtain ⟨hb_tail, htail_pw⟩ := List.pairwise_cons.mp h₂
    -- membership transport: `pre ++ post` sits inside `pre ++ b :: post`
    have hsub : ∀ a ∈ pre ++ post, a ∈ pre ++ b :: post := by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    -- the prefix consists of stages incomparable with `b` (or equal to it)
    have hpreb : ∀ a ∈ pre, Commute (P b) (P a) := by
      intro a ha
      rcases eq_or_ne a b with rfl | hne
      · exact Commute.refl _
      have h1 : ¬ a < b := hcross a ha b (List.mem_cons_self ..)
      have hmem : a ∈ b :: tail :=
        hperm.mem_iff.mp (List.mem_append_left _ ha)
      have h2 : ¬ b < a := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h hne
        · exact hb_tail a h
      exact (hcomm a (List.mem_append_left _ ha) b hb h1 h2).symm
    rw [prod_map_append_cons P hpreb, List.map_cons, List.prod_cons]
    congr 1
    have hperm' : (pre ++ post).Perm tail :=
      (List.perm_middle.symm.trans hperm).cons_inv
    have hpw' : (pre ++ post).Pairwise (fun a b => ¬ a < b) := by
      rw [List.pairwise_append]
      exact ⟨hpre_pw, (List.pairwise_cons.mp hbpost_pw).2,
        fun a ha y hy => hcross a ha y (List.mem_cons_of_mem _ hy)⟩
    exact ih htail_pw (pre ++ post) hperm' hpw'
      (fun a ha c hc h1 h2 => hcomm a (hsub a ha) c (hsub c hc) h1 h2)

/-- **Class operators are well-defined on poset supports with
antichain-commutation.** Two temporal linearizations of the same stage
multiset (latest-first: no stage is listed before a causally later
one), whose assigned values commute at causally incomparable pairs —
microcausality — yield the same class operator. Chains never reorder
between linearizations; only spacelike neighbors do, and those
commute. This is the well-definedness that the
every-maximal-chain-classical clause of `def:su-record-window`
purchases at the quantum tier. -/
theorem classOperator_well_defined (P : X → M) {L₁ L₂ : List X}
    (hperm : L₁.Perm L₂)
    (h₁ : L₁.Pairwise (fun a b => ¬ a < b))
    (h₂ : L₂.Pairwise (fun a b => ¬ a < b))
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₁, ¬ a < b → ¬ b < a → Commute (P a) (P b)) :
    classOperator P L₁ = classOperator P L₂ :=
  well_defined_aux P L₂ h₂ L₁ hperm h₁ hcomm

/-- Microcausality dress of `classOperator_well_defined`: the
commutation hypothesis quantified over *spacelike-separated* stages
(`¬ p ≤ q` and `¬ q ≤ p` in the causal order — e.g. the induced order
on a stage support inside a causal diamond of `Qtsl.DiamondSite`).
Equal stages commute for free; strictly comparable ones never need
to. -/
theorem classOperator_well_defined_of_microcausal (P : X → M)
    {L₁ L₂ : List X} (hperm : L₁.Perm L₂)
    (h₁ : L₁.Pairwise (fun a b => ¬ a < b))
    (h₂ : L₂.Pairwise (fun a b => ¬ a < b))
    (hmicro : ∀ p ∈ L₁, ∀ q ∈ L₁, ¬ p ≤ q → ¬ q ≤ p → Commute (P p) (P q)) :
    classOperator P L₁ = classOperator P L₂ := by
  refine classOperator_well_defined P hperm h₁ h₂ fun a ha b hb h1 h2 => ?_
  rcases eq_or_ne a b with rfl | hne
  · exact Commute.refl _
  · exact hmicro a ha b hb
      (fun hle => h1 (lt_of_le_of_ne hle hne))
      (fun hle => h2 (lt_of_le_of_ne hle hne.symm))

/-- The classical collapse: a chain support has a *unique* temporal
linearization. Proof: instantiate `classOperator_well_defined` at the
free monoid, where the class operator of a stage list is the list
itself — on a chain the commutation hypothesis is vacuous (mutually
non-strictly-comparable pairs on a chain are equal), so the two
linearizations coincide as words. This is the sense in which
`def:su-record-window` degenerates to `def:su-record` over a totally
ordered support. -/
theorem chain_linearization_unique {L₁ L₂ : List X} (hperm : L₁.Perm L₂)
    (hchain : ∀ a ∈ L₁, ∀ b ∈ L₁, a ≤ b ∨ b ≤ a)
    (h₁ : L₁.Pairwise (fun a b => ¬ a < b))
    (h₂ : L₂.Pairwise (fun a b => ¬ a < b)) :
    L₁ = L₂ := by
  have hof : ∀ L : List X,
      (L.map (FreeMonoid.of (α := X))).prod = FreeMonoid.ofList L := by
    intro L
    induction L with
    | nil => rfl
    | cons a L ihL => rw [List.map_cons, List.prod_cons, ihL]; rfl
  have hcomm : ∀ a ∈ L₁, ∀ b ∈ L₁, ¬ a < b → ¬ b < a →
      Commute (FreeMonoid.of a) (FreeMonoid.of b) := by
    intro a ha b hb h1 h2
    rcases hchain a ha b hb with hle | hle
    · rcases lt_or_eq_of_le hle with hlt | rfl
      · exact absurd hlt h1
      · exact Commute.refl _
    · rcases lt_or_eq_of_le hle with hlt | heq
      · exact absurd hlt h2
      · exact heq ▸ Commute.refl _
  have h := classOperator_well_defined (FreeMonoid.of (α := X))
    hperm h₁ h₂ hcomm
  simp only [classOperator, hof] at h
  exact FreeMonoid.ofList.injective h

end ClassOperator

/-! ## The dynamic half: the decoherence functional and records -/

section Decoherence

open Matrix
open scoped ComplexOrder

variable {d : Type*} [Fintype d] {ι : Type*}

/-- The decoherence functional of a family of class operators at a pure
state (matrix form): `D(α,β) = ⟨C_β ψ, C_α ψ⟩`. Diagonal entries are
the branch weights; off-diagonal entries are interference terms. -/
noncomputable def decoherenceFunctional (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (α β : ι) : ℂ :=
  star (C β *ᵥ ψ) ⬝ᵥ (C α *ᵥ ψ)

/-- Medium decoherence: the decoherence functional is diagonal. -/
def MediumDecoherent (C : ι → Matrix d d ℂ) (ψ : d → ℂ) : Prop :=
  ∀ α β, α ≠ β → decoherenceFunctional C ψ α β = 0

/-- Weak consistency (the Griffiths condition): off-diagonal
interference terms have no real part — exactly what probability
additivity consumes. -/
def WeaklyConsistent (C : ι → Matrix d d ℂ) (ψ : d → ℂ) : Prop :=
  ∀ α β, α ≠ β → (decoherenceFunctional C ψ α β).re = 0

/-- The decoherence functional is conjugate-symmetric. -/
theorem decoherenceFunctional_conj (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (α β : ι) :
    decoherenceFunctional C ψ β α = star (decoherenceFunctional C ψ α β) := by
  simp only [decoherenceFunctional]
  rw [Matrix.star_dotProduct]

theorem MediumDecoherent.weaklyConsistent {C : ι → Matrix d d ℂ}
    {ψ : d → ℂ} (h : MediumDecoherent C ψ) : WeaklyConsistent C ψ := by
  intro α β hαβ
  rw [h α β hαβ, Complex.zero_re]

/-- Branch weights are nonnegative: the diagonal of the decoherence
functional is a candidate probability assignment. -/
theorem diagonal_re_nonneg (C : ι → Matrix d d ℂ) (ψ : d → ℂ) (α : ι) :
    0 ≤ (decoherenceFunctional C ψ α α).re := by
  simp only [decoherenceFunctional]
  have h : (0 : ℂ) ≤ star (C α *ᵥ ψ) ⬝ᵥ (C α *ᵥ ψ) :=
    dotProduct_star_self_nonneg _
  simpa using (Complex.le_def.mp h).1

/-- **Records imply medium decoherence** (Gell-Mann–Hartle 1993,
Phys. Rev. D 47, 3345 — the easy direction of the generalized-records
identity, at hypotheses deliberately weaker than theirs): a family of
mutually orthogonal Hermitian record observables correlated with the
class operators at the state forces the decoherence functional
diagonal. Two lines of operator algebra:
`⟨C_β ψ, C_α ψ⟩ = ⟨R_β ψ, R_α ψ⟩ = ⟨ψ, R_β R_α ψ⟩ = 0`. -/
theorem records_imply_medium (C R : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hherm : ∀ α, (R α).IsHermitian)
    (horth : ∀ α β, α ≠ β → R α * R β = 0)
    (hrec : ∀ α, C α *ᵥ ψ = R α *ᵥ ψ) :
    MediumDecoherent C ψ := by
  intro α β hαβ
  simp only [decoherenceFunctional]
  rw [hrec α, hrec β, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, (hherm β).eq, horth β α hαβ.symm,
    Matrix.vecMul_zero, zero_dotProduct]

/-- **Perfect records imply medium decoherence** — the record condition
in Gell-Mann–Hartle's *exact-record* (projection-cell) convention: each
record cell witnesses its branch exactly at the state,
`R β *ᵥ (C α *ᵥ ψ) = δ_{αβ} • (C α *ᵥ ψ)`, stated as its two Kronecker
faces `hfix` (`β = α`) and `hann` (`β ≠ α`). Incomparable with
`records_imply_medium`'s hypothesis package — neither implies the
other: doubling an orthogonal projector family (`R α = 2 • P α`,
`C α = R α`) satisfies that theorem's correlation `C α *ᵥ ψ = R α *ᵥ ψ`
yet fails `hfix` on any nonzero branch (`4 • P α *ᵥ ψ ≠ 2 • P α *ᵥ ψ`);
a zero branch (`C α *ᵥ ψ = 0` with `R α *ᵥ ψ ≠ 0`) satisfies
`hfix`/`hann` vacuously yet fails the correlation. Only Hermiticity and
the two Kronecker faces are consumed: idempotence and mutual
orthogonality of the cells hold in the intended instances but are not
needed for this direction. Two lines:
`⟨v_β, v_α⟩ = ⟨R_β v_β, v_α⟩ = ⟨v_β, R_β v_α⟩ = ⟨v_β, 0⟩ = 0`. -/
theorem perfect_records_imply_medium (C R : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hherm : ∀ α, (R α).IsHermitian)
    (hfix : ∀ α, R α *ᵥ (C α *ᵥ ψ) = C α *ᵥ ψ)
    (hann : ∀ α β, α ≠ β → R β *ᵥ (C α *ᵥ ψ) = 0) :
    MediumDecoherent C ψ := by
  intro α β hαβ
  simp only [decoherenceFunctional]
  rw [← hfix β, Matrix.star_mulVec, (hherm β).eq,
    ← Matrix.dotProduct_mulVec, hann α β hαβ, dotProduct_zero]

/-! ### Consistency as probability additivity

The payoff of diagonality: branch weights are additive over
coarse-grainings, so a decoherent family carries an honest (finitely
additive) probability assignment on its cells. Weak consistency
already suffices at the real level; medium decoherence gives
additivity of the complex functional itself. -/

/-- Additivity at the complex level, from medium decoherence: the
weight of a coarse cell is the sum of its members' weights. -/
theorem mediumDecoherent_additivity (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (S : Finset ι)
    (hm : ∀ α ∈ S, ∀ β ∈ S, α ≠ β → decoherenceFunctional C ψ α β = 0) :
    star ((∑ α ∈ S, C α) *ᵥ ψ) ⬝ᵥ ((∑ α ∈ S, C α) *ᵥ ψ)
      = ∑ α ∈ S, decoherenceFunctional C ψ α α := by
  simp only [decoherenceFunctional] at hm ⊢
  rw [Matrix.sum_mulVec, star_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [dotProduct_sum]
  exact Finset.sum_eq_single_of_mem β hβ fun α hα hne => hm α hα β hβ hne

/-- Additivity of the branch probabilities, from weak consistency
alone (the Griffiths condition): real parts of the off-diagonal
interference terms vanish, so the probability of a coarse cell is the
sum of its members' probabilities. Chained with
`records_imply_medium` and `MediumDecoherent.weaklyConsistent`, this
is *records imply consistency*. -/
theorem weaklyConsistent_additivity (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (S : Finset ι)
    (hw : ∀ α ∈ S, ∀ β ∈ S, α ≠ β →
      (decoherenceFunctional C ψ α β).re = 0) :
    (star ((∑ α ∈ S, C α) *ᵥ ψ) ⬝ᵥ ((∑ α ∈ S, C α) *ᵥ ψ)).re
      = ∑ α ∈ S, (decoherenceFunctional C ψ α α).re := by
  simp only [decoherenceFunctional] at hw ⊢
  rw [Matrix.sum_mulVec, star_sum, sum_dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [dotProduct_sum, Complex.re_sum]
  exact Finset.sum_eq_single_of_mem β hβ fun α hα hne => hw α hα β hβ hne

/-! ### The converse construction: decoherence yields records

For pure states and exhaustive families the Gell-Mann–Hartle identity
is a biconditional: medium decoherence *constructs* the generalized
records — the projector onto each branch vector. (These are the
"formal" records of Riedel–Zurek–Zwolak: one global observable
family, in general accessible to no local observer; accessibility is
a strictly stronger demand, out of scope here.) -/

open scoped Classical in
/-- Branch projector onto a vector, zero-safe: `0` if `v = 0`, else
`|v⟩⟨v| / ⟨v,v⟩`. -/
noncomputable def branchProjector (v : d → ℂ) : Matrix d d ℂ :=
  if v = 0 then 0 else (star v ⬝ᵥ v)⁻¹ • Matrix.vecMulVec v (star v)

omit [Fintype d] in
/-- The unnormalized outer square `|v⟩⟨v|` is Hermitian. -/
theorem vecMulVec_star_self_isHermitian (v : d → ℂ) :
    (Matrix.vecMulVec v (star v)).IsHermitian := by
  show _ᴴ = _
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]

theorem branchProjector_isHermitian (v : d → ℂ) :
    (branchProjector v).IsHermitian := by
  unfold branchProjector
  split
  · exact Matrix.isHermitian_zero
  · have hc : star ((star v ⬝ᵥ v)⁻¹) = (star v ⬝ᵥ v)⁻¹ := by
      rw [star_inv₀, ← Matrix.star_dotProduct]
    show _ᴴ = _
    rw [Matrix.conjTranspose_smul, hc, (vecMulVec_star_self_isHermitian v).eq]

/-- Branch projectors of mutually orthogonal vectors annihilate each
other. -/
theorem branchProjector_orthogonal {v w : d → ℂ}
    (hvw : star v ⬝ᵥ w = 0) :
    branchProjector v * branchProjector w = 0 := by
  unfold branchProjector
  split
  · simp
  · split
    · simp
    · rw [Matrix.smul_mul, Matrix.mul_smul,
        Matrix.vecMulVec_mul_vecMulVec, hvw]
      simp

/-- `branchProjector v` sends any vector whose `v`-component equals
`⟨v,v⟩` to `v` itself. -/
theorem branchProjector_mulVec_of (v ψ : d → ℂ)
    (h : star v ⬝ᵥ ψ = star v ⬝ᵥ v) :
    branchProjector v *ᵥ ψ = v := by
  unfold branchProjector
  split
  · rename_i hv
    subst hv
    simp
  · rename_i hv
    rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, h,
      op_smul_eq_smul, smul_smul,
      inv_mul_cancel₀ (by rwa [Ne, dotProduct_star_self_eq_zero]),
      one_smul]

/-- **Medium decoherence constructs records** (the converse, for pure
states and exhaustive families): if the family is exhaustive at `ψ`
and medium-decoherent, the branch projectors form an orthogonal
Hermitian record family correlated with the class operators. Together
with `records_imply_medium` this is the Gell-Mann–Hartle
biconditional. -/
theorem medium_implies_records_of_exhaustive [Fintype ι]
    (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hexh : (∑ α, C α) *ᵥ ψ = ψ)
    (hmed : MediumDecoherent C ψ) :
    ∃ R : ι → Matrix d d ℂ,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∀ α, C α *ᵥ ψ = R α *ᵥ ψ) := by
  refine ⟨fun α => branchProjector (C α *ᵥ ψ),
    fun α => branchProjector_isHermitian _,
    fun α β hαβ => branchProjector_orthogonal (hmed β α hαβ.symm),
    fun α => ?_⟩
  refine (branchProjector_mulVec_of _ _ ?_).symm
  have hψ : ψ = ∑ β, C β *ᵥ ψ := by
    rw [← Matrix.sum_mulVec, hexh]
  calc star (C α *ᵥ ψ) ⬝ᵥ ψ
      = ∑ β, star (C α *ᵥ ψ) ⬝ᵥ (C β *ᵥ ψ) := by
        nth_rewrite 2 [hψ]
        rw [dotProduct_sum]
    _ = star (C α *ᵥ ψ) ⬝ᵥ (C α *ᵥ ψ) :=
        Finset.sum_eq_single_of_mem α (Finset.mem_univ _)
          fun β _ hne => hmed β α hne

end Decoherence

/-! ## Witnesses: every hypothesis is load-bearing

Concrete two-dimensional counterexamples, one per dropped hypothesis.
The projector families are the standard spin-measurement bases; the
state is the unnormalized `(1,1)` (normalization scales the
decoherence functional and changes no vanishing statement). -/

section Witnesses

open Matrix

/-- z-basis projector, spin-up. -/
noncomputable def Pz0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- z-basis projector, spin-down. -/
noncomputable def Pz1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

/-- x-basis projector, spin-right. -/
noncomputable def Qx0 : Matrix (Fin 2) (Fin 2) ℂ := !![1/2, 1/2; 1/2, 1/2]

/-- x-basis projector, spin-left. -/
noncomputable def Qx1 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1/2, -(1/2); -(1/2), 1/2]

/-- y-basis projector, `(1,i)/√2` direction. -/
noncomputable def Yp : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1/2, -(Complex.I/2); Complex.I/2, 1/2]

/-- y-basis projector, `(1,-i)/√2` direction. -/
noncomputable def Ym : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1/2, Complex.I/2; -(Complex.I/2), 1/2]

/-- A two-point antichain: `Bool` with the discrete order. -/
def AC2 : Type := Bool

instance : PartialOrder AC2 where
  le a b := a = b
  le_refl _ := rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h _ := h

theorem AC2.not_lt (a b : AC2) : ¬ a < b := fun h => h.ne h.le

/-- **Dropping antichain-commutation refutes well-definedness**: on a
two-point antichain carrying the (non-commuting) z- and x-projectors,
the two temporal linearizations yield different class operators —
`Pz0 · Qx0 ≠ Qx0 · Pz0` (they differ at entry `(0,1)`: `1/2` vs `0`).
Microcausality is load-bearing, not decorative: a spacelike pair of
non-commuting observables has no well-defined joint history. -/
theorem exists_orderDependent_without_commutation :
    ∃ (L₁ L₂ : List AC2) (P : AC2 → Matrix (Fin 2) (Fin 2) ℂ),
      L₁.Perm L₂ ∧ L₁.Pairwise (fun a b => ¬ a < b) ∧
      L₂.Pairwise (fun a b => ¬ a < b) ∧
      classOperator P L₁ ≠ classOperator P L₂ := by
  refine ⟨[false, true], [true, false], fun a => bif a then Qx0 else Pz0,
    List.Perm.swap true false [], ?_, ?_, ?_⟩
  · exact List.Pairwise.cons (fun b _ => AC2.not_lt _ b)
      (List.pairwise_singleton _ _)
  · exact List.Pairwise.cons (fun b _ => AC2.not_lt _ b)
      (List.pairwise_singleton _ _)
  · intro hcontra
    simp only [classOperator, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, cond_true, cond_false] at hcontra
    have h := congrFun (congrFun hcontra 0) 1
    rw [Matrix.mul_apply, Matrix.mul_apply] at h
    simp [Fin.sum_univ_two, Pz0, Qx0] at h

/-- The two-stage z-then-x history family (class operators
`C(a,b) = Qx_b · Pz_a`, latest-first): the double-slit shape. -/
noncomputable def zxFamily : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun ab => (if ab.2 = 0 then Qx0 else Qx1) * (if ab.1 = 0 then Pz0 else Pz1)

/-- The two-stage z-then-y history family. -/
noncomputable def zyFamily : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun ab => (if ab.2 = 0 then Yp else Ym) * (if ab.1 = 0 then Pz0 else Pz1)

theorem Pz0_isHermitian : Pz0.IsHermitian := by
  show _ᴴ = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pz0, Matrix.conjTranspose_apply]

theorem Pz1_isHermitian : Pz1.IsHermitian := by
  show _ᴴ = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pz1, Matrix.conjTranspose_apply]

theorem Pz0_mul_Pz1 : Pz0 * Pz1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pz0, Pz1, Matrix.mul_apply, Fin.sum_univ_two]

theorem Pz1_mul_Pz0 : Pz1 * Pz0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pz0, Pz1, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Dropping the record-correlation hypothesis refutes
diagonality**: the z-then-x family on `(1,1)` interferes —
`D((0,0),(1,0)) = 1/2 ≠ 0` — even in the presence of a perfectly good
orthogonal Hermitian family (which merely fails to be correlated with
these class operators). -/
theorem records_hypothesis_load_bearing :
    ∃ (C R : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (ψ : Fin 2 → ℂ),
      (∀ α, (R α).IsHermitian) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      ¬ MediumDecoherent C ψ := by
  refine ⟨zxFamily,
    fun ab => if ab = (0, 0) then Pz0 else if ab = (1, 0) then Pz1 else 0,
    ![1, 1], ?_, ?_, ?_⟩
  · intro α
    dsimp only
    split
    · exact Pz0_isHermitian
    · split
      · exact Pz1_isHermitian
      · exact Matrix.isHermitian_zero
  · intro α β hne
    obtain ⟨a₁, b₁⟩ := α
    obtain ⟨a₂, b₂⟩ := β
    fin_cases a₁ <;> fin_cases b₁ <;> fin_cases a₂ <;> fin_cases b₂ <;>
      simp_all [Pz0_mul_Pz1, Pz1_mul_Pz0]
  · intro h
    have hcontra := h (0, 0) (1, 0) (by decide)
    simp only [decoherenceFunctional, zxFamily] at hcontra
    norm_num [Qx0, Pz0, Pz1, Matrix.mulVec, Matrix.mul_apply, dotProduct,
      Fin.sum_univ_two, Pi.star_apply, Complex.star_def, map_div₀, map_neg,
      map_one, map_ofNat, Complex.conj_I, Complex.ext_iff, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.div_re,
      Complex.div_im, Complex.I_re, Complex.I_im, Complex.normSq_apply] at hcontra

/-- **Dropping Hermiticity refutes diagonality**: nilpotent "records"
(`R₀ = E₀₁`, `R₁ = 2·E₀₁`) are mutually orthogonal and exactly
correlated with their own class operators, yet `D(0,1) = 2 ≠ 0`.
Non-Hermitian records are not observables. -/
theorem hermiticity_load_bearing :
    ∃ (C R : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (ψ : Fin 2 → ℂ),
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∀ α, C α *ᵥ ψ = R α *ᵥ ψ) ∧
      ¬ MediumDecoherent C ψ := by
  refine ⟨![!![0, 1; 0, 0], !![0, 2; 0, 0]],
    ![!![0, 1; 0, 0], !![0, 2; 0, 0]], ![0, 1], ?_, fun α => rfl, ?_⟩
  · intro α β hne
    fin_cases α <;> fin_cases β <;>
      first
        | exact absurd rfl hne
        | (ext i j
           fin_cases i <;> fin_cases j <;>
             simp [Matrix.mul_apply, Fin.sum_univ_two])
  · intro h
    have hcontra := h 0 1 (by decide)
    simp only [decoherenceFunctional] at hcontra
    norm_num [Matrix.mulVec, Matrix.mul_apply, dotProduct,
      Fin.sum_univ_two, Pi.star_apply, Complex.star_def, map_div₀, map_neg,
      map_one, map_ofNat, Complex.conj_I, Complex.ext_iff, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.div_re,
      Complex.div_im, Complex.I_re, Complex.I_im, Complex.normSq_apply] at hcontra

/-- **Consistency does not imply records**: the z-then-y family on
`(1,1)` is weakly consistent — every off-diagonal interference term
is purely imaginary, so branch probabilities are fully additive
(`weaklyConsistent_additivity` applies) — yet it admits *no* record
family whatsoever: `D((0,0),(1,0)) = i/2 ≠ 0` breaks medium
decoherence, and by `records_imply_medium` records would force it.
The formal-records stratum of the Riedel–Zurek–Zwolak arrow. -/
theorem exists_weaklyConsistent_without_records :
    ∃ (C : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (ψ : Fin 2 → ℂ),
      WeaklyConsistent C ψ ∧
      ¬ ∃ R : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℂ,
          (∀ α, (R α).IsHermitian) ∧
          (∀ α β, α ≠ β → R α * R β = 0) ∧
          (∀ α, C α *ᵥ ψ = R α *ᵥ ψ) := by
  refine ⟨zyFamily, ![1, 1], ?_, ?_⟩
  · intro α β hne
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
  · rintro ⟨R, hherm, horth, hrec⟩
    have hmed := records_imply_medium zyFamily R ![1, 1] hherm horth hrec
    have hcontra := hmed (0, 0) (1, 0) (by decide)
    simp only [decoherenceFunctional, zyFamily] at hcontra
    norm_num [Yp, Ym, Pz0, Pz1, Matrix.mulVec, Matrix.mul_apply, dotProduct,
      Fin.sum_univ_two, Pi.star_apply, Complex.star_def, map_div₀, map_neg,
      map_one, map_ofNat, Complex.conj_I, Complex.ext_iff, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.div_re,
      Complex.div_im, Complex.I_re, Complex.I_im, Complex.normSq_apply] at hcontra

/-! ### The spacetime-site instantiation -/

/-- `classOperator_well_defined_of_microcausal` at Minkowski space
(`Qtsl.DiamondSite.Mink`, the derived spacetime site's calibrating
instance): finite stage supports — e.g. inside a causal diamond — have
well-defined class operators as soon as spacelike-separated stages
carry commuting observables. Together with
`minkowski_diamond_spacelike_pair` (a thick diamond contains spacelike
pairs) this is the honest quantum content of a poset-supported record
over the site: the microcausality hypothesis is not vacuous, and it is
exactly what the every-maximal-chain-classical clause needs. -/
theorem classOperator_well_defined_minkowski {E : Type*}
    [NormedAddCommGroup E] {M : Type*} [Monoid M]
    (P : DiamondSite.Mink E → M) {L₁ L₂ : List (DiamondSite.Mink E)}
    (hperm : L₁.Perm L₂)
    (h₁ : L₁.Pairwise (fun a b => ¬ a < b))
    (h₂ : L₂.Pairwise (fun a b => ¬ a < b))
    (hmicro : ∀ p ∈ L₁, ∀ q ∈ L₁, ¬ p ≤ q → ¬ q ≤ p →
      Commute (P p) (P q)) :
    classOperator P L₁ = classOperator P L₂ :=
  classOperator_well_defined_of_microcausal P hperm h₁ h₂ hmicro

end Witnesses

end QuantumRecords

end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumRecords.classOperator_well_defined
#print axioms Qtsl.QuantumRecords.classOperator_well_defined_of_microcausal
#print axioms Qtsl.QuantumRecords.chain_linearization_unique
#print axioms Qtsl.QuantumRecords.records_imply_medium
#print axioms Qtsl.QuantumRecords.perfect_records_imply_medium
#print axioms Qtsl.QuantumRecords.decoherenceFunctional_conj
#print axioms Qtsl.QuantumRecords.diagonal_re_nonneg
#print axioms Qtsl.QuantumRecords.mediumDecoherent_additivity
#print axioms Qtsl.QuantumRecords.weaklyConsistent_additivity
#print axioms Qtsl.QuantumRecords.medium_implies_records_of_exhaustive
#print axioms Qtsl.QuantumRecords.exists_orderDependent_without_commutation
#print axioms Qtsl.QuantumRecords.records_hypothesis_load_bearing
#print axioms Qtsl.QuantumRecords.hermiticity_load_bearing
#print axioms Qtsl.QuantumRecords.exists_weaklyConsistent_without_records
#print axioms Qtsl.QuantumRecords.classOperator_well_defined_minkowski
