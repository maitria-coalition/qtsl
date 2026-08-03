/-
Copyright (c) 2026 The maitria coalition. All rights reserved.
Released under Apache 2.0 / MIT dual license.
-/
import QtslAux.QuantumCompleteness

/-! # Dowker–Kent consistent sets: the domain of the set-selection problem

Dowker–Kent's consistent sets (Dowker–Kent, "On the Consistent Histories
Approach to Quantum Mechanics", J. Stat. Phys. 82 (1996) 1575,
gr-qc/9412067; Phys. Rev. Lett. 75 (1995) 3038) formalized as first-class
structure at the finite-dimensional matrix grade, with pure initial state
and trivial final condition — the domain on which DK pose the
set-selection problem. Three deliverables:

**The domain (`ProjectiveDecomposition`, `History`, `classOp`,
`DKConsistent`, extensions).** DK's basic events are "sets of orthogonal
hermitian projections `P^{(i)}`" satisfying their conditions (their
eq. \conds): `∑ᵢ P^{(i)} = 1` and `P^{(i)} P^{(j)} = δ_{ij} P^{(i)}` —
`ProjectiveDecomposition` packages exactly these fields (idempotence is
the diagonal of the delta condition). A DK set at trivial final condition
is a finite temporal sequence of decompositions; histories choose one
projection per time; class operators are the ordered latest-first
products, taken through the landed `classOperator` list machinery (a
temporal sequence is a chain support, whose linearization is unique —
`chain_linearization_unique` — so no commutation hypothesis is owed).
Consistency is DK's, verbatim: "When the conditions [\decohgmh] hold, we
say that the set of histories, S, is consistent." Their footnote fixes
the terminology this development already uses: "The term *medium
decoherent*, coined by Gell-Mann and Hartle, is used in the literature to
describe sets satisfying [\decohgmh]. *Weakly decoherent* sets satisfy
only the real part of [\decohgmh]." For a pure state `ρ = |ψ⟩⟨ψ|` and
`ρ_f = 1`, DK's `Tr(C_α ρ C_β†) = δ_{αβ} p(α)` is literally the statement
that the decoherence functional `⟨C_β ψ, C_α ψ⟩` is diagonal, so
`DKConsistent := MediumDecoherent` of the induced class-operator family —
the definition is an instantiation, not a paraphrase.

**Exhaustiveness and the automatic-records corollary.**
`dkSet_exhaustive`: the induced family satisfies `∑ over histories of
C = 1` — the product of the per-time sums, distributed over ordered
products. Consequently every DK-consistent set is exhaustive at its
state, and the landed converse
(`medium_implies_projective_records_of_exhaustive`) specializes:
**every pure-state DK-consistent set carries formal projective records**
(`dkConsistent_projective_records`; the full complete package minus
permanence at `dkConsistent_complete_records`). On this domain formal
record existence therefore performs NO selection among consistent sets —
it is a property of all of them (Gell-Mann–Hartle 1995, gr-qc/9509054:
records "follow from medium decoherence and the assumption of a pure
state"). Any record-based selection principle must use a strictly
stronger, physically restricted record notion; that boundary is outside
this module's scope.

**The history cap (DK Lemma 1's core) and the profligacy instance (DK
PRL Lemma 2).** `dkConsistent_card_nonzero_le` machine-checks the
counting core of DK's Lemma 1 proof — "Thus there can be no more than
rn histories with non-zero probability", at the pure-state rank
`r = 1`: a DK-consistent set has at most `dim` histories of nonzero
probability (consistency makes nonzero branch vectors orthogonal, hence
linearly independent). Note this is the history-count cap from DK's
proof, not their length statement `k ≤ rn`. The cheap direction of DK's
pure-case note ("a set is maximally extended if and only if it has n
histories of non-zero probability") is `maximallyExtended_of_card_eq`;
the converse direction of that note is the general Lemma 2's content and
is deliberately not claimed here (it is proven in
`QtslAux.QuantumProfligacy`). The Lemma 2 *instance* lives in the
final section; its naming discipline is stated there.

**Scope fences.** Trivial final condition `ρ_f = 1` only (DK's own
Lemma 2 proof rides plain branch-vector orthogonality, which is this
case; their Lemma 4 shows nontrivial `ρ_f` changes the picture).
Branch-independent decompositions only (DK's branch-dependent refinement
is a named non-goal). Extensions are formalized at the APPEND position
(the new decomposition at the latest time — the case DK's Lemma 2
construction uses); DK's general definition allows insertion at any
position. Finite-dimensional matrix grade, finite time sequences, pure
states, throughout. -/

namespace Qtsl

namespace QuantumConsistentSets

open Matrix QuantumRecords QuantumConverse QuantumCompleteness
open scoped ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## Projective decompositions: DK's `\conds` -/

/-- A projective decomposition of unity (DK gr-qc/9412067, eq. \conds):
a finite family of Hermitian matrices with `∑ᵢ P^{(i)} = 1` and
`P^{(i)} P^{(j)} = δ_{ij} P^{(i)}` — DK's "sets of orthogonal hermitian
projections". Idempotence is the diagonal of `mul_delta`. The size is a
field, so temporal sequences of decompositions of different sizes are
ordinary lists. -/
structure ProjectiveDecomposition (d : Type*) [Fintype d] [DecidableEq d] where
  /-- number of cells (DK's `n_j`) -/
  n : ℕ
  /-- the projections -/
  P : Fin n → Matrix d d ℂ
  isHermitian : ∀ i, (P i).IsHermitian
  /-- DK's `P^{(i)} P^{(j)} = δ_{ij} P^{(i)}`. -/
  mul_delta : ∀ i j, P i * P j = if i = j then P i else 0
  /-- DK's `∑ᵢ P^{(i)} = 1`. -/
  sum_eq_one : ∑ i, P i = 1

namespace ProjectiveDecomposition

variable (σ : ProjectiveDecomposition d)

theorem idem (i : Fin σ.n) : σ.P i * σ.P i = σ.P i := by
  rw [σ.mul_delta, if_pos rfl]

theorem orthogonal {i j : Fin σ.n} (hij : i ≠ j) : σ.P i * σ.P j = 0 := by
  rw [σ.mul_delta, if_neg hij]

/-- On a nonempty space a decomposition has at least one cell (an empty
sum cannot equal `1`). -/
theorem n_pos [Nonempty d] : 0 < σ.n := by
  rcases Nat.eq_zero_or_pos σ.n with h | h
  · exfalso
    have hsum := σ.sum_eq_one
    haveI : IsEmpty (Fin σ.n) := by rw [h]; infer_instance
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    have x := Classical.arbitrary d
    have h01 := congrFun (congrFun hsum x) x
    simp [Matrix.one_apply_eq] at h01
  · exact h

end ProjectiveDecomposition

/-! ## DK sets, histories, class operators

A DK set (at pure state and trivial final condition) is a finite temporal
sequence of projective decompositions. **Storage convention: latest time
first** — DK's `(ρ, {σ₁, …, σ_k})` (earliest first) is the list
`[σ_k, …, σ₁]`. This makes DK's append-a-latest-decomposition extension
literally `τ :: L`, and every definition a structural recursion. -/

/-- The history type of a temporal sequence: one cell index per time.
DK: "the histories given by choosing one projection from each `σ_j` in
all possible ways are an exhaustive and exclusive set of alternatives." -/
def History : List (ProjectiveDecomposition d) → Type
  | [] => Unit
  | σ :: L => Fin σ.n × History L

instance instFintypeHistory :
    ∀ L : List (ProjectiveDecomposition d), Fintype (History L)
  | [] => inferInstanceAs (Fintype Unit)
  | σ :: L =>
    letI := instFintypeHistory L
    inferInstanceAs (Fintype (Fin σ.n × History L))

instance instDecidableEqHistory :
    ∀ L : List (ProjectiveDecomposition d), DecidableEq (History L)
  | [] => inferInstanceAs (DecidableEq Unit)
  | σ :: L =>
    letI := instDecidableEqHistory L
    inferInstanceAs (DecidableEq (Fin σ.n × History L))

instance instNonemptyHistory [Nonempty d] :
    ∀ L : List (ProjectiveDecomposition d), Nonempty (History L)
  | [] => ⟨()⟩
  | σ :: L => (instNonemptyHistory L).elim fun h => ⟨(⟨0, σ.n_pos⟩, h)⟩

/-- The projectors a history selects, as a latest-first list of stage
values — the unique temporal linearization of a chain support
(cf. `QuantumRecords.chain_linearization_unique`), rendered ready for
`classOperator`. -/
def selected : (L : List (ProjectiveDecomposition d)) → History L →
    List (Matrix d d ℂ)
  | [], _ => []
  | σ :: L, (i, h) => σ.P i :: selected L h

/-- The class operator of a history: the ordered latest-first product
`C = P_{t_n} ⋯ P_{t_1}`, via the landed `classOperator` machinery. On a
totally ordered support the linearization is unique, so no
antichain-commutation hypothesis is owed. -/
noncomputable def classOp (L : List (ProjectiveDecomposition d))
    (h : History L) : Matrix d d ℂ :=
  classOperator id (selected L h)

@[simp] theorem classOp_nil (h : History ([] : List (ProjectiveDecomposition d))) :
    classOp [] h = 1 := rfl

theorem classOp_cons (σ : ProjectiveDecomposition d)
    (L : List (ProjectiveDecomposition d)) (i : Fin σ.n) (h : History L) :
    classOp (σ :: L) (i, h) = σ.P i * classOp L h := by
  simp [classOp, selected, classOperator]

/-- The branch vector `C_h ψ` of a history. A history "has non-zero
probability" in DK's sense iff its branch vector is nonzero
(`prob_ne_zero_iff`). -/
noncomputable def branch (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ)
    (h : History L) : d → ℂ :=
  classOp L h *ᵥ ψ

@[simp] theorem branch_nil (ψ : d → ℂ)
    (h : History ([] : List (ProjectiveDecomposition d))) :
    branch [] ψ h = ψ := by
  simp [branch]

theorem branch_cons (τ : ProjectiveDecomposition d)
    (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ) (i : Fin τ.n)
    (h : History L) :
    branch (τ :: L) ψ (i, h) = τ.P i *ᵥ branch L ψ h := by
  rw [branch, branch, classOp_cons, ← Matrix.mulVec_mulVec]

/-- **The induced family is exhaustive** — the sum of all class operators
is the identity: `∑_{histories} C = ∏_j (∑_i P^{(i)}_j) = 1`, the product
of sums distributed over the ordered products. Note this consumes only
`sum_eq_one` of each decomposition. -/
theorem dkSet_exhaustive :
    ∀ L : List (ProjectiveDecomposition d), ∑ h : History L, classOp L h = 1
  | [] => by
    show ∑ _h : Unit, (1 : Matrix d d ℂ) = 1
    simp
  | σ :: L => by
    have ih := dkSet_exhaustive L
    show ∑ x : Fin σ.n × History L, classOp (σ :: L) x = 1
    rw [Fintype.sum_prod_type]
    simp_rw [classOp_cons]
    rw [← Fintype.sum_mul_sum, σ.sum_eq_one, ih, one_mul]

/-- Exhaustiveness at any state — the hypothesis shape the landed
records converse consumes. -/
theorem dkSet_exhaustive_mulVec (L : List (ProjectiveDecomposition d))
    (ψ : d → ℂ) :
    (∑ h : History L, classOp L h) *ᵥ ψ = ψ := by
  rw [dkSet_exhaustive, Matrix.one_mulVec]

/-! ## DK consistency

DK, gr-qc/9412067 (their `\decohgmh`, following Gell-Mann–Hartle):
`Tr(P^{(i_n)}_n ⋯ P^{(i_1)}_1 ρ_i P^{(j_1)}_1 ⋯ P^{(j_n)}_n ρ_f) =
δ_{i_1 j_1} ⋯ δ_{i_n j_n} p(i_1 … i_n)`, and: "When the conditions
[\decohgmh] hold, we say that the set of histories, S, is consistent."
Their footnote: "The term *medium decoherent*, coined by Gell-Mann and
Hartle, is used in the literature to describe sets satisfying
[\decohgmh]. *Weakly decoherent* sets satisfy only the real part of
[\decohgmh]." At pure `ρ_i = |ψ⟩⟨ψ|` and trivial `ρ_f = 1` the trace is
`⟨C_β ψ, C_α ψ⟩`, so DK's condition is exactly diagonality of the landed
decoherence functional. -/

/-- A DK set is **consistent** iff the induced class-operator family is
medium decoherent at the state — DK's definition, instantiated at pure
state and trivial final condition. -/
def DKConsistent (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ) : Prop :=
  MediumDecoherent (classOp L) ψ

/-- DK's history probability `p(h) = Tr(C_h ρ C_h†) = ⟨C_h ψ, C_h ψ⟩` —
the diagonal of the decoherence functional. -/
noncomputable def prob (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ)
    (h : History L) : ℂ :=
  decoherenceFunctional (classOp L) ψ h h

theorem prob_eq (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ)
    (h : History L) :
    prob L ψ h = star (branch L ψ h) ⬝ᵥ branch L ψ h := rfl

/-- "Non-zero probability" is "nonzero branch vector". -/
theorem prob_ne_zero_iff (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ)
    (h : History L) :
    prob L ψ h ≠ 0 ↔ branch L ψ h ≠ 0 := by
  rw [prob_eq, Ne, Ne, dotProduct_star_self_eq_zero]

theorem decoherenceFunctional_classOp_eq (L : List (ProjectiveDecomposition d))
    (ψ : d → ℂ) (α β : History L) :
    decoherenceFunctional (classOp L) ψ α β
      = star (branch L ψ β) ⬝ᵥ branch L ψ α := rfl

theorem decoherenceFunctional_zero_of_branch_left
    (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ) {α : History L}
    (β : History L) (h : branch L ψ α = 0) :
    decoherenceFunctional (classOp L) ψ α β = 0 := by
  rw [decoherenceFunctional_classOp_eq, h, dotProduct_zero]

theorem decoherenceFunctional_zero_of_branch_right
    (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ) (α : History L)
    {β : History L} (h : branch L ψ β = 0) :
    decoherenceFunctional (classOp L) ψ α β = 0 := by
  rw [decoherenceFunctional_classOp_eq, h, star_zero, zero_dotProduct]

/-! ## The automatic-records corollary

On DK's own domain — pure state, exhaustive projective histories, medium
decoherence — formal records are AUTOMATIC (Gell-Mann–Hartle 1995,
gr-qc/9509054: records "follow from medium decoherence and the
assumption of a pure state"). The two theorems below state this on the
DK structure by specializing the landed converse through
`dkSet_exhaustive`. Formal record existence therefore performs NO
selection among DK-consistent sets: it cannot distinguish any consistent
set from any other, and in particular cannot address DK's set-selection
problem. A record-based selection principle requires a strictly
stronger, physically restricted record notion (permanence,
accessibility, redundancy) — outside this module's scope. -/

/-- **Every pure-state DK-consistent set carries formal projective
records**: Hermitian, idempotent, mutually annihilating observables
correlated with the class operators at the state — the landed
`medium_implies_projective_records_of_exhaustive`, specialized through
`dkSet_exhaustive`. -/
theorem dkConsistent_projective_records
    (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ)
    (hcons : DKConsistent L ψ) :
    ∃ R : History L → Matrix d d ℂ,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α, R α * R α = R α) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∀ α, classOp L α *ᵥ ψ = R α *ᵥ ψ) :=
  medium_implies_projective_records_of_exhaustive (classOp L) ψ
    (dkSet_exhaustive_mulVec L ψ) hcons

/-- The full Gell-Mann–Hartle strong record package minus permanence
(complete: `∑ R = 1`), automatic on every DK-consistent set over a
nonempty space — the landed completeness-tier converse, specialized. -/
theorem dkConsistent_complete_records [Nonempty d]
    (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ)
    (hcons : DKConsistent L ψ) :
    ∃ R : History L → Matrix d d ℂ,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α, R α * R α = R α) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∑ α, R α = 1) ∧
      (∀ α, classOp L α *ᵥ ψ = R α *ᵥ ψ) :=
  medium_implies_complete_records_of_exhaustive (classOp L) ψ
    (dkSet_exhaustive_mulVec L ψ) hcons

/-! ## Extensions (DK §4, at the append position)

DK: "`S' = (ρ_i, ρ_f, {σ₁, …, σ_k, τ, σ_{k+1}, …, σ_n})` is a
*consistent extension* of a consistent set of histories
`S = (ρ_i, ρ_f, {σ₁, …, σ_n})` by the set of projections `τ = {Qⁱ}` if
`τ` satisfies [\conds] and `S'` is itself consistent. We say the
consistent extension `S'` is *trivial* if, for each history [...] in
`S`, at most one of the extended histories [...] has non-zero
probability. [...] We say a consistent set `S` is *maximally extended*
if it has no non-trivial consistent extension." Here extensions are
formalized at the append position (`τ` at the new latest time = `τ :: L`
in latest-first storage) — the case DK's Lemma 2 construction produces;
insertion at interior positions is a named non-goal. -/

/-- DK's *trivial* extension: every history of the base acquires at most
one nonzero-probability continuation. -/
def TrivialExtension (τ : ProjectiveDecomposition d)
    (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ) : Prop :=
  ∀ (h : History L) (i i' : Fin τ.n),
    branch (τ :: L) ψ (i, h) ≠ 0 → branch (τ :: L) ψ (i', h) ≠ 0 → i = i'

/-- A *non-trivial consistent extension*: the extended set is consistent
and some base history acquires at least two nonzero-probability
continuations. -/
def NontrivialExtension (τ : ProjectiveDecomposition d)
    (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ) : Prop :=
  DKConsistent (τ :: L) ψ ∧ ¬ TrivialExtension τ L ψ

/-- DK's *maximally extended*: no non-trivial consistent (append)
extension. -/
def MaximallyExtended (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ) :
    Prop :=
  ∀ τ : ProjectiveDecomposition d, DKConsistent (τ :: L) ψ →
    TrivialExtension τ L ψ

theorem base_branch_ne_zero_of_cons (τ : ProjectiveDecomposition d)
    (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ) {i : Fin τ.n}
    {h : History L} (hb : branch (τ :: L) ψ (i, h) ≠ 0) :
    branch L ψ h ≠ 0 := by
  intro h0
  exact hb (by rw [branch_cons, h0, Matrix.mulVec_zero])

/-- A nonzero-probability history has at least one nonzero-probability
continuation under ANY appended decomposition — its continuations sum to
its branch vector. -/
theorem exists_nonzero_continuation (τ : ProjectiveDecomposition d)
    (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ) {h : History L}
    (hb : branch L ψ h ≠ 0) :
    ∃ i : Fin τ.n, branch (τ :: L) ψ (i, h) ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hb
  have hsum : ∑ i : Fin τ.n, branch (τ :: L) ψ (i, h) = branch L ψ h := by
    simp_rw [branch_cons]
    rw [← Matrix.sum_mulVec, τ.sum_eq_one, Matrix.one_mulVec]
  rw [← hsum]
  exact Finset.sum_eq_zero fun i _ => hall i

/-- **Same-base-history continuations always decohere**: for ANY
appended decomposition, two distinct continuations of one base history
have vanishing decoherence functional — Hermiticity plus mutual
annihilation of `τ` alone. (This is why single-nonzero-branch toy sets
extend consistently for free; the genuinely constrained pairs of a
general extension are the cross-history ones.) -/
theorem extend_decoherence_same_base (τ : ProjectiveDecomposition d)
    (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ) (h : History L)
    {i i' : Fin τ.n} (hii : i ≠ i') :
    decoherenceFunctional (classOp (τ :: L)) ψ (i, h) (i', h) = 0 := by
  have hzero : τ.P i' * τ.P i = 0 := τ.orthogonal (Ne.symm hii)
  rw [decoherenceFunctional_classOp_eq, branch_cons, branch_cons,
    Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    (τ.isHermitian i').eq, hzero, Matrix.vecMul_zero, zero_dotProduct]

/-! ## The history cap (DK Lemma 1's counting core) -/

omit [DecidableEq d] in
/-- Nonzero pairwise-orthogonal vectors are linearly independent
(hand-rolled at the `dotProduct` grade this development lives at). -/
theorem linearIndependent_of_pairwise_orthogonal {ι : Type*}
    {v : ι → d → ℂ} (hnz : ∀ i, v i ≠ 0)
    (horth : ∀ i j, i ≠ j → star (v i) ⬝ᵥ v j = 0) :
    LinearIndependent ℂ v := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hdot : star (v i) ⬝ᵥ ∑ j ∈ s, g j • v j = 0 := by
    rw [hsum, dotProduct_zero]
  rw [dotProduct_sum] at hdot
  simp_rw [dotProduct_smul] at hdot
  rw [Finset.sum_eq_single_of_mem i hi
    (fun j _ hji => by rw [horth i j (Ne.symm hji), smul_zero])] at hdot
  rcases smul_eq_zero.mp hdot with h | h
  · exact h
  · exact absurd (dotProduct_star_self_eq_zero.mp h) (hnz i)

open scoped Classical in
/-- **The history cap** (the counting core of DK's Lemma 1 proof — "Thus
there can be no more than rn histories with non-zero probability" — at
the pure-state rank `r = 1`): a DK-consistent set has at most `dim`
histories of nonzero probability. Consistency makes the nonzero branch
vectors pairwise orthogonal, hence linearly independent, hence at most
`dim`-many. This is the history-COUNT cap from DK's proof, not their
length statement `k ≤ rn`. -/
theorem dkConsistent_card_nonzero_le (L : List (ProjectiveDecomposition d))
    (ψ : d → ℂ) (hcons : DKConsistent L ψ) :
    Fintype.card {h : History L // branch L ψ h ≠ 0} ≤ Fintype.card d := by
  have hli : LinearIndependent ℂ
      (fun h : {h : History L // branch L ψ h ≠ 0} => branch L ψ h.1) := by
    refine linearIndependent_of_pairwise_orthogonal (fun h => h.2) ?_
    intro a b hab
    exact hcons b.1 a.1 fun hba => hab (Subtype.ext hba.symm)
  have hcard := hli.fintype_card_le_finrank
  rwa [Module.finrank_fintype_fun_eq_card] at hcard

open scoped Classical in
/-- The cap, restated over the filtered history set. -/
theorem dkConsistent_filter_card_nonzero_le
    (L : List (ProjectiveDecomposition d)) (ψ : d → ℂ)
    (hcons : DKConsistent L ψ) :
    ((Finset.univ : Finset (History L)).filter
      fun h => branch L ψ h ≠ 0).card ≤ Fintype.card d := by
  rw [← Fintype.card_subtype]
  exact dkConsistent_card_nonzero_le L ψ hcons

open scoped Classical in
/-- **Saturation forces maximality** (the cheap direction of DK's
pure-case note: "a set is maximally extended if and only if it has n
histories of non-zero probability"): a DK-consistent set with exactly
`dim` nonzero-probability histories is maximally extended. Counting:
every nonzero base history keeps at least one nonzero continuation
(`exists_nonzero_continuation`), a non-trivial extension adds a second
somewhere, and the cap applied to the extended set bounds the total by
`dim`. The CONVERSE direction of DK's note — maximal forces exactly
`dim` — is the content of their general Lemma 2 and is deliberately not
claimed in this module (see `QuantumProfligacy.maximallyExtended_iff_card_eq`). -/
theorem maximallyExtended_of_card_eq (L : List (ProjectiveDecomposition d))
    (ψ : d → ℂ) (_hcons : DKConsistent L ψ)
    (hcard : Fintype.card {h : History L // branch L ψ h ≠ 0}
      = Fintype.card d) :
    MaximallyExtended L ψ := by
  intro τ hext
  by_contra htriv
  unfold TrivialExtension at htriv
  push Not at htriv
  obtain ⟨h₀, i, i', hbi, hbi', hii⟩ := htriv
  -- one nonzero continuation per nonzero base history, avoiding `i'` at `h₀`
  have hchoice : ∀ h : {h : History L // branch L ψ h ≠ 0},
      ∃ j : Fin τ.n,
        branch (τ :: L) ψ (j, h.1) ≠ 0 ∧ (h.1 = h₀ → j ≠ i') := by
    intro h
    by_cases hh : h.1 = h₀
    · exact ⟨i, by rw [hh]; exact hbi, fun _ => hii⟩
    · obtain ⟨j, hj⟩ := exists_nonzero_continuation τ L ψ h.2
      exact ⟨j, hj, fun hcontra => absurd hcontra hh⟩
  choose c hc1 hc2 using hchoice
  let F : {h : History L // branch L ψ h ≠ 0} ⊕ Unit →
      {x : History (τ :: L) // branch (τ :: L) ψ x ≠ 0} :=
    Sum.elim (fun h => ⟨(c h, h.1), hc1 h⟩) (fun _ => ⟨(i', h₀), hbi'⟩)
  have hFinj : Function.Injective F := by
    rintro (a | a) (b | b) hab
    · have h2 : a.1 = b.1 :=
        congrArg (fun x : {x : History (τ :: L) // branch (τ :: L) ψ x ≠ 0} =>
          (x.1 : Fin τ.n × History L).2) hab
      exact congrArg Sum.inl (Subtype.ext h2)
    · have h2 : a.1 = h₀ :=
        congrArg (fun x : {x : History (τ :: L) // branch (τ :: L) ψ x ≠ 0} =>
          (x.1 : Fin τ.n × History L).2) hab
      have h1 : c a = i' :=
        congrArg (fun x : {x : History (τ :: L) // branch (τ :: L) ψ x ≠ 0} =>
          (x.1 : Fin τ.n × History L).1) hab
      exact absurd h1 (hc2 a h2)
    · have h2 : b.1 = h₀ :=
        (congrArg (fun x : {x : History (τ :: L) // branch (τ :: L) ψ x ≠ 0} =>
          (x.1 : Fin τ.n × History L).2) hab).symm
      have h1 : c b = i' :=
        (congrArg (fun x : {x : History (τ :: L) // branch (τ :: L) ψ x ≠ 0} =>
          (x.1 : Fin τ.n × History L).1) hab).symm
      exact absurd h1 (hc2 b h2)
    · exact congrArg Sum.inr (Subsingleton.elim a b)
  have hle := Fintype.card_le_of_injective F hFinj
  rw [Fintype.card_sum, Fintype.card_unit, hcard] at hle
  have hcap := dkConsistent_card_nonzero_le (τ :: L) ψ hext
  omega

/-! ## Building blocks: rank-one decompositions -/

/-- The (unnormalized) rank-one operator `|u⟩⟨u|`. -/
noncomputable def outer (u : d → ℂ) : Matrix d d ℂ :=
  Matrix.vecMulVec u (star u)

omit [Fintype d] [DecidableEq d] in
theorem outer_isHermitian (u : d → ℂ) : (outer u).IsHermitian :=
  vecMulVec_star_self_isHermitian u

omit [DecidableEq d] in
theorem outer_mul_self {u : d → ℂ} (hu : star u ⬝ᵥ u = 1) :
    outer u * outer u = outer u := by
  rw [outer, Matrix.vecMulVec_mul_vecMulVec, hu, one_smul]

omit [DecidableEq d] in
theorem outer_mul_outer_of_orth {u v : d → ℂ} (huv : star u ⬝ᵥ v = 0) :
    outer u * outer v = 0 := by
  rw [outer, outer, Matrix.vecMulVec_mul_vecMulVec, huv, zero_smul,
    Matrix.vecMulVec_zero]

/-- `{|u⟩⟨u|, 1 − |u⟩⟨u|}` for a unit vector `u`: the two-cell
projective decomposition asking "is the system in state `u`?". -/
@[reducible] noncomputable def basisDecomposition (u : d → ℂ) (hu : star u ⬝ᵥ u = 1) :
    ProjectiveDecomposition d where
  n := 2
  P := ![outer u, 1 - outer u]
  isHermitian := by
    intro i
    fin_cases i
    · exact outer_isHermitian u
    · exact Matrix.isHermitian_one.sub (outer_isHermitian u)
  mul_delta := by
    have hPP := outer_mul_self hu
    have hP1 : outer u * (1 - outer u) = 0 := by
      rw [mul_sub, mul_one, hPP, sub_self]
    have h1P : (1 - outer u) * outer u = 0 := by
      rw [sub_mul, one_mul, hPP, sub_self]
    have h11 : (1 - outer u) * (1 - outer u) = 1 - outer u := by
      rw [mul_sub, mul_one, h1P, sub_zero]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hPP, hP1, h1P, h11]
  sum_eq_one := by
    rw [Fin.sum_univ_two]
    simp

/-- The **DK rotation shape**: an orthonormal pair `u, v` yields the
three-cell projective decomposition `{|u⟩⟨u|, |v⟩⟨v|, 1 − |u⟩⟨u| −
|v⟩⟨v|}` — the `{P₊, P₋, P₃}` of DK's Lemma 2 proof, at general `u, v`.
(A reusable brick: the general Lemma 2 mechanization can instantiate it
at any rotated branch pair.) -/
@[reducible] noncomputable def rotationDecomposition (u v : d → ℂ)
    (hu : star u ⬝ᵥ u = 1) (hv : star v ⬝ᵥ v = 1)
    (huv : star u ⬝ᵥ v = 0) : ProjectiveDecomposition d where
  n := 3
  P := ![outer u, outer v, 1 - outer u - outer v]
  isHermitian := by
    intro i
    fin_cases i
    · exact outer_isHermitian u
    · exact outer_isHermitian v
    · exact (Matrix.isHermitian_one.sub (outer_isHermitian u)).sub
        (outer_isHermitian v)
  mul_delta := by
    have hvu : star v ⬝ᵥ u = 0 := by
      rw [Matrix.star_dotProduct, huv, star_zero]
    have huu := outer_mul_self hu
    have hvv := outer_mul_self hv
    have huv0 : outer u * outer v = 0 := outer_mul_outer_of_orth huv
    have hvu0 : outer v * outer u = 0 := outer_mul_outer_of_orth hvu
    have huA : outer u * (1 - outer u - outer v) = 0 := by
      rw [mul_sub, mul_sub, mul_one, huu, huv0, sub_self, sub_zero]
    have hvA : outer v * (1 - outer u - outer v) = 0 := by
      rw [mul_sub, mul_sub, mul_one, hvu0, hvv, sub_zero, sub_self]
    have hAu : (1 - outer u - outer v) * outer u = 0 := by
      rw [sub_mul, sub_mul, one_mul, huu, hvu0, sub_self, sub_zero]
    have hAv : (1 - outer u - outer v) * outer v = 0 := by
      rw [sub_mul, sub_mul, one_mul, huv0, hvv, sub_zero, sub_self]
    have hAA : (1 - outer u - outer v) * (1 - outer u - outer v)
        = 1 - outer u - outer v := by
      rw [mul_sub, mul_sub, mul_one, hAu, hAv, sub_zero, sub_zero]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [huu, hvv, huv0, hvu0, huA, hvA, hAu, hAv, hAA]
  sum_eq_one := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    abel

/-! ## A kernel-checked instance of the Dowker–Kent construction
(PRL Lemma 2)

**Naming discipline, first**: this section is a kernel-checked INSTANCE
of the Dowker–Kent construction (Dowker–Kent PRL 75 (1995) 3038 /
J. Stat. Phys. 82 (1996) 1575, Lemma 2); it is NOT a mechanization of
Lemma 2 — the fully quantified theorem (every non-maximally-extended
pure-state consistent set admits, for each nonzero-probability history,
a continuous family of non-trivial extensions) is not proven here
(it is proven in `QtslAux.QuantumProfligacy`).

DK's Lemma 2, verbatim: "Let S be a set of consistent histories that is
not maximally extended, with a pure initial state ρ, and let H be either
finite-dimensional or separable. Then there exists a continuous family
of non-trivial extensions for each history in S with non-zero
probability." Their construction: "Choosing states |h_j⟩ and |e_k⟩, and
complex numbers z₁, z₂ with z₁*z₁ + z₂*z₂ = 1, we can define two
orthogonal states |φ₊⟩ = z₁|h_j⟩ + z₂*|e_k⟩, |φ₋⟩ = z₂|h_j⟩ − z₁*|e_k⟩.
Define projections P± = |φ±⟩⟨φ±|, P₃ = 1 − P₊ − P₋ which satisfy
[\conds], and let τ = {P₊, P₋, P₃}. Then S' = (ρ, {σ₁, …, σ_l, τ}) is a
non-trivial consistent extension of S. [...] Since there is a consistent
extension for every choice of z₁ and z₂, the lemma holds."

The instance here: `H = ℂ³`, base set the single decomposition
`{|e₀⟩⟨e₀|, 1 − |e₀⟩⟨e₀|}` at state `ψ₀ = e₀` — consistent, one
nonzero-probability history (branch `ψ₀` itself), not maximally
extended. The DK rotation is instantiated with `h_j = ψ₀`, `e_k = e₁`.
Deliverables: consistency of the appended extension for EVERY complex
parameter choice (DK's "every choice of z₁ and z₂"); non-triviality
whenever `z₁ ≠ 0` and `z₂ ≠ 0` (DK's implicit genericity made explicit:
at `z₁ = 0` or `z₂ = 0` the extension is trivial — one continuation
carries the whole branch); and the **continuous family** — here meaning:
the map `t ↦ dkFamily t` on the OPEN real interval `(0, π/2)` with
`(z₁, z₂) = (cos t, sin t)`, every member a non-trivial DK-consistent
extension, the map INJECTIVE on the interval (distinct parameters give
distinct extensions — no quotient is needed because both coordinates are
positive reals), and the projector entries CONTINUOUS in `t`. A finite
list of extensions would satisfy none of this; that is the bar the word
"continuous" must clear.

Per the automatic-records corollary above, **every member of this family
carries formal projective records** (`dkFamily_extension_records`) —
record existence does not thin the family: the construction mechanizes
the PROBLEM side of set selection (profligacy), not an answer. -/

/-- The toy state: `e₀ ∈ ℂ³`. -/
noncomputable def psi0 : Fin 3 → ℂ := ![1, 0, 0]

theorem psi0_unit : star psi0 ⬝ᵥ psi0 = 1 := by
  simp [psi0, dotProduct, Fin.sum_univ_three]

/-- The base decomposition `{|e₀⟩⟨e₀|, 1 − |e₀⟩⟨e₀|}`. -/
@[reducible] noncomputable def sigma0 : ProjectiveDecomposition (Fin 3) :=
  basisDecomposition psi0 psi0_unit

theorem outer_psi0_mulVec : outer psi0 *ᵥ psi0 = psi0 := by
  rw [outer, Matrix.vecMulVec_mulVec, psi0_unit]
  simp

/-- The surviving branch of the base set is the state itself. -/
theorem sigma0_branch_zero : branch [sigma0] psi0 (0, ()) = psi0 := by
  rw [branch_cons, branch_nil]
  show sigma0.P 0 *ᵥ psi0 = psi0
  have h0 : sigma0.P 0 = outer psi0 := rfl
  rw [h0, outer_psi0_mulVec]

/-- The other branch of the base set is zero. -/
theorem sigma0_branch_one : branch [sigma0] psi0 (1, ()) = 0 := by
  rw [branch_cons, branch_nil]
  show (1 - outer psi0) *ᵥ psi0 = 0
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, outer_psi0_mulVec, sub_self]

theorem psi0_ne_zero : psi0 ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [psi0] at h0

/-- The base set is DK-consistent: its only interference pairs involve
the zero branch. -/
theorem sigma0_consistent : DKConsistent [sigma0] psi0 := by
  intro α β hne
  obtain ⟨i, u⟩ := α
  obtain ⟨j, u'⟩ := β
  cases u; cases u'
  fin_cases i <;> fin_cases j
  · exact absurd rfl hne
  · exact decoherenceFunctional_zero_of_branch_right [sigma0] psi0 _
      sigma0_branch_one
  · exact decoherenceFunctional_zero_of_branch_left [sigma0] psi0 _
      sigma0_branch_one
  · exact absurd rfl hne

/-- DK's `|φ₊⟩ = z₁|h_j⟩ + z₂*|e_k⟩` at `h_j = e₀`, `e_k = e₁`. -/
noncomputable def phiPlus (z₁ z₂ : ℂ) : Fin 3 → ℂ := ![z₁, star z₂, 0]

/-- DK's `|φ₋⟩ = z₂|h_j⟩ − z₁*|e_k⟩` at `h_j = e₀`, `e_k = e₁`. -/
noncomputable def phiMinus (z₁ z₂ : ℂ) : Fin 3 → ℂ := ![z₂, -star z₁, 0]

section Rotation

variable {z₁ z₂ : ℂ} (hz : star z₁ * z₁ + star z₂ * z₂ = 1)

include hz in
theorem phiPlus_unit : star (phiPlus z₁ z₂) ⬝ᵥ phiPlus z₁ z₂ = 1 := by
  simp only [phiPlus, dotProduct, Fin.sum_univ_three, Pi.star_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, star_star, star_zero,
    mul_zero, add_zero]
  linear_combination hz

include hz in
theorem phiMinus_unit : star (phiMinus z₁ z₂) ⬝ᵥ phiMinus z₁ z₂ = 1 := by
  simp only [phiMinus, dotProduct, Fin.sum_univ_three, Pi.star_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, star_star, star_zero,
    star_neg, mul_zero, add_zero, mul_neg, neg_mul, neg_neg]
  linear_combination hz

/-- The load-bearing orthogonality — this is where the conjugate on `z₂`
in `φ₊` earns its keep: `star z₁ · z₂ − z₂ · star z₁ = 0`. -/
theorem phiPlus_orth_phiMinus :
    star (phiPlus z₁ z₂) ⬝ᵥ phiMinus z₁ z₂ = 0 := by
  simp only [phiPlus, phiMinus, dotProduct, Fin.sum_univ_three,
    Pi.star_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, star_star,
    star_zero, mul_zero, add_zero, mul_neg]
  ring

/-- The DK rotation `τ = {P₊, P₋, P₃}`, for any normalized parameter
pair. -/
@[reducible] noncomputable def dkRotation (z₁ z₂ : ℂ)
    (hz : star z₁ * z₁ + star z₂ * z₂ = 1) :
    ProjectiveDecomposition (Fin 3) :=
  rotationDecomposition (phiPlus z₁ z₂) (phiMinus z₁ z₂)
    (phiPlus_unit hz) (phiMinus_unit hz) phiPlus_orth_phiMinus

/-- The `P₊`-continuation of the surviving branch, at its top
component: `(P₊ ψ₀)₀ = z₁ · star z₁`. -/
theorem dkRotation_branch_plus_apply :
    branch (dkRotation z₁ z₂ hz :: [sigma0]) psi0 (0, (0, ())) 0
      = z₁ * star z₁ := by
  rw [branch_cons, sigma0_branch_zero]
  show (outer (phiPlus z₁ z₂) *ᵥ psi0) 0 = z₁ * star z₁
  simp [outer, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.vecMulVec_apply, phiPlus, psi0, Pi.star_apply]

/-- The `P₋`-continuation of the surviving branch, at its top
component: `(P₋ ψ₀)₀ = z₂ · star z₂`. -/
theorem dkRotation_branch_minus_apply :
    branch (dkRotation z₁ z₂ hz :: [sigma0]) psi0 (1, (0, ())) 0
      = z₂ * star z₂ := by
  rw [branch_cons, sigma0_branch_zero]
  show (outer (phiMinus z₁ z₂) *ᵥ psi0) 0 = z₂ * star z₂
  simp [outer, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.vecMulVec_apply, phiMinus, psi0, Pi.star_apply]

/-- **Appending the DK rotation preserves consistency, for EVERY
parameter choice** (DK: "there is a consistent extension for every
choice of z₁ and z₂"): same-base-history pairs decohere by mutual
annihilation (`extend_decoherence_same_base`), and every cross-history
pair involves the zero branch of the base set. -/
theorem dkRotation_consistent :
    DKConsistent (dkRotation z₁ z₂ hz :: [sigma0]) psi0 := by
  intro α β hne
  obtain ⟨i, jh⟩ := α
  obtain ⟨j, u⟩ := jh
  obtain ⟨i', jh'⟩ := β
  obtain ⟨j', u'⟩ := jh'
  cases u; cases u'
  by_cases hjj : j = j'
  · subst hjj
    have hii : i ≠ i' := by
      intro h
      exact hne (by rw [h])
    exact extend_decoherence_same_base _ _ _ _ hii
  · -- distinct base histories: one of them is the zero-branch history
    have hzb : ∀ k : Fin (dkRotation z₁ z₂ hz).n,
        branch (dkRotation z₁ z₂ hz :: [sigma0]) psi0 (k, (1, ())) = 0 := by
      intro k
      rw [branch_cons, sigma0_branch_one, Matrix.mulVec_zero]
    have hv1 : ((1 : Fin sigma0.n)).val = 1 := rfl
    have hcases : j = 1 ∨ j' = 1 := by
      have hb1 : j.val < 2 := j.isLt
      have hb2 : j'.val < 2 := j'.isLt
      have hb3 : j.val ≠ j'.val := fun h => hjj (Fin.ext h)
      rcases eq_or_ne j.val 1 with h | h
      · exact Or.inl (Fin.ext (by omega))
      · exact Or.inr (Fin.ext (by omega))
    rcases hcases with h | h
    · subst h
      exact decoherenceFunctional_zero_of_branch_left _ _ _ (hzb i)
    · subst h
      exact decoherenceFunctional_zero_of_branch_right _ _ _ (hzb i')

/-- **Non-triviality for every parameter choice with both coordinates
nonzero** (DK's implicit genericity, explicit): the surviving base
history acquires two nonzero-probability continuations, `P₊ψ₀` and
`P₋ψ₀`. -/
theorem dkRotation_nontrivial (h1 : z₁ ≠ 0) (h2 : z₂ ≠ 0) :
    NontrivialExtension (dkRotation z₁ z₂ hz) [sigma0] psi0 := by
  refine ⟨dkRotation_consistent hz, fun htriv => ?_⟩
  have hbp : branch (dkRotation z₁ z₂ hz :: [sigma0]) psi0 (0, (0, ())) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    rw [dkRotation_branch_plus_apply] at h0
    exact mul_ne_zero h1 (star_ne_zero.mpr h1) h0
  have hbm : branch (dkRotation z₁ z₂ hz :: [sigma0]) psi0 (1, (0, ())) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    rw [dkRotation_branch_minus_apply] at h0
    exact mul_ne_zero h2 (star_ne_zero.mpr h2) h0
  have h01 := htriv (0, ()) 0 1 hbp hbm
  have hv := congrArg Fin.val h01
  have hv0 : ((0 : Fin (dkRotation z₁ z₂ hz).n)).val = 0 := rfl
  have hv1 : ((1 : Fin (dkRotation z₁ z₂ hz).n)).val = 1 := rfl
  omega

end Rotation

/-- The 3-4-5 witness parameters are admissible. -/
theorem hz345 : star (3/5 : ℂ) * (3/5) + star (4/5 : ℂ) * (4/5) = 1 := by
  norm_num [Complex.star_def, map_div₀, map_ofNat]

/-- The base set is NOT maximally extended — witnessed by the DK
rotation at the rational point `(z₁, z₂) = (3/5, 4/5)`. -/
theorem sigma0_not_maximallyExtended : ¬ MaximallyExtended [sigma0] psi0 := by
  intro hmax
  exact (dkRotation_nontrivial hz345 (by norm_num) (by norm_num)).2
    (hmax _ (dkRotation_consistent hz345))

/-! ### The continuous family -/

/-- The real-interval slice of the DK rotation:
`(z₁, z₂) = (cos t, sin t)`. -/
@[reducible] noncomputable def dkFamily (t : ℝ) : ProjectiveDecomposition (Fin 3) :=
  dkRotation (Real.cos t) (Real.sin t)
    (by
      have hc : (star (↑(Real.cos t) : ℂ)) = (↑(Real.cos t) : ℂ) :=
        Complex.conj_ofReal _
      have hs : (star (↑(Real.sin t) : ℂ)) = (↑(Real.sin t) : ℂ) :=
        Complex.conj_ofReal _
      rw [hc, hs, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        ← Complex.ofReal_add, ← Complex.ofReal_one, Complex.ofReal_inj]
      linear_combination Real.sin_sq_add_cos_sq t)

/-- Every member of the family extends the base set consistently. -/
theorem dkFamily_consistent (t : ℝ) :
    DKConsistent (dkFamily t :: [sigma0]) psi0 :=
  dkRotation_consistent _

/-- Every member with parameter in the open interval `(0, π/2)` is a
non-trivial consistent extension. -/
theorem dkFamily_nontrivial {t : ℝ} (ht : t ∈ Set.Ioo 0 (Real.pi / 2)) :
    NontrivialExtension (dkFamily t) [sigma0] psi0 := by
  have hc : Real.cos t ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩).ne'
  have hs : Real.sin t ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi ht.1
      (by linarith [Real.pi_pos, ht.2])).ne'
  exact dkRotation_nontrivial _ (Complex.ofReal_ne_zero.mpr hc)
    (Complex.ofReal_ne_zero.mpr hs)

/-- **Record existence does not thin the family** (the anti-selection
point, enacted): every member of the continuous family, being an
exhaustive projective medium-consistent pure-state set, carries formal
projective records automatically. -/
theorem dkFamily_extension_records (t : ℝ) :
    ∃ R : History (dkFamily t :: [sigma0]) → Matrix (Fin 3) (Fin 3) ℂ,
      (∀ α, (R α).IsHermitian) ∧
      (∀ α, R α * R α = R α) ∧
      (∀ α β, α ≠ β → R α * R β = 0) ∧
      (∀ α, classOp (dkFamily t :: [sigma0]) α *ᵥ psi0 = R α *ᵥ psi0) :=
  dkConsistent_projective_records _ _ (dkFamily_consistent t)

/-- The probe entry: `(P₊)₀₀ = cos² t` (total on the structure, so
equality of decompositions transports it). -/
private noncomputable def probe (τ : ProjectiveDecomposition (Fin 3)) : ℂ :=
  if h : 0 < τ.n then τ.P ⟨0, h⟩ 0 0 else 0

private theorem probe_dkFamily (t : ℝ) :
    probe (dkFamily t) = (Real.cos t : ℂ) * (Real.cos t : ℂ) := by
  unfold probe
  rw [dif_pos (show 0 < (dkFamily t).n from Nat.succ_pos 2)]
  show phiPlus (Real.cos t) (Real.sin t) 0
      * (star (phiPlus (Real.cos t) (Real.sin t))) 0 = _
  simp only [phiPlus, Matrix.cons_val_zero, Pi.star_apply,
    Complex.star_def, Complex.conj_ofReal]

/-- **The family is injective on the open interval**: distinct
parameters give distinct decompositions (via strict antitonicity of
`cos²` there). No quotient is needed — with both coordinates positive
reals, distinct parameter values are visible in the projector entries
themselves. -/
theorem dkFamily_injOn : Set.InjOn dkFamily (Set.Ioo 0 (Real.pi / 2)) := by
  intro t ht t' ht' heq
  have hprobe := congrArg probe heq
  rw [probe_dkFamily, probe_dkFamily, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, Complex.ofReal_inj] at hprobe
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

/-- The family's projectors, unbundled onto plain matrix-valued
functions of the parameter (definitionally equal to the bundle's `P`
field — `dkFamily_P_eq`), so continuity statements need no dependent
indices. -/
noncomputable def familyProjectors (t : ℝ) : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![outer (phiPlus (Real.cos t) (Real.sin t)),
    outer (phiMinus (Real.cos t) (Real.sin t)),
    1 - outer (phiPlus (Real.cos t) (Real.sin t))
      - outer (phiMinus (Real.cos t) (Real.sin t))]

theorem dkFamily_P_eq (t : ℝ) : (dkFamily t).P = familyProjectors t := rfl

private theorem continuous_phiPlus_entry (a : Fin 3) :
    Continuous fun t => phiPlus (Real.cos t) (Real.sin t) a := by
  fin_cases a
  · exact Complex.continuous_ofReal.comp Real.continuous_cos
  · exact (Complex.continuous_ofReal.comp Real.continuous_sin).star
  · exact continuous_const

private theorem continuous_phiMinus_entry (a : Fin 3) :
    Continuous fun t => phiMinus (Real.cos t) (Real.sin t) a := by
  fin_cases a
  · exact Complex.continuous_ofReal.comp Real.continuous_sin
  · exact ((Complex.continuous_ofReal.comp Real.continuous_cos).star).neg
  · exact continuous_const

/-- **The family is continuous in its parameter**, entrywise: every
entry of every projector of `dkFamily t` is a continuous function of
`t`. Together with `dkFamily_injOn`, `dkFamily_consistent`, and
`dkFamily_nontrivial` this cashes DK's phrase "a continuous family of
non-trivial extensions" for this instance. -/
theorem dkFamily_continuous (i : Fin 3) (a b : Fin 3) :
    Continuous fun t => familyProjectors t i a b := by
  have hp : ∀ a b : Fin 3, Continuous fun t =>
      outer (phiPlus (Real.cos t) (Real.sin t)) a b := by
    intro a b
    simp only [outer, Matrix.vecMulVec_apply, Pi.star_apply]
    exact (continuous_phiPlus_entry a).mul (continuous_phiPlus_entry b).star
  have hm : ∀ a b : Fin 3, Continuous fun t =>
      outer (phiMinus (Real.cos t) (Real.sin t)) a b := by
    intro a b
    simp only [outer, Matrix.vecMulVec_apply, Pi.star_apply]
    exact (continuous_phiMinus_entry a).mul (continuous_phiMinus_entry b).star
  fin_cases i
  · exact hp a b
  · exact hm a b
  · exact (continuous_const.sub (hp a b)).sub (hm a b)

end QuantumConsistentSets

end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumConsistentSets.dkSet_exhaustive
#print axioms Qtsl.QuantumConsistentSets.dkConsistent_projective_records
#print axioms Qtsl.QuantumConsistentSets.dkConsistent_complete_records
#print axioms Qtsl.QuantumConsistentSets.extend_decoherence_same_base
#print axioms Qtsl.QuantumConsistentSets.exists_nonzero_continuation
#print axioms Qtsl.QuantumConsistentSets.linearIndependent_of_pairwise_orthogonal
#print axioms Qtsl.QuantumConsistentSets.dkConsistent_card_nonzero_le
#print axioms Qtsl.QuantumConsistentSets.dkConsistent_filter_card_nonzero_le
#print axioms Qtsl.QuantumConsistentSets.maximallyExtended_of_card_eq
#print axioms Qtsl.QuantumConsistentSets.sigma0_consistent
#print axioms Qtsl.QuantumConsistentSets.dkRotation_consistent
#print axioms Qtsl.QuantumConsistentSets.dkRotation_nontrivial
#print axioms Qtsl.QuantumConsistentSets.sigma0_not_maximallyExtended
#print axioms Qtsl.QuantumConsistentSets.dkFamily_consistent
#print axioms Qtsl.QuantumConsistentSets.dkFamily_nontrivial
#print axioms Qtsl.QuantumConsistentSets.dkFamily_extension_records
#print axioms Qtsl.QuantumConsistentSets.dkFamily_injOn
#print axioms Qtsl.QuantumConsistentSets.dkFamily_continuous
