/-
Copyright (c) 2026 The maitria coalition. All rights reserved.
Released under Apache 2.0 / MIT dual license.
-/
import QtslAux.QuantumTransport

/-! # Coarse-graining: atom-lattice merging as the D-form's covariant face

The transport module (`QtslAux.QuantumTransport`) carried the
base-compatibility clause along
order-ISOMORPHISMS and fenced the rest: "coarse-graining (bi-additive
pushforward along non-injective maps, the clause's other half) is out of
leg scope." This module is that other half, kernel-checked at finite
grade: merging atoms of the alternative-lattice along ANY map
`f : ι → κ` of finite indices pushes a quantum measure forward.

* **The pushforward is a submatrix of the landed event Gram**
  (`QuantumMeasure.pushforward`): the coarse atom `c`'s Gram row IS the
  fine event `f⁻¹(c)`'s row in `eventGram` — `gram :=
  Q.eventGram.submatrix (fiber f) (fiber f)`. Positivity (hermiticity
  included) is therefore a one-line corollary of
  `eventGram_posSemidef`, because positive semidefiniteness is
  submatrix-hereditary along arbitrary reindexings — injectivity is not
  required, which is exactly why non-injective merges ride free.
  Normalization is the fiber-partition regroup. The Sorkin axioms
  (hermitian, bi-additive, strongly positive, normalized, grade-3 sum
  rule) hold because the pushforward IS a `QuantumMeasure` — the axioms
  are theorems of the structure. **Surjectivity is consumed nowhere**: a
  non-surjective `f` merely creates empty fibers = null coarse atoms,
  already priced into the D-form tier (`span_atomClasses`).

* **The event algebra transfers by preimage**: coarse events pull back
  to fine events (`fiberEvent`), and the event form, Sorkin measure, and
  grade-2 interference of the pushforward are the fine values at the
  preimage events (`pushforward_eventForm`, `pushforward_sorkinMeasure`,
  `pushforward_interference` — the last unconditionally: preimage
  commutes with union, so no disjointness hypothesis is needed).

* **Variance, stated by theorems**: transport (`QuantumMeasure.map`)
  reindexes the Gram by PREcomposition with `e.symm` — the iso case.
  The pushforward is the COVARIANT face at general maps: functorial
  (`pushforward_id`, `pushforward_comp`), and its restriction to the
  core recovers transport exactly (`pushforward_equiv : Q.pushforward
  ⇑e = Q.map e` — fibers are singletons). Mixed composites
  (`map_pushforward`, `pushforward_map`) glue the two modules.

* **Records coarsen** (`coarsenFamily f R c := ∑_{a ∈ f⁻¹(c)} R a`):
  hermiticity, mutual orthogonality, correlation, and completeness are
  each preserved consuming ONLY their own hypothesis
  (`coarsenFamily_isHermitian`/`_orthogonal`/`_correlated`/`_complete`);
  idempotence is preserved too (`coarsenFamily_idem`) but consumes
  orthogonality as well — and that consumption is witnessed
  non-droppable (`coarsenFamily_idem_needs_orthogonality`: the doubled
  projector `![Pz0, Pz0]` under the total merge has `(Pz0 + Pz0)² =
  4·Pz0 ≠ 2·Pz0`). The precise failure condition: coarsening a family
  that is idempotent but NOT mutually orthogonal breaks idempotence;
  everything else survives unconditionally. The full GMH strong package
  therefore descends to every coarse-graining
  (`strong_records_coarsen`).

* **Conservativity commutes with coarse-graining**: the classical
  embedding of a coarsened row equals the coarsening of the classical
  embedding (`classical_pushforward`; the naturality-square corner
  chase is `classicalization_pushforward_comm`); presentations coarsen
  through the decoherence functional — the coarse family's decoherence
  functional is the fiber-block sum of the fine one
  (`decoherenceFunctional_coarsenFamily`), so **coarse-graining
  commutes with compilation** (`pushforward_ofPresentation`) and a
  recorded presentation's pushforward is classical
  (`records_conservativity_pushforward`).

* **Diagonality is preserved forward, not reflected**
  (`pushforward_isDiagonal`, one-directional): the converse fails
  non-vacuously — **decoherence by coarse-graining**. `mergeMeasure`,
  a strictly quantum measure on `Fin 3` (branch vectors `(1,0)`,
  `(−1,4/5)`, `(3/5,0)` at the state `(1,0)`), interferes at the pair
  `(0,2)` with value `3/5`; merged along `![0,0,1] : Fin 3 → Fin 2` the
  off-diagonal blocks cancel (`3/5 − 3/5 = 0`) and the coarse measure
  is exactly diagonal (`mergeMeasure_pushforward_isDiagonal`), with
  Born row `(16/25, 9/25)` (`mergeMeasure_pushforward_probRow`) — on a
  coarse index of size two, away from the subsingleton-vacuity cheap
  case.

Scope fences inherited from the record tier: finite indices, matrix
grade, pure states in the presentations; continuum coarse-grainings
(Isham–Linden towers) are out of scope; record permanence remains
unclaimed. -/

namespace Qtsl

namespace QuantumCoarseGraining

open Matrix QuantumRecords QuantumDForm QuantumTransport
open scoped ComplexOrder

variable {ι κ μ' : Type*} [Fintype ι] [Fintype κ] [Fintype μ']

/-! ## Fibers: the preimage bookkeeping -/

/-- The fiber of a coarse atom: the fine event it merges. -/
def fiber [DecidableEq κ] (f : ι → κ) (c : κ) : Finset ι :=
  Finset.univ.filter fun a => f a = c

omit [Fintype κ] in
@[simp] theorem mem_fiber [DecidableEq κ] (f : ι → κ) {a : ι} {c : κ} :
    a ∈ fiber f c ↔ f a = c := by
  simp [fiber]

/-- The preimage of a coarse event: the fine event a coarse event pulls
back to. -/
def fiberEvent [DecidableEq κ] (f : ι → κ) (A : Finset κ) : Finset ι :=
  Finset.univ.filter fun a => f a ∈ A

omit [Fintype κ] in
@[simp] theorem mem_fiberEvent [DecidableEq κ] (f : ι → κ) {a : ι}
    {A : Finset κ} : a ∈ fiberEvent f A ↔ f a ∈ A := by
  simp [fiberEvent]

theorem fiberEvent_univ [DecidableEq κ] (f : ι → κ) :
    fiberEvent f Finset.univ = Finset.univ := by
  ext a
  simp

omit [Fintype κ] in
/-- Preimage commutes with union — the reason interference transfers
without a disjointness hypothesis. -/
theorem fiberEvent_union [DecidableEq ι] [DecidableEq κ] (f : ι → κ)
    (A B : Finset κ) :
    fiberEvent f (A ∪ B) = fiberEvent f A ∪ fiberEvent f B := by
  ext a
  simp [Finset.mem_union]

omit [Fintype μ'] in
/-- The preimage of a fiber is the fiber of the composite. -/
theorem fiberEvent_fiber [DecidableEq κ] [DecidableEq μ'] (f : ι → κ)
    (g : κ → μ') (m : μ') :
    fiberEvent f (fiber g m) = fiber (g ∘ f) m := by
  ext a
  simp [Function.comp]

omit [Fintype κ] in
/-- Summing fiberwise over a coarse event is summing over its preimage
— the single-index regroup workhorse (generic in the codomain: it
serves ℂ, ℝ, and matrix sums alike). -/
theorem sum_fiberEvent {M : Type*} [AddCommMonoid M] [DecidableEq κ]
    (f : ι → κ) (A : Finset κ) (h : ι → M) :
    ∑ c ∈ A, ∑ a ∈ fiber f c, h a = ∑ a ∈ fiberEvent f A, h a := by
  have hfib : ∀ c ∈ A,
      fiber f c = (fiberEvent f A).filter fun a => f a = c := by
    intro c hc
    ext a
    simp only [mem_fiber, Finset.mem_filter, mem_fiberEvent]
    exact ⟨fun hfa => ⟨hfa ▸ hc, hfa⟩, And.right⟩
  calc ∑ c ∈ A, ∑ a ∈ fiber f c, h a
      = ∑ c ∈ A, ∑ a ∈ (fiberEvent f A).filter (fun a => f a = c), h a :=
        Finset.sum_congr rfl fun c hc => by rw [hfib c hc]
    _ = ∑ a ∈ fiberEvent f A, h a :=
        Finset.sum_fiberwise_of_maps_to
          (fun a ha => (mem_fiberEvent f).mp ha) h

/-- The fibers partition the fine index. -/
theorem sum_fiber {M : Type*} [AddCommMonoid M] [DecidableEq κ]
    (f : ι → κ) (h : ι → M) :
    ∑ c, ∑ a ∈ fiber f c, h a = ∑ a, h a := by
  rw [sum_fiberEvent f Finset.univ h, fiberEvent_univ]

omit [Fintype κ] in
/-- The double-index regroup: fiber-block double sums over coarse
events are double sums over the preimage events. -/
private theorem sum_sum_fiberEvent {M : Type*} [AddCommMonoid M]
    [DecidableEq κ] (f : ι → κ) (A B : Finset κ) (g : ι → ι → M) :
    ∑ c ∈ A, ∑ c' ∈ B, ∑ a ∈ fiber f c, ∑ b ∈ fiber f c', g a b
      = ∑ a ∈ fiberEvent f A, ∑ b ∈ fiberEvent f B, g a b := by
  calc ∑ c ∈ A, ∑ c' ∈ B, ∑ a ∈ fiber f c, ∑ b ∈ fiber f c', g a b
      = ∑ c ∈ A, ∑ a ∈ fiber f c, ∑ c' ∈ B, ∑ b ∈ fiber f c', g a b :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c ∈ A, ∑ a ∈ fiber f c, ∑ b ∈ fiberEvent f B, g a b :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
          sum_fiberEvent f B fun b => g a b
    _ = ∑ a ∈ fiberEvent f A, ∑ b ∈ fiberEvent f B, g a b :=
        sum_fiberEvent f A fun a => ∑ b ∈ fiberEvent f B, g a b

/-! ## The pushforward: a submatrix of the event Gram -/

/-- **Coarse-graining pushforward**: merging atoms along `f : ι → κ`
pushes a quantum measure forward — the coarse Gram entry at `(c, c')`
is the fine event form at the fibers, i.e. the coarse Gram matrix IS
the `(fiber f, fiber f)`-submatrix of the landed event-level Gram
matrix. Positivity is inherited (PSD is submatrix-hereditary along
arbitrary reindexings — no injectivity demanded, so non-injective
merges and even non-surjective `f` ride free: empty fibers are null
coarse atoms); normalization is the fiber-partition regroup. -/
noncomputable def _root_.Qtsl.QuantumDForm.QuantumMeasure.pushforward
    [DecidableEq ι] [DecidableEq κ] (f : ι → κ) (Q : QuantumMeasure ι) :
    QuantumMeasure κ where
  gram := Q.eventGram.submatrix (fiber f) (fiber f)
  posSemidef := Q.eventGram_posSemidef.submatrix (fiber f)
  normalized := by
    show ∑ c, ∑ c', Q.eventForm (fiber f c) (fiber f c') = 1
    have h := sum_sum_fiberEvent f Finset.univ Finset.univ
      fun a b => Q.gram a b
    simp only [QuantumMeasure.eventForm]
    rw [h, fiberEvent_univ]
    exact Q.normalized

variable [DecidableEq ι] [DecidableEq κ]

@[simp] theorem pushforward_gram (f : ι → κ) (Q : QuantumMeasure ι)
    (c c' : κ) :
    (Q.pushforward f).gram c c' = Q.eventForm (fiber f c) (fiber f c') :=
  rfl

/-! ## The event algebra transfers by preimage -/

theorem pushforward_eventForm (f : ι → κ) (Q : QuantumMeasure ι)
    (A B : Finset κ) :
    (Q.pushforward f).eventForm A B
      = Q.eventForm (fiberEvent f A) (fiberEvent f B) := by
  simp only [QuantumMeasure.eventForm, pushforward_gram]
  exact sum_sum_fiberEvent f A B fun a b => Q.gram a b

theorem pushforward_sorkinMeasure (f : ι → κ) (Q : QuantumMeasure ι)
    (A : Finset κ) :
    (Q.pushforward f).sorkinMeasure A
      = Q.sorkinMeasure (fiberEvent f A) :=
  pushforward_eventForm f Q A A

/-- Grade-2 interference transfers to the preimage events —
unconditionally: preimage commutes with union, so no disjointness
hypothesis is consumed. -/
theorem pushforward_interference (f : ι → κ) (Q : QuantumMeasure ι)
    (A B : Finset κ) :
    (Q.pushforward f).interference A B
      = Q.interference (fiberEvent f A) (fiberEvent f B) := by
  simp only [QuantumMeasure.interference, pushforward_sorkinMeasure,
    fiberEvent_union]

/-! ## Diagonality is preserved forward -/

/-- Coarse-graining preserves diagonality: distinct coarse atoms have
disjoint fibers, so every Gram term in an off-diagonal block is an
off-diagonal fine entry. One-directional — the converse fails
non-vacuously at `mergeMeasure` below (decoherence by
coarse-graining). -/
theorem pushforward_isDiagonal (f : ι → κ) (Q : QuantumMeasure ι)
    (hd : Q.IsDiagonal) : (Q.pushforward f).IsDiagonal := by
  intro c c' hcc'
  show Q.eventForm (fiber f c) (fiber f c') = 0
  refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
  refine hd fun hab => hcc' ?_
  rw [← (mem_fiber f).mp ha, hab, (mem_fiber f).mp hb]

theorem pushforward_probRow (f : ι → κ) (Q : QuantumMeasure ι) (c : κ) :
    (Q.pushforward f).probRow c = (Q.sorkinMeasure (fiber f c)).re :=
  rfl

/-- For a diagonal fine measure, the coarse probability row is the
fiber sum of the fine row. -/
theorem pushforward_probRow_of_isDiagonal (f : ι → κ)
    (Q : QuantumMeasure ι) (hd : Q.IsDiagonal) (c : κ) :
    (Q.pushforward f).probRow c = ∑ a ∈ fiber f c, Q.probRow a := by
  show (Q.eventForm (fiber f c) (fiber f c)).re = _
  rw [Q.isDiagonal_eventForm_inter hd, Finset.inter_self,
    Complex.re_sum]
  exact Finset.sum_congr rfl fun a _ => Complex.ofReal_re _

/-! ## Conservativity commutes with coarse-graining -/

/-- **Naturality of the classical embedding**: the classical embedding
of a coarsened row equals the coarsening of the classical embedding. -/
theorem classical_pushforward (f : ι → κ) (p : ι → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    (QuantumMeasure.classical p hp hsum).pushforward f
      = QuantumMeasure.classical (fun c => ∑ a ∈ fiber f c, p a)
          (fun c => Finset.sum_nonneg fun a _ => hp a)
          (by rw [sum_fiber f p]; exact hsum) := by
  refine QuantumMeasure.ext ?_
  ext c c'
  rw [pushforward_gram, QuantumMeasure.classical_eventForm,
    QuantumMeasure.classical_gram]
  by_cases h : c = c'
  · subst h
    rw [Finset.inter_self, Matrix.diagonal_apply_eq,
      ← Complex.ofReal_sum]
  · rw [Matrix.diagonal_apply_ne _ h]
    refine Finset.sum_eq_zero fun a ha => absurd ?_ h
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp ha
    rw [← (mem_fiber f).mp h1, (mem_fiber f).mp h2]

/-- A coarsened diagonal measure is the classical embedding of the
fiber-summed probability row. -/
theorem pushforward_isDiagonal_eq_classical (f : ι → κ)
    (Q : QuantumMeasure ι) (hd : Q.IsDiagonal) :
    Q.pushforward f
      = QuantumMeasure.classical (fun c => ∑ a ∈ fiber f c, Q.probRow a)
          (fun c => Finset.sum_nonneg fun a _ => Q.probRow_nonneg a)
          (by rw [sum_fiber f Q.probRow]; exact Q.probRow_sum hd) :=
  (congrArg (QuantumMeasure.pushforward f)
    (Q.isDiagonal_eq_classical hd)).trans
    (classical_pushforward f Q.probRow Q.probRow_nonneg
      (Q.probRow_sum hd))

/-- **Conservativity commutes with coarse-graining**:
classicalize-then-coarsen equals coarsen-then-classicalize — the
naturality square of `isDiagonal_eq_classical` along `f`. -/
theorem classicalization_pushforward_comm (f : ι → κ)
    (Q : QuantumMeasure ι) (hd : Q.IsDiagonal) :
    (QuantumMeasure.classical Q.probRow Q.probRow_nonneg
        (Q.probRow_sum hd)).pushforward f
      = QuantumMeasure.classical ((Q.pushforward f).probRow)
          ((Q.pushforward f).probRow_nonneg)
          ((Q.pushforward f).probRow_sum
            (pushforward_isDiagonal f Q hd)) :=
  (congrArg (QuantumMeasure.pushforward f)
    (Q.isDiagonal_eq_classical hd)).symm.trans
    ((Q.pushforward f).isDiagonal_eq_classical
      (pushforward_isDiagonal f Q hd))

/-! ## Variance: the covariant face, composed with transport

Transport reindexes the Gram by PREcomposition with `e.symm` (the iso
case); the pushforward is the covariant face at general maps —
functorial, with transport recovered on the core. -/

theorem pushforward_id (Q : QuantumMeasure ι) :
    Q.pushforward id = Q := by
  refine QuantumMeasure.ext ?_
  ext a b
  have hfib : ∀ c : ι, fiber (id : ι → ι) c = {c} := fun c => by
    ext x
    simp
  rw [pushforward_gram, hfib, hfib]
  simp [QuantumMeasure.eventForm]

/-- **Transport is the core restriction of the pushforward**: along an
equivalence the fibers are singletons and the pushforward is the
transport map. -/
theorem pushforward_equiv (e : ι ≃ κ) (Q : QuantumMeasure ι) :
    Q.pushforward ⇑e = Q.map e := by
  refine QuantumMeasure.ext ?_
  ext c c'
  have hfib : ∀ c : κ, fiber ⇑e c = {e.symm c} := fun c => by
    ext a
    simp [Equiv.apply_eq_iff_eq_symm_apply]
  rw [pushforward_gram, hfib, hfib]
  simp [QuantumMeasure.eventForm]

/-- Functoriality: coarse-graining in stages is coarse-graining along
the composite. -/
theorem pushforward_comp [DecidableEq μ'] (f : ι → κ) (g : κ → μ')
    (Q : QuantumMeasure ι) :
    Q.pushforward (g ∘ f) = (Q.pushforward f).pushforward g := by
  refine QuantumMeasure.ext ?_
  ext m m'
  rw [pushforward_gram, pushforward_gram, pushforward_eventForm,
    fiberEvent_fiber, fiberEvent_fiber]

theorem map_pushforward [DecidableEq μ'] (e : ι ≃ κ) (g : κ → μ')
    (Q : QuantumMeasure ι) :
    (Q.map e).pushforward g = Q.pushforward (g ∘ ⇑e) := by
  rw [← pushforward_equiv, ← pushforward_comp]

theorem pushforward_map [DecidableEq μ'] (f : ι → κ) (e : κ ≃ μ')
    (Q : QuantumMeasure ι) :
    (Q.pushforward f).map e = Q.pushforward (⇑e ∘ f) := by
  rw [← pushforward_equiv, ← pushforward_comp]

/-! ## Records coarsen -/

section Records

variable {d : Type*} [Fintype d]

/-- Coarsening a family of operators: the coarse atom's operator is the
fiber sum. -/
noncomputable def coarsenFamily (f : ι → κ) (R : ι → Matrix d d ℂ)
    (c : κ) : Matrix d d ℂ :=
  ∑ a ∈ fiber f c, R a

omit [Fintype κ] [DecidableEq ι] [Fintype d] in
/-- Hermiticity coarsens (consuming only hermiticity). -/
theorem coarsenFamily_isHermitian (f : ι → κ) {R : ι → Matrix d d ℂ}
    (hherm : ∀ a, (R a).IsHermitian) (c : κ) :
    (coarsenFamily f R c).IsHermitian := by
  show (∑ a ∈ fiber f c, R a)ᴴ = ∑ a ∈ fiber f c, R a
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun a _ => (hherm a).eq

omit [Fintype κ] [DecidableEq ι] in
/-- Mutual orthogonality coarsens (consuming only orthogonality):
distinct fibers are disjoint, so every cross term is an off-diagonal
product. -/
theorem coarsenFamily_orthogonal (f : ι → κ) {R : ι → Matrix d d ℂ}
    (horth : ∀ a b, a ≠ b → R a * R b = 0) {c c' : κ} (h : c ≠ c') :
    coarsenFamily f R c * coarsenFamily f R c' = 0 := by
  rw [coarsenFamily, coarsenFamily, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
  refine horth a b fun hab => h ?_
  rw [← (mem_fiber f).mp ha, hab, (mem_fiber f).mp hb]

omit [Fintype κ] [DecidableEq ι] in
/-- Correlation coarsens (consuming only correlation). -/
theorem coarsenFamily_correlated (f : ι → κ) {C R : ι → Matrix d d ℂ}
    {ψ : d → ℂ} (hrec : ∀ a, C a *ᵥ ψ = R a *ᵥ ψ) (c : κ) :
    coarsenFamily f C c *ᵥ ψ = coarsenFamily f R c *ᵥ ψ := by
  rw [coarsenFamily, coarsenFamily, Matrix.sum_mulVec, Matrix.sum_mulVec]
  exact Finset.sum_congr rfl fun a _ => hrec a

omit [DecidableEq ι] [Fintype d] in
/-- Completeness coarsens (consuming only completeness): the fibers
partition the fine index. -/
theorem coarsenFamily_complete [DecidableEq d] (f : ι → κ)
    {R : ι → Matrix d d ℂ} (hcomp : ∑ a, R a = 1) :
    ∑ c, coarsenFamily f R c = 1 := by
  simp only [coarsenFamily]
  rw [sum_fiber f R]
  exact hcomp

omit [Fintype κ] [DecidableEq ι] in
/-- Idempotence coarsens — but consumes ORTHOGONALITY as well as
idempotence: within a fiber, cross terms die by orthogonality and the
diagonal survives by idempotence. The orthogonality hypothesis is
witnessed non-droppable by `coarsenFamily_idem_needs_orthogonality`
below. -/
theorem coarsenFamily_idem (f : ι → κ) {R : ι → Matrix d d ℂ}
    (hidem : ∀ a, R a * R a = R a)
    (horth : ∀ a b, a ≠ b → R a * R b = 0) (c : κ) :
    coarsenFamily f R c * coarsenFamily f R c = coarsenFamily f R c := by
  rw [coarsenFamily, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.sum_eq_single_of_mem a ha
    fun b _ hba => horth a b fun hab => hba (hab ▸ rfl)]
  exact hidem a

omit [DecidableEq ι] in
/-- **The GMH strong record package descends to every
coarse-graining**: a Hermitian, idempotent, mutually orthogonal,
complete, correlated family on the fine lattice induces one on the
coarse. -/
theorem strong_records_coarsen [DecidableEq d] (f : ι → κ)
    {C R : ι → Matrix d d ℂ} {ψ : d → ℂ}
    (hherm : ∀ a, (R a).IsHermitian)
    (hidem : ∀ a, R a * R a = R a)
    (horth : ∀ a b, a ≠ b → R a * R b = 0)
    (hcomp : ∑ a, R a = 1)
    (hrec : ∀ a, C a *ᵥ ψ = R a *ᵥ ψ) :
    (∀ c, (coarsenFamily f R c).IsHermitian) ∧
    (∀ c, coarsenFamily f R c * coarsenFamily f R c
      = coarsenFamily f R c) ∧
    (∀ c c', c ≠ c' → coarsenFamily f R c * coarsenFamily f R c' = 0) ∧
    (∑ c, coarsenFamily f R c = 1) ∧
    (∀ c, coarsenFamily f C c *ᵥ ψ = coarsenFamily f R c *ᵥ ψ) :=
  ⟨coarsenFamily_isHermitian f hherm,
   coarsenFamily_idem f hidem horth,
   fun _ _ h => coarsenFamily_orthogonal f horth h,
   coarsenFamily_complete f hcomp,
   coarsenFamily_correlated f hrec⟩

omit [Fintype κ] [DecidableEq ι] in
/-- The coarse family's decoherence functional is the fiber-block sum
of the fine one. -/
theorem decoherenceFunctional_coarsenFamily (f : ι → κ)
    (C : ι → Matrix d d ℂ) (ψ : d → ℂ) (c c' : κ) :
    decoherenceFunctional (coarsenFamily f C) ψ c c'
      = ∑ a ∈ fiber f c, ∑ b ∈ fiber f c',
          decoherenceFunctional C ψ a b := by
  simp only [decoherenceFunctional, coarsenFamily, Matrix.sum_mulVec,
    star_sum, sum_dotProduct, dotProduct_sum]

/-- **Coarse-graining commutes with compilation**: the pushforward of a
presentation's quantum measure is the quantum measure of the coarsened
presentation — the state does not move; only the family's atoms
merge. -/
theorem pushforward_ofPresentation (f : ι → κ) (C : ι → Matrix d d ℂ)
    (ψ : d → ℂ)
    (hnorm : ∑ α, ∑ β, decoherenceFunctional C ψ α β = 1) :
    (QuantumMeasure.ofPresentation C ψ hnorm).pushforward f
      = QuantumMeasure.ofPresentation (coarsenFamily f C) ψ
          (by
            simp only [decoherenceFunctional_coarsenFamily]
            have h := sum_sum_fiberEvent f Finset.univ Finset.univ
              fun a b => decoherenceFunctional C ψ a b
            rw [h, fiberEvent_univ]
            exact hnorm) := by
  refine QuantumMeasure.ext ?_
  ext c c'
  rw [pushforward_gram]
  show (QuantumMeasure.ofPresentation C ψ hnorm).eventForm
      (fiber f c) (fiber f c')
    = decoherenceFunctional (coarsenFamily f C) ψ c c'
  rw [decoherenceFunctional_coarsenFamily]
  simp only [QuantumMeasure.eventForm, QuantumMeasure.ofPresentation_gram]

/-- **Records coarsen, at measure grade**: a recorded presentation's
pushforward quantum measure is (equal to) a classical measure — the
record triple coarsens (`coarsenFamily`), and `records_conservativity`
fires on the coarse side. -/
theorem records_conservativity_pushforward (f : ι → κ)
    (C R : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hnorm : ∑ α, ∑ β, decoherenceFunctional C ψ α β = 1)
    (hherm : ∀ a, (R a).IsHermitian)
    (horth : ∀ a b, a ≠ b → R a * R b = 0)
    (hrec : ∀ a, C a *ᵥ ψ = R a *ᵥ ψ) :
    ∃ (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1),
      (QuantumMeasure.ofPresentation C ψ hnorm).pushforward f
        = QuantumMeasure.classical p hp hs := by
  rw [pushforward_ofPresentation]
  exact QuantumMeasure.records_conservativity
    (R := coarsenFamily f R) _
    (coarsenFamily_isHermitian f hherm)
    (fun c c' h => coarsenFamily_orthogonal f horth h)
    (coarsenFamily_correlated f hrec)

end Records

/-! ## Witnesses -/

section Toys

/-- `Pz0` is idempotent (private re-proof; the completeness module's
copy is private there). -/
private theorem Pz0_idem : Pz0 * Pz0 = Pz0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pz0, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Idempotence does not coarsen without orthogonality**: the doubled
projector `![Pz0, Pz0]` is Hermitian and idempotent atomwise, but its
total merge sums to `Pz0 + Pz0`, whose square is `4·Pz0 ≠ 2·Pz0` — the
`horth` hypothesis of `coarsenFamily_idem` is non-droppable. -/
theorem coarsenFamily_idem_needs_orthogonality :
    ∃ R : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ a, (R a).IsHermitian) ∧ (∀ a, R a * R a = R a) ∧
      ¬ (∀ c, coarsenFamily (fun _ => (0 : Fin 1)) R c
            * coarsenFamily (fun _ => (0 : Fin 1)) R c
          = coarsenFamily (fun _ => (0 : Fin 1)) R c) := by
  refine ⟨![Pz0, Pz0], ?_, ?_, ?_⟩
  · intro a
    fin_cases a <;> exact Pz0_isHermitian
  · intro a
    fin_cases a <;> exact Pz0_idem
  · intro h
    have hfib : fiber (fun _ : Fin 2 => (0 : Fin 1)) 0 = Finset.univ := by
      ext a
      simp
    have h0 := h 0
    rw [coarsenFamily, hfib, Fin.sum_univ_two] at h0
    have hentry := congrFun (congrFun h0 0) 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hentry
    norm_num [Pz0, Matrix.mul_apply, Matrix.add_apply,
      Fin.sum_univ_two, Complex.ext_iff] at hentry

/-! ### Decoherence by coarse-graining

Diagonality is NOT reflected by the pushforward: a strictly quantum
measure on `Fin 3` whose merge along `![0,0,1]` is exactly diagonal —
the two members of the merged fiber interfere with the third atom with
opposite signs that cancel in the block sum. Branch vectors
`v₀ = (1,0)`, `v₁ = (−1, 4/5)`, `v₂ = (3/5, 0)` at the state `(1,0)`:
`v₀ + v₁ = (0, 4/5) ⟂ v₂` while `⟨v₀, v₂⟩ = 3/5 ≠ 0`; the total is the
3-4-5 state, so the fine measure normalizes to `1` on the nose. -/

/-- The fine class operators (first columns are the branch vectors). -/
noncomputable def mergeFamily : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1, 0; 0, 0], !![-1, 0; 4/5, 0], !![3/5, 0; 0, 0]]

/-- The fine state. -/
noncomputable def mergeState : Fin 2 → ℂ := ![1, 0]

/-- Unit total weight of the merge presentation (the 3-4-5 total). -/
private theorem mergeNorm :
    ∑ α, ∑ β, decoherenceFunctional mergeFamily mergeState α β = 1 := by
  simp only [Fin.sum_univ_three, decoherenceFunctional, mergeFamily,
    mergeState, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  norm_num [Matrix.mulVec, Matrix.mul_apply, dotProduct,
    Fin.sum_univ_two, Pi.star_apply, Complex.star_def, map_div₀,
    map_neg, map_one, map_ofNat, Complex.ext_iff, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

/-- The strictly quantum fine measure on `Fin 3`. -/
noncomputable def mergeMeasure : QuantumMeasure (Fin 3) :=
  QuantumMeasure.ofPresentation mergeFamily mergeState mergeNorm

/-- The fine measure genuinely interferes: the `(0,2)` overlap is
`3/5 ≠ 0`. -/
theorem mergeMeasure_not_isDiagonal : ¬ mergeMeasure.IsDiagonal := by
  intro h
  have hc := h (show (0 : Fin 3) ≠ 2 by decide)
  simp only [mergeMeasure, QuantumMeasure.ofPresentation_gram,
    decoherenceFunctional, mergeFamily, mergeState,
    Matrix.cons_val_zero, Matrix.cons_val_two] at hc
  norm_num [Matrix.mulVec, Matrix.mul_apply, dotProduct,
    Fin.sum_univ_two, Pi.star_apply, Complex.star_def, map_div₀,
    map_ofNat, Complex.ext_iff, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] at hc

/-- The merge: atoms `0` and `1` fuse; atom `2` survives alone. -/
def mergeCoarse : Fin 3 → Fin 2 := ![0, 0, 1]

/-- **Decoherence by coarse-graining**: the merged measure is exactly
diagonal — on a coarse index of size two, away from the
subsingleton-vacuity cheap case. Diagonality is preserved forward
(`pushforward_isDiagonal`) but not reflected. -/
theorem mergeMeasure_pushforward_isDiagonal :
    (mergeMeasure.pushforward mergeCoarse).IsDiagonal := by
  intro c c' hcc'
  rw [pushforward_gram]
  fin_cases c <;> fin_cases c' <;>
    first
      | exact absurd rfl hcc'
      | (simp only [QuantumMeasure.eventForm, fiber, Finset.sum_filter,
           mergeMeasure, QuantumMeasure.ofPresentation_gram,
           decoherenceFunctional, Fin.sum_univ_three]
         norm_num [mergeCoarse, mergeFamily, mergeState, Matrix.mulVec,
           Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
           Pi.star_apply, Complex.star_def, map_div₀, map_neg,
           map_one, map_ofNat, Complex.ext_iff, Matrix.cons_val_zero,
           Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two])

/-- The coarse Born row: `(16/25, 9/25)` — the merged fiber's weight is
`|v₀ + v₁|² = (4/5)²`, atom `2` keeps `(3/5)²`. -/
theorem mergeMeasure_pushforward_probRow :
    (mergeMeasure.pushforward mergeCoarse).probRow = ![16/25, 9/25] := by
  funext c
  fin_cases c <;>
    (simp only [QuantumMeasure.probRow, pushforward_gram,
       QuantumMeasure.eventForm, fiber, Finset.sum_filter,
       mergeMeasure, QuantumMeasure.ofPresentation_gram,
       decoherenceFunctional, Fin.sum_univ_three]
     norm_num [mergeCoarse, mergeFamily, mergeState, Matrix.mulVec,
       Matrix.mul_apply, dotProduct, Fin.sum_univ_two, Pi.star_apply,
       Complex.star_def, map_div₀, map_neg, map_one, map_ofNat,
       Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
       Matrix.cons_val_two, Complex.add_re, Complex.mul_re,
       Complex.mul_im])

/-- **Records coarsen, exercised end-to-end**: the landed recorded
z-measure, totally merged, is still (equal to) a classical measure —
`records_conservativity_pushforward` on the D-form module's recorded
presentation. -/
theorem zMeasure_pushforward_conservative :
    ∃ (p : Fin 1 → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1),
      zMeasure.pushforward (fun _ => (0 : Fin 1))
        = QuantumMeasure.classical p hp hs := by
  refine records_conservativity_pushforward (fun _ => (0 : Fin 1))
    ![Pz0, Pz1] ![Pz0, Pz1] ![(3/5 : ℂ), 4/5] _ ?_ ?_ ?_
  · intro α
    fin_cases α
    · exact Pz0_isHermitian
    · exact Pz1_isHermitian
  · intro α β h
    fin_cases α <;> fin_cases β <;>
      first
        | exact absurd rfl h
        | exact Pz0_mul_Pz1
        | exact Pz1_mul_Pz0
  · intro α
    rfl

end Toys

end QuantumCoarseGraining

end Qtsl

-- Axiom receipts (expected: exactly [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumCoarseGraining.sum_fiberEvent
#print axioms Qtsl.QuantumCoarseGraining.sum_fiber
#print axioms Qtsl.QuantumCoarseGraining.pushforward_gram
#print axioms Qtsl.QuantumCoarseGraining.pushforward_eventForm
#print axioms Qtsl.QuantumCoarseGraining.pushforward_sorkinMeasure
#print axioms Qtsl.QuantumCoarseGraining.pushforward_interference
#print axioms Qtsl.QuantumCoarseGraining.pushforward_isDiagonal
#print axioms Qtsl.QuantumCoarseGraining.pushforward_probRow
#print axioms Qtsl.QuantumCoarseGraining.pushforward_probRow_of_isDiagonal
#print axioms Qtsl.QuantumCoarseGraining.classical_pushforward
#print axioms Qtsl.QuantumCoarseGraining.pushforward_isDiagonal_eq_classical
#print axioms Qtsl.QuantumCoarseGraining.classicalization_pushforward_comm
#print axioms Qtsl.QuantumCoarseGraining.pushforward_id
#print axioms Qtsl.QuantumCoarseGraining.pushforward_equiv
#print axioms Qtsl.QuantumCoarseGraining.pushforward_comp
#print axioms Qtsl.QuantumCoarseGraining.map_pushforward
#print axioms Qtsl.QuantumCoarseGraining.pushforward_map
#print axioms Qtsl.QuantumCoarseGraining.coarsenFamily_isHermitian
#print axioms Qtsl.QuantumCoarseGraining.coarsenFamily_orthogonal
#print axioms Qtsl.QuantumCoarseGraining.coarsenFamily_correlated
#print axioms Qtsl.QuantumCoarseGraining.coarsenFamily_complete
#print axioms Qtsl.QuantumCoarseGraining.coarsenFamily_idem
#print axioms Qtsl.QuantumCoarseGraining.strong_records_coarsen
#print axioms Qtsl.QuantumCoarseGraining.decoherenceFunctional_coarsenFamily
#print axioms Qtsl.QuantumCoarseGraining.pushforward_ofPresentation
#print axioms Qtsl.QuantumCoarseGraining.records_conservativity_pushforward
#print axioms Qtsl.QuantumCoarseGraining.coarsenFamily_idem_needs_orthogonality
#print axioms Qtsl.QuantumCoarseGraining.mergeMeasure_not_isDiagonal
#print axioms Qtsl.QuantumCoarseGraining.mergeMeasure_pushforward_isDiagonal
#print axioms Qtsl.QuantumCoarseGraining.mergeMeasure_pushforward_probRow
#print axioms Qtsl.QuantumCoarseGraining.zMeasure_pushforward_conservative
