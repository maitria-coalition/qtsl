import SuFunctor.Adequacy.QuantumContainment

/-! # Certified abstraction under Hilbert-space compression

The block-spin containment of the companion module coarsens the record
index while the matrix algebra stays put — its own scope fence names
state-space compression as the successor.  This module discharges that
successor at the honest finite grade: the state space genuinely
shrinks, and the containment certificate survives unchanged.

* **The isometry stratum** (`IsIsometry`, `compressState`,
  `dilateState`, `compressRecord`, `dilateRecord`): compression along
  an isometry `V` (columns embedding the coarse space into the fine
  one) acts on states by `ρ ↦ Vᴴ ρ V` and on observables by
  `M ↦ V M Vᴴ`, and the two are trace-adjoint — **the
  compression/record-shadow interchange**
  (`recordShadow_compressState`, `recordShadow_dilateState`):
  measuring a compressed state is measuring the dilated record family,
  and dually.  Dilation of states is trace-preserving and
  state-preserving; compression of records sends POVMs to POVMs; and
  compression retracts dilation (`compress_dilate`).  The asymmetry is
  stated, never smoothed: dilating a POVM yields only a sub-POVM,
  summing to the range projection (`dilateRecord_sum`), and
  compression of a state keeps only its range-projection pairing
  (`compressState_trace`) — a single isometry can silently discard
  mass (`compressState_branchIso_upState_trace`: the `|01⟩` state
  compressed along the wrong branch has trace `0`).

* **The channel stratum** (`kchanApply`, `kchanDual`, `KrausTP`): the
  honest compression of a *theory* is therefore a Kraus family — a
  finite set of branch operators with the trace-preserving
  normalization `∑ Aⱼᴴ Aⱼ = 1`.  The channel preserves positivity and
  trace, so it carries states to states (`isState_kchanApply`); its
  dual carries coarse POVMs to fine POVMs (`kchanDual_sum`); and the
  interchange holds channel-wide (`recordShadow_kchanApply`).  A
  single-isometry compression is the one-element Kraus family
  (`compressState_eq_kchanApply`).

* **The block-spin instance**: the two branch isometries of the
  two-qubit toy assemble into the Kraus family `ptrKraus`, whose
  channel is exactly the landed partial trace over the second qubit
  (`kchanApply_ptrKraus_eq_ptR`) — the partial trace acquires an
  explicit trace-preserving Kraus certificate.  The compatibility
  square (`kchanDual_qRecord`): the dual channel pulls the one-qubit
  computational family back to exactly the block-spin observable
  family, so **measuring the compressed state is measuring the block
  observable** (`ptrace_recordShadow`) — the compression story and the
  record-coarsening story agree on every Born row.

* **The compressed effective theory**: a one-qubit kinematic fragment
  (`singleQubitFragment` — one static site, its full matrix algebra,
  the identity mechanism: the truncated theory's own presentation, on
  a Hilbert space of half the dimension), whose ground effective
  state is the compressed ground state (`ptrace_pureProd`).  Its law
  set coincides with the record-coarsened IR theory's
  (`irLaws_eq_smallLaws`): the compression is semantically invisible
  at the record stratum while the state space shrinks.  Consequently
  the containment certificate transfers verbatim — the same declared
  band `49/625` (`uv_smallIR_containment`), still attained
  (`uv_smallIR_containment_lower`), still refuted at zero tolerance
  (`not_uv_smallIR_containment_zero`) — and the certified validity
  window of the effective dynamics rides the compression unchanged
  (`compressed_horizon_bound`).

Scope fences: no compression-ratio or optimality claim of any kind
(which compressions exist or are efficient is producer-side search,
never certificate content); no power-counting claim; no continuum
word; the two-categorical packaging of the containment squares
remains deferred. -/

namespace SuFunctor

universe u

open Finset Matrix
open Qtsl.Imprecise Qtsl.DiamondSite Qtsl.QuantumDescent
open Qtsl.QuantumStates Qtsl.QuantumAssembly Qtsl.QuantumDeterminacy
open Qtsl.QuantumRecords Qtsl.QuantumCoarseGraining Qtsl.QuantumTower
open scoped ComplexOrder

namespace Adequacy

/-! ## The isometry stratum -/

section Isometry

variable {d e : Type*} [Fintype d] [Fintype e]
variable {ι' κ' : Type*}

/-- An isometry from the coarse space into the fine one, presented as
its matrix of columns: `Vᴴ V = 1` on the coarse side. -/
def IsIsometry [DecidableEq e] (V : Matrix d e ℂ) : Prop := Vᴴ * V = 1

/-- Compression of a fine state along an isometry: `ρ ↦ Vᴴ ρ V`. -/
noncomputable def compressState (V : Matrix d e ℂ) (ρ : Matrix d d ℂ) :
    Matrix e e ℂ :=
  Vᴴ * ρ * V

/-- Dilation of a coarse state along an isometry: `σ ↦ V σ Vᴴ`. -/
noncomputable def dilateState (V : Matrix d e ℂ) (σ : Matrix e e ℂ) :
    Matrix d d ℂ :=
  V * σ * Vᴴ

/-- Dilation of a coarse record family: `S ↦ V S Vᴴ`, pointwise. -/
noncomputable def dilateRecord (V : Matrix d e ℂ)
    (S : κ' → Matrix e e ℂ) : κ' → Matrix d d ℂ :=
  fun c => V * S c * Vᴴ

/-- Compression of a fine record family: `R ↦ Vᴴ R V`, pointwise. -/
noncomputable def compressRecord (V : Matrix d e ℂ)
    (R : ι' → Matrix d d ℂ) : ι' → Matrix e e ℂ :=
  fun a => Vᴴ * R a * V

theorem compressState_posSemidef {V : Matrix d e ℂ}
    {ρ : Matrix d d ℂ} (hρ : ρ.PosSemidef) :
    (compressState V ρ).PosSemidef :=
  hρ.conjTranspose_mul_mul_same V

theorem dilateState_posSemidef {V : Matrix d e ℂ}
    {σ : Matrix e e ℂ} (hσ : σ.PosSemidef) :
    (dilateState V σ).PosSemidef :=
  hσ.mul_mul_conjTranspose_same V

theorem compressRecord_posSemidef {V : Matrix d e ℂ}
    {R : ι' → Matrix d d ℂ} (hR : ∀ a, (R a).PosSemidef) (a : ι') :
    (compressRecord V R a).PosSemidef :=
  (hR a).conjTranspose_mul_mul_same V

theorem dilateRecord_posSemidef {V : Matrix d e ℂ}
    {S : κ' → Matrix e e ℂ} (hS : ∀ c, (S c).PosSemidef) (c : κ') :
    (dilateRecord V S c).PosSemidef :=
  (hS c).mul_mul_conjTranspose_same V

/-- **The trace-loss formula**: compression keeps exactly the
range-projection pairing.  No isometry hypothesis — this is bare
cyclicity, and it is the honest statement of what a single isometry
discards. -/
theorem compressState_trace (V : Matrix d e ℂ) (ρ : Matrix d d ℂ) :
    (compressState V ρ).trace = (ρ * (V * Vᴴ)).trace := by
  show ((Vᴴ * ρ) * V).trace = _
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]

/-- Dilation is trace-preserving. -/
theorem dilateState_trace [DecidableEq e] {V : Matrix d e ℂ}
    (hV : IsIsometry V)
    (σ : Matrix e e ℂ) : (dilateState V σ).trace = σ.trace := by
  have hV' : Vᴴ * V = 1 := hV
  show ((V * σ) * Vᴴ).trace = _
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV', Matrix.one_mul]

/-- Dilation carries states to states. -/
theorem isState_dilateState [DecidableEq e] {V : Matrix d e ℂ}
    (hV : IsIsometry V)
    {σ : Matrix e e ℂ} (hσ : IsState σ) : IsState (dilateState V σ) :=
  ⟨dilateState_posSemidef hσ.1, by rw [dilateState_trace hV, hσ.2]⟩

/-- Compression retracts dilation: the coarse theory embeds
losslessly. -/
theorem compress_dilate [DecidableEq e] {V : Matrix d e ℂ}
    (hV : IsIsometry V)
    (σ : Matrix e e ℂ) : compressState V (dilateState V σ) = σ := by
  have hV' : Vᴴ * V = 1 := hV
  show Vᴴ * (V * σ * Vᴴ) * V = σ
  simp only [Matrix.mul_assoc]
  rw [hV', Matrix.mul_one, ← Matrix.mul_assoc, hV', Matrix.one_mul]

omit [Fintype e] in
/-- Fine POVMs compress to coarse POVMs along an isometry. -/
theorem compressRecord_sum [Fintype ι'] [DecidableEq d] [DecidableEq e]
    {V : Matrix d e ℂ}
    (hV : IsIsometry V) {R : ι' → Matrix d d ℂ} (hR : ∑ a, R a = 1) :
    ∑ a, compressRecord V R a = 1 := by
  have hV' : Vᴴ * V = 1 := hV
  show (∑ a, Vᴴ * R a * V) = 1
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, hR, Matrix.mul_one, hV']

omit [Fintype d] in
/-- Dilation of a POVM is only a sub-POVM: it sums to the range
projection.  The honest asymmetry — the coarse family sees nothing
outside the embedded subspace. -/
theorem dilateRecord_sum [Fintype κ'] [DecidableEq e] (V : Matrix d e ℂ)
    {S : κ' → Matrix e e ℂ} (hS : ∑ c, S c = 1) :
    ∑ c, dilateRecord V S c = V * Vᴴ := by
  show (∑ c, V * S c * Vᴴ) = V * Vᴴ
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, hS, Matrix.mul_one]

/-- The conjugation-pairing trace identity behind both interchanges. -/
private theorem trace_conj_pair (V : Matrix d e ℂ) (ρ : Matrix d d ℂ)
    (M : Matrix e e ℂ) :
    ((Vᴴ * ρ * V) * M).trace = (ρ * (V * M * Vᴴ)).trace := by
  rw [Matrix.mul_assoc (Vᴴ * ρ) V M, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, Matrix.trace_mul_comm]

/-- **The compression/record-shadow interchange, state form**:
measuring a compressed state is measuring the dilated record family
on the fine state. -/
theorem recordShadow_compressState (V : Matrix d e ℂ)
    (S : κ' → Matrix e e ℂ) (ρ : Matrix d d ℂ) (c : κ') :
    recordShadow S (compressState V ρ) c
      = recordShadow (dilateRecord V S) ρ c := by
  show ((compressState V ρ * S c).trace).re
      = ((ρ * dilateRecord V S c).trace).re
  exact congrArg Complex.re (trace_conj_pair V ρ (S c))

/-- **The compression/record-shadow interchange, record form**:
measuring a dilated state is measuring the compressed record family
on the coarse state. -/
theorem recordShadow_dilateState (V : Matrix d e ℂ)
    (R : ι' → Matrix d d ℂ) (σ : Matrix e e ℂ) (a : ι') :
    recordShadow R (dilateState V σ) a
      = recordShadow (compressRecord V R) σ a := by
  show ((dilateState V σ * R a).trace).re
      = ((σ * compressRecord V R a).trace).re
  have h := trace_conj_pair Vᴴ σ (R a)
  simp only [Matrix.conjTranspose_conjTranspose] at h
  exact congrArg Complex.re h

end Isometry

/-! ## The channel stratum: Kraus compression -/

section Channel

variable {d e : Type*} [Fintype d] [Fintype e]
variable {J : Type*} [Fintype J]
variable {ι' κ' : Type*}

/-- The Schrödinger action of a Kraus family: `ρ ↦ ∑ⱼ Aⱼ ρ Aⱼᴴ`. -/
noncomputable def kchanApply (A : J → Matrix e d ℂ)
    (ρ : Matrix d d ℂ) : Matrix e e ℂ :=
  ∑ j, A j * ρ * (A j)ᴴ

/-- The Heisenberg (dual) action: `M ↦ ∑ⱼ Aⱼᴴ M Aⱼ`. -/
noncomputable def kchanDual (A : J → Matrix e d ℂ)
    (M : Matrix e e ℂ) : Matrix d d ℂ :=
  ∑ j, (A j)ᴴ * M * A j

/-- Trace preservation, as the Kraus normalization. -/
def KrausTP [DecidableEq d] (A : J → Matrix e d ℂ) : Prop :=
  ∑ j, (A j)ᴴ * A j = 1

/-- Sums of positive-semidefinite matrices are positive-semidefinite
(local apparatus). -/
private theorem posSemidefSum {β : Type*} {d' : Type*} [Fintype d']
    {s : Finset β} {f : β → Matrix d' d' ℂ}
    (h : ∀ b ∈ s, (f b).PosSemidef) : (∑ b ∈ s, f b).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem kchanApply_posSemidef (A : J → Matrix e d ℂ)
    {ρ : Matrix d d ℂ} (hρ : ρ.PosSemidef) :
    (kchanApply A ρ).PosSemidef :=
  posSemidefSum fun j _ => hρ.mul_mul_conjTranspose_same (A j)

theorem kchanDual_posSemidef (A : J → Matrix e d ℂ)
    {M : Matrix e e ℂ} (hM : M.PosSemidef) :
    (kchanDual A M).PosSemidef :=
  posSemidefSum fun j _ => hM.conjTranspose_mul_mul_same (A j)

/-- The channel-pairing trace identity: the Schrödinger and Heisenberg
actions are trace-adjoint. -/
private theorem trace_kchan (A : J → Matrix e d ℂ) (ρ : Matrix d d ℂ)
    (M : Matrix e e ℂ) :
    ((kchanApply A ρ) * M).trace = (ρ * kchanDual A M).trace := by
  show ((∑ j, A j * ρ * (A j)ᴴ) * M).trace
      = (ρ * ∑ j, (A j)ᴴ * M * A j).trace
  rw [Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := trace_conj_pair (A j)ᴴ ρ M
  simp only [Matrix.conjTranspose_conjTranspose] at h
  exact h

/-- A trace-preserving Kraus family preserves the trace. -/
theorem kchanApply_trace [DecidableEq d] [DecidableEq e]
    {A : J → Matrix e d ℂ} (hA : KrausTP A)
    (ρ : Matrix d d ℂ) : (kchanApply A ρ).trace = ρ.trace := by
  have h := trace_kchan A ρ (1 : Matrix e e ℂ)
  rw [Matrix.mul_one] at h
  rw [h]
  have h1 : kchanDual A (1 : Matrix e e ℂ) = (1 : Matrix d d ℂ) := by
    show (∑ j, (A j)ᴴ * (1 : Matrix e e ℂ) * A j) = 1
    have h2 : ∀ j : J, (A j)ᴴ * (1 : Matrix e e ℂ) * A j
        = (A j)ᴴ * A j := fun j => by rw [Matrix.mul_one]
    rw [Finset.sum_congr rfl fun j _ => h2 j]
    exact hA
  rw [h1, Matrix.mul_one]

/-- A trace-preserving Kraus channel carries states to states. -/
theorem isState_kchanApply [DecidableEq d] [DecidableEq e]
    {A : J → Matrix e d ℂ} (hA : KrausTP A)
    {ρ : Matrix d d ℂ} (hρ : IsState ρ) : IsState (kchanApply A ρ) :=
  ⟨kchanApply_posSemidef A hρ.1, by rw [kchanApply_trace hA, hρ.2]⟩

omit [Fintype d] in
/-- Coarse POVMs pull back to fine POVMs along a trace-preserving
channel — the compressed theory's record package, by theorem. -/
theorem kchanDual_sum [Fintype κ'] [DecidableEq d] [DecidableEq e]
    {A : J → Matrix e d ℂ}
    (hA : KrausTP A) {S : κ' → Matrix e e ℂ} (hS : ∑ c, S c = 1) :
    ∑ c, kchanDual A (S c) = 1 := by
  show (∑ c, ∑ j, (A j)ᴴ * S c * A j) = 1
  rw [Finset.sum_comm]
  have hterm : ∀ j : J, (∑ c, (A j)ᴴ * S c * A j) = (A j)ᴴ * A j := by
    intro j
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, hS, Matrix.mul_one]
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  exact hA

/-- **The compression/record-shadow interchange, channel form**:
measuring a channel-compressed state is measuring the dual-channel
image of the record family. -/
theorem recordShadow_kchanApply (A : J → Matrix e d ℂ)
    (S : κ' → Matrix e e ℂ) (ρ : Matrix d d ℂ) (c : κ') :
    recordShadow S (kchanApply A ρ) c
      = recordShadow (fun c => kchanDual A (S c)) ρ c := by
  show ((kchanApply A ρ * S c).trace).re
      = ((ρ * kchanDual A (S c)).trace).re
  exact congrArg Complex.re (trace_kchan A ρ (S c))

omit [Fintype e] in
/-- Single-isometry compression is the one-element Kraus family. -/
theorem compressState_eq_kchanApply (V : Matrix d e ℂ)
    (ρ : Matrix d d ℂ) :
    compressState V ρ = kchanApply (fun _ : Fin 1 => Vᴴ) ρ := by
  show Vᴴ * ρ * V = ∑ _j : Fin 1, Vᴴ * ρ * Vᴴᴴ
  rw [Fin.sum_univ_one, Matrix.conjTranspose_conjTranspose]

end Channel

/-! ## The block-spin instance: the partial trace as a Kraus channel -/

/-- The conjugate transpose of a single-entry matrix (local
apparatus). -/
private theorem conjTranspose_single' {m' n' : Type*} [DecidableEq m']
    [DecidableEq n'] (i : m') (j : n') (c : ℂ) :
    (Matrix.single i j c)ᴴ = Matrix.single j i (star c) := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.single, Matrix.of_apply]
  by_cases h1 : i = b <;> by_cases h2 : j = a <;>
    simp [h1, h2, and_comm]

/-- The block fiber of the first-spin map (local apparatus). -/
private theorem fiber_fst_pair (c : Fin 2) :
    fiber (Prod.fst : Fin 2 × Fin 2 → Fin 2) c = {(c, 0), (c, 1)} := by
  ext ⟨a1, a2⟩
  simp only [mem_fiber, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq]
  constructor
  · intro h
    have h2 : a2 = 0 ∨ a2 = 1 := by omega
    rcases h2 with rfl | rfl
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr ⟨h, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl

/-- The Kraus family of the right-qubit partial trace: the `j`-th
branch operator reads off the first spin against second-spin value
`j`. -/
noncomputable def ptrKraus (j : Fin 2) :
    Matrix (Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ c, Matrix.single c (c, j) 1

private theorem ptrKrausH (j : Fin 2) :
    (ptrKraus j)ᴴ = ∑ c, Matrix.single (c, j) c (1 : ℂ) := by
  show (∑ c, Matrix.single c (c, j) (1 : ℂ))ᴴ = _
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun c _ => by
    rw [conjTranspose_single', star_one]

/-- The Kraus normalization: the branch operators are
trace-preserving.  (Kept immediately after the definition — the
family's first certificate.) -/
theorem ptrKraus_tp : KrausTP ptrKraus := by
  show ∑ j, (ptrKraus j)ᴴ * ptrKraus j = 1
  have hterm : ∀ j : Fin 2, (ptrKraus j)ᴴ * ptrKraus j
      = ∑ c, Matrix.single (c, j) (c, j) (1 : ℂ) := by
    intro j
    rw [ptrKrausH]
    show (∑ c, Matrix.single (c, j) c (1 : ℂ))
        * (∑ c, Matrix.single c (c, j) (1 : ℂ)) = _
    rw [Matrix.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mul_sum]
    have hinner : ∀ c' : Fin 2,
        Matrix.single (c, j) c (1 : ℂ)
            * Matrix.single c' (c', j) (1 : ℂ)
          = if c' = c then Matrix.single (c, j) (c, j) (1 : ℂ)
            else 0 := by
      intro c'
      rcases eq_or_ne c' c with rfl | h
      · rw [if_pos rfl, Matrix.single_mul_single_same, one_mul]
      · rw [if_neg h,
          Matrix.single_mul_single_of_ne (h := Ne.symm h)]
    rw [Finset.sum_congr rfl fun c' _ => hinner c',
      Finset.sum_ite_eq' Finset.univ c
        (fun _ => Matrix.single (c, j) (c, j) (1 : ℂ)),
      if_pos (Finset.mem_univ c)]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_comm]
  exact (Fintype.sum_prod_type
    (f := fun ik : Fin 2 × Fin 2 => Matrix.single ik ik (1 : ℂ))).symm.trans
    sum_single_diag_eq_one

/-- The branch isometries: the adjoints of the Kraus components. -/
noncomputable def branchIso (j : Fin 2) :
    Matrix (Fin 2 × Fin 2) (Fin 2) ℂ :=
  (ptrKraus j)ᴴ

theorem branchIso_isometry (j : Fin 2) : IsIsometry (branchIso j) := by
  show (branchIso j)ᴴ * branchIso j = 1
  rw [branchIso, Matrix.conjTranspose_conjTranspose, ptrKrausH]
  show (∑ c, Matrix.single c (c, j) (1 : ℂ))
      * (∑ c, Matrix.single (c, j) c (1 : ℂ)) = 1
  rw [Matrix.sum_mul]
  have hcollapse : ∀ c : Fin 2,
      Matrix.single c (c, j) (1 : ℂ)
          * (∑ c', Matrix.single (c', j) c' (1 : ℂ))
        = Matrix.single c c (1 : ℂ) := by
    intro c
    rw [Matrix.mul_sum]
    have hterm : ∀ c' : Fin 2,
        Matrix.single c (c, j) (1 : ℂ)
            * Matrix.single (c', j) c' (1 : ℂ)
          = if c' = c then Matrix.single c c (1 : ℂ) else 0 := by
      intro c'
      rcases eq_or_ne c' c with rfl | h
      · rw [if_pos rfl, Matrix.single_mul_single_same, one_mul]
      · rw [if_neg h,
          Matrix.single_mul_single_of_ne
            (h := fun hp => h (congrArg Prod.fst hp).symm)]
    rw [Finset.sum_congr rfl fun c' _ => hterm c',
      Finset.sum_ite_eq' Finset.univ c
        (fun _ => Matrix.single c c (1 : ℂ)),
      if_pos (Finset.mem_univ c)]
  rw [Finset.sum_congr rfl fun c _ => hcollapse c]
  exact sum_single_diag_eq_one

/-- The partial trace over the second qubit, as the Kraus channel of
the branch family. -/
noncomputable def ptrace : TwoQubits → Qubit := kchanApply ptrKraus

set_option maxHeartbeats 1600000 in
/-- **The channel is the landed partial trace**: the Kraus
presentation of `ptR`.  The partial trace thereby carries an explicit
trace-preserving Kraus certificate (`ptrKraus_tp`). -/
theorem kchanApply_ptrKraus_eq_ptR (ρ : TwoQubits) :
    kchanApply ptrKraus ρ = ptR ρ := by
  ext i i'
  show (∑ j, ptrKraus j * ρ * (ptrKraus j)ᴴ) i i' = ptR ρ i i'
  simp only [Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, ptrKraus, Matrix.single,
    Matrix.of_apply, ptR, ite_and, ite_mul, mul_ite, one_mul, mul_one,
    zero_mul, mul_zero, apply_ite (star : ℂ → ℂ), star_one, star_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The one-qubit computational record family. -/
noncomputable def qRecord : Fin 2 → Qubit := fun c =>
  Matrix.single c c 1

set_option maxHeartbeats 1600000 in
theorem qRecord_posSemidef (c : Fin 2) : (qRecord c).PosSemidef := by
  have h : qRecord c =
      Matrix.vecMulVec (Pi.single c 1)
        (star (Pi.single c (1 : ℂ) : Fin 2 → ℂ)) := by
    rw [star_pi_single_one]
    exact Matrix.single_eq_single_vecMulVec_single c c
  rw [h]
  exact posSemidef_vecMulVec_star_self _

theorem qRecord_sum : ∑ c, qRecord c = 1 :=
  sum_single_diag_eq_one

/-- **The compatibility square**: the dual channel pulls the one-qubit
computational family back to exactly the block-spin observable
family. -/
theorem kchanDual_qRecord (c : Fin 2) :
    kchanDual ptrKraus (qRecord c) = blockRecord c := by
  have hterm : ∀ j : Fin 2, (ptrKraus j)ᴴ * qRecord c * ptrKraus j
      = Matrix.single (c, j) (c, j) (1 : ℂ) := by
    intro j
    rw [ptrKrausH]
    show (∑ a, Matrix.single (a, j) a (1 : ℂ)) * qRecord c
        * (∑ b, Matrix.single b (b, j) (1 : ℂ)) = _
    have h1 : (∑ a, Matrix.single (a, j) a (1 : ℂ)) * qRecord c
        = Matrix.single (c, j) c (1 : ℂ) := by
      show (∑ a, Matrix.single (a, j) a (1 : ℂ))
          * Matrix.single c c (1 : ℂ) = _
      rw [Matrix.sum_mul]
      have ha : ∀ a : Fin 2,
          Matrix.single (a, j) a (1 : ℂ)
              * Matrix.single c c (1 : ℂ)
            = if a = c then Matrix.single (c, j) c (1 : ℂ) else 0 := by
        intro a
        rcases eq_or_ne a c with rfl | h
        · rw [if_pos rfl, Matrix.single_mul_single_same, one_mul]
        · rw [if_neg h, Matrix.single_mul_single_of_ne (h := h)]
      rw [Finset.sum_congr rfl fun a _ => ha a,
        Finset.sum_ite_eq' Finset.univ c
          (fun _ => Matrix.single (c, j) c (1 : ℂ)),
        if_pos (Finset.mem_univ c)]
    rw [h1, Matrix.mul_sum]
    have hb : ∀ b : Fin 2,
        Matrix.single (c, j) c (1 : ℂ)
            * Matrix.single b (b, j) (1 : ℂ)
          = if b = c then Matrix.single (c, j) (c, j) (1 : ℂ)
            else 0 := by
      intro b
      rcases eq_or_ne b c with rfl | h
      · rw [if_pos rfl, Matrix.single_mul_single_same, one_mul]
      · rw [if_neg h,
          Matrix.single_mul_single_of_ne (h := Ne.symm h)]
    rw [Finset.sum_congr rfl fun b _ => hb b,
      Finset.sum_ite_eq' Finset.univ c
        (fun _ => Matrix.single (c, j) (c, j) (1 : ℂ)),
      if_pos (Finset.mem_univ c)]
  show (∑ j, (ptrKraus j)ᴴ * qRecord c * ptrKraus j) = blockRecord c
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  show _ = ∑ a ∈ fiber (Prod.fst : Fin 2 × Fin 2 → Fin 2) c, zzRecord a
  rw [fiber_fst_pair c,
    Finset.sum_pair (by simp : ((c, 0) : Fin 2 × Fin 2) ≠ (c, 1)),
    Fin.sum_univ_two]
  rfl

/-- **Measuring the compressed state is measuring the block
observable** — the compression/record-shadow interchange at the
instance: the channel story and the record-coarsening story agree on
every Born row, at every state. -/
theorem ptrace_recordShadow (ρ : TwoQubits) (c : Fin 2) :
    recordShadow qRecord (ptrace ρ) c
      = recordShadow blockRecord ρ c := by
  show recordShadow qRecord (kchanApply ptrKraus ρ) c = _
  rw [recordShadow_kchanApply]
  show ((ρ * kchanDual ptrKraus (qRecord c)).trace).re
      = ((ρ * blockRecord c).trace).re
  rw [kchanDual_qRecord]

/-- The compressed ground state: `|0⟩⟨0|` on the one-qubit space. -/
noncomputable def qPure0 : Qubit := Matrix.single 0 0 1

theorem qPure0_trace : qPure0.trace = 1 := by
  have h := Qtsl.QuantumDescent.trace_mul_single (1 : Qubit)
    (0 : Fin 2) (0 : Fin 2) (1 : ℂ)
  rw [Matrix.one_mul] at h
  rw [show qPure0 = Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) from
    rfl, h, Matrix.one_apply_eq, mul_one]

theorem qPure0_isState : IsState qPure0 :=
  ⟨qRecord_posSemidef 0, qPure0_trace⟩

/-- The small ground state is the compressed ground state. -/
theorem ptrace_pureProd : ptrace pureProd = qPure0 := by
  show kchanApply ptrKraus pureProd = qPure0
  rw [kchanApply_ptrKraus_eq_ptR]
  exact ptR_pureProd

/-- **The honest loss of a lone isometry**: the `|01⟩` state compressed
along the `j = 0` branch has trace zero — a single isometry silently
discards everything outside its range, which is why the honest
block-spin compression is the full Kraus family. -/
theorem compressState_branchIso_upState_trace :
    (compressState (branchIso 0) upState).trace = 0 := by
  unfold compressState branchIso
  rw [Matrix.conjTranspose_conjTranspose]
  have h : ptrKraus 0 * upState = 0 := by
    show (∑ c, Matrix.single c (c, (0 : Fin 2)) (1 : ℂ))
        * Matrix.single ((0 : Fin 2), (1 : Fin 2))
            ((0 : Fin 2), (1 : Fin 2)) (1 : ℂ) = 0
    rw [Matrix.sum_mul]
    have h01 : ¬((0 : Fin 2) = 1) := by decide
    refine Finset.sum_eq_zero fun c _ => ?_
    have hne : ((c, (0 : Fin 2)) : Fin 2 × Fin 2)
        ≠ ((0 : Fin 2), (1 : Fin 2)) :=
      fun hp => h01 (congrArg Prod.snd hp)
    rw [Matrix.single_mul_single_of_ne (h := hne)]
  rw [h, Matrix.zero_mul, Matrix.trace_zero]

/-! ## The compressed effective theory: a one-qubit fragment -/

/-- The single site of the compressed theory. -/
def smallSites : Fin 1 → Mink ℝ := fun _ => p

/-- The one-qubit kinematic net: the frozen Heisenberg net of one
static site carrying the full one-qubit algebra. -/
noncomputable def smallNet : ObservableNet (Mink ℝ) (Fin 2) :=
  heisenbergNet (fun i (_ : ℝ) => smallSites i)
    (fun _ => (⊤ : Subalgebra ℂ Qubit)) (fun _ => AlgEquiv.refl)

open scoped Classical in
theorem smallNet_alg (D : Diamond (Mink ℝ)) :
    smallNet.alg D = if inDiamond p D then ⊤ else ⊥ := by
  unfold smallNet
  rw [heisenbergNet_const_alg]
  simp only [smallSites]
  rw [iSup_const]
  by_cases hp : inDiamond p D
  · rw [if_pos hp, iSup_pos hp]
  · rw [if_neg hp, iSup_neg hp]

theorem smallNet_Dstar : smallNet.alg Dstar = ⊤ := by
  rw [smallNet_alg, if_pos p_mem_Dstar]

theorem smallNet_E₃ : smallNet.alg E₃ = ⊤ := by
  rw [smallNet_alg, if_pos p_mem_E₃]

/-- **The compressed theory is a kinematic fragment**: one static site
at `p`, its full one-qubit algebra, the identity mechanism — the
truncated effective theory's own presentation, on a state space of
half the dimension, with the one-qubit computational records. -/
noncomputable def singleQubitFragment :
    LCQFTFragment (Mink ℝ) (Fin 2) (Fin 1) ℝ (Fin 2) where
  net := smallNet
  sites := smallSites
  worldlines := fun i _ => smallSites i
  factors := fun _ => ⊤
  mechanism := fun _ => AlgEquiv.refl
  sites_on_worldlines := fun i => ⟨0, rfl⟩
  factors_exhaustive := iSup_const
  frozen_shadow := fun _ => rfl
  einstein_causality := by
    intro D₁ D₂ hsep a ha b hb
    by_cases hp1 : inDiamond p D₁
    · have hp2 : ¬ inDiamond p D₂ := fun hp2 => (hsep hp1 hp2).1 le_rfl
      rw [smallNet_alg, if_neg hp2, Algebra.mem_bot] at hb
      obtain ⟨c, rfl⟩ := hb
      exact (Algebra.commutes c a).symm
    · rw [smallNet_alg, if_neg hp1, Algebra.mem_bot] at ha
      obtain ⟨c, rfl⟩ := ha
      exact Algebra.commutes c b
  timeslice_surrogate := by
    intro E D hle hs
    by_cases hp : inDiamond p D
    · have h0 : inDiamond p E := hs 0 hp
      rw [smallNet_alg, smallNet_alg, if_pos hp, if_pos h0]
    · have h0 : ¬ inDiamond p E :=
        fun hpE => hp (inDiamond_mono hle hpE)
      rw [smallNet_alg, smallNet_alg, if_neg hp, if_neg h0]
  kit := (minkowskiKit (E := ℝ)).toMixingKit
  ambient := Dstar
  interior_witness := E₃
  interior_mem := E₃_interior
  interior_attained := by rw [smallNet_Dstar, smallNet_E₃]
  records := qRecord
  records_mem := fun _ => by rw [smallNet_Dstar]; exact Algebra.mem_top
  records_posSemidef := qRecord_posSemidef
  records_exhaustive := qRecord_sum

/-- The compressed ground state's Born row is the effective row. -/
theorem recordShadow_qRecord_qPure0 (c : Fin 2) :
    recordShadow qRecord qPure0 c = ((irRow c : ℚ) : ℝ) := by
  show ((qPure0 * Matrix.single c c 1).trace).re = _
  rw [Qtsl.QuantumDescent.trace_mul_single]
  have hc : c = 0 ∨ c = 1 := by omega
  rcases hc with rfl | rfl <;>
    norm_num [qPure0, Matrix.single, Matrix.of_apply, irRow]

/-- The compressed theory's state set: the compressed ground state
alone (cf. `ptrace_pureProd`). -/
def smallSet : Set {ρ : Qubit // IsState ρ} :=
  {⟨qPure0, qPure0_isState⟩}

/-- The compressed theory's one rational-shadowed member. -/
noncomputable def smallMember :
    QNet.RatShadowMember singleQubitFragment smallSet where
  state := ⟨qPure0, qPure0_isState⟩
  mem := rfl
  row := irRow
  row_spec := fun c => (recordShadow_qRecord_qPure0 c).symm

/-- The compressed theory's law set is pinned to the effective row. -/
theorem smallLaws_pinned (ν : SubPMF (Fin 2))
    (h : QNet.quantumLaws singleQubitFragment smallSet ν) :
    ν = smallMember.law := by
  obtain ⟨w, hw⟩ := h
  obtain rfl : ν = w.law := (singletonC_iff _ _).mp hw
  refine SubPMF.ext' (Finsupp.ext fun c => ?_)
  show w.row c = smallMember.row c
  have hst : w.state = ⟨qPure0, qPure0_isState⟩ :=
    Set.mem_singleton_iff.mp w.mem
  have h1 : ((w.row c : ℚ) : ℝ) = recordShadow qRecord qPure0 c := by
    have hs := w.row_spec c
    rw [hst] at hs
    exact hs
  have h2 : ((smallMember.row c : ℚ) : ℝ)
      = recordShadow qRecord qPure0 c :=
    (recordShadow_qRecord_qPure0 c).symm
  exact_mod_cast h1.trans h2.symm

/-- The compressed theory's law is the record-coarsened IR theory's
law: one row, two presentations. -/
theorem smallMember_law_eq : smallMember.law = irMember.law :=
  SubPMF.ext' (Finsupp.ext fun _ => rfl)

/-- **Semantic conservativity of the compression**: the
record-coarsened IR theory (records merged, algebra unshrunk) and the
compressed theory (a genuinely smaller state space) present the same
law set. -/
theorem irLaws_eq_smallLaws :
    QNet.quantumLaws irFragment irSet
      = QNet.quantumLaws singleQubitFragment smallSet := by
  funext ν
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · obtain rfl := irLaws_pinned ν h
    exact ⟨smallMember, (singletonC_iff _ _).mpr smallMember_law_eq.symm⟩
  · obtain rfl := smallLaws_pinned ν h
    exact ⟨irMember, (singletonC_iff _ _).mpr smallMember_law_eq⟩

/-! ## The containment certificate, transferred to the compressed
theory -/

/-- **The block-spin containment, compressed**: every UV-possible law,
pushed along the block map, lies within the declared band `49/625` of
the compressed effective theory — the same certificate, with the IR
System now on the genuinely smaller Hilbert space. -/
theorem uv_smallIR_containment :
    Containment (QNet.quantumLaws isingQubitFragment uvSeg) Prod.fst
      (QNet.quantumLaws singleQubitFragment smallSet) (49 / 625) := by
  rw [← irLaws_eq_smallLaws]
  exact uv_ir_containment

/-- The band is still attained: compression neither spends nor
manufactures tolerance. -/
theorem uv_smallIR_containment_lower (ε : ℚ)
    (h : Containment (QNet.quantumLaws isingQubitFragment uvSeg)
      Prod.fst (QNet.quantumLaws singleQubitFragment smallSet) ε) :
    49 / 625 ≤ ε := by
  rw [← irLaws_eq_smallLaws] at h
  exact uv_ir_containment_lower ε h

/-- The truncation stays genuine at the compressed grade. -/
theorem not_uv_smallIR_containment_zero :
    ¬ Containment (QNet.quantumLaws isingQubitFragment uvSeg) Prod.fst
      (QNet.quantumLaws singleQubitFragment smallSet) 0 := by
  intro h
  rw [← irLaws_eq_smallLaws] at h
  exact not_uv_ir_containment_zero h

/-! ## The compressed trajectory: the validity window rides the
compression -/

private theorem filter_fst_pair (c : Fin 2) :
    (Finset.univ.filter fun a : Fin 2 × Fin 2 => Prod.fst a = c)
      = {(c, 0), (c, 1)} :=
  fiber_fst_pair c

/-- The compressed orbit rows, exact-rational. -/
def compressedRow (x : Fin 2) : Fin 2 → ℚ := fun c =>
  orbitRow x (c, 0) + orbitRow x (c, 1)

theorem compressedRow_spec (x : Fin 2) (c : Fin 2) :
    ((compressedRow x c : ℚ) : ℝ)
      = recordShadow qRecord (ptrace (orbitState x)) c := by
  rw [ptrace_recordShadow]
  show _ = recordShadow (coarsenFamily Prod.fst zzRecord)
    (orbitState x) c
  rw [recordShadow_coarsenFamily, fiber_fst_pair,
    Finset.sum_pair (by simp : ((c, 0) : Fin 2 × Fin 2) ≠ (c, 1)),
    ← orbitRow_spec, ← orbitRow_spec]
  push_cast [compressedRow]
  ring

/-- The compressed orbit's laws, carried with their certificates —
the state leg is the channel's state preservation
(`isState_kchanApply` at `ptrKraus_tp`), exercised at the instance. -/
noncomputable def compressedOrbitPMF (x : Fin 2) : FinPMF (Fin 2) :=
  recordShadowPMF qRecord (ptrace (orbitState x)) (compressedRow x)
    (compressedRow_spec x) qRecord_posSemidef qRecord_sum
    (isState_kchanApply ptrKraus_tp (orbitState_isState x))

noncomputable def compressedOrbitLaw (x : Fin 2) : SubPMF (Fin 2) :=
  (compressedOrbitPMF x).toSubPMF

/-- The compressed trajectory IS the coarse trajectory: the law of the
channel-compressed orbit state equals the pushed orbit law, at every
window. -/
theorem compressedOrbitLaw_eq_coarseLaw (x : Fin 2) :
    compressedOrbitLaw x = coarseLaw x := by
  refine SubPMF.ext' (Finsupp.ext fun c => ?_)
  show compressedRow x c = (coarseLaw x).wt c
  unfold coarseLaw
  rw [SubPMF.map_wt_apply, filter_fst_pair,
    Finset.sum_pair (by simp : ((c, 0) : Fin 2 × Fin 2) ≠ (c, 1))]
  simp [compressedRow]

/-- **The certified validity window rides the compression**: the
effective dynamics tracks the compressed trajectory to `k · 49/625`
at every horizon — the companion module's bound, consumed through the
compression bridge with nothing re-derived. -/
theorem compressed_horizon_bound (x : Fin 2) (k : ℕ) :
    tvDistQ (compressedOrbitLaw ((· + 1)^[k] x))
        (irStep^[k] (compressedOrbitLaw x))
      ≤ (k : ℚ) * (49 / 625) := by
  rw [compressedOrbitLaw_eq_coarseLaw, compressedOrbitLaw_eq_coarseLaw]
  exact horizon_bound x k

end Adequacy

end SuFunctor

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms SuFunctor.Adequacy.compressState_posSemidef
#print axioms SuFunctor.Adequacy.dilateState_posSemidef
#print axioms SuFunctor.Adequacy.compressRecord_posSemidef
#print axioms SuFunctor.Adequacy.dilateRecord_posSemidef
#print axioms SuFunctor.Adequacy.compressState_trace
#print axioms SuFunctor.Adequacy.dilateState_trace
#print axioms SuFunctor.Adequacy.isState_dilateState
#print axioms SuFunctor.Adequacy.compress_dilate
#print axioms SuFunctor.Adequacy.compressRecord_sum
#print axioms SuFunctor.Adequacy.dilateRecord_sum
#print axioms SuFunctor.Adequacy.recordShadow_compressState
#print axioms SuFunctor.Adequacy.recordShadow_dilateState
#print axioms SuFunctor.Adequacy.kchanApply_posSemidef
#print axioms SuFunctor.Adequacy.kchanDual_posSemidef
#print axioms SuFunctor.Adequacy.kchanApply_trace
#print axioms SuFunctor.Adequacy.isState_kchanApply
#print axioms SuFunctor.Adequacy.kchanDual_sum
#print axioms SuFunctor.Adequacy.recordShadow_kchanApply
#print axioms SuFunctor.Adequacy.compressState_eq_kchanApply
#print axioms SuFunctor.Adequacy.ptrKraus_tp
#print axioms SuFunctor.Adequacy.branchIso_isometry
#print axioms SuFunctor.Adequacy.kchanApply_ptrKraus_eq_ptR
#print axioms SuFunctor.Adequacy.qRecord_posSemidef
#print axioms SuFunctor.Adequacy.qRecord_sum
#print axioms SuFunctor.Adequacy.kchanDual_qRecord
#print axioms SuFunctor.Adequacy.ptrace_recordShadow
#print axioms SuFunctor.Adequacy.qPure0_isState
#print axioms SuFunctor.Adequacy.ptrace_pureProd
#print axioms SuFunctor.Adequacy.compressState_branchIso_upState_trace
#print axioms SuFunctor.Adequacy.smallNet_alg
#print axioms SuFunctor.Adequacy.smallNet_Dstar
#print axioms SuFunctor.Adequacy.smallNet_E₃
#print axioms SuFunctor.Adequacy.singleQubitFragment
#print axioms SuFunctor.Adequacy.recordShadow_qRecord_qPure0
#print axioms SuFunctor.Adequacy.smallLaws_pinned
#print axioms SuFunctor.Adequacy.smallMember_law_eq
#print axioms SuFunctor.Adequacy.irLaws_eq_smallLaws
#print axioms SuFunctor.Adequacy.uv_smallIR_containment
#print axioms SuFunctor.Adequacy.uv_smallIR_containment_lower
#print axioms SuFunctor.Adequacy.not_uv_smallIR_containment_zero
#print axioms SuFunctor.Adequacy.compressedRow_spec
#print axioms SuFunctor.Adequacy.compressedOrbitLaw_eq_coarseLaw
#print axioms SuFunctor.Adequacy.compressed_horizon_bound
