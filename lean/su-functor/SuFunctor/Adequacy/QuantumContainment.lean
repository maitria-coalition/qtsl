import SuFunctor.Adequacy.QuantumNet
import QtslAux.QuantumTower
import QtslAux.QRelChain

/-! # Certified abstraction as credal containment: the block-spin toy

Effective field theory, read at the mechanized finite stratum, is a
two-ingredient move: **coarse-grain exactly** (the landed pushforward
calculus — merging record atoms along any map), then **truncate with a
declared tolerance** (matching: the effective theory agrees with the
pushed-forward theory *inside a declared band*, never on the nose).
This module mechanizes the second ingredient and instantiates both on
a two-qubit toy.

* **The ε-vocabulary** (`tvDistQ`, `credalInflate`, `Containment`):
  exact-rational total-variation distance on subprobability rows, the
  ε-inflation of a law set, and the certified-abstraction statement —
  every UV-possible law is IR-accounted-for within ε,
  `∀ μ ∈ laws_UV, f_*(μ) ∈ credal_IR(ε)`.  The quantifier direction is
  soundness: the abstraction never rules out behavior the fine theory
  permits.  The tolerance is *declared, never derived* — a producer's
  search heuristic proposes it; the containment certificate checks it.
  At finite index and rational rows everything is exact arithmetic.
  The row-level pushforward is the fiber sum (`SubPMF.map_wt_apply`),
  it contracts the distance (`tvDistQ_map_le`), and pushing the law is
  measuring the merged observable family
  (`recordShadow_coarsenFamily`).

* **The lax dynamics square** (`lax_horizon`, `stochAct`,
  `Containment.comp`): a one-step defect bound on a step-invariant
  reachable set propagates to every horizon at budget `k · ε` — the
  triangle inequality and nonexpansiveness of the effective step do
  all the work; row-stochastic kernels are total-variation
  contractions (`tvDistQ_stochAct_le`).  Containments compose with
  *additive* budgets (`Containment.comp`): error bars add along a
  refinement tower, which is what lets a tower of effective theories
  carry one certified budget.

* **The block-spin toy, grade A**: two qubits on the landed two-qubit
  fragment, fine records the four computational-basis projectors,
  block map `Prod.fst` (block value = first spin).  The UV credal face
  is a mixture-closed rational segment of states
  (`uvSeg`, `uvSeg_mixClosed`); the IR theory is *independently
  declared* — the block-spin observable family with the ground
  effective state, "the block spin is `0` and nothing evolves" — and
  is **not** the pushforward of the UV theory: containment holds at
  the declared band `49/625` (`uv_ir_containment`), the band is
  attained (`uv_ir_containment_lower`), and containment at `ε = 0` is
  refuted (`not_uv_ir_containment_zero`) — the truncation is genuine,
  `ε > 0` strictly.  The UV mechanism is an exact-rational involutive
  unitary (`UDyn`, the reflection swapping `|01⟩` with
  `(24/25)|00⟩ − (7/25)|11⟩`); the truncated effective mechanism is
  the identity kernel, and the one-step defect meets the same band
  (`onestep_defect`), giving the `k · ε` validity window
  (`horizon_bound`).  The three-stage tower fine → block → total
  composes at budget `49/625 + 0` (`uv_tot_containment`) — the total
  merge is the trivial exact effective theory, by mass conservation.

* **The Sorkin dividend at the instance**: the toy's D-form measure at
  the projective record family is diagonal already at the fine stage
  (`uvMeasure_isDiagonal` — orthogonal branch images; the projective
  instance of records-force-decoherence), so along this tower the
  off-diagonal mass is constantly zero and classicality is absorbing
  from the root (`eftStage_classical`); the monotonicity theorems are
  quoted at the instance (`eftTower_offDiagMass_antitone`,
  `eftTower_leg`).  The nonvacuous strict decoherence drop lives on
  the library's diamond tower, cited not re-proven.  The two
  pushforward notions — measure-level Gram submatrix and row-level
  fiber sum — agree on the toy (`pushforward_probRow_bridge`).

Scope fences: no state-space compression (the record index coarsens,
the matrix algebra does not shrink); no power-counting claim; no
continuum word; 2-categorical packaging of the lax square deferred.
-/

namespace SuFunctor

universe u

open Finset Matrix
open Qtsl.Imprecise Qtsl.DiamondSite Qtsl.QuantumDescent
open Qtsl.QuantumStates Qtsl.QuantumAssembly
open Qtsl.QuantumRecords Qtsl.QuantumDForm
open Qtsl.QuantumCoarseGraining Qtsl.QuantumTower
open scoped ComplexOrder

/-! ## The row-level pushforward, made explicit -/

namespace SubPMF

/-- The mass bound, as a sum over the whole finite carrier. -/
theorem sum_wt_le_one {κ : Type u} [Fintype κ] (μ : SubPMF κ) :
    ∑ v, μ.wt v ≤ 1 := by
  classical
  refine le_trans (le_of_eq ?_) μ.mass_le_one
  refine (Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_).symm
  by_contra h0
  exact ha (Finsupp.mem_support_iff.mpr h0)

/-- **The row-level pushforward is the fiber sum**: the weight of a
coarse outcome is the total fine weight of its preimage. -/
theorem map_wt_apply {X Y : Type u} [Fintype X] [DecidableEq Y]
    (f : X → Y) (μ : SubPMF X) (c : Y) :
    (μ.map f).wt c
      = ∑ a ∈ Finset.univ.filter (fun a => f a = c), μ.wt a := by
  classical
  have h : (μ.map f).wt c
      = ∑ a ∈ μ.wt.support, if f a = c then μ.wt a else 0 := by
    rw [SubPMF.map_wt, Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun a _ => Finsupp.single_apply
  rw [h, Finset.sum_filter]
  refine Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_
  have h0 : μ.wt a = 0 := by
    by_contra h0
    exact ha (Finsupp.mem_support_iff.mpr h0)
  simp [h0]

/-- Pushforwards compose. -/
theorem map_map {X Y Z : Type u} (f : X → Y) (g : Y → Z) (μ : SubPMF X) :
    (μ.map f).map g = μ.map (g ∘ f) :=
  SubPMF.ext' (by
    rw [SubPMF.map_wt, SubPMF.map_wt, SubPMF.map_wt]
    exact (Finsupp.mapDomain_comp).symm)

end SubPMF

namespace Adequacy

/-! ## The ε-vocabulary: exact-rational total variation and inflation -/

/-- **Total-variation distance on subprobability rows**, exact
rational: half the ℓ¹ distance of the weight rows.  At finite carrier
and rational weights, comparison against a declared tolerance is
decidable arithmetic — a certificate, not an estimate. -/
def tvDistQ {κ : Type u} [Fintype κ] (μ ν : SubPMF κ) : ℚ :=
  (∑ α, |μ.wt α - ν.wt α|) / 2

theorem tvDistQ_nonneg {κ : Type u} [Fintype κ] (μ ν : SubPMF κ) :
    0 ≤ tvDistQ μ ν := by
  have h : (0 : ℚ) ≤ ∑ α, |μ.wt α - ν.wt α| :=
    Finset.sum_nonneg fun α _ => abs_nonneg _
  unfold tvDistQ
  linarith

@[simp] theorem tvDistQ_self {κ : Type u} [Fintype κ] (μ : SubPMF κ) :
    tvDistQ μ μ = 0 := by
  unfold tvDistQ
  simp

theorem tvDistQ_comm {κ : Type u} [Fintype κ] (μ ν : SubPMF κ) :
    tvDistQ μ ν = tvDistQ ν μ := by
  unfold tvDistQ
  exact congrArg (· / 2)
    (Finset.sum_congr rfl fun α _ => abs_sub_comm _ _)

theorem tvDistQ_triangle {κ : Type u} [Fintype κ] (μ ν ξ : SubPMF κ) :
    tvDistQ μ ξ ≤ tvDistQ μ ν + tvDistQ ν ξ := by
  have h : (∑ α, |μ.wt α - ξ.wt α|)
      ≤ (∑ α, |μ.wt α - ν.wt α|) + ∑ α, |ν.wt α - ξ.wt α| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun α _ => abs_sub_le _ _ _
  unfold tvDistQ
  linarith

/-- The distance separates points: zero distance is equality of laws. -/
theorem tvDistQ_eq_zero_iff {κ : Type u} [Fintype κ] {μ ν : SubPMF κ} :
    tvDistQ μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    refine SubPMF.ext' (Finsupp.ext fun α => ?_)
    have hsum : (∑ α, |μ.wt α - ν.wt α|) = 0 := by
      unfold tvDistQ at h
      linarith
    have hα := (Finset.sum_eq_zero_iff_of_nonneg
      fun α _ => abs_nonneg _).mp hsum α (Finset.mem_univ α)
    have h0 := abs_eq_zero.mp hα
    linarith
  · rintro rfl
    exact tvDistQ_self μ

/-- The re-homing stitch: the exact-rational distance casts to the
chain module's real total-variation distance on the cast rows. -/
theorem tvDistQ_cast_eq_qrel {κ : Type u} [Fintype κ] (μ ν : SubPMF κ) :
    ((tvDistQ μ ν : ℚ) : ℝ)
      = Qtsl.QRelChain.tvDist (fun l => (μ.wt l : ℝ))
          (fun l => (ν.wt l : ℝ)) := by
  unfold tvDistQ Qtsl.QRelChain.tvDist
  push_cast
  rfl

/-- **Pushforward contracts total variation** — the row-level face of
"coarse-graining never manufactures distinguishability". -/
theorem tvDistQ_map_le {X Y : Type u} [Fintype X] [Fintype Y]
    (f : X → Y) (μ ν : SubPMF X) :
    tvDistQ (μ.map f) (ν.map f) ≤ tvDistQ μ ν := by
  classical
  have key : ∀ c, |(μ.map f).wt c - (ν.map f).wt c|
      ≤ ∑ a ∈ Finset.univ.filter (fun a => f a = c),
          |μ.wt a - ν.wt a| := by
    intro c
    rw [SubPMF.map_wt_apply, SubPMF.map_wt_apply,
      ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hsum : (∑ c, ∑ a ∈ Finset.univ.filter (fun a => f a = c),
      |μ.wt a - ν.wt a|) = ∑ a, |μ.wt a - ν.wt a| :=
    Finset.sum_fiberwise Finset.univ f _
  have h := (Finset.sum_le_sum
    fun c (_ : c ∈ Finset.univ) => key c).trans_eq hsum
  unfold tvDistQ
  linarith

/-- **The ε-inflation of a law set**: the laws within declared
tolerance of some member.  Error bars become imprecision. -/
def credalInflate {κ : Type u} [Fintype κ] (ε : ℚ)
    (L : SubPMF κ → Prop) : SubPMF κ → Prop :=
  fun ν => ∃ ν', L ν' ∧ tvDistQ ν ν' ≤ ε

theorem credalInflate_mono {κ : Type u} [Fintype κ] {ε ε' : ℚ}
    (h : ε ≤ ε') (L : SubPMF κ → Prop) {ν : SubPMF κ}
    (hν : credalInflate ε L ν) : credalInflate ε' L ν := by
  obtain ⟨ν', hL, hd⟩ := hν
  exact ⟨ν', hL, hd.trans h⟩

theorem credalInflate_mono_set {κ : Type u} [Fintype κ] (ε : ℚ)
    {L L' : SubPMF κ → Prop} (h : ∀ ν, L ν → L' ν) {ν : SubPMF κ}
    (hν : credalInflate ε L ν) : credalInflate ε L' ν := by
  obtain ⟨ν', hL, hd⟩ := hν
  exact ⟨ν', h ν' hL, hd⟩

theorem credalInflate_self {κ : Type u} [Fintype κ] {ε : ℚ}
    (hε : 0 ≤ ε) (L : SubPMF κ → Prop) {ν : SubPMF κ} (hν : L ν) :
    credalInflate ε L ν :=
  ⟨ν, hν, by rw [tvDistQ_self]; exact hε⟩

/-- At `ε = 0` the inflation collapses to the set itself: the exact
and the ε-graded readings agree at zero tolerance. -/
theorem credalInflate_zero_iff {κ : Type u} [Fintype κ]
    (L : SubPMF κ → Prop) (ν : SubPMF κ) :
    credalInflate 0 L ν ↔ L ν := by
  constructor
  · rintro ⟨ν', hL, hd⟩
    have h0 : tvDistQ ν ν' = 0 := le_antisymm hd (tvDistQ_nonneg ν ν')
    rwa [tvDistQ_eq_zero_iff.mp h0]
  · exact credalInflate_self le_rfl L

/-- Inflation distributes over union — union-shaped law sets stay
union-shaped. -/
theorem credalInflate_or {κ : Type u} [Fintype κ] (ε : ℚ)
    (L₁ L₂ : SubPMF κ → Prop) (ν : SubPMF κ) :
    credalInflate ε (fun μ => L₁ μ ∨ L₂ μ) ν
      ↔ credalInflate ε L₁ ν ∨ credalInflate ε L₂ ν := by
  constructor
  · rintro ⟨ν', hL | hL, hd⟩
    · exact Or.inl ⟨ν', hL, hd⟩
    · exact Or.inr ⟨ν', hL, hd⟩
  · rintro (⟨ν', hL, hd⟩ | ⟨ν', hL, hd⟩)
    · exact ⟨ν', Or.inl hL, hd⟩
    · exact ⟨ν', Or.inr hL, hd⟩

/-- Inflating a union of singletons: membership is proximity to some
member — the shape the quantum law sets wear. -/
theorem credalInflate_unionSingletons {κ : Type u} [Fintype κ]
    {ι' : Sort _} (ε : ℚ) (g : ι' → SubPMF κ) (ν : SubPMF κ) :
    credalInflate ε (unionSingletons g) ν
      ↔ ∃ i, tvDistQ ν (g i) ≤ ε := by
  constructor
  · rintro ⟨ν', ⟨i, hs⟩, hd⟩
    obtain rfl : ν' = g i := (singletonC_iff _ _).mp hs
    exact ⟨i, hd⟩
  · rintro ⟨i, hd⟩
    exact ⟨g i, ⟨i, singletonC_self _⟩, hd⟩

/-- **Certified abstraction as credal containment**: every UV-possible
law, pushed along the coarse-graining, lies within the declared
tolerance of the IR theory's law set.  The soundness direction — the
abstraction never rules out behavior the fine theory permits. -/
def Containment {ι κ : Type u} [Fintype ι] [Fintype κ]
    (LUV : SubPMF ι → Prop) (f : ι → κ)
    (LIR : SubPMF κ → Prop) (ε : ℚ) : Prop :=
  ∀ μ, LUV μ → credalInflate ε LIR (μ.map f)

theorem Containment.mono {ι κ : Type u} [Fintype ι] [Fintype κ]
    {LUV : SubPMF ι → Prop} {f : ι → κ} {LIR : SubPMF κ → Prop}
    {ε ε' : ℚ} (h : ε ≤ ε')
    (hc : Containment LUV f LIR ε) : Containment LUV f LIR ε' :=
  fun μ hμ => credalInflate_mono h LIR (hc μ hμ)

set_option maxHeartbeats 800000 in
/-- **Budgets add along towers**: containments compose, with the
composite tolerance the sum of the stage tolerances.  Triangle
inequality plus pushforward contraction do all the work. -/
theorem Containment.comp {ι κ σ : Type u}
    [Fintype ι] [Fintype κ] [Fintype σ]
    {L₁ : SubPMF ι → Prop} {f : ι → κ} {L₂ : SubPMF κ → Prop} {ε₁ : ℚ}
    {g : κ → σ} {L₃ : SubPMF σ → Prop} {ε₂ : ℚ}
    (h₁ : Containment L₁ f L₂ ε₁) (h₂ : Containment L₂ g L₃ ε₂) :
    Containment L₁ (g ∘ f) L₃ (ε₁ + ε₂) := by
  intro μ hμ
  obtain ⟨ν', hν', hd₁⟩ := h₁ μ hμ
  obtain ⟨ν'', hν'', hd₂⟩ := h₂ ν' hν'
  refine ⟨ν'', hν'', ?_⟩
  rw [← SubPMF.map_map f g μ]
  have t1 : tvDistQ ((μ.map f).map g) ν''
      ≤ tvDistQ ((μ.map f).map g) (ν'.map g) + tvDistQ (ν'.map g) ν'' :=
    tvDistQ_triangle ((μ.map f).map g) (ν'.map g) ν''
  have t2 : tvDistQ ((μ.map f).map g) (ν'.map g) ≤ tvDistQ (μ.map f) ν' :=
    tvDistQ_map_le g (μ.map f) ν'
  linarith

/-! ## Coarsened observables measure the pushed law -/

/-- Sums of positive-semidefinite matrices are positive-semidefinite. -/
private theorem posSemidef_sum' {β : Type*} {d : Type*} [Fintype d]
    {s : Finset β} {f : β → Matrix d d ℂ}
    (h : ∀ b ∈ s, (f b).PosSemidef) : (∑ b ∈ s, f b).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

/-- **Pushing the law is measuring the block observable**: the Born
row of a coarsened family is the fiber sum of the fine Born row —
linearity of the trace. -/
theorem recordShadow_coarsenFamily {ι' κ' : Type*} [Fintype ι']
    [Fintype κ'] [DecidableEq ι'] [DecidableEq κ']
    {d : Type*} [Fintype d]
    (f : ι' → κ') (R : ι' → Matrix d d ℂ) (ρ : Matrix d d ℂ) (c : κ') :
    recordShadow (coarsenFamily f R) ρ c
      = ∑ a ∈ fiber f c, recordShadow R ρ a := by
  unfold recordShadow coarsenFamily
  rw [Finset.mul_sum, Matrix.trace_sum, Complex.re_sum]

/-! ## The lax dynamics square -/

/-- A row-stochastic rational kernel acting on subprobability rows:
the effective (classical) mechanism at the coarse stratum. -/
noncomputable def stochAct {κ : Type u} [Fintype κ] (Q : κ → κ → ℚ)
    (hQ0 : ∀ c c', 0 ≤ Q c c') (hQ1 : ∀ c, ∑ c', Q c c' = 1)
    (μ : SubPMF κ) : SubPMF κ where
  wt := Finsupp.onFinset Finset.univ (fun c => ∑ c', μ.wt c' * Q c' c)
    (fun _ _ => Finset.mem_univ _)
  nonneg := fun c =>
    Finset.sum_nonneg fun c' _ => mul_nonneg (μ.nonneg c') (hQ0 c' c)
  mass_le_one := by
    classical
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun c _ _ =>
        Finset.sum_nonneg fun c' _ =>
          mul_nonneg (μ.nonneg c') (hQ0 c' c))) ?_
    show (∑ c, ∑ c', μ.wt c' * Q c' c) ≤ 1
    have hswap : (∑ c, ∑ c', μ.wt c' * Q c' c) = ∑ c', μ.wt c' := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c' _ => by
        rw [← Finset.mul_sum, hQ1 c', mul_one]
    rw [hswap]
    exact μ.sum_wt_le_one

@[simp] theorem stochAct_wt {κ : Type u} [Fintype κ] (Q : κ → κ → ℚ)
    (hQ0 : ∀ c c', 0 ≤ Q c c') (hQ1 : ∀ c, ∑ c', Q c c' = 1)
    (μ : SubPMF κ) (c : κ) :
    (stochAct Q hQ0 hQ1 μ).wt c = ∑ c', μ.wt c' * Q c' c :=
  rfl

/-- **Stochastic maps contract total variation** at row grade. -/
theorem tvDistQ_stochAct_le {κ : Type u} [Fintype κ] (Q : κ → κ → ℚ)
    (hQ0 : ∀ c c', 0 ≤ Q c c') (hQ1 : ∀ c, ∑ c', Q c c' = 1)
    (μ ν : SubPMF κ) :
    tvDistQ (stochAct Q hQ0 hQ1 μ) (stochAct Q hQ0 hQ1 ν)
      ≤ tvDistQ μ ν := by
  have key : ∀ c,
      |(stochAct Q hQ0 hQ1 μ).wt c - (stochAct Q hQ0 hQ1 ν).wt c|
        ≤ ∑ c', |μ.wt c' - ν.wt c'| * Q c' c := by
    intro c
    rw [stochAct_wt, stochAct_wt, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [← sub_mul, abs_mul, abs_of_nonneg (hQ0 c' c)]
  have hsum : (∑ c, ∑ c', |μ.wt c' - ν.wt c'| * Q c' c)
      = ∑ c', |μ.wt c' - ν.wt c'| := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c' _ => by
      rw [← Finset.mul_sum, hQ1 c', mul_one]
  have h := (Finset.sum_le_sum
    fun c (_ : c ∈ Finset.univ) => key c).trans_eq hsum
  unfold tvDistQ
  linarith

/-- **The lax square propagates to every horizon**: a one-step defect
bound `ε` on a step-invariant reachable set, a nonexpansive effective
step, and the triangle inequality give the `k · ε` budget — the
certified validity window of an effective dynamics. -/
theorem lax_horizon {A : Type*} {B : Type*}
    (push : A → B) (stepA : A → A) (stepB : B → B)
    (d : B → B → ℚ) (ε : ℚ) (Reach : A → Prop)
    (hself : ∀ x, d x x = 0)
    (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (hnonexp : ∀ x y, d (stepB x) (stepB y) ≤ d x y)
    (hinv : ∀ a, Reach a → Reach (stepA a))
    (hdef : ∀ a, Reach a → d (push (stepA a)) (stepB (push a)) ≤ ε) :
    ∀ a, Reach a → ∀ k : ℕ,
      d (push (stepA^[k] a)) (stepB^[k] (push a)) ≤ (k : ℚ) * ε := by
  have hiter : ∀ (k : ℕ) (x y : B),
      d (stepB^[k] x) (stepB^[k] y) ≤ d x y := by
    intro k
    induction k with
    | zero => intro x y; simp
    | succ k ih =>
      intro x y
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact (ih _ _).trans (hnonexp x y)
  have main : ∀ (k : ℕ) (a : A), Reach a →
      d (push (stepA^[k] a)) (stepB^[k] (push a)) ≤ (k : ℚ) * ε := by
    intro k
    induction k with
    | zero =>
      intro a _
      simp [hself]
    | succ k ih =>
      intro a ha
      have h1 := ih (stepA a) (hinv a ha)
      have h2 : d (stepB^[k] (push (stepA a)))
          (stepB^[k + 1] (push a)) ≤ ε := by
        rw [Function.iterate_succ_apply]
        exact (hiter k _ _).trans (hdef a ha)
      rw [Function.iterate_succ_apply]
      refine le_trans (htri _ (stepB^[k] (push (stepA a))) _) ?_
      push_cast
      linarith
  exact fun a ha k => main k a ha

/-! ## The block-spin toy: UV data -/

/-- The `|01⟩` basis vector. -/
noncomputable def e01 : Fin 2 × Fin 2 → ℂ :=
  Pi.single ((0 : Fin 2), (1 : Fin 2)) 1

/-- A rational two-branch amplitude table: `a` on `|00⟩`, `b` on
`|11⟩`. -/
def mkPhiQ (a b : ℚ) : Fin 2 × Fin 2 → ℚ := fun ik =>
  if ik = ((0 : Fin 2), (0 : Fin 2)) then a
  else if ik = ((1 : Fin 2), (1 : Fin 2)) then b else 0

/-- The complex branch vector. -/
noncomputable def mkPhi (a b : ℚ) : Fin 2 × Fin 2 → ℂ := fun ik =>
  ((mkPhiQ a b ik : ℚ) : ℂ)

theorem star_mkPhi (a b : ℚ) : star (mkPhi a b) = mkPhi a b := by
  funext ik
  simp [mkPhi, Pi.star_apply, star_ratCast]

/-- The branch vector vanishes on the `|01⟩` slot: it is orthogonal to
its swap partner. -/
theorem mkPhi_apply_01 (a b : ℚ) :
    mkPhi a b ((0 : Fin 2), (1 : Fin 2)) = 0 := by
  simp [mkPhi, mkPhiQ]

/-- `|01⟩⟨01|` — the UV distinguished pure state. -/
noncomputable def upState : TwoQubits :=
  zzRecord ((0 : Fin 2), (1 : Fin 2))

theorem upState_vecMulVec :
    upState = Matrix.vecMulVec e01 (star e01) := by
  rw [show star e01 = e01 from star_pi_single_one _]
  exact Matrix.single_eq_single_vecMulVec_single _ _

theorem upState_trace : upState.trace = 1 := by
  have h := Qtsl.QuantumDescent.trace_mul_single (1 : TwoQubits)
    ((0 : Fin 2), (1 : Fin 2)) ((0 : Fin 2), (1 : Fin 2)) (1 : ℂ)
  simp only [one_mul, Matrix.one_apply_eq, mul_one] at h
  exact h

theorem upState_isState : IsState upState :=
  ⟨zzRecord_posSemidef _, upState_trace⟩

/-- The outer product of a branch vector. -/
noncomputable def mkOuter (a b : ℚ) : TwoQubits :=
  Matrix.vecMulVec (mkPhi a b) (star (mkPhi a b))

theorem mkOuter_trace (a b : ℚ) :
    (mkOuter a b).trace = ((a * a + b * b : ℚ) : ℂ) := by
  have h := trace_mul_vecMulVec (1 : TwoQubits) (mkPhi a b) (mkPhi a b)
  rw [one_mul, Matrix.one_mulVec] at h
  rw [mkOuter, h]
  show (∑ ik, (star (mkPhi a b)) ik * mkPhi a b ik) = _
  have hterm : ∀ ik, (star (mkPhi a b)) ik * mkPhi a b ik
      = ((mkPhiQ a b ik * mkPhiQ a b ik : ℚ) : ℂ) := fun ik => by
    simp only [Pi.star_apply, mkPhi, star_ratCast]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun ik _ => hterm ik]
  norm_cast
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [mkPhiQ]

set_option maxHeartbeats 1600000 in
theorem mkOuter_isState (a b : ℚ) (h : a * a + b * b = 1) :
    IsState (mkOuter a b) := by
  constructor
  · unfold mkOuter
    exact posSemidef_vecMulVec_star_self (mkPhi a b)
  · rw [mkOuter_trace, h]
    norm_num

/-- The zz Born row of a branch outer product: squared amplitudes. -/
theorem recordShadow_zz_mkOuter (a b : ℚ) (ik : Fin 2 × Fin 2) :
    recordShadow zzRecord (mkOuter a b) ik
      = ((mkPhiQ a b ik * mkPhiQ a b ik : ℚ) : ℝ) := by
  show ((mkOuter a b * Matrix.single ik ik 1).trace).re = _
  rw [Qtsl.QuantumDescent.trace_mul_single, one_mul]
  show (Matrix.vecMulVec (mkPhi a b) (star (mkPhi a b)) ik ik).re = _
  rw [Matrix.vecMulVec_apply]
  simp only [Pi.star_apply, mkPhi, star_ratCast]
  rw [show ((mkPhiQ a b ik : ℚ) : ℂ) * ((mkPhiQ a b ik : ℚ) : ℂ)
      = (((mkPhiQ a b ik * mkPhiQ a b ik : ℚ)) : ℂ) by push_cast; ring]
  exact Complex.ratCast_re _

/-- The zz Born row of `|01⟩⟨01|`. -/
theorem recordShadow_zz_upState (ik : Fin 2 × Fin 2) :
    recordShadow zzRecord upState ik
      = if ik = ((0 : Fin 2), (1 : Fin 2)) then (1 : ℝ) else 0 := by
  show ((upState * Matrix.single ik ik 1).trace).re = _
  rw [Qtsl.QuantumDescent.trace_mul_single, one_mul]
  show ((Matrix.single ((0 : Fin 2), (1 : Fin 2))
    ((0 : Fin 2), (1 : Fin 2)) (1 : ℂ)) ik ik).re = _
  fin_cases ik <;>
    norm_num [Matrix.single, Matrix.of_apply, ite_and]

/-- The kinematic 24-7 branch state `(24/25)|00⟩ − (7/25)|11⟩`. -/
noncomputable def entState : TwoQubits := mkOuter (24 / 25) (-(7 / 25))

theorem entState_isState : IsState entState :=
  mkOuter_isState _ _ (by norm_num)

/-- The `|01⟩` extreme's rational zz row. -/
def upRow : Fin 2 × Fin 2 → ℚ := fun ik =>
  if ik = ((0 : Fin 2), (1 : Fin 2)) then 1 else 0

/-- The 24-7 branch state's rational zz row. -/
def entRow : Fin 2 × Fin 2 → ℚ := fun ik =>
  if ik = ((0 : Fin 2), (0 : Fin 2)) then 576 / 625
  else if ik = ((1 : Fin 2), (1 : Fin 2)) then 49 / 625 else 0

theorem upRow_spec (ik : Fin 2 × Fin 2) :
    ((upRow ik : ℚ) : ℝ) = recordShadow zzRecord upState ik := by
  rw [recordShadow_zz_upState]
  rcases eq_or_ne ik ((0 : Fin 2), (1 : Fin 2)) with rfl | h
  · norm_num [upRow]
  · simp [upRow, h]

theorem entRow_spec (ik : Fin 2 × Fin 2) :
    ((entRow ik : ℚ) : ℝ) = recordShadow zzRecord entState ik := by
  show _ = recordShadow zzRecord (mkOuter (24 / 25) (-(7 / 25))) ik
  rw [recordShadow_zz_mkOuter]
  norm_cast
  fin_cases ik <;> norm_num [entRow, mkPhiQ]

/-! ## The UV credal face: a mixture-closed rational segment -/

/-- The UV state set: the rational segment between the `|01⟩` extreme
and the 24-7 branch state. -/
def uvSeg : Set {ρ : TwoQubits // IsState ρ} :=
  {x | ∃ t : ℚ, 0 ≤ t ∧ t ≤ 1 ∧
    x.1 = ((t : ℚ) : ℂ) • upState + (((1 - t : ℚ)) : ℂ) • entState}

/-- The segment is closed under rational convex mixture — the credal
face's hypothesis, exercised. -/
theorem uvSeg_mixClosed : QNet.MixClosed uvSeg := by
  rintro ⟨ρ, hρ⟩ ⟨σ, hσ⟩ ⟨t₁, ht₁0, ht₁1, hρe⟩ ⟨t₂, ht₂0, ht₂1, hσe⟩
    s hs0 hs1
  refine ⟨s * t₁ + (1 - s) * t₂, ?_, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg hs0 ht₁0)
      (mul_nonneg (by linarith) ht₂0)
  · nlinarith
  · have hρe' : ρ = ((t₁ : ℚ) : ℂ) • upState
        + (((1 - t₁ : ℚ)) : ℂ) • entState := hρe
    have hσe' : σ = ((t₂ : ℚ) : ℂ) • upState
        + (((1 - t₂ : ℚ)) : ℂ) • entState := hσe
    show ((s : ℚ) : ℂ) • ρ + (((1 - s : ℚ)) : ℂ) • σ = _
    rw [hρe', hσe']
    push_cast
    module

/-- Membership extraction: every rational-shadowed member of the
segment carries the segment parameter, and its row is pinned to the
affine combination of the extreme rows. -/
theorem uvSeg_member_row
    (w : QNet.RatShadowMember isingQubitFragment uvSeg) :
    ∃ t : ℚ, 0 ≤ t ∧ t ≤ 1 ∧
      ∀ α, w.row α = t * upRow α + (1 - t) * entRow α := by
  obtain ⟨t, h₀, h₁, hstate⟩ := w.mem
  refine ⟨t, h₀, h₁, fun α => ?_⟩
  have hspec : ((w.row α : ℚ) : ℝ)
      = recordShadow zzRecord w.state.1 α := w.row_spec α
  rw [hstate, recordShadow_mix zzRecord upState entState α,
    ← upRow_spec α, ← entRow_spec α] at hspec
  exact_mod_cast hspec

/-- The `|01⟩` extreme, as a rational-shadowed member. -/
noncomputable def upMember :
    QNet.RatShadowMember isingQubitFragment uvSeg where
  state := ⟨upState, upState_isState⟩
  mem := ⟨1, by norm_num, le_refl 1, by push_cast; module⟩
  row := upRow
  row_spec := fun α => upRow_spec α

/-- The 24-7 branch extreme, as a rational-shadowed member. -/
noncomputable def entMember :
    QNet.RatShadowMember isingQubitFragment uvSeg where
  state := ⟨entState, entState_isState⟩
  mem := ⟨0, le_refl 0, by norm_num, by push_cast; module⟩
  row := entRow
  row_spec := fun α => entRow_spec α

/-- **The credal face is exercised**: the midpoint mixture of the two
extreme members' laws lies in the UV law set — through the landed
convexity seam, consuming mixture-closedness. -/
theorem uvLaws_mix_exercised :
    QNet.quantumLaws isingQubitFragment uvSeg
      ((FinPMF.mix upMember.pmf entMember.pmf (1 / 2)
        (by norm_num) (by norm_num)).toSubPMF) :=
  QNet.quantumLaws_mix uvSeg_mixClosed upMember entMember
    (by norm_num) (by norm_num)

/-! ## The IR theory, independently declared -/

/-- The block-spin observable family: the two rank-two projectors
obtained by merging the fine records along the block map. -/
noncomputable def blockRecord : Fin 2 → TwoQubits :=
  coarsenFamily Prod.fst zzRecord

theorem blockRecord_posSemidef (c : Fin 2) :
    (blockRecord c).PosSemidef :=
  posSemidef_sum' fun a _ => zzRecord_posSemidef a

theorem blockRecord_sum : ∑ c, blockRecord c = 1 :=
  coarsenFamily_complete Prod.fst zzRecord_sum

theorem blockRecord_mem (c : Fin 2) :
    blockRecord c ∈ qubitNet.alg Dstar := by
  rw [qubitNet_Dstar]
  exact Algebra.mem_top

/-- The IR fragment: the same net, spacetime, matter, and mechanism as
the landed two-qubit fragment — only the record family coarsens to the
block-spin observables.  Effective theories truncate observables, not
spacetime. -/
noncomputable def irFragment :
    LCQFTFragment (Mink ℝ) (Fin 2 × Fin 2) (Fin 2) ℝ (Fin 2) :=
  { isingQubitFragment with
    records := blockRecord
    records_mem := blockRecord_mem
    records_posSemidef := blockRecord_posSemidef
    records_exhaustive := blockRecord_sum }

/-- The IR effective row: the block spin is `0`. -/
def irRow : Fin 2 → ℚ := fun c => if c = 0 then 1 else 0

/-- The zz row of the ground state. -/
theorem recordShadow_zz_pureProd (ik : Fin 2 × Fin 2) :
    recordShadow zzRecord pureProd ik
      = if ik = ((0 : Fin 2), (0 : Fin 2)) then (1 : ℝ) else 0 := by
  show ((pureProd * Matrix.single ik ik 1).trace).re = _
  rw [Qtsl.QuantumDescent.trace_mul_single, one_mul]
  fin_cases ik <;>
    norm_num [pureProd, Matrix.diagonal_apply_eq]

/-- The block fibers, computed once. -/
private theorem fiber_fst (c : Fin 2) :
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

private theorem filter_fst (c : Fin 2) :
    (Finset.univ.filter fun a : Fin 2 × Fin 2 => Prod.fst a = c)
      = {(c, 0), (c, 1)} :=
  fiber_fst c

/-- The block-spin row of the ground state is the IR effective row. -/
theorem blockRecord_shadow_pureProd (c : Fin 2) :
    recordShadow blockRecord pureProd c = ((irRow c : ℚ) : ℝ) := by
  show recordShadow (coarsenFamily Prod.fst zzRecord) pureProd c = _
  rw [recordShadow_coarsenFamily, fiber_fst,
    Finset.sum_pair (by simp : ((c, 0) : Fin 2 × Fin 2) ≠ (c, 1)),
    recordShadow_zz_pureProd, recordShadow_zz_pureProd]
  have hc : c = 0 ∨ c = 1 := by omega
  rcases hc with rfl | rfl <;> norm_num [irRow, Prod.mk.injEq]

/-- The IR state set: the ground effective state alone. -/
def irSet : Set {ρ : TwoQubits // IsState ρ} :=
  {⟨pureProd, pureProd_isState⟩}

/-- The IR theory's one rational-shadowed member. -/
noncomputable def irMember : QNet.RatShadowMember irFragment irSet where
  state := ⟨pureProd, pureProd_isState⟩
  mem := rfl
  row := irRow
  row_spec := fun c => (blockRecord_shadow_pureProd c).symm

/-- The IR law set is pinned: every member's law is the effective
row. -/
theorem irLaws_pinned (ν : SubPMF (Fin 2))
    (h : QNet.quantumLaws irFragment irSet ν) : ν = irMember.law := by
  obtain ⟨w, hw⟩ := h
  obtain rfl : ν = w.law := (singletonC_iff _ _).mp hw
  refine SubPMF.ext' (Finsupp.ext fun c => ?_)
  show w.row c = irMember.row c
  have hst : w.state = ⟨pureProd, pureProd_isState⟩ :=
    Set.mem_singleton_iff.mp w.mem
  have h1 : ((w.row c : ℚ) : ℝ)
      = recordShadow blockRecord pureProd c := by
    have hs := w.row_spec c
    rw [hst] at hs
    exact hs
  have h2 : ((irMember.row c : ℚ) : ℝ)
      = recordShadow blockRecord pureProd c :=
    (blockRecord_shadow_pureProd c).symm
  exact_mod_cast h1.trans h2.symm

/-! ## The containment certificate -/

/-- The pushed weight of a segment member at block value `0`. -/
private theorem seg_pushed_wt0
    (w : QNet.RatShadowMember isingQubitFragment uvSeg) {t : ℚ}
    (hrow : ∀ α, w.row α = t * upRow α + (1 - t) * entRow α) :
    (w.law.map Prod.fst).wt 0 = t + (1 - t) * (576 / 625) := by
  rw [SubPMF.map_wt_apply]
  rw [show (Finset.univ.filter fun a : Fin 2 × Fin 2 => a.1 = 0)
      = ({((0 : Fin 2), (0 : Fin 2)), ((0 : Fin 2), (1 : Fin 2))} :
        Finset (Fin 2 × Fin 2)) from by decide]
  rw [Finset.sum_pair (by decide)]
  simp only [QNet.RatShadowMember.law_wt, hrow]
  simp [upRow, entRow]
  ring

/-- The pushed weight of a segment member at block value `1`. -/
private theorem seg_pushed_wt1
    (w : QNet.RatShadowMember isingQubitFragment uvSeg) {t : ℚ}
    (hrow : ∀ α, w.row α = t * upRow α + (1 - t) * entRow α) :
    (w.law.map Prod.fst).wt 1 = (1 - t) * (49 / 625) := by
  rw [SubPMF.map_wt_apply]
  rw [show (Finset.univ.filter fun a : Fin 2 × Fin 2 => a.1 = 1)
      = ({((1 : Fin 2), (0 : Fin 2)), ((1 : Fin 2), (1 : Fin 2))} :
        Finset (Fin 2 × Fin 2)) from by decide]
  rw [Finset.sum_pair (by decide)]
  simp only [QNet.RatShadowMember.law_wt, hrow]
  simp [upRow, entRow]

/-- **The block-spin containment certificate**: every UV-possible law,
pushed along the block map, lies within the declared band `49/625` of
the IR theory.  The pushed distance at segment parameter `t` is
`(1 − t) · 49/625`. -/
theorem uv_ir_containment :
    Containment (QNet.quantumLaws isingQubitFragment uvSeg) Prod.fst
      (QNet.quantumLaws irFragment irSet) (49 / 625) := by
  rintro μ ⟨w, hw⟩
  obtain rfl : μ = w.law := (singletonC_iff _ _).mp hw
  obtain ⟨t, h₀, h₁, hrow⟩ := uvSeg_member_row w
  refine ⟨irMember.law, ⟨irMember, singletonC_self _⟩, ?_⟩
  unfold tvDistQ
  rw [Fin.sum_univ_two, seg_pushed_wt0 w hrow, seg_pushed_wt1 w hrow]
  have hlaw0 : irMember.law.wt 0 = 1 := by
    show irRow 0 = 1
    norm_num [irRow]
  have hlaw1 : irMember.law.wt 1 = 0 := by
    show irRow 1 = 0
    norm_num [irRow]
  rw [hlaw0, hlaw1, sub_zero,
    show t + (1 - t) * (576 / 625) - 1 = -((1 - t) * (49 / 625)) by ring,
    abs_neg,
    abs_of_nonneg (mul_nonneg (by linarith)
      (by norm_num : (0 : ℚ) ≤ 49 / 625))]
  linarith

/-- **The band is attained**: no smaller tolerance certifies the
containment — the 24-7 extreme sits at exactly `49/625` from the IR
theory. -/
theorem uv_ir_containment_lower (ε : ℚ)
    (h : Containment (QNet.quantumLaws isingQubitFragment uvSeg)
      Prod.fst (QNet.quantumLaws irFragment irSet) ε) :
    49 / 625 ≤ ε := by
  obtain ⟨ν', hν', hd⟩ := h entMember.law ⟨entMember, singletonC_self _⟩
  obtain rfl : ν' = irMember.law := irLaws_pinned ν' hν'
  have hrow : ∀ α, entMember.row α
      = 0 * upRow α + (1 - 0) * entRow α := by
    intro α
    show entRow α = _
    ring
  have hd' : tvDistQ (entMember.law.map Prod.fst) irMember.law
      = 49 / 625 := by
    unfold tvDistQ
    rw [Fin.sum_univ_two, seg_pushed_wt0 entMember hrow,
      seg_pushed_wt1 entMember hrow]
    have hlaw0 : irMember.law.wt 0 = 1 := by
      show irRow 0 = 1
      norm_num [irRow]
    have hlaw1 : irMember.law.wt 1 = 0 := by
      show irRow 1 = 0
      norm_num [irRow]
    rw [hlaw0, hlaw1]
    norm_num
  linarith [hd' ▸ hd]

/-- **The truncation is genuine**: containment at zero tolerance is
refuted — the IR theory is *not* the pushforward of the UV theory, and
`ε > 0` strictly is where the effective-theory content lives. -/
theorem not_uv_ir_containment_zero :
    ¬ Containment (QNet.quantumLaws isingQubitFragment uvSeg) Prod.fst
      (QNet.quantumLaws irFragment irSet) 0 := by
  intro h
  have := uv_ir_containment_lower 0 h
  norm_num at this

/-! ## The dynamics: an exact-rational mechanism and its truncation -/

private theorem pi_single_dot {d : Type*} [Fintype d] [DecidableEq d]
    (i : d) (ψ : d → ℂ) : Pi.single i (1 : ℂ) ⬝ᵥ ψ = ψ i := by
  simp [dotProduct, Pi.single_apply]

/-- The zz projectors act on vectors by slot extraction. -/
private theorem zz_mulVec (α : Fin 2 × Fin 2) (ψ : Fin 2 × Fin 2 → ℂ) :
    zzRecord α *ᵥ ψ = ψ α • Pi.single α (1 : ℂ) := by
  show Matrix.single α α (1 : ℂ) *ᵥ ψ = _
  rw [Matrix.single_eq_single_vecMulVec_single, Matrix.vecMulVec_mulVec,
    pi_single_dot, op_smul_eq_smul]

/-- The dynamics-side branch vector (its own definition site). -/
noncomputable def phiDyn : Fin 2 × Fin 2 → ℂ := mkPhi (24 / 25) (-(7 / 25))

/-- The dynamics-side branch state. -/
noncomputable def entStateDyn : TwoQubits := mkOuter (24 / 25) (-(7 / 25))

theorem entStateDyn_isState : IsState entStateDyn :=
  mkOuter_isState _ _ (by norm_num)

/-- The dynamics-side concrete zz row. -/
def entRowDyn : Fin 2 × Fin 2 → ℚ := fun ik =>
  if ik = ((0 : Fin 2), (0 : Fin 2)) then 576 / 625
  else if ik = ((1 : Fin 2), (1 : Fin 2)) then 49 / 625 else 0

theorem entRowDyn_spec (ik : Fin 2 × Fin 2) :
    ((entRowDyn ik : ℚ) : ℝ)
      = recordShadow zzRecord entStateDyn ik := by
  show _ = recordShadow zzRecord (mkOuter (24 / 25) (-(7 / 25))) ik
  rw [recordShadow_zz_mkOuter]
  norm_cast
  fin_cases ik <;> norm_num [entRowDyn, mkPhiQ]

/-- **The UV mechanism**: the reflection swapping `|01⟩` with the 24-7
branch vector — identity on the orthogonal complement, exact rational
entries, self-adjoint, involutive. -/
noncomputable def UDyn : TwoQubits :=
  1 - Matrix.vecMulVec e01 (star e01)
    - Matrix.vecMulVec phiDyn (star phiDyn)
    + Matrix.vecMulVec phiDyn (star e01)
    + Matrix.vecMulVec e01 (star phiDyn)

/-- Conjugation transports outer products along the vector action. -/
theorem conj_vecMulVec {d : Type*} [Fintype d]
    (A : Matrix d d ℂ) (u v : d → ℂ) :
    A * Matrix.vecMulVec u (star v) * Aᴴ
      = Matrix.vecMulVec (A *ᵥ u) (star (A *ᵥ v)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Pi.star_apply, star_sum, star_mul']
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem conjTranspose_vecMulVec' {d : Type*} [Fintype d]
    (u v : d → ℂ) :
    (Matrix.vecMulVec u (star v))ᴴ = Matrix.vecMulVec v (star u) := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, star_mul', mul_comm]

/-- The inner-product table of the swapped pair. -/
private theorem dot_e01_e01 : star e01 ⬝ᵥ e01 = 1 := by
  rw [show star e01 = e01 from star_pi_single_one _]
  show Pi.single ((0 : Fin 2), (1 : Fin 2)) (1 : ℂ) ⬝ᵥ e01 = 1
  rw [pi_single_dot]
  simp [e01]

private theorem dot_e01_phi : star e01 ⬝ᵥ phiDyn = 0 := by
  rw [show star e01 = e01 from star_pi_single_one _]
  show Pi.single ((0 : Fin 2), (1 : Fin 2)) (1 : ℂ) ⬝ᵥ phiDyn = 0
  rw [pi_single_dot]
  exact mkPhi_apply_01 _ _

private theorem dot_phi_e01 : star phiDyn ⬝ᵥ e01 = 0 := by
  rw [show star phiDyn = phiDyn from star_mkPhi _ _]
  show (∑ ik, phiDyn ik * e01 ik) = 0
  refine Finset.sum_eq_zero fun ik _ => ?_
  rcases eq_or_ne ik ((0 : Fin 2), (1 : Fin 2)) with rfl | h
  · rw [show phiDyn ((0 : Fin 2), (1 : Fin 2)) = 0 from
      mkPhi_apply_01 _ _, zero_mul]
  · rw [show e01 ik = 0 from Pi.single_eq_of_ne h 1, mul_zero]

private theorem dot_phi_phi : star phiDyn ⬝ᵥ phiDyn = 1 := by
  rw [show star phiDyn = phiDyn from star_mkPhi _ _]
  show (∑ ik, phiDyn ik * phiDyn ik) = 1
  have hterm : ∀ ik, phiDyn ik * phiDyn ik
      = ((mkPhiQ (24 / 25) (-(7 / 25)) ik
          * mkPhiQ (24 / 25) (-(7 / 25)) ik : ℚ) : ℂ) := fun ik => by
    show ((mkPhiQ _ _ ik : ℚ) : ℂ) * ((mkPhiQ _ _ ik : ℚ) : ℂ) = _
    push_cast
    ring
  rw [Finset.sum_congr rfl fun ik _ => hterm ik]
  norm_cast
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [mkPhiQ]

theorem UDyn_conjTranspose : UDynᴴ = UDyn := by
  unfold UDyn
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, conjTranspose_vecMulVec']
  abel

theorem UDyn_mulVec_e01 : UDyn *ᵥ e01 = phiDyn := by
  unfold UDyn
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, dot_e01_e01, dot_phi_e01,
    op_smul_eq_smul, one_smul, zero_smul]
  abel

theorem UDyn_mulVec_phi : UDyn *ᵥ phiDyn = e01 := by
  unfold UDyn
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, dot_e01_phi, dot_phi_phi,
    op_smul_eq_smul, one_smul, zero_smul]
  abel

/-- The mechanism is involutive. -/
theorem UDyn_invol : UDyn * UDyn = 1 := by
  unfold UDyn
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.vecMulVec_mul_vecMulVec]
  simp only [dot_e01_e01, dot_e01_phi, dot_phi_e01, dot_phi_phi,
    one_smul, zero_smul]
  abel

/-- The mechanism is unitary. -/
theorem UDyn_unitary : UDyn * UDynᴴ = 1 := by
  rw [UDyn_conjTranspose]
  exact UDyn_invol

/-- The reachable orbit: the `|01⟩` extreme and the branch state. -/
noncomputable def orbitState : Fin 2 → TwoQubits :=
  ![upState, entStateDyn]

theorem orbitState_isState (x : Fin 2) : IsState (orbitState x) := by
  fin_cases x
  · exact upState_isState
  · exact entStateDyn_isState

/-- **The mechanism cycles the orbit**: one Heisenberg step swaps the
two reachable states. -/
theorem orbit_step (x : Fin 2) :
    UDyn * orbitState x * UDynᴴ = orbitState (x + 1) := by
  fin_cases x
  · show UDyn * upState * UDynᴴ = entStateDyn
    rw [upState_vecMulVec, conj_vecMulVec, UDyn_mulVec_e01]
    rfl
  · show UDyn * entStateDyn * UDynᴴ = upState
    rw [show entStateDyn
        = Matrix.vecMulVec phiDyn (star phiDyn) from rfl,
      conj_vecMulVec, UDyn_mulVec_phi]
    exact upState_vecMulVec.symm

/-- The orbit's exact-rational zz rows. -/
def orbitRow : Fin 2 → Fin 2 × Fin 2 → ℚ := ![upRow, entRowDyn]

theorem orbitRow_spec (x : Fin 2) (α : Fin 2 × Fin 2) :
    ((orbitRow x α : ℚ) : ℝ)
      = recordShadow zzRecord (orbitState x) α := by
  fin_cases x
  · exact upRow_spec α
  · exact entRowDyn_spec α

/-- The orbit's laws, carried with their certificates. -/
noncomputable def orbitPMF (x : Fin 2) : FinPMF (Fin 2 × Fin 2) :=
  recordShadowPMF zzRecord (orbitState x) (orbitRow x)
    (orbitRow_spec x) zzRecord_posSemidef zzRecord_sum
    (orbitState_isState x)

noncomputable def orbitLaw (x : Fin 2) : SubPMF (Fin 2 × Fin 2) :=
  (orbitPMF x).toSubPMF

@[simp] theorem orbitLaw_wt (x : Fin 2) (α : Fin 2 × Fin 2) :
    (orbitLaw x).wt α = orbitRow x α := rfl

/-- The coarse trajectory: the orbit laws pushed along the block map. -/
noncomputable def coarseLaw (x : Fin 2) : SubPMF (Fin 2) :=
  (orbitLaw x).map Prod.fst

private theorem coarseLaw_wt (x : Fin 2) (c : Fin 2) :
    (coarseLaw x).wt c
      = orbitRow x (c, 0) + orbitRow x (c, 1) := by
  unfold coarseLaw
  rw [SubPMF.map_wt_apply, filter_fst,
    Finset.sum_pair (by simp : ((c, 0) : Fin 2 × Fin 2) ≠ (c, 1))]
  simp

/-- The truncated effective mechanism: the identity kernel — the
effective coupling is zero. -/
def irKernel : Fin 2 → Fin 2 → ℚ := fun c c' => if c = c' then 1 else 0

theorem irKernel_nonneg : ∀ c c', 0 ≤ irKernel c c' := by
  intro c c'
  unfold irKernel
  split <;> norm_num

theorem irKernel_rowSum : ∀ c : Fin 2, ∑ c', irKernel c c' = 1 := by
  intro c
  simp [irKernel]

/-- The effective step. -/
noncomputable def irStep : SubPMF (Fin 2) → SubPMF (Fin 2) :=
  stochAct irKernel irKernel_nonneg irKernel_rowSum

theorem irStep_wt (μ : SubPMF (Fin 2)) (c : Fin 2) :
    (irStep μ).wt c = μ.wt c := by
  show (∑ c', μ.wt c' * irKernel c' c) = μ.wt c
  simp [irKernel]

/-- A two-outcome total-variation bound from four linear
inequalities — the abs-free interface the concrete defect checks
use. -/
private theorem tvDistQ_pair_le {μ ν : SubPMF (Fin 2)} {ε : ℚ}
    (h0l : -ε ≤ μ.wt 0 - ν.wt 0) (h0r : μ.wt 0 - ν.wt 0 ≤ ε)
    (h1l : -ε ≤ μ.wt 1 - ν.wt 1) (h1r : μ.wt 1 - ν.wt 1 ≤ ε) :
    tvDistQ μ ν ≤ ε := by
  unfold tvDistQ
  rw [Fin.sum_univ_two]
  have a0 := abs_le.mpr ⟨h0l, h0r⟩
  have a1 := abs_le.mpr ⟨h1l, h1r⟩
  linarith

/-- **The one-step defect meets the band**: the coarse trajectory
after one UV step is within `49/625` of the effective step applied to
the coarse state — matching, certified at the dynamics tier. -/
theorem onestep_defect (x : Fin 2) :
    tvDistQ (coarseLaw (x + 1)) (irStep (coarseLaw x)) ≤ 49 / 625 := by
  have hx : x = 0 ∨ x = 1 := by omega
  rcases hx with rfl | rfl
  · show tvDistQ (coarseLaw 1) (irStep (coarseLaw 0)) ≤ 49 / 625
    refine tvDistQ_pair_le ?_ ?_ ?_ ?_ <;>
      · rw [irStep_wt, coarseLaw_wt, coarseLaw_wt]
        norm_num [orbitRow, upRow, entRowDyn, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Prod.mk.injEq]
  · show tvDistQ (coarseLaw 0) (irStep (coarseLaw 1)) ≤ 49 / 625
    refine tvDistQ_pair_le ?_ ?_ ?_ ?_ <;>
      · rw [irStep_wt, coarseLaw_wt, coarseLaw_wt]
        norm_num [orbitRow, upRow, entRowDyn, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Prod.mk.injEq]

/-- **The certified validity window**: the effective dynamics tracks
the true coarse trajectory to `k · 49/625` at every horizon `k`. -/
theorem horizon_bound (x : Fin 2) (k : ℕ) :
    tvDistQ (coarseLaw ((· + 1)^[k] x)) (irStep^[k] (coarseLaw x))
      ≤ (k : ℚ) * (49 / 625) :=
  lax_horizon coarseLaw (· + 1) irStep tvDistQ (49 / 625)
    (fun _ => True) tvDistQ_self tvDistQ_triangle
    (fun μ ν => tvDistQ_stochAct_le irKernel irKernel_nonneg
      irKernel_rowSum μ ν)
    (fun _ _ => trivial) (fun a _ => onestep_defect a) x trivial k

/-! ## The tower: fine → block → total, additive budget -/

/-- The total merge. -/
def totalMerge : Fin 2 → Fin 1 := fun _ => 0

/-- The total record family: one observable, the identity. -/
noncomputable def totRecord : Fin 1 → TwoQubits :=
  coarsenFamily totalMerge blockRecord

theorem totRecord_posSemidef (c : Fin 1) : (totRecord c).PosSemidef :=
  posSemidef_sum' fun a _ => blockRecord_posSemidef a

theorem totRecord_sum : ∑ c, totRecord c = 1 :=
  coarsenFamily_complete totalMerge blockRecord_sum

theorem totRecord_mem (c : Fin 1) :
    totRecord c ∈ qubitNet.alg Dstar := by
  rw [qubitNet_Dstar]
  exact Algebra.mem_top

/-- The total fragment: the trivial effective theory. -/
noncomputable def totFragment :
    LCQFTFragment (Mink ℝ) (Fin 2 × Fin 2) (Fin 2) ℝ (Fin 1) :=
  { isingQubitFragment with
    records := totRecord
    records_mem := totRecord_mem
    records_posSemidef := totRecord_posSemidef
    records_exhaustive := totRecord_sum }

def totSet : Set {ρ : TwoQubits // IsState ρ} :=
  {⟨pureProd, pureProd_isState⟩}

theorem totRecord_shadow_pureProd (c : Fin 1) :
    recordShadow totRecord pureProd c = ((1 : ℚ) : ℝ) := by
  show recordShadow (coarsenFamily totalMerge blockRecord) pureProd c = _
  rw [recordShadow_coarsenFamily]
  rw [show fiber totalMerge c = (Finset.univ : Finset (Fin 2)) from by
    ext a
    simp [Subsingleton.elim (totalMerge a) c]]
  rw [Fin.sum_univ_two, blockRecord_shadow_pureProd,
    blockRecord_shadow_pureProd]
  norm_num [irRow]

noncomputable def totMember :
    QNet.RatShadowMember totFragment totSet where
  state := ⟨pureProd, pureProd_isState⟩
  mem := rfl
  row := fun _ => 1
  row_spec := fun c => (totRecord_shadow_pureProd c).symm

/-- **The total merge is the trivial exact effective theory**: every
IR law pushes to the unit row on the point index — containment at
`ε = 0`, by mass conservation. -/
theorem ir_tot_containment :
    Containment (QNet.quantumLaws irFragment irSet) totalMerge
      (QNet.quantumLaws totFragment totSet) 0 := by
  rintro μ ⟨w, hw⟩
  obtain rfl : μ = w.law := (singletonC_iff _ _).mp hw
  refine ⟨totMember.law, ⟨totMember, singletonC_self _⟩,
    le_of_eq ?_⟩
  have hlaw : w.law.map totalMerge = totMember.law := by
    refine SubPMF.ext' (Finsupp.ext fun c => ?_)
    have hc : c = 0 := Subsingleton.elim _ _
    subst hc
    rw [SubPMF.map_wt_apply]
    rw [show (Finset.univ.filter fun a : Fin 2 => totalMerge a = 0)
        = (Finset.univ : Finset (Fin 2)) from by decide]
    have htot := w.pmf.total
    simp only [QNet.RatShadowMember.pmf_prob] at htot
    show (∑ a, w.law.wt a) = totMember.law.wt 0
    simp only [QNet.RatShadowMember.law_wt]
    rw [htot]
    rfl
  rw [hlaw, tvDistQ_self]

/-- **The tower budget is additive**: fine → block → total certifies
at `49/625 + 0` — stage tolerances add along the descent. -/
theorem uv_tot_containment :
    Containment (QNet.quantumLaws isingQubitFragment uvSeg)
      (totalMerge ∘ Prod.fst)
      (QNet.quantumLaws totFragment totSet) (49 / 625 + 0) :=
  Containment.comp uv_ir_containment ir_tot_containment

/-! ## The Sorkin dividend at the instance -/

/-- The decoherence functional of the zz projectors is diagonal at
every state: orthogonal branch images — the projective instance of
records-force-decoherence. -/
theorem decoh_zz (ψ : Fin 2 × Fin 2 → ℂ) (α β : Fin 2 × Fin 2) :
    decoherenceFunctional zzRecord ψ α β
      = if α = β then star (ψ α) * ψ α else 0 := by
  show star (zzRecord β *ᵥ ψ) ⬝ᵥ (zzRecord α *ᵥ ψ) = _
  rw [zz_mulVec, zz_mulVec, star_smul, smul_dotProduct,
    dotProduct_smul, star_pi_single_one, pi_single_dot,
    Pi.single_apply]
  rcases eq_or_ne α β with rfl | h
  · simp [smul_eq_mul, mul_comm]
  · rw [if_neg h, if_neg fun hh => h hh.symm]
    simp

private theorem uvNorm :
    ∑ α, ∑ β, decoherenceFunctional zzRecord
      (mkPhi (24 / 25) (-(7 / 25))) α β = 1 := by
  have hrow : ∀ α : Fin 2 × Fin 2,
      (∑ β, decoherenceFunctional zzRecord
        (mkPhi (24 / 25) (-(7 / 25))) α β)
      = star (mkPhi (24 / 25) (-(7 / 25)) α)
          * mkPhi (24 / 25) (-(7 / 25)) α := by
    intro α
    rw [Finset.sum_congr rfl fun β _ => decoh_zz _ α β]
    simp
  rw [Finset.sum_congr rfl fun α _ => hrow α]
  have hterm : ∀ ik, star (mkPhi (24 / 25) (-(7 / 25)) ik)
      * mkPhi (24 / 25) (-(7 / 25)) ik
      = ((mkPhiQ (24 / 25) (-(7 / 25)) ik
          * mkPhiQ (24 / 25) (-(7 / 25)) ik : ℚ) : ℂ) := fun ik => by
    simp only [mkPhi, star_ratCast]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun ik _ => hterm ik]
  norm_cast
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [mkPhiQ]

/-- The toy's D-form measure: the zz-branch presentation of the 24-7
state. -/
noncomputable def uvMeasure : QuantumMeasure (Fin 2 × Fin 2) :=
  QuantumMeasure.ofPresentation zzRecord
    (mkPhi (24 / 25) (-(7 / 25))) uvNorm

/-- Projective records decohere every branch presentation: the toy's
measure is diagonal already at the fine stage. -/
theorem uvMeasure_isDiagonal : uvMeasure.IsDiagonal := by
  intro α β h
  show decoherenceFunctional zzRecord
    (mkPhi (24 / 25) (-(7 / 25))) α β = 0
  rw [decoh_zz, if_neg h]

theorem uvMeasure_probRow (α : Fin 2 × Fin 2) :
    uvMeasure.probRow α = ((entRow α : ℚ) : ℝ) := by
  show (decoherenceFunctional zzRecord
    (mkPhi (24 / 25) (-(7 / 25))) α α).re = _
  rw [decoh_zz, if_pos rfl]
  simp only [mkPhi, star_ratCast]
  rw [show ((mkPhiQ (24 / 25) (-(7 / 25)) α : ℚ) : ℂ)
        * ((mkPhiQ (24 / 25) (-(7 / 25)) α : ℚ) : ℂ)
      = (((mkPhiQ (24 / 25) (-(7 / 25)) α
          * mkPhiQ (24 / 25) (-(7 / 25)) α : ℚ)) : ℂ) by
    push_cast; ring,
    Complex.ratCast_re]
  norm_cast
  fin_cases α <;> norm_num [entRow, mkPhiQ]

/-- The stage types of the toy's refinement tower. -/
def eftTowerX : ℕ → Type
  | 0 => Fin 2 × Fin 2
  | 1 => Fin 2
  | _ + 2 => Fin 1

instance : ∀ n, Fintype (eftTowerX n)
  | 0 => inferInstanceAs (Fintype (Fin 2 × Fin 2))
  | 1 => inferInstanceAs (Fintype (Fin 2))
  | _ + 2 => inferInstanceAs (Fintype (Fin 1))

instance : ∀ n, DecidableEq (eftTowerX n)
  | 0 => inferInstanceAs (DecidableEq (Fin 2 × Fin 2))
  | 1 => inferInstanceAs (DecidableEq (Fin 2))
  | _ + 2 => inferInstanceAs (DecidableEq (Fin 1))

/-- The step merges: block, then total, then the constant tail. -/
def eftTowerStep : ∀ n, eftTowerX n → eftTowerX (n + 1)
  | 0 => Prod.fst
  | 1 => totalMerge
  | _ + 2 => id

/-- The toy's stage measures. -/
noncomputable def eftStage : ∀ n, QuantumMeasure (eftTowerX n) :=
  stageMeasure (X := eftTowerX) uvMeasure eftTowerStep

/-- Classicality holds at every stage — absorbing from the root. -/
theorem eftStage_isDiagonal (n : ℕ) : (eftStage n).IsDiagonal := by
  unfold eftStage
  exact stageMeasure_isDiagonal_mono (X := eftTowerX) uvMeasure
    eftTowerStep (Nat.zero_le n) uvMeasure_isDiagonal

/-- Every stage is (equal to) a classical measure. -/
theorem eftStage_classical (n : ℕ) :
    ∃ (p : eftTowerX n → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1),
      eftStage n = QuantumMeasure.classical p hp hs := by
  unfold eftStage
  exact stageMeasure_classical_absorbing (X := eftTowerX) uvMeasure
    eftTowerStep (Nat.zero_le n) uvMeasure_isDiagonal

/-- Sorkin monotonicity, quoted at the instance. -/
theorem eftTower_offDiagMass_antitone :
    Antitone fun n => (eftStage n).offDiagMass := by
  unfold eftStage
  exact offDiagMass_stageMeasure_antitone (X := eftTowerX) uvMeasure
    eftTowerStep

/-- On this tower the defect functional is constantly zero — the
projective-records dividend (the strict drop lives on the diamond
tower). -/
theorem eftTower_offDiagMass_zero (n : ℕ) :
    (eftStage n).offDiagMass = 0 :=
  (offDiagMass_eq_zero_iff _).mpr (eftStage_isDiagonal n)

/-- The composite leg fine → total is an honest single
coarse-graining — the tower functoriality, quoted at the instance. -/
theorem eftTower_leg :
    (eftStage 0).pushforward
        (towerLeg (X := eftTowerX) uvMeasure eftTowerStep
          (by norm_num : (0 : ℕ) ≤ 2))
      = eftStage 2 := by
  unfold eftStage
  exact towerLeg_pushforward (X := eftTowerX) uvMeasure eftTowerStep _

/-- **The two pushforward notions agree on the toy**: the
measure-level pushforward's Born row is the row-level pushed law of
the 24-7 member. -/
theorem pushforward_probRow_bridge (c : Fin 2) :
    (uvMeasure.pushforward Prod.fst).probRow c
      = (((entMember.law.map Prod.fst).wt c : ℚ) : ℝ) := by
  rw [pushforward_probRow_of_isDiagonal Prod.fst uvMeasure
    uvMeasure_isDiagonal c]
  rw [SubPMF.map_wt_apply]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [uvMeasure_probRow]
  norm_cast

end Adequacy

end SuFunctor

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms SuFunctor.SubPMF.sum_wt_le_one
#print axioms SuFunctor.SubPMF.map_wt_apply
#print axioms SuFunctor.SubPMF.map_map
#print axioms SuFunctor.Adequacy.tvDistQ_nonneg
#print axioms SuFunctor.Adequacy.tvDistQ_self
#print axioms SuFunctor.Adequacy.tvDistQ_comm
#print axioms SuFunctor.Adequacy.tvDistQ_triangle
#print axioms SuFunctor.Adequacy.tvDistQ_eq_zero_iff
#print axioms SuFunctor.Adequacy.tvDistQ_cast_eq_qrel
#print axioms SuFunctor.Adequacy.tvDistQ_map_le
#print axioms SuFunctor.Adequacy.credalInflate_mono
#print axioms SuFunctor.Adequacy.credalInflate_mono_set
#print axioms SuFunctor.Adequacy.credalInflate_self
#print axioms SuFunctor.Adequacy.credalInflate_zero_iff
#print axioms SuFunctor.Adequacy.credalInflate_or
#print axioms SuFunctor.Adequacy.credalInflate_unionSingletons
#print axioms SuFunctor.Adequacy.Containment.mono
#print axioms SuFunctor.Adequacy.Containment.comp
#print axioms SuFunctor.Adequacy.recordShadow_coarsenFamily
#print axioms SuFunctor.Adequacy.stochAct_wt
#print axioms SuFunctor.Adequacy.tvDistQ_stochAct_le
#print axioms SuFunctor.Adequacy.lax_horizon
#print axioms SuFunctor.Adequacy.star_mkPhi
#print axioms SuFunctor.Adequacy.mkPhi_apply_01
#print axioms SuFunctor.Adequacy.upState_vecMulVec
#print axioms SuFunctor.Adequacy.upState_trace
#print axioms SuFunctor.Adequacy.upState_isState
#print axioms SuFunctor.Adequacy.mkOuter_trace
#print axioms SuFunctor.Adequacy.mkOuter_isState
#print axioms SuFunctor.Adequacy.recordShadow_zz_mkOuter
#print axioms SuFunctor.Adequacy.recordShadow_zz_upState
#print axioms SuFunctor.Adequacy.entState_isState
#print axioms SuFunctor.Adequacy.upRow_spec
#print axioms SuFunctor.Adequacy.entRow_spec
#print axioms SuFunctor.Adequacy.uvSeg_mixClosed
#print axioms SuFunctor.Adequacy.uvSeg_member_row
#print axioms SuFunctor.Adequacy.uvLaws_mix_exercised
#print axioms SuFunctor.Adequacy.blockRecord_posSemidef
#print axioms SuFunctor.Adequacy.blockRecord_sum
#print axioms SuFunctor.Adequacy.blockRecord_mem
#print axioms SuFunctor.Adequacy.recordShadow_zz_pureProd
#print axioms SuFunctor.Adequacy.blockRecord_shadow_pureProd
#print axioms SuFunctor.Adequacy.irLaws_pinned
#print axioms SuFunctor.Adequacy.uv_ir_containment
#print axioms SuFunctor.Adequacy.uv_ir_containment_lower
#print axioms SuFunctor.Adequacy.not_uv_ir_containment_zero
#print axioms SuFunctor.Adequacy.entStateDyn_isState
#print axioms SuFunctor.Adequacy.entRowDyn_spec
#print axioms SuFunctor.Adequacy.conj_vecMulVec
#print axioms SuFunctor.Adequacy.UDyn_conjTranspose
#print axioms SuFunctor.Adequacy.UDyn_mulVec_e01
#print axioms SuFunctor.Adequacy.UDyn_mulVec_phi
#print axioms SuFunctor.Adequacy.UDyn_invol
#print axioms SuFunctor.Adequacy.UDyn_unitary
#print axioms SuFunctor.Adequacy.orbitState_isState
#print axioms SuFunctor.Adequacy.orbit_step
#print axioms SuFunctor.Adequacy.orbitRow_spec
#print axioms SuFunctor.Adequacy.orbitLaw_wt
#print axioms SuFunctor.Adequacy.irKernel_nonneg
#print axioms SuFunctor.Adequacy.irKernel_rowSum
#print axioms SuFunctor.Adequacy.irStep_wt
#print axioms SuFunctor.Adequacy.onestep_defect
#print axioms SuFunctor.Adequacy.horizon_bound
#print axioms SuFunctor.Adequacy.totRecord_posSemidef
#print axioms SuFunctor.Adequacy.totRecord_sum
#print axioms SuFunctor.Adequacy.totRecord_mem
#print axioms SuFunctor.Adequacy.totRecord_shadow_pureProd
#print axioms SuFunctor.Adequacy.ir_tot_containment
#print axioms SuFunctor.Adequacy.uv_tot_containment
#print axioms SuFunctor.Adequacy.decoh_zz
#print axioms SuFunctor.Adequacy.uvMeasure_isDiagonal
#print axioms SuFunctor.Adequacy.uvMeasure_probRow
#print axioms SuFunctor.Adequacy.eftStage_isDiagonal
#print axioms SuFunctor.Adequacy.eftStage_classical
#print axioms SuFunctor.Adequacy.eftTower_offDiagMass_antitone
#print axioms SuFunctor.Adequacy.eftTower_offDiagMass_zero
#print axioms SuFunctor.Adequacy.eftTower_leg
#print axioms SuFunctor.Adequacy.pushforward_probRow_bridge
