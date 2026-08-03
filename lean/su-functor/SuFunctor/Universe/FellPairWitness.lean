import SuFunctor.Universe.FellPairLocus
import QtslAux.DiamondTopology
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The null-awakening and spacelike-merge witnesses: the record class does not bundle

Refuting fixtures for the interior-pair record locus
(`FellPairLocus`), delimiting its two site hypotheses mathematically —
the weakened statements are false, not merely unproved.  Both
countermodels live in the Minkowski site over `ℝ^{1+1}` (the
kernel-checked `minkowskiKit` cone order, state fibre `ℝ`) — the
best-behaved relativistic site with the tamest fibre, so no
hypothesis package rescues what they refute.

* **(S1) cannot be weakened to the causal order** — the locus stated
  on *all* causal pairs (`Chron := (· ≤ ·)`, against the Lorentzian
  time-separation) is not closed, two ways:

  - **null awakening** (`not_isClosed_causalPairLocus`): a spacelike
    stage-pair Fell-converges onto a *null* pair.  Every approximant
    is in the locus vacuously — its two stages are incomparable, so
    no constraint is active — while the limit pair is comparable with
    time-separation zero: a zero-duration constraint awakened in the
    limit that no approximant felt.  Comparability is closed under
    limits (that is the good direction); *incomparability is not*,
    and the constraint set jumps exactly on the null boundary.
    Companion (`not_isOpen_le_mink`): the causal order's graph is not
    open — the same spacelike approach — so the (S1) hypothesis
    genuinely fails for `≤`, and the closedness conclusion fails with
    it: hypothesis and conclusion refuted as a pair.

  - **spacelike merge** (`not_isClosed_causalPairLocus_merge`,
    `not_isClosed_minkGraphLocus`): two mutually spacelike stages
    merge to one stage carrying two states.  Single-valuedness — the
    reflexive, equal-stage face of the per-pair condition — dies in
    the limit; bare graph-hood over a genuinely partial stage order
    is already not Fell-closed, with two-point *antichain*
    approximants (over a total order this evasion is impossible: a
    merging pair is comparable en route, hence constrained en route —
    the classical closedness of graph-hood was comparability-totality
    in disguise).

  Both limits ARE members of the interior-pair locus
  (`cm1_limit_mem_chronPairLocus`, `cm2_limit_mem_chronPairLocus`):
  the violations sit on null and equal-stage pairs, exactly where the
  chronology deliberately does not look.  The repair keeps the
  boundary specimens — as it must, being closed.

* **(S2) cannot be dropped** (`not_isClosed_spikePairLocus`): on the
  classical stage line with `Chron := (<)` open — (S1) holding — a
  pair-duration with one downward spike (zero at a single pair,
  honest distance elsewhere; `not_upperSemicontinuousOn_spikeDist`
  pins that it fails upper semicontinuity exactly there) loses
  closedness to the same margin argument the USC hypothesis exists to
  run.

The two-point Fell convergence machinery (`tendsto_pairF`) is the
witness-grade analogue of the steepening family's: hit faces by
eventual membership, miss faces by eventual avoidance of the compact.
Directedness fixtures are *not* duplicated here: the nondirected
witness of `FellRecordWitness` refutes the locality hypothesis at the
speed instantiation, which the degeneracy identity
(`pairLocus_trivial_eq_speedLocus`) embeds in the pair-locus family.
-/

namespace SuFunctor.Universe

open Set Topology TopologicalSpace Filter Qtsl.DiamondSite
open scoped NNReal

/-! ## The manifold topology on Minkowski space -/

section MinkTopology

variable {E : Type*} [NormedAddCommGroup E]

/-- The **manifold topology** of Minkowski space over `E`: induced
from the coordinate product `ℝ × E`.  The cone *order* is never a
topology source here — `not_isOpen_le_mink` below is exactly the
point that the order's graph is not open in this topology. -/
instance minkTopology : TopologicalSpace (Mink E) :=
  TopologicalSpace.induced (fun p => (p.t, p.x)) inferInstance

theorem isInducing_minkCoord :
    IsInducing (fun p : Mink E => ((p.t, p.x) : ℝ × E)) := ⟨rfl⟩

theorem isEmbedding_minkCoord :
    IsEmbedding (fun p : Mink E => ((p.t, p.x) : ℝ × E)) :=
  ⟨isInducing_minkCoord, fun p q h => by
    cases p
    cases q
    simpa [Prod.ext_iff, Mink.mk.injEq] using h⟩

instance : T2Space (Mink E) := isEmbedding_minkCoord.t2Space

/-- Coordinatewise convergence gives convergence in Minkowski
space. -/
theorem tendsto_mink {f : ℕ → Mink E} {p : Mink E}
    (ht : Tendsto (fun n => (f n).t) atTop (𝓝 p.t))
    (hx : Tendsto (fun n => (f n).x) atTop (𝓝 p.x)) :
    Tendsto f atTop (𝓝 p) := by
  rw [isInducing_minkCoord.tendsto_nhds_iff]
  exact ht.prodMk_nhds hx

open Classical in
/-- The **Lorentzian time-separation** (the two-stage duration of the
Minkowski site): `√((Δt)² − ‖Δx‖²)` on causal pairs, zero elsewhere.
Zero on null pairs and on the diagonal — the two faces the
countermodels exploit. -/
noncomputable def lorentzDist (p q : Mink E) : ℝ :=
  if p ≤ q then Real.sqrt ((q.t - p.t) ^ 2 - ‖q.x - p.x‖ ^ 2) else 0

@[simp]
theorem lorentzDist_self (p : Mink E) : lorentzDist p p = 0 := by
  rw [lorentzDist, if_pos le_rfl]
  simp

end MinkTopology

/-! ## Two-point Fell convergence -/

section PairTendsto

variable {γ : Type*} [TopologicalSpace γ]

attribute [local instance] SuFunctor.Universe.fell

/-- Pointwise convergence of two points gives Fell convergence of the
two-point sets: hit faces by eventual membership, miss faces by
eventual avoidance of the compact. -/
theorem tendsto_pair_fell [T2Space γ] {x y : ℕ → γ} {a b : γ}
    (hx : Tendsto x atTop (𝓝 a)) (hy : Tendsto y atTop (𝓝 b)) :
    Tendsto (fun n => ({x n, y n} : Set γ)) atTop
      (𝓝 ({a, b} : Set γ)) := by
  refine tendsto_nhds_generateFrom_iff.mpr ?_
  rintro s (⟨K, hK, rfl⟩ | ⟨V, hV, rfl⟩) hBs
  · -- miss face: the compact `K` avoids `{a, b}`, hence eventually
    -- both moving points
    have hdisj : Disjoint ({a, b} : Set γ) K := hBs
    have hKo : IsOpen Kᶜ := hK.isClosed.isOpen_compl
    have haK : a ∈ Kᶜ := fun haK' =>
      Set.disjoint_left.mp hdisj (mem_insert _ _) haK'
    have hbK : b ∈ Kᶜ := fun hbK' =>
      Set.disjoint_left.mp hdisj (mem_insert_of_mem _ rfl) hbK'
    filter_upwards [hx.eventually (hKo.eventually_mem haK),
      hy.eventually (hKo.eventually_mem hbK)] with n hxn hyn
    refine Set.disjoint_left.mpr ?_
    rintro z hz hzK
    rcases hz with rfl | hz
    · exact hxn hzK
    · rw [mem_singleton_iff] at hz
      subst hz
      exact hyn hzK
  · -- hit face: the open `V` is met by `a` or by `b`, hence
    -- eventually by the corresponding moving point
    obtain ⟨z, hzab, hzV⟩ := hBs
    rcases hzab with rfl | hz
    · filter_upwards [hx.eventually (hV.eventually_mem hzV)] with n hn
      exact ⟨x n, mem_insert _ _, hn⟩
    · rw [mem_singleton_iff] at hz
      subst hz
      filter_upwards [hy.eventually (hV.eventually_mem hzV)] with n hn
      exact ⟨y n, mem_insert_of_mem _ rfl, hn⟩

variable [T2Space γ]

/-- A two-point set, at the closeds carrier. -/
def pairF (u v : γ) : FellCloseds γ :=
  ⟨{u, v}, ((finite_singleton v).insert u).isClosed⟩

@[simp]
theorem coe_pairF (u v : γ) : ((pairF u v : FellCloseds γ) : Set γ) = {u, v} :=
  rfl

/-- Two-point Fell convergence at the closeds carrier. -/
theorem tendsto_pairF {x y : ℕ → γ} {a b : γ}
    (hx : Tendsto x atTop (𝓝 a)) (hy : Tendsto y atTop (𝓝 b)) :
    Tendsto (fun n => pairF (x n) (y n)) atTop (𝓝 (pairF a b)) :=
  FellCloseds.isEmbedding_coe.isInducing.tendsto_nhds_iff.mpr
    (tendsto_pair_fell hx hy)

end PairTendsto

/-! ## CM1: null awakening -/

section NullAwakening

/-- The lower stage: the origin. -/
def cmS : Mink ℝ := ⟨0, 0⟩

/-- The upper stage of the limit: null-related to the origin. -/
def cmT : Mink ℝ := ⟨1, 1⟩

/-- The approximating stages: spacelike from the origin, converging
onto the null point. -/
noncomputable def cmT' (n : ℕ) : Mink ℝ := ⟨1, 1 + ((n : ℝ) + 1)⁻¹⟩

theorem cmS_le_cmT : cmS ≤ cmT := by
  show ‖(1 : ℝ) - 0‖ ≤ (1 : ℝ) - 0
  rw [sub_zero, Real.norm_eq_abs]
  norm_num

theorem lorentzDist_cmS_cmT : lorentzDist cmS cmT = 0 := by
  have h : (cmT.t - cmS.t) ^ 2 - ‖cmT.x - cmS.x‖ ^ 2 = 0 := by
    show ((1 : ℝ) - 0) ^ 2 - ‖(1 : ℝ) - 0‖ ^ 2 = 0
    rw [Real.norm_eq_abs]
    norm_num
  rw [lorentzDist, if_pos cmS_le_cmT, h, Real.sqrt_zero]

theorem not_cmS_le_cmT' (n : ℕ) : ¬ cmS ≤ cmT' n := by
  show ¬ ‖(1 + ((n : ℝ) + 1)⁻¹) - 0‖ ≤ (1 : ℝ) - 0
  have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  rw [sub_zero, sub_zero, Real.norm_eq_abs, abs_of_pos (by linarith)]
  intro h
  linarith

theorem not_cmT'_le_cmS (n : ℕ) : ¬ cmT' n ≤ cmS := by
  show ¬ ‖(0 : ℝ) - (1 + ((n : ℝ) + 1)⁻¹)‖ ≤ (0 : ℝ) - 1
  intro h
  have hnn := norm_nonneg ((0 : ℝ) - (1 + ((n : ℝ) + 1)⁻¹))
  linarith

theorem tendsto_cmT' : Tendsto cmT' atTop (𝓝 cmT) := by
  refine tendsto_mink ?_ ?_
  · show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ))
    exact tendsto_const_nhds
  · show Tendsto (fun n : ℕ => 1 + ((n : ℝ) + 1)⁻¹) atTop (𝓝 (1 : ℝ))
    have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using tendsto_const_nhds.add h

/-- Every approximant is in the causal-pair locus **vacuously**: its
two stages are spacelike, so no constraint is active. -/
theorem cm1_approx_mem (c : ℝ≥0) (n : ℕ) :
    pairF ((cmS, (0 : ℝ)) : Mink ℝ × ℝ) (cmT' n, 1)
      ∈ pairLocus (Prod.fst : Mink ℝ × ℝ → Mink ℝ) Prod.snd c (· ≤ ·) lorentzDist := by
  intro p hp q hq hle
  simp only [coe_pairF, mem_insert_iff, mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · simp
  · exact absurd hle (not_cmS_le_cmT' n)
  · exact absurd hle (not_cmT'_le_cmS n)
  · simp

/-- The limit violates the causal-pair locus at the **null** pair: the
awakened constraint has duration zero and state distance one. -/
theorem cm1_limit_notMem (c : ℝ≥0) :
    pairF ((cmS, (0 : ℝ)) : Mink ℝ × ℝ) (cmT, 1)
      ∉ pairLocus (Prod.fst : Mink ℝ × ℝ → Mink ℝ) Prod.snd c (· ≤ ·) lorentzDist := by
  intro h
  have hd := h (cmS, 0) (mem_insert _ _) (cmT, 1)
    (mem_insert_of_mem _ rfl) cmS_le_cmT
  dsimp only at hd
  rw [lorentzDist_cmS_cmT, mul_zero, Real.dist_eq] at hd
  norm_num at hd

/-- The approximants Fell-converge to the limit. -/
theorem cm1_tendsto :
    Tendsto (fun n => pairF ((cmS, (0 : ℝ)) : Mink ℝ × ℝ) (cmT' n, 1))
      atTop (𝓝 (pairF (cmS, 0) (cmT, 1))) :=
  tendsto_pairF tendsto_const_nhds
    (tendsto_cmT'.prodMk_nhds tendsto_const_nhds)

/-- **Null awakening**: the locus of speed graphs over *all causal
pairs* — the causal order in place of its interior — is not closed, at
any speed.  (S1) cannot be weakened to comparability: incomparability
is not closed under Fell limits, and the constraint set jumps on the
null boundary. -/
theorem not_isClosed_causalPairLocus (c : ℝ≥0) :
    ¬ IsClosed (pairLocus (Prod.fst : Mink ℝ × ℝ → Mink ℝ) Prod.snd c
      (· ≤ ·) lorentzDist) := fun h =>
  cm1_limit_notMem c
    (h.mem_of_tendsto cm1_tendsto
      (Eventually.of_forall fun n => cm1_approx_mem c n))

/-- **The causal order's graph is not open** in the manifold topology:
the same spacelike approach onto the null pair.  The (S1) hypothesis
of `isClosed_pairLocus` genuinely fails for `≤` — with
`not_isClosed_causalPairLocus`, hypothesis and conclusion are refuted
as a pair. -/
theorem not_isOpen_le_mink :
    ¬ IsOpen {r : Mink ℝ × Mink ℝ | r.1 ≤ r.2} := by
  intro hopen
  have hmem : ((cmS, cmT) : Mink ℝ × Mink ℝ)
      ∈ {r : Mink ℝ × Mink ℝ | r.1 ≤ r.2} := cmS_le_cmT
  have htend : Tendsto (fun n => ((cmS, cmT' n) : Mink ℝ × Mink ℝ))
      atTop (𝓝 (cmS, cmT)) :=
    tendsto_const_nhds.prodMk_nhds tendsto_cmT'
  obtain ⟨n, hn⟩ := (htend.eventually (hopen.eventually_mem hmem)).exists
  exact not_cmS_le_cmT' n hn

theorem mink_chron_irrefl {E : Type*} [NormedAddCommGroup E]
    (p : Mink E) : ¬ Mink.chron p p := by
  show ¬ ‖p.x - p.x‖ < p.t - p.t
  simp

theorem not_chron_cmS_cmT : ¬ Mink.chron cmS cmT := by
  show ¬ ‖(1 : ℝ) - 0‖ < (1 : ℝ) - 0
  rw [sub_zero, Real.norm_eq_abs]
  norm_num

theorem not_chron_cmT_cmS : ¬ Mink.chron cmT cmS := by
  show ¬ ‖(0 : ℝ) - 1‖ < (0 : ℝ) - 1
  intro h
  have hnn := norm_nonneg ((0 : ℝ) - 1)
  linarith

/-- **The repair keeps the specimen**: the null-awakening limit is a
member of the interior-pair locus — its violating pair is null, where
the chronology deliberately does not look.  (Necessarily so:
`isClosed_pairLocus` applies to the chronology, and the approximants
are members.) -/
theorem cm1_limit_mem_chronPairLocus (c : ℝ≥0) :
    pairF ((cmS, (0 : ℝ)) : Mink ℝ × ℝ) (cmT, 1)
      ∈ pairLocus (Prod.fst : Mink ℝ × ℝ → Mink ℝ) Prod.snd c
        (minkowskiKit (E := ℝ)).chron lorentzDist := by
  intro p hp q hq hchron
  simp only [coe_pairF, mem_insert_iff, mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact absurd hchron (mink_chron_irrefl _)
  · exact absurd hchron not_chron_cmS_cmT
  · exact absurd hchron not_chron_cmT_cmS
  · exact absurd hchron (mink_chron_irrefl _)

end NullAwakening

/-! ## CM2: spacelike merge -/

section SpacelikeMerge

/-- The right-moving approximant stage. -/
noncomputable def cmP (n : ℕ) : Mink ℝ := ⟨0, ((n : ℝ) + 1)⁻¹⟩

/-- The left-moving approximant stage: spacelike from `cmP n`. -/
noncomputable def cmM (n : ℕ) : Mink ℝ := ⟨0, -((n : ℝ) + 1)⁻¹⟩

theorem not_cmP_le_cmM (n : ℕ) : ¬ cmP n ≤ cmM n := by
  show ¬ ‖-((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 1)⁻¹‖ ≤ (0 : ℝ) - 0
  have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  rw [Real.norm_eq_abs, abs_of_neg (by linarith)]
  intro h
  linarith

theorem not_cmM_le_cmP (n : ℕ) : ¬ cmM n ≤ cmP n := by
  show ¬ ‖((n : ℝ) + 1)⁻¹ - -((n : ℝ) + 1)⁻¹‖ ≤ (0 : ℝ) - 0
  have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
  intro h
  linarith

theorem tendsto_cmP : Tendsto cmP atTop (𝓝 cmS) := by
  refine tendsto_mink ?_ ?_
  · show Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ))
    exact tendsto_const_nhds
  · show Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ))
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

theorem tendsto_cmM : Tendsto cmM atTop (𝓝 cmS) := by
  refine tendsto_mink ?_ ?_
  · show Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ))
    exact tendsto_const_nhds
  · show Tendsto (fun n : ℕ => -((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ))
    have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using h.neg

/-- Every merge approximant is in the causal-pair locus vacuously: its
two stages are mutually spacelike. -/
theorem cm2_approx_mem (c : ℝ≥0) (n : ℕ) :
    pairF ((cmP n, (0 : ℝ)) : Mink ℝ × ℝ) (cmM n, 1)
      ∈ pairLocus (Prod.fst : Mink ℝ × ℝ → Mink ℝ) Prod.snd c (· ≤ ·) lorentzDist := by
  intro p hp q hq hle
  simp only [coe_pairF, mem_insert_iff, mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · simp
  · exact absurd hle (not_cmP_le_cmM n)
  · exact absurd hle (not_cmM_le_cmP n)
  · simp

/-- The merged limit violates the causal-pair locus at the
**equal-stage** pair: single-valuedness is the reflexive face of the
per-pair condition, and it dies in the merge. -/
theorem cm2_limit_notMem (c : ℝ≥0) :
    pairF ((cmS, (0 : ℝ)) : Mink ℝ × ℝ) (cmS, 1)
      ∉ pairLocus (Prod.fst : Mink ℝ × ℝ → Mink ℝ) Prod.snd c (· ≤ ·) lorentzDist := by
  intro h
  have hd := h (cmS, 0) (mem_insert _ _) (cmS, 1)
    (mem_insert_of_mem _ rfl) le_rfl
  dsimp only at hd
  rw [lorentzDist_self, mul_zero, Real.dist_eq] at hd
  norm_num at hd

theorem cm2_tendsto :
    Tendsto (fun n => pairF ((cmP n, (0 : ℝ)) : Mink ℝ × ℝ) (cmM n, 1))
      atTop (𝓝 (pairF (cmS, 0) (cmS, 1))) :=
  tendsto_pairF (tendsto_cmP.prodMk_nhds tendsto_const_nhds)
    (tendsto_cmM.prodMk_nhds tendsto_const_nhds)

/-- **Spacelike merge**: a second refutation of the causal-pair locus,
through the equal-stage face — two antichain-supported approximants
merge onto one stage with two states. -/
theorem not_isClosed_causalPairLocus_merge (c : ℝ≥0) :
    ¬ IsClosed (pairLocus (Prod.fst : Mink ℝ × ℝ → Mink ℝ) Prod.snd c
      (· ≤ ·) lorentzDist) := fun h =>
  cm2_limit_notMem c
    (h.mem_of_tendsto cm2_tendsto
      (Eventually.of_forall fun n => cm2_approx_mem c n))

/-- Bare single-valuedness over Minkowski stages: functional
graph-hood, no speed row. -/
def minkGraphLocus : Set (FellCloseds (Mink ℝ × ℝ)) :=
  {G | ∀ p ∈ (G : Set (Mink ℝ × ℝ)), ∀ q ∈ (G : Set (Mink ℝ × ℝ)),
    p.1 = q.1 → p.2 = q.2}

theorem cm2_approx_mem_graphLocus (n : ℕ) :
    pairF ((cmP n, (0 : ℝ)) : Mink ℝ × ℝ) (cmM n, 1) ∈ minkGraphLocus := by
  intro p hp q hq heq
  simp only [coe_pairF, mem_insert_iff, mem_singleton_iff] at hp hq
  have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · rfl
  · exfalso
    dsimp only at heq
    have hx : ((n : ℝ) + 1)⁻¹ = -((n : ℝ) + 1)⁻¹ := congrArg Mink.x heq
    linarith
  · exfalso
    dsimp only at heq
    have hx : -((n : ℝ) + 1)⁻¹ = ((n : ℝ) + 1)⁻¹ := congrArg Mink.x heq
    linarith
  · rfl

theorem cm2_limit_notMem_graphLocus :
    pairF ((cmS, (0 : ℝ)) : Mink ℝ × ℝ) (cmS, 1) ∉ minkGraphLocus := by
  intro h
  have h01 := h (cmS, 0) (mem_insert _ _) (cmS, 1)
    (mem_insert_of_mem _ rfl) rfl
  norm_num at h01

/-- **Graph-hood does not survive a genuinely partial stage order**:
bare single-valuedness over Minkowski stages is not Fell-closed, with
two-point antichain approximants.  (Over a total order the merging
pair would be comparable en route, hence constrained en route: the
classical closedness of graph-hood was comparability-totality in
disguise.) -/
theorem not_isClosed_minkGraphLocus : ¬ IsClosed minkGraphLocus := fun h =>
  cm2_limit_notMem_graphLocus
    (h.mem_of_tendsto cm2_tendsto
      (Eventually.of_forall cm2_approx_mem_graphLocus))

/-- The merged limit is a member of the interior-pair locus: every
stage pair of the merged record is diagonal, and the strict cone is
irreflexive. -/
theorem cm2_limit_mem_chronPairLocus (c : ℝ≥0) :
    pairF ((cmS, (0 : ℝ)) : Mink ℝ × ℝ) (cmS, 1)
      ∈ pairLocus (Prod.fst : Mink ℝ × ℝ → Mink ℝ) Prod.snd c
        (minkowskiKit (E := ℝ)).chron lorentzDist := by
  intro p hp q hq hchron
  simp only [coe_pairF, mem_insert_iff, mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
    exact absurd hchron (mink_chron_irrefl _)

end SpacelikeMerge

/-! ## The spike witness: (S2) cannot be dropped -/

section SpikeWitness

open Classical in
/-- A pair-duration with one downward spike: zero at the single pair
`(0, 1)`, the honest distance elsewhere.  Fails upper semicontinuity
exactly at the spike — and (S1) holds, the chronology being the
classical `<`. -/
noncomputable def spikeDist (s t : ℝ) : ℝ :=
  if s = 0 ∧ t = 1 then 0 else |t - s|

theorem spikeDist_spike : spikeDist 0 1 = 0 := by
  simp [spikeDist]

theorem spikeDist_off (n : ℕ) :
    spikeDist 0 (1 + ((n : ℝ) + 1)⁻¹) = 1 + ((n : ℝ) + 1)⁻¹ := by
  have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  have hne : ¬ ((0 : ℝ) = 0 ∧ (1 + ((n : ℝ) + 1)⁻¹ : ℝ) = 1) := by
    rintro ⟨-, h⟩
    linarith
  rw [spikeDist, if_neg hne, sub_zero, abs_of_pos (by linarith)]

/-- The spiked duration is not upper semicontinuous on the (open)
chronology: approach the spike from above and the duration jumps
up. -/
theorem not_upperSemicontinuousOn_spikeDist :
    ¬ UpperSemicontinuousOn (fun r : ℝ × ℝ => spikeDist r.1 r.2)
      {r : ℝ × ℝ | r.1 < r.2} := by
  intro h
  have h₀ : (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) ∈ {r : ℝ × ℝ | r.1 < r.2} := by
    norm_num
  have hlt : spikeDist ((0 : ℝ), (1 : ℝ)).1 ((0 : ℝ), (1 : ℝ)).2
      < 1 / 2 := by
    dsimp only
    rw [spikeDist_spike]
    norm_num
  have hev := h _ h₀ (1 / 2) hlt
  have hseq : Tendsto
      (fun n : ℕ => (((0 : ℝ), 1 + ((n : ℝ) + 1)⁻¹) : ℝ × ℝ)) atTop
      (𝓝[{r : ℝ × ℝ | r.1 < r.2}] ((0 : ℝ), (1 : ℝ))) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · refine Tendsto.prodMk_nhds tendsto_const_nhds ?_
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
        simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using tendsto_const_nhds.add h1
    · refine Eventually.of_forall fun n => ?_
      show (0 : ℝ) < 1 + ((n : ℝ) + 1)⁻¹
      positivity
  obtain ⟨n, hn⟩ := (hseq.eventually hev).exists
  dsimp only at hn
  rw [spikeDist_off] at hn
  have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  linarith

/-- Every spike approximant is in the locus at speed one: the
constraint is active — the chronology holds — and the *unspiked*
duration honestly covers the state distance. -/
theorem spike_approx_mem (n : ℕ) :
    pairF (((0 : ℝ), (0 : ℝ)) : ℝ × ℝ) (1 + ((n : ℝ) + 1)⁻¹, 1)
      ∈ pairLocus (Prod.fst : ℝ × ℝ → ℝ) Prod.snd 1 (· < ·) spikeDist := by
  intro p hp q hq hlt
  simp only [coe_pairF, mem_insert_iff, mem_singleton_iff] at hp hq
  have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact absurd hlt (lt_irrefl _)
  · dsimp only
    rw [spikeDist_off, Real.dist_eq, NNReal.coe_one, one_mul,
      abs_of_neg (by norm_num : (0 : ℝ) - 1 < 0)]
    linarith
  · exfalso
    dsimp only at hlt
    linarith
  · exact absurd hlt (lt_irrefl _)

/-- The spike limit violates the locus at the spiked pair: the
duration collapsed to zero under a unit state distance. -/
theorem spike_limit_notMem :
    pairF (((0 : ℝ), (0 : ℝ)) : ℝ × ℝ) (1, 1)
      ∉ pairLocus (Prod.fst : ℝ × ℝ → ℝ) Prod.snd 1 (· < ·) spikeDist := by
  intro h
  have hd := h (0, 0) (mem_insert _ _) (1, 1) (mem_insert_of_mem _ rfl)
    (by norm_num)
  dsimp only at hd
  rw [spikeDist_spike, mul_zero, Real.dist_eq] at hd
  norm_num at hd

theorem spike_tendsto :
    Tendsto (fun n : ℕ => pairF (((0 : ℝ), (0 : ℝ)) : ℝ × ℝ)
      (1 + ((n : ℝ) + 1)⁻¹, 1)) atTop (𝓝 (pairF (0, 0) (1, 1))) := by
  refine tendsto_pairF tendsto_const_nhds
    (Tendsto.prodMk_nhds ?_ tendsto_const_nhds)
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa using tendsto_const_nhds.add h1

/-- **(S2) is load-bearing**: with the chronology open — (S1) holding —
a single downward spike in the pair-duration already loses
closedness.  Upper semicontinuity is exactly what forbids the
duration jumping down in a limit, awakening a tighter constraint than
any approximant felt. -/
theorem not_isClosed_spikePairLocus :
    ¬ IsClosed (pairLocus (Prod.fst : ℝ × ℝ → ℝ) Prod.snd 1
      (· < ·) spikeDist) := fun h =>
  spike_limit_notMem
    (h.mem_of_tendsto spike_tendsto
      (Eventually.of_forall spike_approx_mem))

end SpikeWitness

end SuFunctor.Universe

#print axioms SuFunctor.Universe.tendsto_pair_fell
#print axioms SuFunctor.Universe.tendsto_pairF
#print axioms SuFunctor.Universe.not_isClosed_causalPairLocus
#print axioms SuFunctor.Universe.not_isOpen_le_mink
#print axioms SuFunctor.Universe.cm1_limit_mem_chronPairLocus
#print axioms SuFunctor.Universe.not_isClosed_causalPairLocus_merge
#print axioms SuFunctor.Universe.not_isClosed_minkGraphLocus
#print axioms SuFunctor.Universe.cm2_limit_mem_chronPairLocus
#print axioms SuFunctor.Universe.not_upperSemicontinuousOn_spikeDist
#print axioms SuFunctor.Universe.not_isClosed_spikePairLocus
