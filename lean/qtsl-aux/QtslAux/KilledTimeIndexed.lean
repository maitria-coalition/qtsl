import QtslAux.Battery
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Kernel.WithDensity

/-! # The killed time-indexed comparison for jump chains with holding times

A continuous-time jump process presented by a jump-skeleton kernel and a
holding-time family can be read at a fixed time horizon: the state
occupied at time `T`, weighted by the probability that the clock has not
been exhausted by infinitely many jumps within the horizon. This module
constructs that *killed* time-indexed read over the Ionescu–Tulcea
trajectory measure and proves the comparison theorem it exists for: two
models with equal jump-skeleton prefix laws and equal holding families
have equal killed time-indexed transient reads at every horizon. This
lifts a jump-index (skeleton-level) comparison — such as the composed
corollary of the stochastic Petri net flattening development
(`SuFunctor.Adequacy.StochasticPetriComposed`, which ships skeleton
prefix-law agreement together with exit-rate data agreement) — to the
genuinely time-indexed transient reading.

## The objects

The grain is that of a continuous-time chain presented by its jump
skeleton: a kernel `K : Kernel S S` plus a holding-time family
`dur : Kernel S ℝ≥0`, both Markov. **Nothing below uses memorylessness**:
the read is a fixed-horizon marginal, not a process-level Markov claim,
so `dur` stays abstract and the exponential (exit-rate) family enters
only as the closing instance (`expHold`). A Markov `dur` has no
zero-mass state by type, which confines the rate-0/absorbing subtlety
entirely to that instance's positivity hypothesis.

* `timedStep K dur` — the one-step kernel of the timed chain on
  `S × ℝ≥0` (state, ENTRY clock): from `(x, s)` draw `y ~ K x` and
  `d ~ dur x` independently, emit `(y, s + d)`.
* `timedLaw K dur x := Battery.pathMeasure (timedStep K dur) (x, 0)` —
  the killed Ionescu–Tulcea trajectory measure, on the same
  `Battery.pathMeasure` substrate (mathlib's `Kernel.traj`) as the
  package's discrete-profile batteries.
* `readEvent` / `readAll` / `killedRead` — the time-indexed killed
  (sub-probability) transient read at horizon `T`: the state occupied at
  time `T` lies in `A`, read at the jump index whose entry clock brackets
  `T`. The union form is deliberate: no disjointness (hence no clock
  monotonicity) is consumed anywhere.

## The theorems

* **Mass dichotomy** (`killedRead_add_accum`,
  `killedRead_univ_eq_one_iff`): killed mass and clock-exhaustion mass
  partition the unit — pointwise set algebra from the a.e. fact that the
  start clock is `0`. `accumEvent T` is the by-horizon clock-exhaustion
  event: the qualitative face of the finite-expected-jumps hypothesis
  (hypothesis G4 of Everdij and Blom's bisimulation theory). Its nullity
  enters as a hypothesis here; for hybrid-system outcome chains,
  Zeno-freedom theorems of the kind proved in `LayerD/WZFreedom`
  discharge divergence of jump times, and the type-level identification
  of this module's timed chain with such a counted chain is deliberately
  out of scope (see the scope notes below).
* **Factorization** (`lintegral_timed_prefix`): the timed prefix
  marginals factor through the SKELETON prefix laws and the holding
  data — the strengthened indexing (states `≤ N+1`, durations `≤ N`) is
  chosen exactly so the last drawn duration is never integrated out
  before the next level consumes it. This is what makes the comparison
  law-grain rather than trivial kernel congruence.
* **The lift — the time-indexed comparison itself**
  (`killedRead_eq_of_prefix_eq`, `accum_eq_of_prefix_eq`): two models
  with (a) equal skeleton prefix laws at every level and (b) EQUAL
  holding families as functions (at the exponential instance: exactly an
  exit-rate data agreement) have equal killed time-indexed reads at
  every horizon, and equal accumulation masses — so a Zeno-freedom
  certificate transported through either model discharges full mass for
  both. The heterogeneous grains (skeleton at LAW level, durations at
  FUNCTION level) are deliberate and match what a flattening development
  delivers; a law-level duration hypothesis would need disintegration
  uniqueness (standard-Borel machinery) and is not taken.
* **The exponential pin** (`expHold`, `isMarkovKernel_expHold`,
  `expHold_congr`): the exit-rate family as a holding kernel, Markov
  under strict positivity; its congruence is the face where exit-rate
  data agreement enters.

## Scope notes

Deliberately out of scope, each a separate development: (i) the type
bridge identifying this module's timed chain with a counted-segment
chain, so that a Zeno-freedom conclusion is consumed verbatim for a
continuous-time chain presented as a segment model; (ii) rate-0 /
absorbing states at the exponential pin (strict positivity is taken;
absorbing states admit the usual Dirac-self-loop representation);
(iii) the tsum/disjointified form of the read (not needed by any
consumer-facing statement); (iv) identification with the deadline
development's timed skeleton at the exponential-segment instance;
(v) coloured (marked) refinements of the skeleton comparison.

No `sorry`; axiom receipts in `AxiomReceipts.lean`.
-/

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ENNReal NNReal

namespace Qtsl.KilledTimeIndexed

variable {S : Type*} [MeasurableSpace S]

/-! ## The killed one-step kernel -/

/-- The clock-advance kernel: from `(x, s)`, the law of `s + d` with
`d ~ dur x`. -/
noncomputable def clockStep (dur : Kernel S ℝ≥0) : Kernel (S × ℝ≥0) ℝ≥0 :=
  ((dur.comap Prod.fst measurable_fst) ×ₖ
      (Kernel.deterministic Prod.snd measurable_snd)).map
    (fun p : ℝ≥0 × ℝ≥0 => p.2 + p.1)

instance (dur : Kernel S ℝ≥0) [IsMarkovKernel dur] :
    IsMarkovKernel (clockStep dur) := by
  unfold clockStep
  exact Kernel.IsMarkovKernel.map _ (measurable_snd.add measurable_fst)

/-- **The killed one-step kernel**: from `(x, s)` draw the skeleton
step `y ~ K x` and the holding time `d ~ dur x` independently, emit
`(y, s + d)`. The second coordinate is the ENTRY clock of the new
state. -/
noncomputable def timedStep (K : Kernel S S) (dur : Kernel S ℝ≥0) :
    Kernel (S × ℝ≥0) (S × ℝ≥0) :=
  (K.comap Prod.fst measurable_fst) ×ₖ clockStep dur

instance (K : Kernel S S) (dur : Kernel S ℝ≥0) [IsMarkovKernel K]
    [IsMarkovKernel dur] : IsMarkovKernel (timedStep K dur) := by
  unfold timedStep; infer_instance

variable {K : Kernel S S} {dur : Kernel S ℝ≥0}

/-- The one-step read of `timedStep`, unfolded to the two independent
draws. -/
lemma lintegral_timedStep [IsMarkovKernel K] [IsMarkovKernel dur]
    (x : S) (s : ℝ≥0) {g : S × ℝ≥0 → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ v, g v ∂(timedStep K dur (x, s))
      = ∫⁻ y, ∫⁻ d, g (y, s + d) ∂(dur x) ∂(K x) := by
  rw [timedStep, Kernel.lintegral_prod _ _ _ hg, Kernel.comap_apply]
  refine lintegral_congr fun y => ?_
  have hadd : Measurable fun p : ℝ≥0 × ℝ≥0 => p.2 + p.1 :=
    measurable_snd.add measurable_fst
  have hgy : Measurable fun c : ℝ≥0 => g (y, c) :=
    hg.comp measurable_prodMk_left
  have hgy' : Measurable fun p : ℝ≥0 × ℝ≥0 => g (y, p.2 + p.1) :=
    hgy.comp hadd
  rw [clockStep, Kernel.lintegral_map _ hadd _ hgy,
    Kernel.lintegral_prod_deterministic measurable_snd _ _ hgy',
    Kernel.comap_apply]

/-! ## The killed trajectory measure and the time-indexed read -/

/-- **The killed Ionescu–Tulcea trajectory measure**: the timed chain
started at `(x, 0)`, on the `Battery.pathMeasure` substrate (mathlib's
`Kernel.traj`). -/
noncomputable def timedLaw (K : Kernel S S) (dur : Kernel S ℝ≥0)
    [IsMarkovKernel K] [IsMarkovKernel dur] (x : S) :
    Measure (ℕ → S × ℝ≥0) :=
  Battery.pathMeasure (timedStep K dur) (x, 0)

instance [IsMarkovKernel K] [IsMarkovKernel dur] (x : S) :
    IsProbabilityMeasure (timedLaw K dur x) := by
  unfold timedLaw; infer_instance

/-- The `n`-th read event at horizon `T`: the chain's `n`-th state lies
in `A`, entered by `T`, with the NEXT entry past `T` — the state
occupied at time `T`, read at jump index `n`. -/
def readEvent (n : ℕ) (T : ℝ≥0) (A : Set S) : Set (ℕ → S × ℝ≥0) :=
  {ω | (ω n).1 ∈ A ∧ (ω n).2 ≤ T ∧ T < (ω (n + 1)).2}

/-- The time-indexed killed read event (union form — deliberately; no
disjointness is consumed anywhere). -/
def readAll (T : ℝ≥0) (A : Set S) : Set (ℕ → S × ℝ≥0) :=
  ⋃ n, readEvent n T A

/-- The by-horizon clock-exhaustion (accumulation) event: every jump's
entry clock is within the horizon — infinitely many events by `T`. The
qualitative face of the finite-expected-jumps hypothesis (Everdij and
Blom's G4); its nullity enters as a hypothesis here, dischargeable by a
Zeno-freedom theorem (see the module docstring's scope notes). -/
def accumEvent (T : ℝ≥0) : Set (ℕ → S × ℝ≥0) :=
  {ω | ∀ n, (ω n).2 ≤ T}

lemma measurable_coordFst (n : ℕ) :
    Measurable fun ω : ℕ → S × ℝ≥0 => (ω n).1 :=
  (measurable_pi_apply n).fst

lemma measurable_coordSnd (n : ℕ) :
    Measurable fun ω : ℕ → S × ℝ≥0 => (ω n).2 :=
  (measurable_pi_apply n).snd

lemma measurableSet_readEvent {A : Set S} (hA : MeasurableSet A)
    (n : ℕ) (T : ℝ≥0) : MeasurableSet (readEvent n T A) :=
  ((measurable_coordFst (S := S) n) hA).inter
    (((measurable_coordSnd (S := S) n) measurableSet_Iic).inter
      ((measurable_coordSnd (S := S) (n + 1)) measurableSet_Ioi))

lemma measurableSet_readAll {A : Set S} (hA : MeasurableSet A)
    (T : ℝ≥0) : MeasurableSet (readAll T A) :=
  MeasurableSet.iUnion fun n => measurableSet_readEvent hA n T

lemma measurableSet_accumEvent (T : ℝ≥0) :
    MeasurableSet (accumEvent (S := S) T) := by
  have h : accumEvent (S := S) T = ⋂ n, {ω | (ω n).2 ≤ T} := by
    ext ω; simp [accumEvent]
  rw [h]
  exact MeasurableSet.iInter fun n =>
    measurableSet_le (measurable_coordSnd n) measurable_const

/-- **The time-indexed killed read**: the sub-probability mass with
which the process, not yet clock-exhausted by `T`, occupies `A` at
time `T`. -/
noncomputable def killedRead (K : Kernel S S) (dur : Kernel S ℝ≥0)
    [IsMarkovKernel K] [IsMarkovKernel dur] (x : S) (T : ℝ≥0)
    (A : Set S) : ℝ≥0∞ :=
  timedLaw K dur x (readAll T A)

/-! ## The mass dichotomy (the G4-recovery face) -/

/-- The pointwise complement identity: on paths whose start clock is
`0`, missing every read window at horizon `T` is EXACTLY clock
exhaustion by `T`. Pure set algebra — the complement induction from
`τ₀ = 0 ≤ T`; no null sets, no clock monotonicity. -/
lemma notMem_readAll_iff {ω : ℕ → S × ℝ≥0} (h0 : (ω 0).2 = 0)
    (T : ℝ≥0) : ω ∉ readAll T Set.univ ↔ ω ∈ accumEvent T := by
  constructor
  · intro h
    have hstep : ∀ n, (ω n).2 ≤ T → (ω (n + 1)).2 ≤ T := by
      intro n hn
      by_contra hlt
      exact h (Set.mem_iUnion.2 ⟨n, Set.mem_univ _, hn, not_le.1 hlt⟩)
    intro n
    induction n with
    | zero => rw [h0]; exact bot_le
    | succ n ih => exact hstep n ih
  · intro hacc hmem
    obtain ⟨n, -, -, hlt⟩ := Set.mem_iUnion.1 hmem
    exact absurd (hacc (n + 1)) (not_le.2 hlt)

section Dichotomy

variable [IsMarkovKernel K] [IsMarkovKernel dur]

/-- The start clock is `0` almost surely (only the CLOCK component of
coordinate `0` is consumed, so no singleton-class hypothesis on `S` is
needed). -/
lemma ae_clock_zero (x : S) :
    ∀ᵐ ω ∂(timedLaw K dur x), (ω 0).2 = 0 := by
  rw [ae_iff]
  have hset : {ω : ℕ → S × ℝ≥0 | ¬(ω 0).2 = 0}
      = (frestrictLe (π := fun _ : ℕ => S × ℝ≥0) 0) ⁻¹'
        {u | ¬(u ⟨0, mem_Iic.2 le_rfl⟩).2 = 0} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rfl
  have humeas : MeasurableSet
      {u : Π _i : Iic 0, S × ℝ≥0 | ¬(u ⟨0, mem_Iic.2 le_rfl⟩).2 = 0} :=
    ((measurable_snd.comp (measurable_pi_apply _))
      (measurableSet_singleton 0)).compl
  rw [hset, ← Measure.map_apply (measurable_frestrictLe 0) humeas]
  have hmap : (timedLaw K dur x).map (frestrictLe 0)
      = Measure.dirac (fun _ : Iic 0 => ((x : S), (0 : ℝ≥0))) := by
    rw [timedLaw, Battery.pathMeasure, Kernel.traj_map_frestrictLe_apply,
      Kernel.partialTraj_self, Kernel.id_apply]
  rw [hmap, Measure.dirac_apply' _ humeas]
  have hnot : (fun _ : Iic 0 => ((x : S), (0 : ℝ≥0)))
      ∉ {u : Π _i : Iic 0, S × ℝ≥0 | ¬(u ⟨0, mem_Iic.2 le_rfl⟩).2 = 0} := by
    simp
  exact Set.indicator_of_notMem hnot _

/-- **The mass dichotomy**: the killed read's total mass and the
accumulation mass partition the unit — the killed reading loses exactly
the clock-exhausted mass, no more. -/
theorem killedRead_add_accum (x : S) (T : ℝ≥0) :
    killedRead K dur x T Set.univ + timedLaw K dur x (accumEvent T)
      = 1 := by
  have hcongr : timedLaw K dur x (accumEvent T)
      = timedLaw K dur x (readAll T Set.univ)ᶜ := by
    refine measure_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [ae_clock_zero (K := K) (dur := dur) x] with ω h0
    rw [Set.mem_compl_iff]
    exact ⟨fun hacc => (notMem_readAll_iff h0 T).2 hacc,
      fun h => (notMem_readAll_iff h0 T).1 h⟩
  rw [killedRead, hcongr]
  have h := measure_add_measure_compl
    (μ := timedLaw K dur x) (measurableSet_readAll MeasurableSet.univ T)
  rwa [measure_univ] at h

/-- Full mass exactly on non-exhausting models: the finite-expected-
jumps hypothesis (G4), as an iff against the accumulation event. A
Zeno-freedom theorem discharges the right-hand side for models carrying
one (the type bridge is scope note (i) of the module docstring). -/
theorem killedRead_univ_eq_one_iff (x : S) (T : ℝ≥0) :
    killedRead K dur x T Set.univ = 1
      ↔ timedLaw K dur x (accumEvent T) = 0 := by
  have h := killedRead_add_accum (K := K) (dur := dur) x T
  constructor
  · intro h1
    rw [h1] at h
    have h' : (1 : ℝ≥0∞) + timedLaw K dur x (accumEvent T) = 1 + 0 := by
      rw [add_zero]; exact h
    exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 h'
  · intro h0
    rw [h0, add_zero] at h
    exact h

end Dichotomy

/-! ## Prefix plumbing: snoc maps and prefix clocks

The prefix-extension vocabulary mirrors mathlib's `partialTraj`
recursion (`IicProdIoc`, `MeasurableEquiv.piSingleton`) so both sides of
the factorization unfold through the same combinators; the only custom
glue is the duration snoc. Clocks are prefix sums over `Finset.range` of
the zero-extended duration vector, so all clock algebra is
`Finset.sum_range_succ`-shaped. -/

section Plumbing

variable {X : Type*}

/-- Append one value to an `Iic b`-indexed prefix. (`IicProdIoc` with a
`piSingleton` second leg computes the same function — the bridge is
`IicProdIoc_piSingleton` below — but the plain dite needs no measurable
structure.) -/
def snocS {b : ℕ} (u : Π _i : Iic b, X) (v : X) (i : Iic (b + 1)) : X :=
  if h : (i : ℕ) ≤ b then u ⟨i, mem_Iic.2 h⟩ else v

lemma snocS_of_le {b : ℕ} (u : Π _i : Iic b, X) (v : X)
    {i : ℕ} {hi : i ∈ Iic (b + 1)} (h : i ≤ b) :
    snocS u v ⟨i, hi⟩ = u ⟨i, mem_Iic.2 h⟩ :=
  dif_pos h

lemma snocS_last {b : ℕ} (u : Π _i : Iic b, X) (v : X)
    {hi : b + 1 ∈ Iic (b + 1)} : snocS u v ⟨b + 1, hi⟩ = v :=
  dif_neg (Nat.not_succ_le_self b)

lemma measurable_snocS [MeasurableSpace X] {b : ℕ} :
    Measurable (fun p : (Π _i : Iic b, X) × X => snocS p.1 p.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : (i : ℕ) ≤ b
  · have hm : Measurable fun p : (Π _i : Iic b, X) × X =>
        p.1 ⟨(i : ℕ), mem_Iic.2 h⟩ := measurable_fst.eval
    have he : (fun p : (Π _i : Iic b, X) × X => snocS p.1 p.2 i)
        = fun p => p.1 ⟨(i : ℕ), mem_Iic.2 h⟩ := by
      funext p; exact dif_pos h
    rw [he]; exact hm
  · have he : (fun p : (Π _i : Iic b, X) × X => snocS p.1 p.2 i)
        = fun p => p.2 := by
      funext p; exact dif_neg h
    rw [he]; exact measurable_snd

lemma frestrictLe₂_snocS {b : ℕ} (u : Π _i : Iic b, X) (v : X) :
    frestrictLe₂ (π := fun _ : ℕ => X) (Nat.le_succ b) (snocS u v) = u := by
  funext i
  exact dif_pos (mem_Iic.1 i.2)

/-- Partially-applied face of `measurable_snocS` (the eta-collapsed form
elaboration produces for `fun v => snocS u v`). -/
lemma measurable_snocS_right [MeasurableSpace X] {b : ℕ}
    (u : Π _i : Iic b, X) : Measurable (snocS u) := by
  have h : snocS u
      = fun v => (fun p : (Π _i : Iic b, X) × X => snocS p.1 p.2) (u, v) :=
    rfl
  rw [h]
  exact measurable_snocS.comp measurable_prodMk_left

/-- The bridge to mathlib's `partialTraj` extension vocabulary:
`IicProdIoc` with a `piSingleton` leg IS the snoc. -/
lemma IicProdIoc_piSingleton [MeasurableSpace X] {b : ℕ}
    (u : Π _i : Iic b, X) (v : X) :
    IicProdIoc (X := fun _ => X) b (b + 1)
        (u, MeasurableEquiv.piSingleton (X := fun _ => X) b v)
      = snocS u v := by
  funext i
  rcases i with ⟨i, hi⟩
  by_cases h : i ≤ b
  · have h1 : IicProdIoc (X := fun _ => X) b (b + 1)
        (u, MeasurableEquiv.piSingleton (X := fun _ => X) b v) ⟨i, hi⟩
          = u ⟨i, mem_Iic.2 h⟩ := dif_pos h
    have h2 : snocS u v ⟨i, hi⟩ = u ⟨i, mem_Iic.2 h⟩ := dif_pos h
    rw [h1, h2]
  · have hEq : i = b + 1 := by
      have := mem_Iic.1 hi; omega
    subst hEq
    have h1 : IicProdIoc (X := fun _ => X) b (b + 1)
        (u, MeasurableEquiv.piSingleton (X := fun _ => X) b v) ⟨b + 1, hi⟩
          = (MeasurableEquiv.piSingleton (X := fun _ => X) b) v
              ⟨b + 1, mem_Ioc.2 ⟨Nat.lt_succ_self b, le_rfl⟩⟩ :=
      dif_neg (Nat.not_succ_le_self b)
    rw [h1, snocS_last]
    exact
      (MeasurableEquiv.piSingleton (X := fun _ => X) b).symm_apply_apply v

/-- Zero-extension of an `Iic N`-indexed vector to a total function. -/
def extZ {N : ℕ} [Zero X] (ds : Π _j : Iic N, X) (j : ℕ) : X :=
  if h : j ≤ N then ds ⟨j, mem_Iic.2 h⟩ else 0

lemma extZ_of_le {N : ℕ} [Zero X] (ds : Π _j : Iic N, X) {j : ℕ}
    (h : j ≤ N) : extZ ds j = ds ⟨j, mem_Iic.2 h⟩ := dif_pos h

lemma measurable_extZ [MeasurableSpace X] [Zero X] {N j : ℕ} :
    Measurable (fun ds : Π _j : Iic N, X => extZ ds j) := by
  by_cases h : j ≤ N
  · have he : (fun ds : Π _j : Iic N, X => extZ ds j)
        = fun ds => ds ⟨j, mem_Iic.2 h⟩ := by
      funext ds; exact dif_pos h
    rw [he]; exact measurable_pi_apply _
  · have he : (fun ds : Π _j : Iic N, X => extZ ds j)
        = fun _ => 0 := by
      funext ds; exact dif_neg h
    rw [he]; exact measurable_const

/-- Append one duration. -/
def snocV {N : ℕ} (ds : Π _j : Iic N, X) (d : X) (j : Iic (N + 1)) : X :=
  if h : (j : ℕ) ≤ N then ds ⟨j, mem_Iic.2 h⟩ else d

lemma snocV_of_le {N : ℕ} (ds : Π _j : Iic N, X) (d : X)
    {j : Iic (N + 1)} (h : (j : ℕ) ≤ N) :
    snocV ds d j = ds ⟨j, mem_Iic.2 h⟩ := dif_pos h

lemma snocV_last {N : ℕ} (ds : Π _j : Iic N, X) (d : X)
    {hj : N + 1 ∈ Iic (N + 1)} : snocV ds d ⟨N + 1, hj⟩ = d :=
  dif_neg (Nat.not_succ_le_self N)

lemma measurable_snocV [MeasurableSpace X] {N : ℕ} :
    Measurable (fun p : (Π _j : Iic N, X) × X => snocV p.1 p.2) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases h : (j : ℕ) ≤ N
  · have hm : Measurable fun p : (Π _j : Iic N, X) × X =>
        p.1 ⟨(j : ℕ), mem_Iic.2 h⟩ := measurable_fst.eval
    have he : (fun p : (Π _j : Iic N, X) × X => snocV p.1 p.2 j)
        = fun p => p.1 ⟨(j : ℕ), mem_Iic.2 h⟩ := by
      funext p; exact dif_pos h
    rw [he]; exact hm
  · have he : (fun p : (Π _j : Iic N, X) × X => snocV p.1 p.2 j)
        = fun p => p.2 := by
      funext p; exact dif_neg h
    rw [he]; exact measurable_snd

lemma extZ_snocV_of_le {N : ℕ} [Zero X] (ds : Π _j : Iic N, X) (d : X)
    {j : ℕ} (h : j ≤ N) : extZ (snocV ds d) j = extZ ds j := by
  rw [extZ_of_le _ (h.trans (Nat.le_succ N)), extZ_of_le _ h]
  exact snocV_of_le ds d h

lemma extZ_snocV_last {N : ℕ} [Zero X] (ds : Π _j : Iic N, X) (d : X) :
    extZ (snocV ds d) (N + 1) = d := by
  rw [extZ_of_le _ le_rfl]
  exact snocV_last ds d

end Plumbing

/-- The prefix clock: the entry clock of coordinate `i` is the sum of
the holding times at indices `< i`. -/
def clockOf {N : ℕ} (ds : Π _j : Iic N, ℝ≥0) (i : ℕ) : ℝ≥0 :=
  ∑ j ∈ Finset.range i, extZ ds j

lemma clockOf_zero {N : ℕ} (ds : Π _j : Iic N, ℝ≥0) : clockOf ds 0 = 0 :=
  Finset.sum_range_zero _

lemma clockOf_singleton (d : ℝ≥0) :
    clockOf (fun _ : Iic 0 => d) 1 = d := by
  rw [clockOf, Finset.sum_range_one, extZ_of_le _ le_rfl]

lemma measurable_clockOf {N i : ℕ} :
    Measurable (fun ds : Π _j : Iic N, ℝ≥0 => clockOf ds i) := by
  unfold clockOf
  exact Finset.measurable_sum _ fun j _ => measurable_extZ

/-- Extending the durations does not move clocks at indices `≤ N + 1`. -/
lemma clockOf_snocV_of_le {N : ℕ} (ds : Π _j : Iic N, ℝ≥0) (d : ℝ≥0)
    {i : ℕ} (hi : i ≤ N + 1) :
    clockOf (snocV ds d) i = clockOf ds i := by
  unfold clockOf
  refine Finset.sum_congr rfl fun j hj => ?_
  exact extZ_snocV_of_le ds d (by have := Finset.mem_range.1 hj; omega)

/-- The new top clock: the old top clock plus the appended holding
time. -/
lemma clockOf_snocV_last {N : ℕ} (ds : Π _j : Iic N, ℝ≥0) (d : ℝ≥0) :
    clockOf (snocV ds d) (N + 2) = clockOf ds (N + 1) + d := by
  unfold clockOf
  rw [Finset.sum_range_succ, extZ_snocV_last]
  congr 1
  exact Finset.sum_congr rfl fun j hj =>
    extZ_snocV_of_le ds d (by have := Finset.mem_range.1 hj; omega)

/-- The zip: pair a state prefix with the clocks its durations
generate. Durations at index `j` are the holding time AT state `j`;
they enter clocks only at strictly later indices. -/
def zipPair {N : ℕ}
    (p : (Π _i : Iic (N + 1), S) × (Π _j : Iic N, ℝ≥0))
    (i : Iic (N + 1)) : S × ℝ≥0 :=
  (p.1 i, clockOf p.2 (i : ℕ))

lemma measurable_zipPair {N : ℕ} :
    Measurable (zipPair (S := S) (N := N)) := by
  refine measurable_pi_lambda _ fun i => Measurable.prodMk ?_ ?_
  · exact (measurable_pi_apply i).comp measurable_fst
  · exact measurable_clockOf.comp measurable_snd

/-- The snoc/zip exchange: extending then zipping is zipping then
extending by the top clock plus the fresh holding time. The whole
index bookkeeping of the factorization, as one function identity. -/
lemma zipPair_snoc {N : ℕ} (xs : Π _i : Iic (N + 1), S)
    (ds : Π _j : Iic N, ℝ≥0) (y : S) (d : ℝ≥0) :
    zipPair (S := S) (snocS xs y, snocV ds d)
      = snocS (zipPair (S := S) (xs, ds))
          (y, clockOf ds (N + 1) + d) := by
  funext i
  rcases i with ⟨i, hi⟩
  by_cases h : i ≤ N + 1
  · rw [snocS_of_le _ _ h]
    show (snocS xs y ⟨i, hi⟩, clockOf (snocV ds d) i) = _
    rw [snocS_of_le _ _ h, clockOf_snocV_of_le _ _ h]
    rfl
  · have hEq : i = N + 2 := by
      have := mem_Iic.1 hi; omega
    subst hEq
    show (snocS xs y ⟨N + 2, hi⟩, clockOf (snocV ds d) (N + 2)) = _
    rw [snocS_last, clockOf_snocV_last, snocS_last]

/-! ## The duration-attachment kernel -/

/-- Attach independent holding times `d_j ~ dur (x_j)`, `j ≤ N`, to a
state prefix of length `N + 2` (states `≤ N + 1`, durations `≤ N` — the
strengthened indexing the factorization induction needs). Built by
recursion from kernel combinators so measurability and the Markov
property ride the constructors. -/
noncomputable def durKle (dur : Kernel S ℝ≥0) :
    (N : ℕ) → Kernel (Π _i : Iic (N + 1), S) (Π _j : Iic N, ℝ≥0)
  | 0 =>
      (dur.comap (fun xs => xs ⟨0, mem_Iic.2 (Nat.zero_le 1)⟩)
          (measurable_pi_apply _)).map
        (fun d => fun _ : Iic 0 => d)
  | N + 1 =>
      (((durKle dur N).comap
            (frestrictLe₂ (π := fun _ : ℕ => S) (Nat.le_succ (N + 1)))
            (measurable_frestrictLe₂ _)) ×ₖ
          (dur.comap
            (fun xs => xs ⟨N + 1, mem_Iic.2 (Nat.le_succ (N + 1))⟩)
            (measurable_pi_apply _))).map
        (fun p => snocV p.1 p.2)

instance (dur : Kernel S ℝ≥0) [IsMarkovKernel dur] (N : ℕ) :
    IsMarkovKernel (durKle dur N) := by
  induction N with
  | zero =>
    rw [durKle]
    exact Kernel.IsMarkovKernel.map _
      (measurable_pi_lambda _ fun _ => measurable_id)
  | succ N ih =>
    rw [durKle]
    exact Kernel.IsMarkovKernel.map _ measurable_snocV

lemma lintegral_durKle_zero [IsMarkovKernel dur]
    (xs : Π _i : Iic 1, S) {g : (Π _j : Iic 0, ℝ≥0) → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ ds, g ds ∂(durKle dur 0 xs)
      = ∫⁻ d, g (fun _ => d)
          ∂(dur (xs ⟨0, mem_Iic.2 (Nat.zero_le 1)⟩)) := by
  have hconst : Measurable fun d : ℝ≥0 => (fun _ : Iic 0 => d) :=
    measurable_pi_lambda _ fun _ => measurable_id
  rw [durKle, Kernel.lintegral_map _ hconst _ hg, Kernel.lintegral_comap]

lemma lintegral_durKle_succ [IsMarkovKernel dur] (N : ℕ)
    (xs : Π _i : Iic (N + 2), S)
    {g : (Π _j : Iic (N + 1), ℝ≥0) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ds, g ds ∂(durKle dur (N + 1) xs)
      = ∫⁻ ds, ∫⁻ d, g (snocV ds d)
          ∂(dur (xs ⟨N + 1, mem_Iic.2 (Nat.le_succ (N + 1))⟩))
          ∂(durKle dur N
            (frestrictLe₂ (π := fun _ : ℕ => S)
              (Nat.le_succ (N + 1)) xs)) := by
  have hsn : Measurable fun p : (Π _j : Iic N, ℝ≥0) × ℝ≥0 =>
      snocV p.1 p.2 := measurable_snocV
  have hgs : Measurable fun p : (Π _j : Iic N, ℝ≥0) × ℝ≥0 =>
      g (snocV p.1 p.2) := hg.comp measurable_snocV
  rw [durKle, Kernel.lintegral_map _ hsn _ hg,
    Kernel.lintegral_prod _ _ _ hgs]
  simp only [Kernel.comap_apply]

/-! ## Chain-prefix unfolding lemmas (generic in the state space) -/

section ChainPrefix

variable {S' : Type*} [MeasurableSpace S'] (K' : Kernel S' S')
  [IsMarkovKernel K']

/-- Level-zero prefix: the deterministic start. -/
lemma lintegral_partialTraj_zero (x : S')
    {f : (Π _i : Iic 0, S') → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ u, f u
        ∂(Kernel.partialTraj (X := fun _ => S')
          (Battery.mchain K') 0 0 (fun _ => x))
      = f (fun _ => x) := by
  rw [Kernel.partialTraj_self, Kernel.id_apply, lintegral_dirac' _ hf]

/-- One-step unfolding of the applied `partialTraj` prefix: extend by
the chain kernel at the last coordinate. -/
lemma lintegral_partialTraj_succ (x : S') (b : ℕ)
    {f : (Π _i : Iic (b + 1), S') → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ u, f u
        ∂(Kernel.partialTraj (X := fun _ => S')
          (Battery.mchain K') 0 (b + 1) (fun _ => x))
      = ∫⁻ u, ∫⁻ y, f (snocS u y) ∂(K' (u ⟨b, mem_Iic.2 le_rfl⟩))
          ∂(Kernel.partialTraj (X := fun _ => S')
            (Battery.mchain K') 0 b (fun _ => x)) := by
  haveI : IsMarkovKernel
      ((Battery.mchain K' b).map
        (MeasurableEquiv.piSingleton (X := fun _ => S') b)) :=
    Kernel.IsMarkovKernel.map _
      (MeasurableEquiv.piSingleton (X := fun _ => S') b).measurable
  have hfi : Measurable fun p :
      (Π _i : Iic b, S') × (Π _i : Ioc b (b + 1), S') =>
      f (IicProdIoc (X := fun _ => S') b (b + 1) p) :=
    hf.comp (measurable_IicProdIoc (X := fun _ => S'))
  rw [Kernel.partialTraj_succ_of_le (Nat.zero_le b),
    Kernel.map_apply _ (measurable_IicProdIoc (X := fun _ => S')),
    lintegral_map hf (measurable_IicProdIoc (X := fun _ => S')),
    Kernel.comp_apply,
    Measure.lintegral_bind (Kernel.aemeasurable _) hfi.aemeasurable]
  refine lintegral_congr fun u => ?_
  have hfu : Measurable fun c : Π _i : Ioc b (b + 1), S' =>
      f (IicProdIoc (X := fun _ => S') b (b + 1) (u, c)) :=
    hfi.comp measurable_prodMk_left
  rw [Kernel.lintegral_id_prod hfi,
    Kernel.lintegral_map _
      (MeasurableEquiv.piSingleton (X := fun _ => S') b).measurable _ hfu,
    Battery.mchain_apply]
  exact lintegral_congr fun y => by rw [IicProdIoc_piSingleton]

/-- The `Iic`-prefix marginal of a chain law is the applied
`partialTraj`. -/
lemma pathMeasure_map_frestrictLe (x : S') (N : ℕ) :
    (Battery.pathMeasure K' x).map (frestrictLe N)
      = Kernel.partialTraj (X := fun _ => S')
          (Battery.mchain K') 0 N (fun _ => x) := by
  rw [Battery.pathMeasure, Kernel.traj_map_frestrictLe_apply]

end ChainPrefix

/-! ## The factorization (the load-bearing lemma) -/

section Factorization

variable [IsMarkovKernel K] [IsMarkovKernel dur]

/-- Parameter-measurability of a one-step read against a kernel
composed with a measurable selection — the workhorse for the
side conditions below. -/
private lemma measurable_kernelRead {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (κ : Kernel B C)
    [IsSFiniteKernel κ] {sel : A → B} (hsel : Measurable sel)
    {h : A × C → ℝ≥0∞} (hh : Measurable h) :
    Measurable fun a => ∫⁻ c, h (a, c) ∂(κ (sel a)) :=
  Measurable.lintegral_kernel_prod_right'
    (κ := κ.comap sel hsel) hh

/-- **The factorization theorem**: the timed prefix marginal is the
skeleton prefix law with independent holding times attached and clocks
accumulated. Stated over applied `partialTraj` prefixes; the
`pathMeasure`-marginal face is `pathMeasure_map_frestrictLe`. The
strengthened indexing (states `≤ N + 1`, durations `≤ N`) is what lets
the induction carry the last holding time to the level that consumes
it. -/
theorem lintegral_timed_prefix (x : S) :
    ∀ (N : ℕ) {f : (Π _i : Iic (N + 1), S × ℝ≥0) → ℝ≥0∞},
      Measurable f →
      ∫⁻ u, f u
          ∂(Kernel.partialTraj (X := fun _ => S × ℝ≥0)
            (Battery.mchain (timedStep K dur)) 0
            (N + 1) (fun _ => ((x : S), (0 : ℝ≥0))))
        = ∫⁻ xs, ∫⁻ ds, f (zipPair (xs, ds)) ∂(durKle dur N xs)
            ∂(Kernel.partialTraj (X := fun _ => S)
              (Battery.mchain K) 0 (N + 1)
              (fun _ => x)) := by
  intro N
  induction N with
  | zero =>
    intro f hf
    have hFmeas : Measurable fun u : Π _i : Iic 0, S × ℝ≥0 =>
        ∫⁻ v, f (snocS u v)
          ∂(timedStep K dur (u ⟨0, mem_Iic.2 le_rfl⟩)) :=
      measurable_kernelRead (timedStep K dur) (measurable_pi_apply _)
        (hf.comp measurable_snocS)
    have hsn0 : Measurable fun v : S × ℝ≥0 =>
        f (snocS (fun _ : Iic 0 => ((x : S), (0 : ℝ≥0))) v) :=
      hf.comp (measurable_snocS_right _)
    have hzip : Measurable fun p :
        (Π _i : Iic 1, S) × (Π _j : Iic 0, ℝ≥0) => f (zipPair p) :=
      hf.comp measurable_zipPair
    have hGmeas : Measurable fun xs : Π _i : Iic 1, S =>
        ∫⁻ ds, f (zipPair (xs, ds)) ∂(durKle dur 0 xs) :=
      measurable_kernelRead (durKle dur 0) measurable_id hzip
    have hF2 : Measurable fun u : Π _i : Iic 0, S =>
        ∫⁻ y, ∫⁻ ds, f (zipPair (snocS u y, ds))
          ∂(durKle dur 0 (snocS u y)) ∂(K (u ⟨0, mem_Iic.2 le_rfl⟩)) :=
      measurable_kernelRead K (measurable_pi_apply _)
        (hGmeas.comp measurable_snocS)
    calc ∫⁻ u, f u
          ∂(Kernel.partialTraj (X := fun _ => S × ℝ≥0)
            (Battery.mchain (timedStep K dur)) 0 (0 + 1)
            (fun _ => ((x : S), (0 : ℝ≥0))))
        = ∫⁻ u, ∫⁻ v, f (snocS u v)
            ∂(timedStep K dur (u ⟨0, mem_Iic.2 le_rfl⟩))
            ∂(Kernel.partialTraj (X := fun _ => S × ℝ≥0)
              (Battery.mchain (timedStep K dur)) 0 0
              (fun _ => ((x : S), (0 : ℝ≥0)))) :=
          lintegral_partialTraj_succ (timedStep K dur) _ 0 hf
      _ = ∫⁻ v, f (snocS (fun _ : Iic 0 => ((x : S), (0 : ℝ≥0))) v)
            ∂(timedStep K dur ((x : S), (0 : ℝ≥0))) :=
          lintegral_partialTraj_zero (timedStep K dur) _ hFmeas
      _ = ∫⁻ y, ∫⁻ d,
            f (snocS (fun _ : Iic 0 => ((x : S), (0 : ℝ≥0))) (y, 0 + d))
            ∂(dur x) ∂(K x) :=
          lintegral_timedStep x 0 hsn0
      _ = ∫⁻ y, ∫⁻ d,
            f (zipPair (snocS (fun _ : Iic 0 => x) y, fun _ : Iic 0 => d))
            ∂(dur x) ∂(K x) := by
          refine lintegral_congr fun y => lintegral_congr fun d => ?_
          congr 1
          funext i
          rcases i with ⟨i, hi⟩
          have hi' : i ≤ 1 := mem_Iic.1 hi
          interval_cases i
          · have h1 : snocS (fun _ : Iic 0 => ((x : S), (0 : ℝ≥0)))
                (y, 0 + d) ⟨0, hi⟩ = ((x : S), (0 : ℝ≥0)) :=
              snocS_of_le _ _ (Nat.le_refl 0)
            have h2 : snocS (fun _ : Iic 0 => x) y ⟨0, hi⟩ = x :=
              snocS_of_le _ _ (Nat.le_refl 0)
            show snocS (fun _ : Iic 0 => ((x : S), (0 : ℝ≥0)))
                (y, 0 + d) ⟨0, hi⟩
              = (snocS (fun _ : Iic 0 => x) y ⟨0, hi⟩,
                clockOf (fun _ : Iic 0 => d) 0)
            rw [h1, h2, clockOf_zero]
          · show snocS (fun _ : Iic 0 => ((x : S), (0 : ℝ≥0)))
                (y, 0 + d) ⟨1, hi⟩
              = (snocS (fun _ : Iic 0 => x) y ⟨1, hi⟩,
                clockOf (fun _ : Iic 0 => d) 1)
            rw [snocS_last, snocS_last, clockOf_singleton, zero_add]
      _ = ∫⁻ y, ∫⁻ ds, f (zipPair (snocS (fun _ : Iic 0 => x) y, ds))
            ∂(durKle dur 0 (snocS (fun _ : Iic 0 => x) y)) ∂(K x) := by
          refine lintegral_congr fun y => ?_
          have hgy : Measurable fun ds : Π _j : Iic 0, ℝ≥0 =>
              f (zipPair (snocS (fun _ : Iic 0 => x) y, ds)) :=
            hf.comp (measurable_zipPair.comp measurable_prodMk_left)
          have harg : (snocS (fun _ : Iic 0 => x) y)
              ⟨0, mem_Iic.2 (Nat.zero_le 1)⟩ = x :=
            snocS_of_le _ _ (Nat.le_refl 0)
          rw [lintegral_durKle_zero (snocS (fun _ : Iic 0 => x) y) hgy,
            harg]
      _ = ∫⁻ u, ∫⁻ y, ∫⁻ ds, f (zipPair (snocS u y, ds))
            ∂(durKle dur 0 (snocS u y)) ∂(K (u ⟨0, mem_Iic.2 le_rfl⟩))
            ∂(Kernel.partialTraj (X := fun _ => S)
              (Battery.mchain K) 0 0 (fun _ => x)) :=
          (lintegral_partialTraj_zero K _ hF2).symm
      _ = ∫⁻ xs, ∫⁻ ds, f (zipPair (xs, ds)) ∂(durKle dur 0 xs)
            ∂(Kernel.partialTraj (X := fun _ => S)
              (Battery.mchain K) 0 (0 + 1) (fun _ => x)) :=
          (lintegral_partialTraj_succ K x 0 hGmeas).symm
  | succ N ih =>
    intro f hf
    have hfsnoc : Measurable fun p :
        (Π _i : Iic (N + 1), S × ℝ≥0) × (S × ℝ≥0) =>
        f (snocS p.1 p.2) := hf.comp measurable_snocS
    have hGmeas : Measurable fun u : Π _i : Iic (N + 1), S × ℝ≥0 =>
        ∫⁻ v, f (snocS u v)
          ∂(timedStep K dur (u ⟨N + 1, mem_Iic.2 le_rfl⟩)) :=
      measurable_kernelRead (timedStep K dur) (measurable_pi_apply _)
        hfsnoc
    have hzip : Measurable fun p :
        (Π _i : Iic (N + 2), S) × (Π _j : Iic (N + 1), ℝ≥0) =>
        f (zipPair p) := hf.comp measurable_zipPair
    have hHmeas : Measurable fun xs : Π _i : Iic (N + 2), S =>
        ∫⁻ ds, f (zipPair (xs, ds)) ∂(durKle dur (N + 1) xs) :=
      measurable_kernelRead (durKle dur (N + 1)) measurable_id hzip
    calc ∫⁻ u, f u
          ∂(Kernel.partialTraj (X := fun _ => S × ℝ≥0)
            (Battery.mchain (timedStep K dur)) 0 (N + 1 + 1)
            (fun _ => ((x : S), (0 : ℝ≥0))))
        = ∫⁻ u, ∫⁻ v, f (snocS u v)
            ∂(timedStep K dur (u ⟨N + 1, mem_Iic.2 le_rfl⟩))
            ∂(Kernel.partialTraj (X := fun _ => S × ℝ≥0)
              (Battery.mchain (timedStep K dur)) 0 (N + 1)
              (fun _ => ((x : S), (0 : ℝ≥0)))) :=
          lintegral_partialTraj_succ (timedStep K dur) _ (N + 1) hf
      _ = ∫⁻ xs, ∫⁻ ds, ∫⁻ v,
            f (snocS (zipPair (xs, ds)) v)
            ∂(timedStep K dur
              (xs ⟨N + 1, mem_Iic.2 le_rfl⟩, clockOf ds (N + 1)))
            ∂(durKle dur N xs)
            ∂(Kernel.partialTraj (X := fun _ => S)
              (Battery.mchain K) 0 (N + 1) (fun _ => x)) :=
          ih hGmeas
      _ = ∫⁻ xs, ∫⁻ ds, ∫⁻ y, ∫⁻ d,
            f (snocS (zipPair (xs, ds))
              (y, clockOf ds (N + 1) + d))
            ∂(dur (xs ⟨N + 1, mem_Iic.2 le_rfl⟩))
            ∂(K (xs ⟨N + 1, mem_Iic.2 le_rfl⟩))
            ∂(durKle dur N xs)
            ∂(Kernel.partialTraj (X := fun _ => S)
              (Battery.mchain K) 0 (N + 1) (fun _ => x)) := by
          refine lintegral_congr fun xs => lintegral_congr fun ds => ?_
          exact lintegral_timedStep _ _
            (hf.comp (measurable_snocS_right _))
      _ = ∫⁻ xs, ∫⁻ ds, ∫⁻ y, ∫⁻ d,
            f (zipPair (snocS xs y, snocV ds d))
            ∂(dur (xs ⟨N + 1, mem_Iic.2 le_rfl⟩))
            ∂(K (xs ⟨N + 1, mem_Iic.2 le_rfl⟩))
            ∂(durKle dur N xs)
            ∂(Kernel.partialTraj (X := fun _ => S)
              (Battery.mchain K) 0 (N + 1) (fun _ => x)) := by
          refine lintegral_congr fun xs => lintegral_congr fun ds =>
            lintegral_congr fun y => lintegral_congr fun d => ?_
          rw [zipPair_snoc]
      _ = ∫⁻ xs, ∫⁻ y, ∫⁻ ds, ∫⁻ d,
            f (zipPair (snocS xs y, snocV ds d))
            ∂(dur (xs ⟨N + 1, mem_Iic.2 le_rfl⟩))
            ∂(durKle dur N xs)
            ∂(K (xs ⟨N + 1, mem_Iic.2 le_rfl⟩))
            ∂(Kernel.partialTraj (X := fun _ => S)
              (Battery.mchain K) 0 (N + 1) (fun _ => x)) := by
          refine lintegral_congr fun xs => ?_
          have hinner : Measurable fun q :
              ((Π _j : Iic N, ℝ≥0) × S) × ℝ≥0 =>
              f (zipPair (snocS xs q.1.2, snocV q.1.1 q.2)) := by
            refine hf.comp
              (measurable_zipPair.comp (Measurable.prodMk ?_ ?_))
            · exact measurable_snocS.comp
                (measurable_const.prodMk
                  (measurable_snd.comp measurable_fst))
            · exact measurable_snocV.comp
                ((measurable_fst.comp measurable_fst).prodMk
                  measurable_snd)
          have hΨ : Measurable fun p : (Π _j : Iic N, ℝ≥0) × S =>
              ∫⁻ d, f (zipPair (snocS xs p.2, snocV p.1 d))
                ∂(dur (xs ⟨N + 1, mem_Iic.2 le_rfl⟩)) :=
            Measurable.lintegral_prod_right' hinner
          exact lintegral_lintegral_swap hΨ.aemeasurable
      _ = ∫⁻ xs, ∫⁻ y, ∫⁻ ds, f (zipPair (snocS xs y, ds))
            ∂(durKle dur (N + 1) (snocS xs y))
            ∂(K (xs ⟨N + 1, mem_Iic.2 le_rfl⟩))
            ∂(Kernel.partialTraj (X := fun _ => S)
              (Battery.mchain K) 0 (N + 1) (fun _ => x)) := by
          refine lintegral_congr fun xs => lintegral_congr fun y => ?_
          have hgy : Measurable fun ds' : Π _j : Iic (N + 1), ℝ≥0 =>
              f (zipPair (snocS xs y, ds')) :=
            hf.comp (measurable_zipPair.comp measurable_prodMk_left)
          have harg : (snocS xs y)
              ⟨N + 1, mem_Iic.2 (Nat.le_succ (N + 1))⟩
                = xs ⟨N + 1, mem_Iic.2 le_rfl⟩ :=
            snocS_of_le _ _ le_rfl
          rw [lintegral_durKle_succ N (snocS xs y) hgy,
            frestrictLe₂_snocS, harg]
      _ = ∫⁻ xs, ∫⁻ ds, f (zipPair (xs, ds))
            ∂(durKle dur (N + 1) xs)
            ∂(Kernel.partialTraj (X := fun _ => S)
              (Battery.mchain K) 0 (N + 1 + 1) (fun _ => x)) :=
          (lintegral_partialTraj_succ K x (N + 1) hHmeas).symm

end Factorization

/-! ## The lift: the time-indexed comparison -/

section Lift

variable {K₁ K₂ : Kernel S S} {dur₁ dur₂ : Kernel S ℝ≥0}
  [IsMarkovKernel K₁] [IsMarkovKernel K₂]
  [IsMarkovKernel dur₁] [IsMarkovKernel dur₂] {x₁ x₂ : S}

/-- Skeleton prefix-law agreement + holding-data agreement transport to
the timed prefix marginals — the factorization consumed at both models.
Note the heterogeneous grains: the skeleton hypothesis is LAW-level,
the duration hypothesis FUNCTION-level, exactly what a flattening
development delivers. -/
theorem mapped_timed_prefix_eq
    (hskel : ∀ N : ℕ,
      (Battery.pathMeasure K₁ x₁).map (frestrictLe N)
        = (Battery.pathMeasure K₂ x₂).map (frestrictLe N))
    (hdur : dur₁ = dur₂) (N : ℕ) :
    (timedLaw K₁ dur₁ x₁).map (frestrictLe (N + 1))
      = (timedLaw K₂ dur₂ x₂).map (frestrictLe (N + 1)) := by
  subst hdur
  ext B hB
  have hind : Measurable
      (B.indicator (1 : (Π _i : Iic (N + 1), S × ℝ≥0) → ℝ≥0∞)) :=
    measurable_one.indicator hB
  rw [← lintegral_indicator_one hB, ← lintegral_indicator_one hB,
    timedLaw, timedLaw, Battery.pathMeasure, Battery.pathMeasure,
    Kernel.traj_map_frestrictLe_apply, Kernel.traj_map_frestrictLe_apply,
    lintegral_timed_prefix x₁ N hind, lintegral_timed_prefix x₂ N hind,
    ← pathMeasure_map_frestrictLe K₁ x₁ (N + 1),
    ← pathMeasure_map_frestrictLe K₂ x₂ (N + 1), hskel (N + 1)]

/-- The bounded read events, as prefix cylinders. -/
lemma readPartial_eq_preimage (N : ℕ) (T : ℝ≥0) (A : Set S) :
    (⋃ n, ⋃ (_ : n ≤ N), readEvent (S := S) n T A)
      = (frestrictLe (π := fun _ : ℕ => S × ℝ≥0) (N + 1)) ⁻¹'
        (⋃ n, ⋃ (h : n ≤ N),
          {u : Π _i : Iic (N + 1), S × ℝ≥0 |
            (u ⟨n, mem_Iic.2 (h.trans (Nat.le_succ N))⟩).1 ∈ A ∧
            (u ⟨n, mem_Iic.2 (h.trans (Nat.le_succ N))⟩).2 ≤ T ∧
            T < (u ⟨n + 1, mem_Iic.2 (Nat.succ_le_succ h)⟩).2}) := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_preimage, readEvent,
    Set.mem_setOf_eq]
  rfl

lemma measurable_cylFst {M : ℕ} (i : Iic M) :
    Measurable fun u : Π _i : Iic M, S × ℝ≥0 => (u i).1 :=
  (measurable_pi_apply i).fst

lemma measurable_cylSnd {M : ℕ} (i : Iic M) :
    Measurable fun u : Π _i : Iic M, S × ℝ≥0 => (u i).2 :=
  (measurable_pi_apply i).snd

lemma measurableSet_readCyl (N : ℕ) (T : ℝ≥0) {A : Set S}
    (hA : MeasurableSet A) :
    MeasurableSet (⋃ n, ⋃ (h : n ≤ N),
      {u : Π _i : Iic (N + 1), S × ℝ≥0 |
        (u ⟨n, mem_Iic.2 (h.trans (Nat.le_succ N))⟩).1 ∈ A ∧
        (u ⟨n, mem_Iic.2 (h.trans (Nat.le_succ N))⟩).2 ≤ T ∧
        T < (u ⟨n + 1, mem_Iic.2 (Nat.succ_le_succ h)⟩).2}) := by
  refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun h => ?_
  exact ((measurable_cylFst (S := S) _) hA).inter
    (((measurable_cylSnd (S := S) _) measurableSet_Iic).inter
      ((measurable_cylSnd (S := S) _) measurableSet_Ioi))

/-- The bounded accumulation events, as prefix cylinders. -/
lemma accumPartial_eq_preimage (N : ℕ) (T : ℝ≥0) :
    {ω : ℕ → S × ℝ≥0 | ∀ n ≤ N + 1, (ω n).2 ≤ T}
      = (frestrictLe (π := fun _ : ℕ => S × ℝ≥0) (N + 1)) ⁻¹'
        {u : Π _i : Iic (N + 1), S × ℝ≥0 |
          ∀ n, ∀ h : n ≤ N + 1, (u ⟨n, mem_Iic.2 h⟩).2 ≤ T} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  exact ⟨fun hω n h => hω n h, fun hω n h => hω n h⟩

lemma measurableSet_accumCyl (N : ℕ) (T : ℝ≥0) :
    MeasurableSet {u : Π _i : Iic (N + 1), S × ℝ≥0 |
      ∀ n, ∀ h : n ≤ N + 1, (u ⟨n, mem_Iic.2 h⟩).2 ≤ T} := by
  have h : {u : Π _i : Iic (N + 1), S × ℝ≥0 |
        ∀ n, ∀ h : n ≤ N + 1, (u ⟨n, mem_Iic.2 h⟩).2 ≤ T}
      = ⋂ n, ⋂ (h : n ≤ N + 1),
          {u : Π _i : Iic (N + 1), S × ℝ≥0 |
            (u ⟨n, mem_Iic.2 h⟩).2 ≤ T} := by
    ext u; simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [h]
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun h =>
    (measurable_cylSnd (S := S) _) measurableSet_Iic

/-- **The time-indexed comparison** (the lift): skeleton prefix-law
agreement plus holding-data agreement give equality of the killed
time-indexed reads at every horizon and every measurable target — the
jump-skeleton comparison lifted through the killed-IT construction. -/
theorem killedRead_eq_of_prefix_eq
    (hskel : ∀ N : ℕ,
      (Battery.pathMeasure K₁ x₁).map (frestrictLe N)
        = (Battery.pathMeasure K₂ x₂).map (frestrictLe N))
    (hdur : dur₁ = dur₂) (T : ℝ≥0) {A : Set S} (hA : MeasurableSet A) :
    killedRead K₁ dur₁ x₁ T A = killedRead K₂ dur₂ x₂ T A := by
  have hpartial : ∀ (μ : Measure (ℕ → S × ℝ≥0)),
      μ (readAll T A) = ⨆ N : ℕ,
        μ (⋃ n, ⋃ (_ : n ≤ N), readEvent n T A) := by
    intro μ
    have hmono : Monotone fun N : ℕ =>
        ⋃ n, ⋃ (_ : n ≤ N), readEvent (S := S) n T A := by
      intro a b hab
      exact Set.iUnion_mono fun n =>
        Set.iUnion_subset fun h => Set.subset_iUnion_of_subset
          (h.trans hab) le_rfl
    have hcover : readAll (S := S) T A
        = ⋃ N : ℕ, ⋃ n, ⋃ (_ : n ≤ N), readEvent n T A := by
      ext ω
      simp only [readAll, Set.mem_iUnion]
      exact ⟨fun ⟨n, hn⟩ => ⟨n, n, le_rfl, hn⟩,
        fun ⟨N, n, _, hn⟩ => ⟨n, hn⟩⟩
    rw [hcover, hmono.measure_iUnion]
  rw [killedRead, killedRead, hpartial (timedLaw K₁ dur₁ x₁),
    hpartial (timedLaw K₂ dur₂ x₂)]
  refine iSup_congr fun N => ?_
  rw [readPartial_eq_preimage N T A,
    ← Measure.map_apply (measurable_frestrictLe (N + 1))
      (measurableSet_readCyl N T hA),
    ← Measure.map_apply (measurable_frestrictLe (N + 1))
      (measurableSet_readCyl N T hA),
    mapped_timed_prefix_eq hskel hdur N]

/-- Accumulation-mass agreement under the same hypotheses: the
clock-exhaustion (G4) hypothesis transports across the comparison, so a
Zeno-freedom certificate discharging it for one model discharges it for
both. -/
theorem accum_eq_of_prefix_eq
    (hskel : ∀ N : ℕ,
      (Battery.pathMeasure K₁ x₁).map (frestrictLe N)
        = (Battery.pathMeasure K₂ x₂).map (frestrictLe N))
    (hdur : dur₁ = dur₂) (T : ℝ≥0) :
    timedLaw K₁ dur₁ x₁ (accumEvent T)
      = timedLaw K₂ dur₂ x₂ (accumEvent T) := by
  have hpartial : ∀ (μ : Measure (ℕ → S × ℝ≥0)),
      IsProbabilityMeasure μ →
      μ (accumEvent T) = ⨅ N : ℕ,
        μ {ω : ℕ → S × ℝ≥0 | ∀ n ≤ N + 1, (ω n).2 ≤ T} := by
    intro μ hμ
    have hanti : Antitone fun N : ℕ =>
        {ω : ℕ → S × ℝ≥0 | ∀ n ≤ N + 1, (ω n).2 ≤ T} := by
      intro a b hab ω hω n hn
      exact hω n (hn.trans (Nat.succ_le_succ hab))
    have hcover : accumEvent (S := S) T
        = ⋂ N : ℕ, {ω : ℕ → S × ℝ≥0 | ∀ n ≤ N + 1, (ω n).2 ≤ T} := by
      ext ω
      simp only [accumEvent, Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun hω N n hn => hω n, fun hω n => hω n n (by omega)⟩
    have hnm : ∀ N : ℕ, NullMeasurableSet
        {ω : ℕ → S × ℝ≥0 | ∀ n ≤ N + 1, (ω n).2 ≤ T} μ := by
      intro N
      refine (MeasurableSet.nullMeasurableSet ?_)
      have h : {ω : ℕ → S × ℝ≥0 | ∀ n ≤ N + 1, (ω n).2 ≤ T}
          = ⋂ n, ⋂ (_ : n ≤ N + 1), {ω : ℕ → S × ℝ≥0 | (ω n).2 ≤ T} := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [h]
      exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
        measurableSet_le (measurable_coordSnd n) measurable_const
    rw [hcover, hanti.measure_iInter hnm ⟨0, measure_ne_top μ _⟩]
  rw [hpartial _ inferInstance, hpartial _ inferInstance]
  refine iInf_congr fun N => ?_
  rw [accumPartial_eq_preimage N T,
    ← Measure.map_apply (measurable_frestrictLe (N + 1))
      (measurableSet_accumCyl N T),
    ← Measure.map_apply (measurable_frestrictLe (N + 1))
      (measurableSet_accumCyl N T),
    mapped_timed_prefix_eq hskel hdur N]

end Lift

/-! ## The exponential pin (the exit-rate face) -/

section Exponential

/-- The exit-rate (exponential) holding family: density
`t ↦ r·exp(−r·t)` on `[0, ∞)` against Lebesgue, pushed into `ℝ≥0`. -/
noncomputable def expHold (lam : S → ℝ) : Kernel S ℝ≥0 :=
  (Kernel.withDensity (Kernel.const S (volume : Measure ℝ))
      (fun x t => exponentialPDF (lam x) t)).map Real.toNNReal

/-- Joint measurability of the exponential density family. -/
lemma measurable_expDensity {lam : S → ℝ} (hlam : Measurable lam) :
    Measurable
      (Function.uncurry fun x t => exponentialPDF (lam x) t) := by
  have h1 : Measurable fun p : S × ℝ =>
      (if 0 ≤ p.2 then lam p.1 * Real.exp (-(lam p.1 * p.2)) else 0) := by
    refine Measurable.ite
      (measurableSet_le measurable_const measurable_snd) ?_
      measurable_const
    exact (hlam.comp measurable_fst).mul
      ((((hlam.comp measurable_fst).mul measurable_snd).neg).exp)
  have h2 : (Function.uncurry fun x t => exponentialPDF (lam x) t)
      = fun p : S × ℝ => ENNReal.ofReal
          (if 0 ≤ p.2 then lam p.1 * Real.exp (-(lam p.1 * p.2))
            else 0) := by
    funext p
    rw [Function.uncurry, exponentialPDF_eq]
  rw [h2]
  exact ENNReal.measurable_ofReal.comp h1

/-- The exponential holding family is Markov under strictly positive
rates — the ONLY place the rate-0/absorbing subtlety lives (scope
note (ii) of the module docstring). -/
lemma isMarkovKernel_expHold {lam : S → ℝ} (hlam : Measurable lam)
    (hpos : ∀ x, 0 < lam x) : IsMarkovKernel (expHold lam) := by
  have hd := measurable_expDensity hlam
  constructor
  intro x
  constructor
  rw [expHold, Kernel.map_apply _ measurable_real_toNNReal,
    Measure.map_apply measurable_real_toNNReal MeasurableSet.univ,
    Set.preimage_univ, Kernel.withDensity_apply _ hd,
    Kernel.const_apply, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ]
  exact lintegral_exponentialPDF_eq_one (hpos x)

/-- The exit-rate congruence face: equal rate data give equal holding
families — where an exit-rate data agreement plugs into
`killedRead_eq_of_prefix_eq`'s `hdur`. -/
lemma expHold_congr {lam₁ lam₂ : S → ℝ} (h : lam₁ = lam₂) :
    expHold (S := S) lam₁ = expHold lam₂ := by rw [h]

end Exponential

end Qtsl.KilledTimeIndexed
