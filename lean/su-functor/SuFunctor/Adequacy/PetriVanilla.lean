import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import SuFunctor.Adequacy.SemanticUniverseWiring

/-! # Adequacy: vanilla place/transition nets, demonic (scheduler-seat) face

The interleaving adequacy square of the *vanilla* Petri species —
ordinary place/transition nets: arc multiplicities in `ℕ`, no
inhibitors, no guards beyond arcs, and *no stochastic structure at
all*.  The stochastic-Petri squares (`StochasticPetriCascade`,
`StochasticPetriDemonic`) close compiled nets onto path *laws*; the
vanilla species compiles to a bag-former system whose every kernel is
Dirac and whose every transition clock is the demonic wing at a
strictly positive dwell floor, so its semantics is a *scheduler-seat
family of deterministic timed runs*, and its classical corner is not a
law but a reachability relation.  This module states that square and
wires it to the semantic universe in the same record shape as the
demonic net square (`su_ispn_demonic_adequacy`).

**The compile, in one breath.**  Places at unit colour (a bag of
unit-colour tokens *is* its count, so markings are count vectors); one
transition row per `t` with the demonic clock at dwell floor `d t > 0`,
a Dirac kernel, the atomic affine reset `m ↦ m − pre + post` (no
consume/produce half-states), and the arc-cover guard
`∀ p, pre t p ≤ m p`.  The declared meter semantics of the demonic
clock: a transition may fire only after a contiguously-enabled window
spanning at least its dwell floor, where the transition's *own* firing
resets its meter and other transitions' firings do not.  `DemonicRun`
transcribes exactly that semantics as model data — finitely many
firings at strictly monotone positive rational times (strict
monotonicity *is* the interleaving reading), each admitted by the meter
law in existential-window form, with the window's endpoint included so
that enabledness-at-fire is *derived*, never assumed.

**The square.**  `face_eq_reach`: the possibilistic visited-marking
face of the scheduler-seat family equals classical interleaving
reachability, for *every* strictly positive dwell assignment — the
soundness leg spends only enabledness (the dwell floor is not consumed;
containment holds a fortiori over the meter class), and the
completeness leg realizes each classical firing at exactly the dwell
floor.  `face_dwell_uniform` is the flagged corollary: the face is
*independent* of the dwell assignment — the time-embedding is
quotiented away by the possibilistic retract, so the uniform unit dwell
used by transcription conventions is nowhere load-bearing: the compile
is faithful for ordering-and-counting properties, deliberately not for
metric-time properties an untimed net never had.

**Why the demonic reading is resolution-quantified directly.**  The
stochastic species' demonic faces quantify an adversary over compiled
*rows* (scheduler-row mechanisms closing rate rows onto chains).  The
vanilla species has no rows-level compilation in this tree — every
kernel being Dirac, the scheduler seat's resolutions *are* the whole
mechanism — so the compiled demonic reading enters as the
resolution-quantified constraint itself, the feeding lemma
(`vanillaDemonicC_iff`) is definitional, and the square's semantic
content lives one retract below the law stratum: at the possibilistic
visited-marking face, where the timed meter semantics meets classical
reachability (`recordVisited_eq_face`, then `face_eq_reach`).  The
module says so rather than manufacturing a rows detour.

**The semantic-universe wiring** (in-module, per the standing
precedent).  Each resolution's law at horizon `k` is the Dirac law on
its marking trajectory (runs shorter than the horizon idle at their
final marking — the seat's idling member is the honest semantics);
the demonic law-set is the union of singletons over resolutions, its
credal presentation the union of rays; the compiled presentation is the
one-atom projection `diagramDnf`, so finite presentation is untouched
by the resolution family's infinitude, exactly as at the other demonic
corners.  `su_vanilla_demonic_adequacy` is the record-shape square:
the ideal point of a law models the compiled demonic presentation
exactly when the law is a member of the demonic law-set.  The headline
retract theorem is `su_vanilla_reach_iff`: a marking is visited by the
support of *some* law whose ideal point models the presentation at
*some* horizon exactly when it is classically reachable —
compile-then-denote-then-retract equals classical Petri semantics, read
at the semantic universe's judgment.

**Scope fences.**  Liveness is absent by design: the demonic clock
carries no fairness, priority, or weight vocabulary, and the idling
resolution is always seated.  Step/set-firing semantics (simultaneous
multi-firing beyond interleaving), inhibitor arcs, and mixed
race-plus-demonic systems are untouched.  The infinite-horizon face
adds nothing at this retract: every visited marking is visited at a
finite index, and prefixes of admissible runs are admissible, so the
finite-run family carries the whole reachability face.  No certificate
rows are minted. -/

namespace SuFunctor

namespace Adequacy

namespace PetriVanilla

open CategoryTheory PseudoDoubleCategoryStruct
open SuFunctor.Universe (SpecDnf)

variable {P T : Type}

/-! ## The classical corner: nets, firing, reachability -/

/-- Markings are place-indexed token counts — the count dictionary's
codomain (a bag of unit-colour tokens is its count). -/
abbrev Marking (P : Type) := P → ℕ

/-- A vanilla place/transition net: arc multiplicities only — no
inhibitors, no guards beyond arcs, no stochastic structure. -/
structure PetriNet (P T : Type) where
  /-- consumption multiplicities -/
  pre : T → P → ℕ
  /-- production multiplicities -/
  post : T → P → ℕ

/-- Classical enabling: the marking covers the consumption row — the
compiled stay-face gate. -/
def enabled (N : PetriNet P T) (t : T) (m : Marking P) : Prop :=
  ∀ p, N.pre t p ≤ m p

instance [Fintype P] (N : PetriNet P T) (t : T) (m : Marking P) :
    Decidable (enabled N t m) :=
  inferInstanceAs (Decidable (∀ p, N.pre t p ≤ m p))

/-- The firing update `m − pre + post` (`ℕ`-truncated; under `enabled`
it agrees with the exact affine reset — the compiled Dirac kernel's
atomic update: no consume/produce half-states). -/
def fire (N : PetriNet P T) (t : T) (m : Marking P) : Marking P :=
  fun p => m p - N.pre t p + N.post t p

/-- Classical interleaving reachability — the square's classical
corner. -/
inductive Reach (N : PetriNet P T) (m0 : Marking P) : Marking P → Prop
  | refl : Reach N m0 m0
  | step {m : Marking P} (t : T) (hm : Reach N m0 m)
      (ht : enabled N t m) : Reach N m0 (fire N t m)

/-! ## The timed corner: markings along a firing sequence, the meter
law -/

/-- The marking after `k` firings of the sequence `tr` (stabilizes past
`n`): the piecewise-constant trajectory's value on its `k`-th
interval. -/
def marks (N : PetriNet P T) (m0 : Marking P) {n : ℕ} (tr : Fin n → T) :
    ℕ → Marking P
  | 0 => m0
  | k + 1 =>
    if h : k < n then fire N (tr ⟨k, h⟩) (marks N m0 tr k)
    else marks N m0 tr k

/-- The time at which the `s`-th marking interval begins: 0 for the
initial marking, else the `(s−1)`-th firing time.  `onset time n` is
the final firing time (0 for the empty run) — the run's end time. -/
def onset {n : ℕ} (time : Fin n → ℚ) : ℕ → ℚ
  | 0 => 0
  | s + 1 => if h : s < n then time ⟨s, h⟩ else 0

/-- **The declared meter law of the demonic clock**, existential-window
form: firing `k` is admitted iff some window of marking indices
`[s, k]` (i) is contiguously enabled for `tr k` — endpoint INCLUDED, so
enabledness-at-fire is derived; (ii) contains no earlier firing of
`tr k` itself (the transition's own firing resets its meter; other
transitions' firings are tolerated); and (iii) spans at least the dwell
floor: `d (tr k) ≤ time k − onset s` (fire allowed AT the floor; the
face below is boundary-insensitive — a strict reading pads the
completeness spacing by any positive margin). -/
def MeterOK (N : PetriNet P T) (d : T → ℚ) (m0 : Marking P) {n : ℕ}
    (tr : Fin n → T) (time : Fin n → ℚ) (k : Fin n) : Prop :=
  ∃ s : ℕ, s ≤ (k : ℕ) ∧
    (∀ i : ℕ, s ≤ i → i ≤ (k : ℕ) → enabled N (tr k) (marks N m0 tr i)) ∧
    (∀ j : Fin n, s ≤ (j : ℕ) → (j : ℕ) < (k : ℕ) → tr j ≠ tr k) ∧
    d (tr k) ≤ time k - onset time s

/-- **One resolution of the demonic scheduler seat** for the compiled
net: finitely many firings at strictly monotone positive rational times
(strict monotonicity IS interleaving — one firing per instant), each
admitted by the meter law.  All fields are model data — the declared
semantics transcribed. -/
structure DemonicRun (N : PetriNet P T) (d : T → ℚ) (m0 : Marking P) where
  /-- number of firings -/
  n : ℕ
  /-- which transition fires at each step -/
  tr : Fin n → T
  /-- when it fires -/
  time : Fin n → ℚ
  /-- interleaving: firing times strictly increase -/
  mono : StrictMono time
  /-- records begin at time 0 -/
  pos : ∀ i, 0 < time i
  /-- every firing is meter-admitted -/
  meter : ∀ k, MeterOK N d m0 tr time k

variable {N : PetriNet P T} {d : T → ℚ} {m0 : Marking P}

/-- **The possibilistic face**, projected to visited markings:
everything some resolution visits. -/
def face (N : PetriNet P T) (d : T → ℚ) (m0 : Marking P) :
    Set (Marking P) :=
  {m | ∃ R : DemonicRun N d m0, ∃ k, k ≤ R.n ∧ marks N m0 R.tr k = m}

/-! ## Soundness: visited ⊆ reachable -/

/-- Enabledness-at-fire, DERIVED from the meter window's included
endpoint (with the endpoint excluded this is underivable and the
soundness theorem is false — the `ℕ`-truncated update would visit
unreachable markings). -/
theorem DemonicRun.enabled_at (R : DemonicRun N d m0) (k : Fin R.n) :
    enabled N (R.tr k) (marks N m0 R.tr (k : ℕ)) := by
  obtain ⟨s, hs, hen, -, -⟩ := R.meter k
  exact hen (k : ℕ) hs le_rfl

/-- Every prefix marking of an enabling-respecting firing sequence is
classically reachable — the dwell floor is not consumed (soundness
holds a fortiori over the meter class). -/
theorem marks_reach {n : ℕ} (N : PetriNet P T) (m0 : Marking P)
    (tr : Fin n → T)
    (hen : ∀ k : Fin n, enabled N (tr k) (marks N m0 tr (k : ℕ))) :
    ∀ k, k ≤ n → Reach N m0 (marks N m0 tr k) := by
  intro k
  induction k with
  | zero => exact fun _ => Reach.refl
  | succ k ih =>
    intro hk
    have hkn : k < n := hk
    simp only [marks]
    rw [dif_pos hkn]
    exact Reach.step (tr ⟨k, hkn⟩) (ih hkn.le) (hen ⟨k, hkn⟩)

/-- **Soundness leg of the square**: the possibilistic face is
contained in classical reachability. -/
theorem face_sound : face N d m0 ⊆ {m | Reach N m0 m} := by
  rintro m ⟨R, k, hk, rfl⟩
  exact marks_reach N m0 R.tr (fun j => R.enabled_at j) k hk

/-! ## Completeness: reachable ⊆ visited — the realization move -/

/-- The empty resolution (zero firings) — inhabits every net. -/
def DemonicRun.nil (N : PetriNet P T) (d : T → ℚ) (m0 : Marking P) :
    DemonicRun N d m0 where
  n := 0
  tr := Fin.elim0
  time := Fin.elim0
  mono := by intro a; exact a.elim0
  pos := by intro a; exact a.elim0
  meter := by intro a; exact a.elim0

instance : Nonempty (DemonicRun N d m0) := ⟨DemonicRun.nil N d m0⟩

/-- Snoc-invariance of prefix markings: appending a firing does not
change the markings before it. -/
theorem marks_snoc {n : ℕ} (N : PetriNet P T) (m0 : Marking P)
    (tr : Fin n → T) (t : T) :
    ∀ {k : ℕ}, k ≤ n → marks N m0 (Fin.snoc tr t) k = marks N m0 tr k := by
  intro k
  induction k with
  | zero => exact fun _ => rfl
  | succ k ih =>
    intro hk
    have hkn : k < n := hk
    have h : (⟨k, Nat.lt_succ_of_lt hkn⟩ : Fin (n + 1))
        = Fin.castSucc ⟨k, hkn⟩ := Fin.ext rfl
    simp only [marks]
    rw [dif_pos (Nat.lt_succ_of_lt hkn), dif_pos hkn, ih hkn.le, h,
      Fin.snoc_castSucc]

/-- The appended firing's marking: the extended run ends at
`fire t (end marking)`. -/
theorem marks_snoc_last {n : ℕ} (N : PetriNet P T) (m0 : Marking P)
    (tr : Fin n → T) (t : T) :
    marks N m0 (Fin.snoc tr t) (n + 1) = fire N t (marks N m0 tr n) := by
  have h : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n :=
    Fin.ext rfl
  simp only [marks]
  rw [dif_pos (Nat.lt_succ_self n), marks_snoc N m0 tr t le_rfl, h,
    Fin.snoc_last]

/-- Snoc-invariance of interval-onset times, below the appended
index. -/
theorem onset_snoc {n : ℕ} (time : Fin n → ℚ) (a : ℚ) {s : ℕ}
    (hs : s ≤ n) :
    onset (Fin.snoc time a : Fin (n + 1) → ℚ) s = onset time s := by
  cases s with
  | zero => rfl
  | succ s =>
    have hsn : s < n := hs
    have h : (⟨s, Nat.lt_succ_of_lt hsn⟩ : Fin (n + 1))
        = Fin.castSucc ⟨s, hsn⟩ := Fin.ext rfl
    simp only [onset]
    rw [dif_pos (Nat.lt_succ_of_lt hsn), dif_pos hsn, h, Fin.snoc_castSucc]

/-- Every firing time is at most the run's end time `onset time n`. -/
theorem le_onset_top {n : ℕ} {time : Fin n → ℚ} (hmono : Monotone time)
    (i : Fin n) : time i ≤ onset time n := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    simp only [onset]
    rw [dif_pos (Nat.lt_succ_self m)]
    exact hmono (Fin.le_def.mpr (Nat.lt_succ_iff.mp i.2))

/-- The end time is nonnegative. -/
theorem onset_top_nonneg {n : ℕ} {time : Fin n → ℚ}
    (hpos : ∀ i, 0 < time i) : 0 ≤ onset time n := by
  cases n with
  | zero => exact le_refl 0
  | succ m =>
    simp only [onset]
    rw [dif_pos (Nat.lt_succ_self m)]
    exact (hpos _).le

/-- Appending a strictly later point preserves strict monotonicity. -/
theorem strictMono_snoc {n : ℕ} {f : Fin n → ℚ} (hf : StrictMono f)
    (a : ℚ) (ha : ∀ i, f i < a) :
    StrictMono (Fin.snoc f a : Fin (n + 1) → ℚ) := by
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hf (Fin.castSucc_lt_castSucc_iff.mp hij)
    · have h1 : (n : ℕ) < (j' : ℕ) := by simpa [Fin.lt_def] using hij
      exact absurd h1 (not_lt.mpr j'.2.le)
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc, Fin.snoc_last]
      exact ha i'
    · exact absurd hij (lt_irrefl _)

/-- **The realization move** (completeness's engine): a resolution
whose end marking enables `t` extends by one firing at EXACTLY the
dwell floor — the meter's window is the single final interval.  Strict
positivity of the floor powers monotonicity and positivity; the
exact-floor meter check witnesses the fire-at-the-floor boundary
convention. -/
def DemonicRun.extend (R : DemonicRun N d m0) (t : T)
    (hen : enabled N t (marks N m0 R.tr R.n)) (hd : 0 < d t) :
    DemonicRun N d m0 where
  n := R.n + 1
  tr := Fin.snoc R.tr t
  time := Fin.snoc R.time (onset R.time R.n + d t)
  mono := strictMono_snoc R.mono _ fun i =>
    (le_onset_top R.mono.monotone i).trans_lt (lt_add_of_pos_right _ hd)
  pos := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]
      exact R.pos i'
    · rw [Fin.snoc_last]
      exact add_pos_of_nonneg_of_pos (onset_top_nonneg R.pos) hd
  meter := by
    intro k
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
    · -- old firings: transport the old window through the snoc glue
      obtain ⟨s, hs, hen', hown, hmet⟩ := R.meter k'
      refine ⟨s, by simpa using hs, fun i hsi hik => ?_,
        fun j hsj hjk => ?_, ?_⟩
      · have hik' : i ≤ (k' : ℕ) := by simpa using hik
        rw [Fin.snoc_castSucc, marks_snoc N m0 R.tr t (hik'.trans k'.2.le)]
        exact hen' i hsi hik'
      · have hjk' : (j : ℕ) < (k' : ℕ) := by simpa using hjk
        have hjn : (j : ℕ) < R.n := hjk'.trans k'.2
        have hj : j = Fin.castSucc ⟨(j : ℕ), hjn⟩ := Fin.ext rfl
        rw [hj]
        simp only [Fin.snoc_castSucc]
        exact hown ⟨(j : ℕ), hjn⟩ hsj hjk'
      · simp only [Fin.snoc_castSucc]
        rw [onset_snoc R.time _ (hs.trans k'.2.le)]
        exact hmet
    · -- the new firing: window = the single final interval
      refine ⟨R.n, by simp, fun i hsi hik => ?_, fun j hsj hjk => ?_, ?_⟩
      · have hi : i = R.n := le_antisymm (by simpa using hik) hsi
        subst hi
        simp only [Fin.snoc_last]
        rw [marks_snoc N m0 R.tr t le_rfl]
        exact hen
      · have hj : (j : ℕ) < R.n := by simpa using hjk
        exact absurd (hsj.trans_lt hj) (lt_irrefl _)
      · simp only [Fin.snoc_last]
        rw [onset_snoc R.time _ le_rfl]
        linarith

/-- Every classically reachable marking is some resolution's END
marking (induction through the realization move). -/
theorem reach_endrun (hd : ∀ t, 0 < d t) {m : Marking P}
    (h : Reach N m0 m) :
    ∃ R : DemonicRun N d m0, marks N m0 R.tr R.n = m := by
  induction h with
  | refl => exact ⟨DemonicRun.nil N d m0, rfl⟩
  | step t hm ht ih =>
    obtain ⟨R, hR⟩ := ih
    have hen : enabled N t (marks N m0 R.tr R.n) := by
      rw [hR]; exact ht
    refine ⟨R.extend t hen (hd t), ?_⟩
    show marks N m0 (Fin.snoc R.tr t) (R.n + 1) = _
    rw [marks_snoc_last, hR]

/-- **Completeness leg of the square**. -/
theorem face_complete (hd : ∀ t, 0 < d t) {m : Marking P}
    (h : Reach N m0 m) : m ∈ face N d m0 := by
  obtain ⟨R, hR⟩ := reach_endrun hd h
  exact ⟨R, R.n, le_rfl, hR⟩

/-! ## The square, at the marking face -/

/-- **THE ADEQUACY SQUARE, face level**: the possibilistic
visited-marking face of the compiled net's scheduler-seat family equals
classical interleaving reachability — for EVERY strictly positive dwell
assignment. -/
theorem face_eq_reach (hd : ∀ t, 0 < d t) :
    face N d m0 = {m | Reach N m0 m} :=
  Set.Subset.antisymm face_sound fun _ hm => face_complete hd hm

/-- **Dwell-uniformity of the face**: the face is INDEPENDENT of the
dwell assignment — the time-embedding is quotiented away by the
possibilistic retract, so a transcription convention's uniform unit
dwell is nowhere load-bearing.  Faithful for ordering-and-counting,
deliberately not for metric time. -/
theorem face_dwell_uniform {d' : T → ℚ} (hd : ∀ t, 0 < d t)
    (hd' : ∀ t, 0 < d' t) : face N d m0 = face N d' m0 := by
  rw [face_eq_reach hd, face_eq_reach hd']

/-! ## The record space: resolutions as trajectory laws

Marking trajectories stabilize past a run's last firing, so a run
shorter than the horizon idles at its final marking — the scheduler
seat's idling member, honestly seated. -/

/-- Markings stabilize past the run's last firing. -/
theorem marks_stab {n : ℕ} (N : PetriNet P T) (m0 : Marking P)
    (tr : Fin n → T) : ∀ {k : ℕ}, n ≤ k →
    marks N m0 tr k = marks N m0 tr n := by
  intro k
  induction k with
  | zero =>
    intro hk
    obtain rfl : n = 0 := Nat.le_zero.mp hk
    rfl
  | succ k ih =>
    intro hk
    rcases Nat.lt_or_ge n (k + 1) with h | h
    · have hnk : n ≤ k := Nat.lt_succ_iff.mp h
      simp only [marks]
      rw [dif_neg (Nat.not_lt.mpr hnk), ih hnk]
    · obtain rfl : n = k + 1 := le_antisymm hk h
      rfl

/-- The point mass's weight is supported exactly at its point. -/
theorem dirac_wt_ne_zero_iff {V : Type*} {x y : V} :
    (SubPMF.dirac x).wt y ≠ 0 ↔ y = x := by
  classical
  have h : (SubPMF.dirac x).wt y = Finsupp.single x 1 y := rfl
  rw [h, Finsupp.single_apply]
  constructor
  · intro hne
    by_contra hxy
    exact hne (if_neg fun hc => hxy hc.symm)
  · rintro rfl
    rw [if_pos rfl]
    exact one_ne_zero

/-- The horizon-`k` marking trajectory of a resolution: the visited
markings, idling at the final one past the last firing. -/
def DemonicRun.traj (R : DemonicRun N d m0) (k : ℕ) :
    Traj (Marking P) k :=
  fun i => marks N m0 R.tr (i : ℕ)

/-- **The law of a resolution at horizon `k`**: every kernel of the
compiled vanilla net is Dirac, so a resolution's trajectory law is the
point mass on its marking trajectory. -/
noncomputable def DemonicRun.law (R : DemonicRun N d m0) (k : ℕ) :
    SubPMF (Traj (Marking P) k) :=
  SubPMF.dirac (R.traj k)

/-- A resolution's law has full mass — the equal-mass hypothesis the
slice reconciliation spends. -/
theorem DemonicRun.law_mass (R : DemonicRun N d m0) (k : ℕ) :
    (R.law k).mass = 1 :=
  SubPMF.dirac_prob_of_mem (Set.mem_univ _)

/-- **The demonic semantics of the compiled vanilla net**, per horizon:
the set of trajectory laws over all scheduler-seat resolutions, as a
set-valued constraint. -/
noncomputable def vanillaDemonicLaws (N : PetriNet P T) (d : T → ℚ)
    (m0 : Marking P) (k : ℕ) : SubPMF (Traj (Marking P) k) → Prop :=
  unionSingletons fun R : DemonicRun N d m0 => R.law k

/-- The credal presentation of the demonic face: the union of the
members' rays. -/
noncomputable def vanillaDemonicCredal (N : PetriNet P T) (d : T → ℚ)
    (m0 : Marking P) (k : ℕ) : SubPMF (Traj (Marking P) k) → Prop :=
  unionRays fun R : DemonicRun N d m0 => R.law k

/-- Every member of the demonic law-set is some resolution's trajectory
law — the set is exactly the resolution-indexed family. -/
theorem vanillaDemonicLaws_iff (k : ℕ) (μ : SubPMF (Traj (Marking P) k)) :
    vanillaDemonicLaws N d m0 k μ ↔
      ∃ R : DemonicRun N d m0, μ = R.law k :=
  Iff.rfl

/-! ## The compiled demonic reading and the record-shape square -/

/-- **The demonic reading of the compiled vanilla net**: `μ` is
admitted exactly when some scheduler-seat resolution produces it.  The
vanilla species has no rows-level compilation — every kernel is Dirac,
so the resolutions are the whole mechanism and the demon is quantified
over them directly. -/
noncomputable def vanillaDemonicC (N : PetriNet P T) (d : T → ℚ)
    (m0 : Marking P) (k : ℕ) : SubPMF (Traj (Marking P) k) → Prop :=
  fun μ => ∃ R : DemonicRun N d m0, μ = R.law k

/-- **The feeding lemma — definitional at this species.**  With no rows
machinery intervening, the compiled demonic reading and the demonic
law-set coincide by unfolding; the square's semantic content lives at
the possibilistic retract below (`recordVisited_eq_face`). -/
theorem vanillaDemonicC_iff (k : ℕ) (μ : SubPMF (Traj (Marking P) k)) :
    vanillaDemonicC N d m0 k μ ↔ vanillaDemonicLaws N d m0 k μ :=
  Iff.rfl

/-- The set-valued square at the law stratum, as an invertible globular
cell — definitional at this species, recorded for shape parity with the
stochastic demonic corners. -/
theorem vanilla_demonic_adequacy (k : ℕ)
    {a : Crd (Traj (Marking P) k)} :
    ∃ α : Cell (vanillaDemonicC N d m0 k : Loose a a)
        (vanillaDemonicLaws N d m0 k) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  Crd.looseIso_ofIff fun μ => vanillaDemonicC_iff k μ

/-- The radially maximal slice of the demonic credal set is exactly the
demonic law-set — the equal-mass reconciliation at full mass, every
resolution's law being a point mass. -/
theorem vanilla_demonic_maxSlice (k : ℕ)
    (ν : SubPMF (Traj (Marking P) k)) :
    maxSlice (vanillaDemonicCredal N d m0 k) ν ↔
      vanillaDemonicLaws N d m0 k ν :=
  maxSlice_unionRays (fun R => R.law_mass k) one_ne_zero ν

/-- **The demonic lower verdict is the uniform-over-resolutions
bound**: a lower-kind constraint holds of the demonic credal set
exactly when it holds of every resolution's trajectory law. -/
theorem satCredal_lower_vanillaDemonicCredal (k : ℕ)
    (c : SubPMF (Traj (Marking P) k) → Prop) :
    SatCredal .lower (vanillaDemonicCredal N d m0 k) c ↔
      ∀ R : DemonicRun N d m0, c (R.law k) :=
  satCredal_lower_unionRays (fun R => R.law_mass k) one_ne_zero c

/-- **The demonic upper verdict**, for down-closed constraints —
mass-free, through down-closure. -/
theorem satCredal_upper_vanillaDemonicCredal (k : ℕ)
    {c : SubPMF (Traj (Marking P) k) → Prop} (hc : DownClosed c) :
    SatCredal .upper (vanillaDemonicCredal N d m0 k) c ↔
      ∀ R : DemonicRun N d m0, c (R.law k) :=
  satCredal_upper_unionRays hc

/-! ## The semantic-universe wiring -/

/-- The compiled vanilla net's demonic presentation in the semantic
universe's fibre: the resolution-quantified reading as a one-atom
projection — the set-valued face presents as a single wall atom, so
finite presentation is untouched by the resolution family's
infinitude, exactly as at the other demonic corners. -/
noncomputable def vanillaDemonicDnf (N : PetriNet P T) (d : T → ℚ)
    (m0 : Marking P) (k : ℕ) :
    SpecDnf (Plain.Joint (Traj (Marking P) k)) :=
  diagramDnf [vanillaDemonicC N d m0 k]

/-- **The vanilla demonic square, wired to the semantic universe**: the
ideal point of a law models the compiled demonic presentation exactly
when the law is a member of the demonic law-set. -/
theorem su_vanilla_demonic_adequacy (k : ℕ)
    (μ : SubPMF (Traj (Marking P) k)) :
    idealPoint μ ∈ (vanillaDemonicDnf N d m0 k).modelClass
      ↔ vanillaDemonicLaws N d m0 k μ := by
  have h := idealPoint_mem_diagramDnf_iff [vanillaDemonicC N d m0 k] μ
  constructor
  · intro hm
    obtain ⟨h1, -⟩ := h.mp hm
    exact (vanillaDemonicC_iff k μ).mp h1
  · intro hl
    exact h.mpr ⟨(vanillaDemonicC_iff k μ).mpr hl, trivial⟩

/-- The positive face: every resolution's trajectory law models the
compiled demonic presentation. -/
theorem su_vanilla_demonic_mem (R : DemonicRun N d m0) (k : ℕ) :
    idealPoint (R.law k) ∈ (vanillaDemonicDnf N d m0 k).modelClass :=
  (su_vanilla_demonic_adequacy k _).mpr ⟨R, singletonC_self _⟩

/-- Ex falso at the vanilla demonic corner. -/
theorem su_vanilla_demonic_bottom (k : ℕ) :
    (⊤ : Plain.Pen (Traj (Marking P) k))
      ∉ (vanillaDemonicDnf N d m0 k).modelClass :=
  top_notMem_diagramDnf _

/-- The credal reading at the vanilla demonic corner: membership at the
semantic universe's judgment is exactly radial maximality in the
union-of-rays credal object. -/
theorem su_vanilla_demonic_slice (k : ℕ)
    (ν : SubPMF (Traj (Marking P) k)) :
    idealPoint ν ∈ (vanillaDemonicDnf N d m0 k).modelClass
      ↔ maxSlice (vanillaDemonicCredal N d m0 k) ν :=
  (su_vanilla_demonic_adequacy k ν).trans
    (vanilla_demonic_maxSlice k ν).symm

/-! ## The possibilistic retract: the record-space face is the
workshop face -/

/-- **The visited-marking retract of the record family**: the markings
visited by the support of some admitted law, at some horizon — the
possibilistic face of the demonic record-space semantics, projected to
marking coordinates. -/
def recordVisited (N : PetriNet P T) (d : T → ℚ) (m0 : Marking P) :
    Set (Marking P) :=
  {m | ∃ k : ℕ, ∃ μ : SubPMF (Traj (Marking P) k),
    vanillaDemonicLaws N d m0 k μ ∧ ∃ ω, μ.wt ω ≠ 0 ∧ ∃ i, ω i = m}

/-- **The record-space identification**: the visited-marking retract of
the trajectory-law family IS the run-model face.  Laws are point
masses, so supports are trajectories; trajectories read `marks`, which
stabilizes past the last firing, so horizon overshoot idles at the end
marking and horizon shortfall is recovered by reading the run at its
own length. -/
theorem recordVisited_eq_face :
    recordVisited N d m0 = face N d m0 := by
  ext m
  constructor
  · rintro ⟨k, μ, ⟨R, hR⟩, ω, hω, i, rfl⟩
    rw [(singletonC_iff _ _).mp hR] at hω
    have hωt : ω = R.traj k := dirac_wt_ne_zero_iff.mp hω
    subst hωt
    rcases Nat.lt_or_ge R.n (i : ℕ) with h | h
    · exact ⟨R, R.n, le_rfl, (marks_stab N m0 R.tr h.le).symm⟩
    · exact ⟨R, (i : ℕ), h, rfl⟩
  · rintro ⟨R, j, hj, rfl⟩
    exact ⟨j, R.law j, ⟨R, singletonC_self _⟩, R.traj j,
      dirac_wt_ne_zero_iff.mpr rfl, ⟨j, Nat.lt_succ_self j⟩, rfl⟩

/-- **THE ADEQUACY SQUARE AT THE RECORD STRATUM**: the visited-marking
retract of the record-space demonic family equals classical
interleaving reachability — compile, denote into the record space,
retract possibilistically: classical Petri semantics. -/
theorem su_vanilla_face_eq_reach (hd : ∀ t, 0 < d t) :
    recordVisited N d m0 = {m | Reach N m0 m} := by
  rw [recordVisited_eq_face]
  exact face_eq_reach hd

/-- **The square, read at the semantic universe's judgment**: a marking
is visited by the support of some law whose ideal point models the
compiled demonic presentation, at some horizon, exactly when it is
classically reachable. -/
theorem su_vanilla_reach_iff (hd : ∀ t, 0 < d t) (m : Marking P) :
    (∃ (k : ℕ) (μ : SubPMF (Traj (Marking P) k)),
        idealPoint μ ∈ (vanillaDemonicDnf N d m0 k).modelClass
          ∧ ∃ ω, μ.wt ω ≠ 0 ∧ ∃ i, ω i = m)
      ↔ Reach N m0 m := by
  constructor
  · rintro ⟨k, μ, hm, hvis⟩
    have hv : m ∈ recordVisited N d m0 :=
      ⟨k, μ, (su_vanilla_demonic_adequacy k μ).mp hm, hvis⟩
    rw [su_vanilla_face_eq_reach hd] at hv
    exact hv
  · intro h
    have hv : m ∈ recordVisited N d m0 := by
      rw [su_vanilla_face_eq_reach hd]
      exact h
    obtain ⟨k, μ, hl, hvis⟩ := hv
    exact ⟨k, μ, (su_vanilla_demonic_adequacy k μ).mpr hl, hvis⟩

/-- Dwell-uniformity at the record stratum: the visited-marking retract
is independent of the dwell assignment — no metric-time structure
survives the possibilistic face of the record semantics. -/
theorem su_vanilla_dwell_uniform {d' : T → ℚ} (hd : ∀ t, 0 < d t)
    (hd' : ∀ t, 0 < d' t) :
    recordVisited N d m0 = recordVisited N d' m0 := by
  rw [recordVisited_eq_face, recordVisited_eq_face,
    face_dwell_uniform hd hd']

/-- **Safety transfer at the record stratum** — the customer shape for
invariant-class examinations (one-safeness, bounds): a marking
predicate holds on everything the record semantics can visit iff it
holds on the classical reachable set. -/
theorem su_vanilla_safety (hd : ∀ t, 0 < d t) (Φ : Marking P → Prop) :
    (∀ m ∈ recordVisited N d m0, Φ m) ↔
      ∀ m, Reach N m0 m → Φ m := by
  rw [su_vanilla_face_eq_reach hd]
  exact Iff.rfl

end PetriVanilla

/-! ## Controls

Second witnesses at the designed mutant loci, on two closed-form nets:
the two-place toggle (finite face, one-safe) and the one-place source
(unbounded face — the dwell floor bounds nothing). -/

namespace PetriVanillaControls

open PetriVanilla

/-- The toggle net: transition `t` consumes one token from place `t`
and produces one on the other place. -/
def toggle : PetriNet (Fin 2) (Fin 2) where
  pre := fun t p => if p = t then 1 else 0
  post := fun t p => if p = t then 0 else 1

/-- Initial marking `(1, 0)`. -/
def toggleM0 : Marking (Fin 2) := fun p => if p = 0 then 1 else 0

/-- The other marking `(0, 1)`. -/
def toggleM1 : Marking (Fin 2) := fun p => if p = 0 then 0 else 1

/-- The reachable set, closed form: exactly the two markings. -/
theorem toggle_reach_iff {m : Marking (Fin 2)} :
    Reach toggle toggleM0 m ↔ m = toggleM0 ∨ m = toggleM1 := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | step t hm ht ih =>
      rcases ih with rfl | rfl
      · fin_cases t
        · exact Or.inr (by decide)
        · exact absurd ht (by decide)
      · fin_cases t
        · exact absurd ht (by decide)
        · exact Or.inl (by decide)
  · rintro (rfl | rfl)
    · exact Reach.refl
    · have h := Reach.step (N := toggle) (m0 := toggleM0) (m := toggleM0)
        0 Reach.refl (by decide)
      rwa [show fire toggle 0 toggleM0 = toggleM1 by decide] at h

/-- One-safeness: every reachable marking is 0/1-bounded. -/
theorem toggle_onesafe {m : Marking (Fin 2)}
    (h : Reach toggle toggleM0 m) (p : Fin 2) : m p ≤ 1 := by
  rcases toggle_reach_iff.mp h with rfl | rfl
  · fin_cases p <;> decide
  · fin_cases p <;> decide

/-- The record-stratum face at the toggle pin: exactly the two
markings, for every positive dwell assignment. -/
theorem su_toggle_visited {d : Fin 2 → ℚ} (hd : ∀ t, 0 < d t) :
    recordVisited toggle d toggleM0 = {toggleM0, toggleM1} := by
  rw [su_vanilla_face_eq_reach hd]
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact toggle_reach_iff

/-- One-safeness through the record semantics — the safety-transfer
shape, concretely. -/
theorem su_toggle_onesafe {d : Fin 2 → ℚ} (hd : ∀ t, 0 < d t)
    {m : Marking (Fin 2)} (hm : m ∈ recordVisited toggle d toggleM0)
    (p : Fin 2) : m p ≤ 1 := by
  rw [su_vanilla_face_eq_reach hd] at hm
  exact toggle_onesafe hm p

/-- The source net: one place, one transition, no consumption, unit
production. -/
def source : PetriNet (Fin 1) (Fin 1) where
  pre := fun _ _ => 0
  post := fun _ _ => 1

/-- Empty initial marking. -/
def sourceM0 : Marking (Fin 1) := fun _ => 0

/-- Every count is classically reachable. -/
theorem source_reach (c : ℕ) :
    Reach source sourceM0 (fun _ => (c : ℕ)) := by
  induction c with
  | zero => exact Reach.refl
  | succ c ih =>
    have h := Reach.step (N := source) (m0 := sourceM0) 0 ih
      (fun p => Nat.zero_le _)
    rwa [show fire source 0 (fun _ => (c : ℕ)) = (fun _ => (c + 1 : ℕ))
      from funext fun p => by simp [fire, source]] at h

/-- **The unbounded face at the record stratum**: every count is
visited — the dwell floor does not bound reachability. -/
theorem su_source_unbounded {d : Fin 1 → ℚ} (hd : ∀ t, 0 < d t)
    (c : ℕ) : (fun _ => (c : ℕ)) ∈ recordVisited source d sourceM0 := by
  rw [su_vanilla_face_eq_reach hd]
  exact source_reach c

end PetriVanillaControls

end Adequacy

end SuFunctor
