import SuFunctor.Adequacy.MarkovAutomaton
import SuFunctor.Adequacy.MdpDemonic

/-! # Adequacy: Markov automata, demonic face

The scheduler-quantification face of the Markov-automaton square — the
continuous-time sibling of the demonic decision square
(`SuFunctor.Adequacy.MdpDemonic`).  The fixed-scheduler square
(`SuFunctor.Adequacy.MarkovAutomaton`) closes the automaton at a
declared memoryless randomized scheduler and lands a singleton in the
credal stratum; the demonic face quantifies over the schedulers
instead, and its classical semantics is a **set** of laws: the
jump-chain path laws of the scheduler-closed automaton over every
memoryless randomized scheduler (the scheduler-quantified reading of
the Markov-automaton literature, Eisentraut–Hermanns–Zhang, LICS 2010;
demonic choice in the sense of McIver–Morgan).  Per jump horizon `k`,
at the time-abstract stratum, exactly as for the fixed-scheduler face.

**The one genuinely automaton-shaped complication**: each scheduler's
closure consumes a Zeno-freedom certificate.  The face is therefore
stated at the **branch-certified stratum** — a single rank that
strictly decreases on every immediate branch row
(`FinMA.BranchZenoFree`), which by `zenoFree_of_branch` serves *every*
scheduler at once: one certificate, uniform in the adversary.  This is
the literature's own convention (non-Zenoness is a property of the
automaton, not of a scheduler), and two canonicity receipts keep the
certificate honest:

* **rank-irrelevance** (`FinMA.pathLaw_rank_irrel`,
  `FinMA.demonicLaws_rank_irrel`): the closed law — hence the demonic
  set — does not depend on *which* rank certifies; the certificate is
  a witness, the object is the automaton's.  Both certificates are
  spent at a common fuel past both ranks
  (`absorbIter_absFuel_rank_irrel`).
* **the certified-family agreement** (`FinMA.demonicLawsCert_iff`):
  the fully general demonic set — the union over *all* Zeno-certified
  scheduler resolutions, each carrying its own rank
  (`FinMA.CertScheduler`, the honest object for automata where only
  some schedulers admit a rank) — collapses to the
  memoryless-scheduler family under a branch-level certificate.

The compiled presentation stays scheduler-free, honoring the shipped
factoring: the demon's choice is the *existentially quantified
scheduler-row mechanism* — a subprobability mass function is admitted
by the compiled automaton rows exactly when some well-formed
scheduler-row set closes them, at the certificate's working fuel,
onto a chain diagram that it satisfies (`maDemonicC`).  The fuel is
pinned to the certificate: an arbitrary-fuel existential would admit
un-stabilized closures, whose initial rows are sub-stochastic — the
feeding lemma is exactly where the certificate is spent.  The feeding
lemma (`maDemonicC_iff`) identifies the admission with the demonic
law-set, and **the square** (`ma_demonic_adequacy`) packages it as an
invertible globular cell of `Crd (Traj S k)` — the set-valued square
at continuous time.  The proof is four-storey engine reuse
(demonic-automaton → automaton → chain-jump → chain): the stored
scheduler rows assemble a scheduler (`PolicyRows.toPolicy`, reused
verbatim from the demonic decision face), the rate-closure triangle
and the jump triangle collapse the pipeline, and the chain engine
pins the law.  No new induction.

The credal presentation is the union of the members' rays
(`FinMA.demonicCredal`); every closed law has mass one
(`FinMA.pathLaw_mass` — load-bearing here, not a remark), so the
equal-mass slice reconciliation of `SuFunctor.Adequacy.EnvelopeUnion`
applies at `m = 1`: the radially maximal slice of the demonic credal
set is exactly the demonic law-set (`ma_demonic_maxSlice`), and the
kind-selected verdicts reduce to uniform-over-scheduler bounds at both
polarities (`satCredal_lower_maDemonicCredal` through the slice,
`satCredal_upper_maDemonicCredal` through down-closure).  The angelic
(existential-over-schedulers) face is a different operator and is
deliberately not built, exactly as at the decision former.

Degeneracies, mechanized rather than smoothed: one scheduler suffices
for the whole-set reading of a lower-bound atom to refuse every
positive threshold (`not_satCredal_upper_maDemonicCredal_geC` — the
union contains the zero model); the scheduler space has **two**
nonemptiness routes — an automaton with no instantaneous states always
has a scheduler (`Policy.nonempty_of_isEmpty`: the closed-chain
boundary, where the demonic family is a singleton), and with
instantaneous states present the space is empty precisely when the
action set is (`Policy.isEmpty_iff`); with no schedulers both verdict
kinds pass vacuously (`satCredal_maDemonic_of_isEmpty_policy`, the
∀-over-no-adversaries convention).  And one degeneracy the decision
face had no room for: **the certificate forces somewhere to absorb
into** — a branch-certified automaton with an instantaneous state and
an action must have a Markovian state (`FinMA.nonempty_markovian`),
since the minimal-rank instantaneous state's branch row needs a
destination that does not descend.

Deliberately separate strata, named: the **time-law stratum**
(exponential holding times — inherited unchanged);
**history-dependent or time-dependent schedulers** (the adversary
class here is memoryless randomized, deterministic as the
probability-one case, exactly the demonic decision face's class);
**parallel composition and visible actions** (this face quantifies
the closed reading); and **compiled admission for
non-uniformly-Zeno automata** — the classical side of that object is
`FinMA.demonicLawsCert`, built here; a compiled square for it would
carry rank witnesses inside the admission predicate, and is priced,
not built.  The infinite-horizon extension is separate exactly as for
chains.  No new community connector is owed: the fixed-scheduler
face's double-transported connector is the community tie per member;
this face adds set-level structure only. -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Finset

variable {S I A : Type} [Fintype S] [DecidableEq S]
  [Fintype I] [DecidableEq I] [Fintype A]

/-! ## The branch-certified stratum: one rank, every adversary -/

/-- **The branch-level Zeno certificate**: a rank on instantaneous
states that strictly decreases along every immediate branch row —
the hypothesis shape of `zenoFree_of_branch`, named.  One such rank
certifies Zeno-freedom for *every* scheduler's mixed kernel at once:
non-Zenoness as a property of the automaton, which is what a
scheduler-quantified face needs. -/
def FinMA.BranchZenoFree (M : FinMA S I A) (r : I → ℕ) : Prop :=
  ∀ i a j, M.branch i a (Sum.inr j) ≠ 0 → r j < r i

omit [DecidableEq S] [DecidableEq I] in
/-- A branch-level certificate serves every scheduler — dot-notation
face of `zenoFree_of_branch`. -/
theorem FinMA.BranchZenoFree.zenoFree {M : FinMA S I A} {r : I → ℕ}
    (hb : M.BranchZenoFree r) (σ : Policy I A) :
    ZenoFree (M.imStep σ) r :=
  zenoFree_of_branch M r hb σ

/-! ## Rank-irrelevance: the certificate witnesses, the object is the
automaton's -/

/-- The absorbing computation at the working fuel does not depend on
which rank certifies: both certificates are spent at a common fuel
past both ranks, where the computation has stabilized twice over. -/
theorem absorbIter_absFuel_rank_irrel (f : I → S ⊕ I → ℚ)
    {r r' : I → ℕ} (hr : ZenoFree f r) (hr' : ZenoFree f r')
    (x : S ⊕ I) (m : S) :
    absorbIter f (absFuel r) x m = absorbIter f (absFuel r') x m := by
  cases x with
  | inl m' => rw [absorbIter_inl, absorbIter_inl]
  | inr i =>
    have h1 : absorbIter f (absFuel r) (Sum.inr i) m
        = absorbIter f (max (absFuel r) (absFuel r')) (Sum.inr i) m :=
      absorbIter_stab f r hr i m (lt_absFuel r i)
        (lt_of_lt_of_le (lt_absFuel r i) (le_max_left _ _))
    have h2 : absorbIter f (absFuel r') (Sum.inr i) m
        = absorbIter f (max (absFuel r) (absFuel r')) (Sum.inr i) m :=
      absorbIter_stab f r' hr' i m (lt_absFuel r' i)
        (lt_of_lt_of_le (lt_absFuel r' i) (le_max_right _ _))
    rw [h1, h2]

/-- The absorption kernel is rank-irrelevant. -/
theorem FinMA.absorb_rank_irrel (M : FinMA S I A) (σ : Policy I A)
    {r r' : I → ℕ} (hr : ZenoFree (M.imStep σ) r)
    (hr' : ZenoFree (M.imStep σ) r') :
    M.absorb σ r = M.absorb σ r' := by
  funext x m
  exact absorbIter_absFuel_rank_irrel (M.imStep σ) hr hr' x m

/-- **Rank-irrelevance of the closed law**: the fixed-scheduler
semantics does not depend on which rank certifies — the certificate is
a witness, never data.  Proved through the diagonal-blindness receipt
of the chain face: once absorption agrees, the two closures agree on
everything the jump law reads. -/
theorem FinMA.pathLaw_rank_irrel (M : FinMA S I A) (σ : Policy I A)
    {r r' : I → ℕ} (hr : ZenoFree (M.imStep σ) r)
    (hr' : ZenoFree (M.imStep σ) r') (k : ℕ) :
    M.pathLaw σ r hr k = M.pathLaw σ r' hr' k := by
  have habs : M.absorb σ r = M.absorb σ r' :=
    M.absorb_rank_irrel σ hr hr'
  show (M.close σ r hr).jumpLaw k = (M.close σ r' hr').jumpLaw k
  refine FinCTMC.jumpLaw_diag_blind _ _ (fun s s' _ => ?_) ?_ k
  · show (∑ x, M.offRate s x * M.absorb σ r x s')
      = ∑ x, M.offRate s x * M.absorb σ r' x s'
    rw [habs]
  · funext m
    show (∑ x, M.init x * M.absorb σ r x m)
      = ∑ x, M.init x * M.absorb σ r' x m
    rw [habs]

/-! ## The classical object: the demonic law-set -/

/-- **The demonic semantics of a branch-certified Markov automaton**,
per jump horizon: the set of fixed-scheduler jump-chain path laws over
all memoryless randomized schedulers, as a set-valued constraint (the
union of singletons).  The adversary ranges over exactly the scheduler
class of the fixed-scheduler square. -/
def FinMA.demonicLaws (M : FinMA S I A) (r : I → ℕ)
    (hb : M.BranchZenoFree r) (k : ℕ) : SubPMF (Traj S k) → Prop :=
  unionSingletons fun σ : Policy I A =>
    M.pathLaw σ r (hb.zenoFree σ) k

/-- The credal presentation of the demonic face: the union of the
members' rays — the downward-closed credal denotation of the
scheduler-quantified reading. -/
def FinMA.demonicCredal (M : FinMA S I A) (r : I → ℕ)
    (hb : M.BranchZenoFree r) (k : ℕ) : SubPMF (Traj S k) → Prop :=
  unionRays fun σ : Policy I A =>
    M.pathLaw σ r (hb.zenoFree σ) k

/-- The demonic law-set is a property of the automaton and the
horizon; the certificate only witnesses. -/
theorem FinMA.demonicLaws_rank_irrel (M : FinMA S I A) {r r' : I → ℕ}
    (hb : M.BranchZenoFree r) (hb' : M.BranchZenoFree r') (k : ℕ) :
    M.demonicLaws r hb k = M.demonicLaws r' hb' k := by
  have h : (fun σ : Policy I A => M.pathLaw σ r (hb.zenoFree σ) k)
      = fun σ : Policy I A => M.pathLaw σ r' (hb'.zenoFree σ) k := by
    funext σ
    exact M.pathLaw_rank_irrel σ (hb.zenoFree σ) (hb'.zenoFree σ) k
  unfold FinMA.demonicLaws
  rw [h]

/-- The demonic credal set is rank-irrelevant. -/
theorem FinMA.demonicCredal_rank_irrel (M : FinMA S I A) {r r' : I → ℕ}
    (hb : M.BranchZenoFree r) (hb' : M.BranchZenoFree r') (k : ℕ) :
    M.demonicCredal r hb k = M.demonicCredal r' hb' k := by
  have h : (fun σ : Policy I A => M.pathLaw σ r (hb.zenoFree σ) k)
      = fun σ : Policy I A => M.pathLaw σ r' (hb'.zenoFree σ) k := by
    funext σ
    exact M.pathLaw_rank_irrel σ (hb.zenoFree σ) (hb'.zenoFree σ) k
  unfold FinMA.demonicCredal
  rw [h]

/-! ## The compiled side: scheduler-free rows, existential mechanism -/

/-- **The demonic reading of the compiled automaton rows**: the rows
carry no scheduler (the shipped factoring), and the demon's choice is
the existentially quantified scheduler-row mechanism — `μ` is admitted
exactly when some well-formed scheduler-row set closes the automaton
rows, at absorption fuel `n`, onto a chain diagram (through the jump
closure) that `μ` satisfies.  The square instantiates `n` at the
certificate's working fuel; the definition is fuel-generic by
design. -/
def maDemonicC (R : MaRows S I A) (n k : ℕ) :
    SubPMF (Traj S k) → Prop :=
  fun μ => ∃ σr : PolicyRows I A, σr.WF ∧
    looseConj (atoms (jumpRows (closeMaRows R σr n)) k) μ

/-- The ray-closure of the compiled demonic reading: the credal
(downward-closed) object it denotes. -/
def maDemonicCredalC (R : MaRows S I A) (n k : ℕ) :
    SubPMF (Traj S k) → Prop :=
  fun ν => ∃ μ, maDemonicC R n k μ ∧ rayC μ ν

/-! ## The feeding lemma and the square -/

/-- **The pointwise demonic equivalence**: a subprobability mass
function is admitted by the compiled automaton rows under some
scheduler-row mechanism, at the certificate's working fuel, exactly
when it is a member of the demonic law-set.  Each direction is the
fixed-scheduler engine at the appropriate scheduler: the stored rows
assemble a scheduler whose closure the rate-closure and jump triangles
collapse to a compiled chain the chain engine pins; conversely every
scheduler compiles to a witnessing row set.  Four-storey engine reuse,
no new induction — and the one place the branch certificate is spent
on the compiled side: it supplies Zeno-freedom for whichever scheduler
the demon stored. -/
theorem maDemonicC_iff (M : FinMA S I A) {r : I → ℕ}
    (hb : M.BranchZenoFree r) (k : ℕ) (μ : SubPMF (Traj S k)) :
    maDemonicC (compileMa M) (absFuel r) k μ ↔
      M.demonicLaws r hb k μ := by
  classical
  constructor
  · rintro ⟨σr, hσ, hsat⟩
    refine ⟨σr.toPolicy hσ, ?_⟩
    have hrows : closeMaRows (compileMa M) σr (absFuel r)
        = compileCtmc (M.close (σr.toPolicy hσ) r
            (hb.zenoFree (σr.toPolicy hσ))) := by
      rw [← compile_closeMa_comm M (σr.toPolicy hσ) r
        (hb.zenoFree (σr.toPolicy hσ)), compilePolicy_toPolicy]
    rw [hrows, compile_jump_comm] at hsat
    have hlaw := (satAtoms_iff
      (compile_wf (M.close (σr.toPolicy hσ) r
        (hb.zenoFree (σr.toPolicy hσ))).jumpChain) μ).mp hsat
    rw [compile_rowsLaw] at hlaw
    exact (singletonC_iff _ _).mpr hlaw
  · rintro ⟨σ, hσ⟩
    refine ⟨compilePolicy σ, compilePolicy_wf σ, ?_⟩
    rw [compile_closeMa_comm M σ r (hb.zenoFree σ), compile_jump_comm,
      satAtoms_iff (compile_wf (M.close σ r (hb.zenoFree σ)).jumpChain) μ,
      compile_rowsLaw]
    exact (singletonC_iff _ _).mp hσ

/-- **Adequacy of the Markov-automaton compilation, demonic face** —
the set-valued square at continuous time.

In the double category `Crd (Traj S k)`: the demonic reading of the
compiled, scheduler-free automaton rows — admitted by *some*
well-formed scheduler-row mechanism at the certificate's working fuel,
each choice denoting through the shipped closure pipeline — is
isomorphic, by an invertible globular cell, to the **set-valued**
inclusion of the demonic law-set.  Compile-then-denote agrees with
interpret-then-include, where interpretation now yields a set of
closed laws. -/
theorem ma_demonic_adequacy (M : FinMA S I A) {r : I → ℕ}
    (hb : M.BranchZenoFree r) (k : ℕ) {a : Crd (Traj S k)} :
    ∃ α : Cell (maDemonicC (compileMa M) (absFuel r) k : Loose a a)
        (M.demonicLaws r hb k) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  Crd.looseIso_ofIff (maDemonicC_iff M hb k)

/-- The feeding lemma at the credal stratum: the ray-closure of the
compiled demonic reading is the demonic credal set. -/
theorem maDemonicCredalC_iff (M : FinMA S I A) {r : I → ℕ}
    (hb : M.BranchZenoFree r) (k : ℕ) (ν : SubPMF (Traj S k)) :
    maDemonicCredalC (compileMa M) (absFuel r) k ν ↔
      M.demonicCredal r hb k ν := by
  constructor
  · rintro ⟨μ, hμ, hray⟩
    obtain ⟨σ, hσ⟩ := (maDemonicC_iff M hb k μ).mp hμ
    exact ⟨σ, (singletonC_iff _ _).mp hσ ▸ hray⟩
  · rintro ⟨σ, hray⟩
    exact ⟨M.pathLaw σ r (hb.zenoFree σ) k,
      (maDemonicC_iff M hb k _).mpr ⟨σ, singletonC_self _⟩, hray⟩

/-! ## The slice: the credal presentation reconciled with the law-set -/

/-- **The demonic slice**: the radially maximal slice of the demonic
credal set is exactly the demonic law-set — the equal-mass
reconciliation at `m = 1`, every closed law having full mass
(`FinMA.pathLaw_mass`, load-bearing here). -/
theorem ma_demonic_maxSlice (M : FinMA S I A) {r : I → ℕ}
    (hb : M.BranchZenoFree r) (k : ℕ) (ν : SubPMF (Traj S k)) :
    maxSlice (M.demonicCredal r hb k) ν ↔ M.demonicLaws r hb k ν :=
  maxSlice_unionRays
    (fun σ => M.pathLaw_mass σ r (hb.zenoFree σ) k) one_ne_zero ν

/-- The demonic reconciliation, packaged: the slice of the credal
presentation and the exact law-set are isomorphic as loose arrows of
`Crd (Traj S k)`. -/
theorem ma_demonic_ray_singleton_reconciliation (M : FinMA S I A)
    {r : I → ℕ} (hb : M.BranchZenoFree r) (k : ℕ)
    {a : Crd (Traj S k)} :
    ∃ α : Cell (maxSlice (M.demonicCredal r hb k) : Loose a a)
        (M.demonicLaws r hb k) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  Crd.looseIso_ofIff (ma_demonic_maxSlice M hb k)

/-! ## The verdicts: uniform-over-scheduler bounds at both polarities -/

/-- **The demonic lower verdict is the uniform-over-schedulers
bound**: a lower-kind constraint holds of the demonic credal set
exactly when it holds of every scheduler's closed law — recovered
through the slice. -/
theorem satCredal_lower_maDemonicCredal (M : FinMA S I A) {r : I → ℕ}
    (hb : M.BranchZenoFree r) (k : ℕ) (c : SubPMF (Traj S k) → Prop) :
    SatCredal .lower (M.demonicCredal r hb k) c ↔
      ∀ σ : Policy I A, c (M.pathLaw σ r (hb.zenoFree σ) k) :=
  satCredal_lower_unionRays
    (fun σ => M.pathLaw_mass σ r (hb.zenoFree σ) k) one_ne_zero c

/-- **The demonic upper verdict is the uniform-over-schedulers
bound**, for down-closed constraints — mass-free, through
down-closure. -/
theorem satCredal_upper_maDemonicCredal (M : FinMA S I A) {r : I → ℕ}
    (hb : M.BranchZenoFree r) (k : ℕ) {c : SubPMF (Traj S k) → Prop}
    (hc : DownClosed c) :
    SatCredal .upper (M.demonicCredal r hb k) c ↔
      ∀ σ : Policy I A, c (M.pathLaw σ r (hb.zenoFree σ) k) :=
  satCredal_upper_unionRays hc

theorem satCredal_lower_maDemonicLaws (M : FinMA S I A) {r : I → ℕ}
    (hb : M.BranchZenoFree r) (k : ℕ) (c : SubPMF (Traj S k) → Prop) :
    SatCredal .lower (M.demonicLaws r hb k) c ↔
      ∀ σ : Policy I A, c (M.pathLaw σ r (hb.zenoFree σ) k) :=
  satCredal_lower_unionSingletons
    (fun σ => M.pathLaw_mass σ r (hb.zenoFree σ) k) one_ne_zero c

theorem satCredal_upper_maDemonicLaws (M : FinMA S I A) {r : I → ℕ}
    (hb : M.BranchZenoFree r) (k : ℕ) (c : SubPMF (Traj S k) → Prop) :
    SatCredal .upper (M.demonicLaws r hb k) c ↔
      ∀ σ : Policy I A, c (M.pathLaw σ r (hb.zenoFree σ) k) :=
  satCredal_upper_unionSingletons c

/-- **Verdict agreement, lower kind**: the credal and exact
presentations of the demonic face agree on every lower-kind
constraint. -/
theorem satCredal_lower_maDemonic_ray_singleton (M : FinMA S I A)
    {r : I → ℕ} (hb : M.BranchZenoFree r) (k : ℕ)
    (c : SubPMF (Traj S k) → Prop) :
    SatCredal .lower (M.demonicCredal r hb k) c ↔
      SatCredal .lower (M.demonicLaws r hb k) c := by
  rw [satCredal_lower_maDemonicCredal M hb k,
    satCredal_lower_maDemonicLaws M hb k]

/-- **Verdict agreement, upper kind**: for down-closed constraints. -/
theorem satCredal_upper_maDemonic_ray_singleton (M : FinMA S I A)
    {r : I → ℕ} (hb : M.BranchZenoFree r) (k : ℕ)
    {c : SubPMF (Traj S k) → Prop} (hc : DownClosed c) :
    SatCredal .upper (M.demonicCredal r hb k) c ↔
      SatCredal .upper (M.demonicLaws r hb k) c := by
  rw [satCredal_upper_maDemonicCredal M hb k hc,
    satCredal_upper_maDemonicLaws M hb k]

/-! ## Degeneracies, mechanized -/

omit [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I] in
/-- A state space with no states always admits (exactly one)
scheduler, vacuously — the closed-chain boundary of the automaton
frame: with no instantaneous states there is nothing to schedule, and
the demonic family is a singleton. -/
theorem Policy.nonempty_of_isEmpty {X : Type} [IsEmpty X] :
    Nonempty (Policy X A) :=
  ⟨{ choice := fun x => isEmptyElim x
     nonneg := fun x => isEmptyElim x
     row_sum := fun x => isEmptyElim x }⟩

omit [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I] in
/-- **The no-scheduler boundary, located exactly**: with an inhabited
state space, the scheduler space is empty precisely when the action
set is.  (The decision face's `isEmpty_policy_iff` derives the
inhabitation from the process's initial rows; an automaton's
instantaneous sort is genuinely free, so here it is a hypothesis.) -/
theorem Policy.isEmpty_iff {X : Type} [Nonempty X] [DecidableEq A] :
    IsEmpty (Policy X A) ↔ IsEmpty A := by
  constructor
  · intro h
    by_contra hA
    rw [not_isEmpty_iff] at hA
    exact h.false (Policy.det fun _ => Classical.arbitrary A)
  · intro hA
    refine ⟨fun π => ?_⟩
    have h1 := π.row_sum (Classical.arbitrary X)
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact one_ne_zero h1.symm

/-- **Why the slice discipline survives the passage to sets, at
continuous time**: as soon as one scheduler exists, the demonic credal
set contains the zero model, so the whole-set reading of a lower-bound
atom refuses every positive threshold.  Stated at the weakest natural
hypothesis — the scheduler space itself — since the automaton frame
has two nonemptiness routes to it (`Policy.nonempty` from an action;
`Policy.nonempty_of_isEmpty` from an empty instantaneous sort). -/
theorem not_satCredal_upper_maDemonicCredal_geC (M : FinMA S I A)
    {r : I → ℕ} (hb : M.BranchZenoFree r) (k : ℕ)
    [hp : Nonempty (Policy I A)] {E : Set (Traj S k)} {q : ℚ}
    (hq : 0 < q) :
    ¬ SatCredal .upper (M.demonicCredal r hb k) (geC E q) := by
  intro h
  obtain ⟨σ⟩ := hp
  have h0 : q ≤ (SubPMF.zero (Traj S k)).prob E :=
    h (SubPMF.zero _) ⟨σ, rayC_zero _⟩
  rw [SubPMF.zero_prob] at h0
  linarith

/-- **The empty demonic set validates everything**: with no
schedulers, both verdict kinds pass vacuously — the
∀-over-no-adversaries convention, recorded rather than smoothed,
exactly as at the decision former's demonic corner. -/
theorem satCredal_maDemonic_of_isEmpty_policy (M : FinMA S I A)
    {r : I → ℕ} (hb : M.BranchZenoFree r) (k : ℕ)
    [h : IsEmpty (Policy I A)] (kind : EnvelopeKind)
    (c : SubPMF (Traj S k) → Prop) :
    SatCredal kind (M.demonicCredal r hb k) c := by
  cases kind with
  | lower =>
    rintro ν ⟨⟨σ, -⟩, -⟩
    exact (h.false σ).elim
  | upper =>
    rintro ν ⟨σ, -⟩
    exact (h.false σ).elim

omit [DecidableEq S] [DecidableEq I] in
/-- **The certificate forces somewhere to absorb into**: a
branch-certified automaton with an instantaneous state and an action
must have a Markovian state.  The minimal-rank instantaneous state's
branch row is a distribution, so it is supported somewhere — and every
instantaneous destination would have to descend below the minimum.
The decision face had no analogue: nothing there forced a floor. -/
theorem FinMA.nonempty_markovian (M : FinMA S I A) [Nonempty I]
    [Nonempty A] {r : I → ℕ} (hb : M.BranchZenoFree r) : Nonempty S := by
  obtain ⟨i₀, -, hmin⟩ :=
    Finset.exists_min_image univ r Finset.univ_nonempty
  by_contra hS
  rw [not_nonempty_iff] at hS
  have hsum : ∑ x, M.branch i₀ (Classical.arbitrary A) x ≠ 0 := by
    rw [M.branch_row_sum i₀ (Classical.arbitrary A)]
    exact one_ne_zero
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  cases x with
  | inl s => exact hS.false s
  | inr j =>
    exact absurd (hb i₀ (Classical.arbitrary A) j hx)
      (not_lt.mpr (hmin j (mem_univ j)))

/-! ## The certified-family stratum: the general demonic set

For an automaton that is not branch-certified, some schedulers may
admit a rank while others do not; the honest demonic object then
ranges over the *Zeno-certified scheduler resolutions*.  Its classical
side is built here — the union machinery is index-generic, and this is
its first genuinely dependent index — and under a branch-level
certificate it collapses to the memoryless family above
(rank-irrelevance is exactly what the collapse spends).  A compiled
square for the partial-Zeno stratum would carry rank witnesses inside
the admission predicate; that is a separate, priced grain. -/

/-- A Zeno-certified scheduler resolution: a scheduler together with a
rank witness for its mixed immediate kernel. -/
structure FinMA.CertScheduler (M : FinMA S I A) where
  /-- The memoryless randomized scheduler. -/
  scheduler : Policy I A
  /-- The rank certifying Zeno-freedom of the mixed kernel. -/
  rank : I → ℕ
  /-- The certificate. -/
  zenoFree : ZenoFree (M.imStep scheduler) rank

/-- The demonic law-set over all Zeno-certified scheduler resolutions
— defined with no automaton-level hypothesis: the honest object for
automata where only some schedulers admit a rank. -/
def FinMA.demonicLawsCert (M : FinMA S I A) (k : ℕ) :
    SubPMF (Traj S k) → Prop :=
  unionSingletons fun w : M.CertScheduler =>
    M.pathLaw w.scheduler w.rank w.zenoFree k

/-- The credal presentation of the certified-family demonic set. -/
def FinMA.demonicCredalCert (M : FinMA S I A) (k : ℕ) :
    SubPMF (Traj S k) → Prop :=
  unionRays fun w : M.CertScheduler =>
    M.pathLaw w.scheduler w.rank w.zenoFree k

/-- **The certified-family agreement**: under a branch-level
certificate, the general demonic set is the memoryless-scheduler
family.  One direction is the injection of a scheduler with the
uniform certificate; the other is rank-irrelevance — a resolution's
own rank and the uniform rank close to the same law. -/
theorem FinMA.demonicLawsCert_iff (M : FinMA S I A) {r : I → ℕ}
    (hb : M.BranchZenoFree r) (k : ℕ) (ν : SubPMF (Traj S k)) :
    M.demonicLawsCert k ν ↔ M.demonicLaws r hb k ν := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w.scheduler, ?_⟩
    have hw' : singletonC (M.pathLaw w.scheduler w.rank w.zenoFree k) ν :=
      hw
    show singletonC (M.pathLaw w.scheduler r (hb.zenoFree w.scheduler) k) ν
    rwa [M.pathLaw_rank_irrel w.scheduler w.zenoFree
      (hb.zenoFree w.scheduler) k] at hw'
  · rintro ⟨σ, hσ⟩
    exact ⟨⟨σ, r, hb.zenoFree σ⟩, hσ⟩

/-- The certified-family agreement, credal presentation. -/
theorem FinMA.demonicCredalCert_iff (M : FinMA S I A) {r : I → ℕ}
    (hb : M.BranchZenoFree r) (k : ℕ) (ν : SubPMF (Traj S k)) :
    M.demonicCredalCert k ν ↔ M.demonicCredal r hb k ν := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w.scheduler, ?_⟩
    have hw' : rayC (M.pathLaw w.scheduler w.rank w.zenoFree k) ν := hw
    show rayC (M.pathLaw w.scheduler r (hb.zenoFree w.scheduler) k) ν
    rwa [M.pathLaw_rank_irrel w.scheduler w.zenoFree
      (hb.zenoFree w.scheduler) k] at hw'
  · rintro ⟨σ, hσ⟩
    exact ⟨⟨σ, r, hb.zenoFree σ⟩, hσ⟩

/-- The lower verdict on the certified-family credal set is the
uniform bound over all certified resolutions — the union machinery at
its first dependent index, no automaton-level hypothesis. -/
theorem satCredal_lower_maDemonicCredalCert (M : FinMA S I A) (k : ℕ)
    (c : SubPMF (Traj S k) → Prop) :
    SatCredal .lower (M.demonicCredalCert k) c ↔
      ∀ w : M.CertScheduler,
        c (M.pathLaw w.scheduler w.rank w.zenoFree k) := by
  unfold FinMA.demonicCredalCert
  exact satCredal_lower_unionRays
    (μs := fun w : M.CertScheduler =>
      M.pathLaw w.scheduler w.rank w.zenoFree k) (m := 1)
    (fun w => M.pathLaw_mass w.scheduler w.rank w.zenoFree k)
    one_ne_zero c

/-- The upper verdict on the certified-family credal set, for
down-closed constraints. -/
theorem satCredal_upper_maDemonicCredalCert (M : FinMA S I A) (k : ℕ)
    {c : SubPMF (Traj S k) → Prop} (hc : DownClosed c) :
    SatCredal .upper (M.demonicCredalCert k) c ↔
      ∀ w : M.CertScheduler,
        c (M.pathLaw w.scheduler w.rank w.zenoFree k) := by
  unfold FinMA.demonicCredalCert
  exact satCredal_upper_unionRays
    (μs := fun w : M.CertScheduler =>
      M.pathLaw w.scheduler w.rank w.zenoFree k) hc

end Adequacy
end SuFunctor
