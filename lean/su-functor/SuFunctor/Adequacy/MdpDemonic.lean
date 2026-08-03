import SuFunctor.Adequacy.Mdp
import SuFunctor.Adequacy.EnvelopeUnion

/-! # Adequacy: Markov decision processes, demonic face

The first *genuinely imprecise* adequacy square.  The fixed-policy
square (`SuFunctor.Adequacy.Mdp`) closes the loop at a declared policy
and lands a singleton in the credal stratum; the demonic — open-policy —
face quantifies over the policies instead, and its classical semantics
is a **set** of laws: the trajectory laws of the closed loop under every
memoryless randomized policy (Puterman's stationary randomized class;
the adversary-quantified reading of the probabilistic model-checking
literature, Baier–Katoen §10.6; demonic choice in the sense of
McIver–Morgan).  Per-horizon `k`, as always; time-dependent policies
remain the named separate grain of the fixed-policy module, and the
infinite-horizon stratum is separate exactly as for chains.

The compiled presentation stays policy-free, honoring the shipped
factoring: the decision former's rows carry no policy family, and the
demon's choice is the *existentially quantified scheduler mechanism* —
a subprobability mass function is admitted by the compiled decision
former exactly when some well-formed policy-row set closes the loop
onto it (`demonicC`).  The feeding lemma (`demonicC_iff`) identifies
this with the demonic law-set, and **the square**
(`mdp_demonic_adequacy`) packages it as an invertible globular cell of
`Crd (Traj S k)` between the compiled reading and the *set-valued*
inclusion `unionSingletons` — the first square whose bottom edge is not
a singleton.

The credal presentation of the same face is the union of the members'
rays (`FinMDP.demonicCredal`), the downward-closed object the
semantic-universe chapter's axioms require.  Because every closed-loop
law has mass one (`FinMDP.pathLaw_mass` — the mass theorem turns from
remark to load-bearing here), the equal-mass slice reconciliation of
`SuFunctor.Adequacy.EnvelopeUnion` applies at `m = 1`: the radially
maximal slice of the demonic credal set is exactly the demonic law-set
(`demonic_maxSlice`), and the kind-selected verdicts reduce to the
literature's uniform-over-policies bounds at *both* polarities —
`satCredal_lower_demonicCredal` through the slice,
`satCredal_upper_demonicCredal` through down-closure of the constraint.
The angelic (existential-over-policies) face is a *different* operator
— not `SatCredal`-shaped, which is universally quantified on both kinds
— and is deliberately not built here.

Degeneracies, mechanized rather than smoothed: reading a lower-bound
atom with the whole-set reader refuses every positive threshold as soon
as one policy exists (`not_satCredal_upper_demonicCredal_geC` — the
union contains the zero model), locating the polarity split at the set
stratum; and an MDP over an *empty action set* is well-formed but
admits no policy at all (`isEmpty_policy_iff`, given that `FinMDP`
forces an inhabited state space), so its demonic set is empty and both
verdict kinds pass vacuously (`satCredal_demonic_of_isEmpty_policy`) —
the ∀-over-no-adversaries convention.  The empty demonic set sits below
even the chapter's bottom credal object (which an inhabited policy
family supplies through the rays' zero element); the literature's
enabled-actions convention corresponds to `Nonempty A`. -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Finset

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-! ## The classical object: the demonic law-set -/

/-- **The demonic semantics of an MDP**, per horizon: the set of
closed-loop trajectory laws over all memoryless randomized policies,
as a set-valued constraint (the union of singletons).  This is the
uncertain-policy object of the literature — the adversary ranges over
Puterman's stationary randomized class, exactly the policies of the
fixed-policy square. -/
def FinMDP.demonicLaws (M : FinMDP S A) (k : ℕ) :
    SubPMF (Traj S k) → Prop :=
  unionSingletons (fun π : Policy S A => M.pathLaw π k)

/-- The credal presentation of the demonic face: the union of the
members' rays — the downward-closed credal denotation the
semantic-universe chapter assigns to the open-policy reading. -/
def FinMDP.demonicCredal (M : FinMDP S A) (k : ℕ) :
    SubPMF (Traj S k) → Prop :=
  unionRays (fun π : Policy S A => M.pathLaw π k)

/-! ## The compiled side: policy-free rows, existential scheduler -/

/-- **The demonic reading of the compiled decision former**: the rows
carry no policy family (the shipped grain), and the demon's choice is
the existentially quantified scheduler mechanism — `μ` is admitted
exactly when some well-formed policy-row set closes the loop onto a
chain diagram that `μ` satisfies. -/
def demonicC (R : MdpRows S A) (k : ℕ) : SubPMF (Traj S k) → Prop :=
  fun μ => ∃ σ : PolicyRows S A, σ.WF ∧
    looseConj (atoms (closeRows R σ) k) μ

/-- The ray-closure of the compiled demonic reading: the credal
(downward-closed) object it denotes. -/
def demonicCredalC (R : MdpRows S A) (k : ℕ) :
    SubPMF (Traj S k) → Prop :=
  fun ν => ∃ μ, demonicC R k μ ∧ rayC μ ν

/-! ## Scheduler rows assemble the classical policy -/

/-- Well-formed policy rows assemble the classical policy object. -/
def PolicyRows.toPolicy (σ : PolicyRows S A) (hσ : σ.WF) :
    Policy S A where
  choice s a := σ.rows (s, a)
  nonneg s a := hσ.nonneg (s, a)
  row_sum s := hσ.row_sum s

omit [DecidableEq S] [DecidableEq A] in
/-- The assembly is a section of compilation: compiling the assembled
policy returns the stored rows. -/
theorem compilePolicy_toPolicy (σ : PolicyRows S A) (hσ : σ.WF) :
    compilePolicy (σ.toPolicy hσ) = σ := by
  obtain ⟨rows⟩ := σ
  exact congrArg PolicyRows.mk (Finsupp.ext fun p => rfl)

/-! ## The feeding lemma and the square -/

/-- **The pointwise demonic equivalence**: a subprobability mass
function is admitted by the compiled decision former under some
scheduler exactly when it is a member of the demonic law-set.  Each
direction is the fixed-policy engine at the appropriate policy: the
stored scheduler rows assemble a policy whose closed loop the chain
engine pins, and conversely every policy compiles to a witnessing
scheduler. -/
theorem demonicC_iff (M : FinMDP S A) (k : ℕ) (μ : SubPMF (Traj S k)) :
    demonicC (compileMdp M) k μ ↔ M.demonicLaws k μ := by
  constructor
  · rintro ⟨σ, hσ, hsat⟩
    refine ⟨σ.toPolicy hσ, ?_⟩
    have hrows : closeRows (compileMdp M) σ =
        compile (M.closedLoop (σ.toPolicy hσ)) := by
      rw [← compile_close_comm, compilePolicy_toPolicy]
    rw [hrows] at hsat
    have hlaw :=
      (satAtoms_iff (compile_wf (M.closedLoop (σ.toPolicy hσ))) μ).mp hsat
    rw [compile_rowsLaw] at hlaw
    exact (singletonC_iff _ _).mpr hlaw
  · rintro ⟨π, hπ⟩
    refine ⟨compilePolicy π, compilePolicy_wf π, ?_⟩
    rw [compile_close_comm,
      satAtoms_iff (compile_wf (M.closedLoop π)) μ, compile_rowsLaw]
    exact (singletonC_iff _ _).mp hπ

/-- **Adequacy of the MDP compilation, demonic face** — the first
genuinely imprecise adequacy square.

In the double category `Crd (Traj S k)`: the demonic reading of the
compiled, policy-free decision former — admitted by *some* well-formed
scheduler mechanism, each choice denoting through the shipped chain
diagram — is isomorphic, by an invertible globular cell, to the
**set-valued** inclusion of the demonic law-set.  Compile-then-denote
agrees with interpret-then-include, where interpretation now yields a
set of laws and inclusion is the union of their singletons. -/
theorem mdp_demonic_adequacy (M : FinMDP S A) (k : ℕ)
    {a : Crd (Traj S k)} :
    ∃ α : Cell (demonicC (compileMdp M) k : Loose a a)
        (M.demonicLaws k) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  Crd.looseIso_ofIff (demonicC_iff M k)

/-- The feeding lemma at the credal stratum: the ray-closure of the
compiled demonic reading is the demonic credal set. -/
theorem demonicCredalC_iff (M : FinMDP S A) (k : ℕ)
    (ν : SubPMF (Traj S k)) :
    demonicCredalC (compileMdp M) k ν ↔ M.demonicCredal k ν := by
  constructor
  · rintro ⟨μ, hμ, hray⟩
    obtain ⟨π, hπ⟩ := (demonicC_iff M k μ).mp hμ
    exact ⟨π, (singletonC_iff _ _).mp hπ ▸ hray⟩
  · rintro ⟨π, hray⟩
    exact ⟨M.pathLaw π k,
      (demonicC_iff M k _).mpr ⟨π, singletonC_self _⟩, hray⟩

/-! ## The slice: the credal presentation reconciled with the law-set -/

/-- **The demonic slice**: the radially maximal slice of the demonic
credal set is exactly the demonic law-set — the equal-mass
reconciliation at `m = 1`, every closed-loop law having full mass
(`FinMDP.pathLaw_mass`; the mass theorem is load-bearing here, not a
remark). -/
theorem demonic_maxSlice (M : FinMDP S A) (k : ℕ)
    (ν : SubPMF (Traj S k)) :
    maxSlice (M.demonicCredal k) ν ↔ M.demonicLaws k ν :=
  maxSlice_unionRays (fun π => M.pathLaw_mass π k) one_ne_zero ν

/-- The demonic reconciliation, packaged: the slice of the credal
presentation and the exact law-set are isomorphic as loose arrows of
`Crd (Traj S k)`. -/
theorem demonic_ray_singleton_reconciliation (M : FinMDP S A) (k : ℕ)
    {a : Crd (Traj S k)} :
    ∃ α : Cell (maxSlice (M.demonicCredal k) : Loose a a)
        (M.demonicLaws k) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  Crd.looseIso_ofIff (demonic_maxSlice M k)

/-! ## The verdicts: uniform-over-policies bounds at both polarities -/

/-- **The demonic lower verdict is the uniform-over-policies bound**:
a lower-kind constraint holds of the demonic credal set exactly when it
holds of every policy's closed-loop law — the ∀-adversary reading of
the literature, recovered through the slice. -/
theorem satCredal_lower_demonicCredal (M : FinMDP S A) (k : ℕ)
    (c : SubPMF (Traj S k) → Prop) :
    SatCredal .lower (M.demonicCredal k) c ↔
      ∀ π : Policy S A, c (M.pathLaw π k) :=
  satCredal_lower_unionRays (fun π => M.pathLaw_mass π k) one_ne_zero c

omit [DecidableEq A] in
/-- **The demonic upper verdict is the uniform-over-policies bound**,
for down-closed constraints — mass-free, through down-closure. -/
theorem satCredal_upper_demonicCredal (M : FinMDP S A) (k : ℕ)
    {c : SubPMF (Traj S k) → Prop} (hc : DownClosed c) :
    SatCredal .upper (M.demonicCredal k) c ↔
      ∀ π : Policy S A, c (M.pathLaw π k) :=
  satCredal_upper_unionRays hc

theorem satCredal_lower_demonicLaws (M : FinMDP S A) (k : ℕ)
    (c : SubPMF (Traj S k) → Prop) :
    SatCredal .lower (M.demonicLaws k) c ↔
      ∀ π : Policy S A, c (M.pathLaw π k) :=
  satCredal_lower_unionSingletons (fun π => M.pathLaw_mass π k)
    one_ne_zero c

omit [DecidableEq A] in
theorem satCredal_upper_demonicLaws (M : FinMDP S A) (k : ℕ)
    (c : SubPMF (Traj S k) → Prop) :
    SatCredal .upper (M.demonicLaws k) c ↔
      ∀ π : Policy S A, c (M.pathLaw π k) :=
  satCredal_upper_unionSingletons c

/-- **Verdict agreement, lower kind**: the credal and exact
presentations of the demonic face agree on every lower-kind
constraint. -/
theorem satCredal_lower_demonic_ray_singleton (M : FinMDP S A) (k : ℕ)
    (c : SubPMF (Traj S k) → Prop) :
    SatCredal .lower (M.demonicCredal k) c ↔
      SatCredal .lower (M.demonicLaws k) c := by
  rw [satCredal_lower_demonicCredal, satCredal_lower_demonicLaws]

omit [DecidableEq A] in
/-- **Verdict agreement, upper kind**: for down-closed constraints. -/
theorem satCredal_upper_demonic_ray_singleton (M : FinMDP S A) (k : ℕ)
    {c : SubPMF (Traj S k) → Prop} (hc : DownClosed c) :
    SatCredal .upper (M.demonicCredal k) c ↔
      SatCredal .upper (M.demonicLaws k) c := by
  rw [satCredal_upper_demonicCredal M k hc,
    satCredal_upper_demonicLaws]

/-! ## Degeneracies, mechanized -/

omit [Fintype S] [DecidableEq S] in
/-- An inhabited action set yields a policy — the deterministic
constant policy; the literature's enabled-actions convention
corresponds to `Nonempty A`. -/
theorem Policy.nonempty [Nonempty A] : Nonempty (Policy S A) :=
  ⟨Policy.det fun _ => Classical.arbitrary A⟩

/-- **Why the slice discipline survives the passage to sets**: as soon
as one policy exists, the demonic credal set contains the zero model,
so the whole-set reading of a lower-bound atom refuses every positive
threshold — the set-stratum face of the single-ray degeneracy. -/
theorem not_satCredal_upper_demonicCredal_geC (M : FinMDP S A) (k : ℕ)
    [Nonempty A] {E : Set (Traj S k)} {q : ℚ} (hq : 0 < q) :
    ¬ SatCredal .upper (M.demonicCredal k) (geC E q) := by
  intro h
  obtain ⟨π⟩ : Nonempty (Policy S A) := Policy.nonempty
  have h0 : q ≤ (SubPMF.zero (Traj S k)).prob E :=
    h (SubPMF.zero _) ⟨π, rayC_zero _⟩
  rw [SubPMF.zero_prob] at h0
  linarith

omit [DecidableEq S] [DecidableEq A] in
/-- A decision process forces an inhabited state space: the initial
rows sum to one. -/
theorem FinMDP.nonempty_state (M : FinMDP S A) : Nonempty S := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h1 := M.init_sum
  rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
  exact one_ne_zero h1.symm

omit [DecidableEq S] in
/-- **The no-policy boundary, located exactly**: given a decision
process (hence an inhabited state space), the policy space is empty
precisely when the action set is — an action-free MDP is well-formed
but admits no scheduler. -/
theorem isEmpty_policy_iff (M : FinMDP S A) :
    IsEmpty (Policy S A) ↔ IsEmpty A := by
  constructor
  · intro h
    by_contra hA
    rw [not_isEmpty_iff] at hA
    exact h.false (Policy.det fun _ => Classical.arbitrary A)
  · intro hA
    refine ⟨fun π => ?_⟩
    obtain ⟨s⟩ := M.nonempty_state
    have h1 := π.row_sum s
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact one_ne_zero h1.symm

omit [DecidableEq A] in
/-- **The empty demonic set validates everything**: with no policies,
both verdict kinds pass vacuously — the ∀-over-no-adversaries
convention, recorded rather than smoothed.  (The empty set sits below
even the chapter's bottom credal object `{0}`: an inhabited policy
family supplies `⊥` through its rays; no policy family supplies
nothing.) -/
theorem satCredal_demonic_of_isEmpty_policy (M : FinMDP S A) (k : ℕ)
    [h : IsEmpty (Policy S A)] (kind : EnvelopeKind)
    (c : SubPMF (Traj S k) → Prop) :
    SatCredal kind (M.demonicCredal k) c := by
  cases kind with
  | lower =>
    rintro ν ⟨⟨π, -⟩, -⟩
    exact (h.false π).elim
  | upper =>
    rintro ν ⟨π, -⟩
    exact (h.false π).elim

end Adequacy
end SuFunctor
