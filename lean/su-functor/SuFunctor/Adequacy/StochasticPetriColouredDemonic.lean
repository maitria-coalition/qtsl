import SuFunctor.Adequacy.StochasticPetriColouredCascade
import SuFunctor.Adequacy.StochasticPetriAngelic

/-! # Adequacy: coloured stochastic Petri frames, demonic and angelic faces

The scheduler-quantification faces of the **coloured**
immediate/cascade species — the coloured companions of
`SuFunctor.Adequacy.StochasticPetriDemonic` and the net-tier of
`SuFunctor.Adequacy.StochasticPetriAngelic`, over the formation and
compile of `SuFunctor.Adequacy.StochasticPetriColouredCascade`.  The
fixed-scheduler coloured square closes a net at a *declared*
memoryless randomized scheduler over (transition, colour-vector)
pairs and lands a singleton credal constraint; this module quantifies
the demon over the enabling-respecting arena and lands the set-valued
face, its angelic dual, and the membership machinery from which both
directed transfer faces flow.

**The demon selects tokens, not just transitions.**  At the coloured
grain the adversary's alternatives are *pairs*: which immediate
transition fires and which coloured tokens it consumes.  The arena is
therefore strictly richer than any transitions-only reading — the
plurality control below exhibits two arena members that differ only
in how they resolve a *colour* conflict (the same sole transition,
two enabled selections), which no uncoloured net can express.

**The obstruction, manufactured by colour selection.**  As at the
uncoloured face, the donor Markov-automaton square's branch-level
hypothesis `FinMA.BranchZenoFree` is refutable rather than merely
unproven: a *disabled* pair's branch row is the honest zero-time
no-op, a point mass at the source, so the certificate would demand
`r i < r i`.  What is new at colour is how cheaply disabled pairs
arise: a single immediate transition already has one branch row per
colour vector, so supply gaps (a blue selection at a red-only
marking) and guard cylinders (a blue selection the guard refuses even
when supplied) each manufacture the refutation at a *singleton*
transition roster — the shipped control net's uncoloured shadow has
one action, enabled at every vanishing marking, and would satisfy the
donor's hypothesis.  Both flavours are pinned below
(`cnet₁_not_branchZenoFree`, supply-blocked;
`cnet₁_not_branchZenoFree_guard`, guard-blocked — the guard-cylinder
face of the identification the flattening's guard rows will consume).
The repair is the cascade face's own: quantify the demon over
**enabling-respecting** schedulers, the class for which `CascadeRank`
certifies Zeno-freedom (`zenoFree_of_cascadeRank`), inhabited by the
shipped `uniformPolicy`.

**The rank hypothesis has real teeth at colour.**  The recolouring
control net (`cnet₂`, shipped by the cascade face) admits **no**
cascade rank at all: its red selection recolours to blue and its blue
selection recolours to red, so the immediate layer cycles between two
vanishing markings and every candidate rank is refuted
(`cnet₂_no_cascadeRank`).  The demonic law-set correctly refuses to
form there — Zeno honesty, not a formation gap — while the *arena*
still exists (membership needs no rank), which is exactly where the
colour-conflict plurality control lives.

**What is claimed.**  The set-valued square
`cispn_demonic_adequacy`: in `Crd (Traj N.Tangible k)`, the demonic
reading of the compiled, scheduler-free coloured net rows — timed
rows in the unordered convention with the compiler-owned coloured
dictionary, immediate branch rows keyed by pairs, admitted by *some*
well-formed scheduler-row mechanism whose assembled policy respects
enabling, at the cascade rank's working fuel — is isomorphic, by an
invertible globular cell, to the set-valued inclusion of the net's
demonic tangible law-set.  Alongside it: the credal presentation and
its rank-irrelevance, the radially-maximal-slice reconciliation, both
`SatCredal` verdicts, the angelic feeding equivalence and both
directed verdict transfers from the one membership lemma
(`cispnDemonicC_uniform`), and the semantic-universe wiring quartet.
The proofs are the uncoloured face's six-storey engine reuse through
the coloured dictionary triangle `compile_cispn_comm`; zero new
inductions.

**Scope fences.**  Kernel-valued firing measures, boundary-hitting
guard transitions, set-firings at colour, and the GSHS side of the
flattening triangle are untouched, exactly as at the cascade face.
The flatten-facing transfer forms (agreement in, verdicts out) are
the coloured composed square's to instantiate once its constructed
flattening lands — the machinery here is deliberately
flattening-free, so that module can consume it whole.  Law-level
plurality of the coloured arena (path laws differing at a horizon) is
a named successor at the recolouring net; the control tier here pins
plurality at the scheduler grain, as the uncoloured face did.  No
certificate rows are minted. -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open SuFunctor.Universe (SpecDnf)
open Finset

variable {P T U : Type} [Fintype P] [DecidableEq P] [Fintype T]
  [Fintype U] [DecidableEq U] {K : P → Type} [∀ p, Fintype (K p)]
  [∀ p, DecidableEq (K p)] {B : ℕ}

/- The scheduler-row machinery keys rows by (marking, pair) and its
well-formedness/assembly lemmas ask for decidable equality on the
action type; at colour the actions are `Σ u, IVec u`, whose instance
search runs through the Σ- and Π-instances — give it the same
headroom the coloured cascade face's decidability instances needed. -/
set_option synthInstance.maxHeartbeats 400000

namespace FinCISPN

variable (N : FinCISPN P T U K B)

/-! ## The obstruction: the donor's hypothesis is refutable at
coloured nets -/

/-- **The disabled-pair self-loop refutes the branch-level
certificate.**  If some vanishing marking `i` of `N` has a *disabled*
pair `a` — whether the supply, the capacity, or the guard cylinder
blocks it — then no rank whatsoever is branch-Zeno-free for `N`'s
automaton: the disabled branch is the zero-time no-op, a point mass
at the source, so the certificate would demand `r i < r i`.

At colour this is the generic situation even for a single immediate
transition: one branch row per colour vector, one refutation per
blocked selection. -/
theorem not_branchZenoFree_of_disabled {i : N.Vanishing} {a : N.IAct}
    (h : ¬ N.IEnabled a i.1) (r : N.Vanishing → ℕ) :
    ¬ N.toFinMA.BranchZenoFree r := by
  intro hb
  have hne : N.toFinMA.branch i a (Sum.inr i) ≠ 0 := by
    rw [toFinMA_branch, if_neg h, if_pos rfl]
    norm_num
  exact absurd (hb i a i hne) (lt_irrefl _)

/-! ## The scheduler subclass: enabling-respecting adversaries over
pairs -/

/-- **The demon's arena at colour**: memoryless randomized schedulers
over (transition, colour-vector) pairs that respect enabling.  The
community's conflict randomizations all live here; the rank
certificate `CascadeRank` certifies Zeno-freedom for exactly this
class, and `uniformPolicy` — uniform among enabled *pairs* —
witnesses that it is inhabited. -/
def RespScheduler : Type :=
  {σ : Policy N.Vanishing N.IAct // N.RespectsEnabling σ}

/-- A cascade rank certifies Zeno-freedom at every member of the
arena — the subclass's defining service, at colour. -/
theorem respZenoFree {r : N.Vanishing → ℕ} (hr : N.CascadeRank r)
    (σ : N.RespScheduler) :
    ZenoFree (N.toFinMA.imStep σ.1) r :=
  N.zenoFree_of_cascadeRank σ.1 σ.2 hr

/-- The uniform-over-pairs scheduler is a member: the arena is
inhabited. -/
def uniformResp : N.RespScheduler :=
  ⟨N.uniformPolicy, N.uniformPolicy_respects⟩

instance : Nonempty N.RespScheduler := ⟨N.uniformResp⟩

/-! ## The classical objects: the demonic tangible law-set at
colour -/

/-- **The demonic semantics of a cascade-certified coloured net**,
per jump horizon: the set of tangible path laws over all
enabling-respecting adversaries — token selections quantified along
with transition choices — as a set-valued constraint. -/
def demonicTangibleLaws {r : N.Vanishing → ℕ} (hr : N.CascadeRank r)
    (k : ℕ) : SubPMF (Traj N.Tangible k) → Prop :=
  unionSingletons fun σ : N.RespScheduler =>
    N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k

/-- The credal presentation of the coloured demonic face: the union
of the members' rays. -/
def demonicTangibleCredal {r : N.Vanishing → ℕ} (hr : N.CascadeRank r)
    (k : ℕ) : SubPMF (Traj N.Tangible k) → Prop :=
  unionRays fun σ : N.RespScheduler =>
    N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k

/-- **Rank-irrelevance of the demonic law-set**: the object is the
net's and the horizon's; the cascade certificate only witnesses. -/
theorem demonicTangibleLaws_rank_irrel {r r' : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (hr' : N.CascadeRank r') (k : ℕ) :
    N.demonicTangibleLaws hr k = N.demonicTangibleLaws hr' k := by
  have h : (fun σ : N.RespScheduler =>
        N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k)
      = fun σ : N.RespScheduler =>
        N.tangiblePathLaw σ.1 r' (N.respZenoFree hr' σ) k := by
    funext σ
    exact N.toFinMA.pathLaw_rank_irrel σ.1
      (N.respZenoFree hr σ) (N.respZenoFree hr' σ) k
  unfold demonicTangibleLaws
  rw [h]

/-- The credal presentation is rank-irrelevant. -/
theorem demonicTangibleCredal_rank_irrel {r r' : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (hr' : N.CascadeRank r') (k : ℕ) :
    N.demonicTangibleCredal hr k = N.demonicTangibleCredal hr' k := by
  have h : (fun σ : N.RespScheduler =>
        N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k)
      = fun σ : N.RespScheduler =>
        N.tangiblePathLaw σ.1 r' (N.respZenoFree hr' σ) k := by
    funext σ
    exact N.toFinMA.pathLaw_rank_irrel σ.1
      (N.respZenoFree hr σ) (N.respZenoFree hr' σ) k
  unfold demonicTangibleCredal
  rw [h]

/-! ## The compiled side: scheduler rows whose assembly respects
enabling -/

/-- **Well-formed scheduler rows assembling an enabling-respecting
policy** — the compiled-side face of the arena at colour.
`PolicyRows` stores probabilities per (vanishing marking, pair) and
nothing about enabling, so the subclass must be carried explicitly;
this is the named strengthening of the compiled admission predicate,
not a definitional coincidence. -/
structure RespectingRows where
  /-- The stored scheduler rows, keyed by pairs. -/
  rows : PolicyRows N.Vanishing N.IAct
  /-- Well-formedness of the stored rows. -/
  wf : rows.WF
  /-- The assembled policy respects enabling. -/
  resp : N.RespectsEnabling (rows.toPolicy wf)

/-- The arena member assembled from respecting rows. -/
def RespectingRows.toResp (σr : N.RespectingRows) : N.RespScheduler :=
  ⟨σr.rows.toPolicy σr.wf, σr.resp⟩

/-- Compilation of an arena member, packaged back as respecting
rows — the section, at the subclass. -/
noncomputable def RespScheduler.toRows (σ : N.RespScheduler) :
    N.RespectingRows where
  rows := compilePolicy σ.1
  wf := compilePolicy_wf σ.1
  resp := by
    have h : (compilePolicy σ.1).toPolicy (compilePolicy_wf σ.1) = σ.1 := by
      obtain ⟨⟨choice, nonneg, row_sum⟩, hresp⟩ := σ
      rfl
    rw [h]
    exact σ.2

/-- **The demonic reading of the compiled coloured net rows**: the
rows carry no scheduler, and the demon's choice is the existentially
quantified *respecting* scheduler-row mechanism — `μ` is admitted
exactly when some such mechanism closes the compiled rows, at
absorption fuel `n`, onto a chain diagram that `μ` satisfies. -/
noncomputable def cispnDemonicC (n k : ℕ) :
    SubPMF (Traj N.Tangible k) → Prop :=
  fun μ => ∃ σr : N.RespectingRows,
    looseConj (atoms (jumpRows
      (closeMaRows N.compileCispn σr.rows n)) k) μ

/-- The ray-closure of the compiled demonic reading. -/
noncomputable def cispnDemonicCredalC (n k : ℕ) :
    SubPMF (Traj N.Tangible k) → Prop :=
  fun ν => ∃ μ, N.cispnDemonicC n k μ ∧ rayC μ ν

/-! ## The feeding lemma and the square -/

/-- **The pointwise demonic equivalence at the coloured net level**:
a subprobability mass function is admitted by the compiled net rows
under some respecting scheduler-row mechanism, at the cascade rank's
working fuel, exactly when it is a member of the demonic tangible
law-set.

Each direction is the fixed-scheduler engine at the appropriate arena
member, reached through the coloured dictionary triangle
`compile_cispn_comm`; the cascade certificate is spent exactly once
on the compiled side, supplying Zeno-freedom for whichever member the
demon stored. -/
theorem cispnDemonicC_iff {r : N.Vanishing → ℕ} (hr : N.CascadeRank r)
    (k : ℕ) (μ : SubPMF (Traj N.Tangible k)) :
    N.cispnDemonicC (absFuel r) k μ ↔ N.demonicTangibleLaws hr k μ := by
  classical
  constructor
  · rintro ⟨σr, hsat⟩
    refine ⟨σr.toResp, ?_⟩
    have hrows : closeMaRows N.compileCispn σr.rows (absFuel r)
        = compileCtmc (N.toFinMA.close σr.toResp.1 r
            (N.respZenoFree hr σr.toResp)) := by
      rw [compile_cispn_comm, ← compile_closeMa_comm N.toFinMA
        σr.toResp.1 r (N.respZenoFree hr σr.toResp)]
      have hcp : compilePolicy σr.toResp.1 = σr.rows := by
        obtain ⟨⟨rows⟩, hwf, hresp⟩ := σr
        exact congrArg PolicyRows.mk (Finsupp.ext fun p => rfl)
      rw [hcp]
    rw [hrows, compile_jump_comm] at hsat
    have hlaw := (satAtoms_iff
      (compile_wf (N.toFinMA.close σr.toResp.1 r
        (N.respZenoFree hr σr.toResp)).jumpChain) μ).mp hsat
    rw [compile_rowsLaw] at hlaw
    exact (singletonC_iff _ _).mpr hlaw
  · rintro ⟨σ, hσ⟩
    refine ⟨σ.toRows, ?_⟩
    show looseConj (atoms (jumpRows
      (closeMaRows N.compileCispn (compilePolicy σ.1) (absFuel r))) k) μ
    rw [compile_cispn_comm, compile_closeMa_comm N.toFinMA σ.1 r
        (N.respZenoFree hr σ), compile_jump_comm,
      satAtoms_iff (compile_wf (N.toFinMA.close σ.1 r
        (N.respZenoFree hr σ)).jumpChain) μ,
      compile_rowsLaw]
    exact (singletonC_iff _ _).mp hσ

/-- **Adequacy of the coloured stochastic-Petri compilation, demonic
face** — the set-valued square at the coloured net level.

In the double category `Crd (Traj N.Tangible k)`: the demonic reading
of the compiled, scheduler-free coloured net rows — timed rows in the
unordered convention with the compiler-owned coloured dictionary,
immediate rows keyed by (transition, colour-vector) pairs, admitted
by *some* respecting scheduler-row mechanism at the cascade rank's
working fuel — is isomorphic, by an invertible globular cell, to the
set-valued inclusion of the net's demonic tangible law-set.
Compile-then-denote agrees with interpret-then-include, where
interpretation now yields a set of closed tangible laws, one per
enabling-respecting adversary over pairs. -/
theorem cispn_demonic_adequacy {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ α : Cell (N.cispnDemonicC (absFuel r) k : Loose a a)
        (N.demonicTangibleLaws hr k) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  Crd.looseIso_ofIff (N.cispnDemonicC_iff hr k)

/-- The feeding lemma at the credal stratum. -/
theorem cispnDemonicCredalC_iff {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ) (ν : SubPMF (Traj N.Tangible k)) :
    N.cispnDemonicCredalC (absFuel r) k ν ↔
      N.demonicTangibleCredal hr k ν := by
  constructor
  · rintro ⟨μ, hμ, hray⟩
    obtain ⟨σ, hσ⟩ := (N.cispnDemonicC_iff hr k μ).mp hμ
    exact ⟨σ, (singletonC_iff _ _).mp hσ ▸ hray⟩
  · rintro ⟨σ, hray⟩
    exact ⟨N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k,
      (N.cispnDemonicC_iff hr k _).mpr ⟨σ, singletonC_self _⟩, hray⟩

/-! ## The slice: credal presentation reconciled with the law-set -/

/-- **The demonic slice at the coloured net level**: the radially
maximal slice of the demonic credal set is exactly the demonic
law-set — the equal-mass reconciliation at `m = 1`, every tangible
path law having full mass. -/
theorem cispn_demonic_maxSlice {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ) (ν : SubPMF (Traj N.Tangible k)) :
    maxSlice (N.demonicTangibleCredal hr k) ν ↔
      N.demonicTangibleLaws hr k ν :=
  maxSlice_unionRays
    (fun σ : N.RespScheduler =>
      N.toFinMA.pathLaw_mass σ.1 r (N.respZenoFree hr σ) k)
    one_ne_zero ν

/-- The demonic reconciliation at the coloured net level, packaged as
loose arrows. -/
theorem cispn_demonic_ray_singleton_reconciliation
    {r : N.Vanishing → ℕ} (hr : N.CascadeRank r) (k : ℕ)
    {a : Crd (Traj N.Tangible k)} :
    ∃ α : Cell (maxSlice (N.demonicTangibleCredal hr k) : Loose a a)
        (N.demonicTangibleLaws hr k) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  Crd.looseIso_ofIff (N.cispn_demonic_maxSlice hr k)

/-! ## The verdicts: uniform-over-adversary bounds at both
polarities -/

/-- **The demonic lower verdict is the uniform-over-adversaries
bound**: a lower-kind constraint holds of the net's demonic credal
set exactly when it holds of every enabling-respecting adversary's
tangible law — token selections included. -/
theorem satCredal_lower_cispnDemonicCredal {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ)
    (c : SubPMF (Traj N.Tangible k) → Prop) :
    SatCredal .lower (N.demonicTangibleCredal hr k) c ↔
      ∀ σ : N.RespScheduler,
        c (N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k) :=
  satCredal_lower_unionRays
    (fun σ : N.RespScheduler =>
      N.toFinMA.pathLaw_mass σ.1 r (N.respZenoFree hr σ) k)
    one_ne_zero c

/-- **The demonic upper verdict**, for down-closed constraints —
mass-free, through down-closure. -/
theorem satCredal_upper_cispnDemonicCredal {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ)
    {c : SubPMF (Traj N.Tangible k) → Prop} (hc : DownClosed c) :
    SatCredal .upper (N.demonicTangibleCredal hr k) c ↔
      ∀ σ : N.RespScheduler,
        c (N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k) :=
  satCredal_upper_unionRays hc

/-! ## The membership lemma -/

/-- **The demonic square at the uniform member**: the uniform-over-
pairs scheduler's tangible path law is admitted by the compiled
demonic reading — the one membership lemma from which both directed
transfer faces flow. -/
theorem cispnDemonicC_uniform {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ) :
    N.cispnDemonicC (absFuel r) k
      (N.tangiblePathLaw N.uniformPolicy r
        (N.respZenoFree hr N.uniformResp) k) :=
  (N.cispnDemonicC_iff hr k _).mpr ⟨N.uniformResp, singletonC_self _⟩

/-- Every member of the demonic law-set is some adversary's tangible
path law — the set is exactly the adversary-indexed family. -/
theorem demonicTangibleLaws_iff {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ) (μ : SubPMF (Traj N.Tangible k)) :
    N.demonicTangibleLaws hr k μ ↔
      ∃ σ : N.RespScheduler,
        μ = N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k :=
  Iff.rfl

/-! ## The angelic face at the coloured net corner -/

/-- **The angelic feeding equivalence at colour**: the angelic
verdict on the net's demonic credal set is existential quantification
over the enabling-respecting arena — some adversary's tangible path
law, token selections included, satisfies the constraint.  The
∃-mirror of `satCredal_lower_cispnDemonicCredal`, spending the same
mass theorem on the same slice reconciliation. -/
theorem satAngelic_cispnDemonicCredal {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ)
    (c : SubPMF (Traj N.Tangible k) → Prop) :
    SatAngelic (N.demonicTangibleCredal hr k) c ↔
      ∃ σ : N.RespScheduler,
        c (N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k) :=
  satAngelic_unionRays
    (fun σ : N.RespScheduler =>
      N.toFinMA.pathLaw_mass σ.1 r (N.respZenoFree hr σ) k)
    one_ne_zero c

/-- **The angelic witness transfer** — one half of what the
membership lemma yields: a claim established on any arena member's
law transfers to the angelic reading, by exhibition. -/
theorem cispn_angelic_of_member {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (σ : N.RespScheduler) (k : ℕ)
    {c : SubPMF (Traj N.Tangible k) → Prop}
    (hc : c (N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k)) :
    SatAngelic (N.demonicTangibleCredal hr k) c :=
  (N.satAngelic_cispnDemonicCredal hr k c).mpr ⟨σ, hc⟩

/-- **The demonic restriction transfer** — the other half: a claim
certified universally against the demonic credal set holds of every
arena member's law.  (Lower kind, through the slice.)  Sound
direction only; no envelope equality is stated anywhere in this
module. -/
theorem cispn_demonic_verdict_to_member {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (σ : N.RespScheduler) (k : ℕ)
    {c : SubPMF (Traj N.Tangible k) → Prop}
    (h : SatCredal .lower (N.demonicTangibleCredal hr k) c) :
    c (N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k) :=
  (N.satCredal_lower_cispnDemonicCredal hr k c).mp h σ

/-- The upper-kind twin of the restriction transfer: the whole-set
universal reading restricts to every member unconditionally. -/
theorem cispn_demonic_upper_to_member {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (σ : N.RespScheduler) (k : ℕ)
    {c : SubPMF (Traj N.Tangible k) → Prop}
    (h : SatCredal .upper (N.demonicTangibleCredal hr k) c) :
    c (N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k) :=
  h _ (unionRays_self _ σ)

/-- The net-level face of the un-sliced degeneracy at colour: the
demonic credal set admits the zero model as a whole-set existential
witness for any constraint it satisfies — the reason the angelic
verdict reads the slice. -/
theorem satAngelic_unsliced_degenerate {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ)
    {c : SubPMF (Traj N.Tangible k) → Prop}
    (hc : c (SubPMF.zero (Traj N.Tangible k))) :
    ∃ ν, N.demonicTangibleCredal hr k ν ∧ c ν :=
  satAngelic_whole_degenerate _ hc

/-- The concrete degenerate family: every zero-threshold upper-bound
event atom has an un-sliced whole-set witness on the demonic credal
set. -/
theorem satAngelic_unsliced_leC_degenerate {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ) (A : Set (Traj N.Tangible k)) :
    ∃ ν, N.demonicTangibleCredal hr k ν ∧ leC A 0 ν :=
  N.satAngelic_unsliced_degenerate hr k (leC_zero_of_zero A)

/-! ## The semantic-universe wiring (in-module, per the standing
precedent) -/

/-- The compiled coloured net's demonic presentation in the semantic
universe's fibre: the scheduler-free rows with the existentially
quantified enabling-respecting scheduler-row mechanism at the working
fuel, as a one-atom projection — the set-valued face presents as a
single wall atom, so finite presentation is untouched by the arena's
infinitude. -/
noncomputable def cispnDemonicDnf (n k : ℕ) :
    SpecDnf (Plain.Joint (Traj N.Tangible k)) :=
  diagramDnf [N.cispnDemonicC n k]

/-- **The demonic coloured net square, wired to the semantic
universe**: the ideal point of a law models the compiled demonic
presentation, at the certificate's working fuel, exactly when the law
is a member of the demonic tangible law-set. -/
theorem su_cispn_demonic_adequacy {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ) (μ : SubPMF (Traj N.Tangible k)) :
    idealPoint μ ∈ (N.cispnDemonicDnf (absFuel r) k).modelClass
      ↔ N.demonicTangibleLaws hr k μ := by
  have h := idealPoint_mem_diagramDnf_iff [N.cispnDemonicC (absFuel r) k] μ
  constructor
  · intro hm
    obtain ⟨h1, -⟩ := h.mp hm
    exact (N.cispnDemonicC_iff hr k μ).mp h1
  · intro hd
    exact h.mpr ⟨(N.cispnDemonicC_iff hr k μ).mpr hd, trivial⟩

/-- The positive face: every arena member's tangible path law models
the compiled demonic presentation. -/
theorem su_cispn_demonic_mem {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (σ : N.RespScheduler) (k : ℕ) :
    idealPoint (N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k)
      ∈ (N.cispnDemonicDnf (absFuel r) k).modelClass :=
  (N.su_cispn_demonic_adequacy hr k _).mpr
    ((N.demonicTangibleLaws_iff hr k _).mpr ⟨σ, rfl⟩)

/-- Ex falso at the demonic coloured net corner. -/
theorem su_cispn_demonic_bottom (n k : ℕ) :
    (⊤ : Plain.Pen (Traj N.Tangible k))
      ∉ (N.cispnDemonicDnf n k).modelClass :=
  top_notMem_diagramDnf _

/-- The credal reading at the demonic coloured net corner: membership
at the semantic universe's judgment is exactly radial maximality in
the union-of-rays credal object — the equal-mass reconciliation
consumed whole, at the coloured net level. -/
theorem su_cispn_demonic_slice {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ) (ν : SubPMF (Traj N.Tangible k)) :
    idealPoint ν ∈ (N.cispnDemonicDnf (absFuel r) k).modelClass
      ↔ maxSlice (N.demonicTangibleCredal hr k) ν :=
  (N.su_cispn_demonic_adequacy hr k ν).trans
    (N.cispn_demonic_maxSlice hr k ν).symm

end FinCISPN

/-! ## Controls

Second witnesses at the designed mutant loci, on the cascade face's
shipped control nets.  The headline pair is the **refutation, twice
over**: the donor's branch-level hypothesis fails at the guarded net
by supply *and* by guard — two coloured mechanisms, each sufficient
alone, at a singleton transition roster whose uncoloured shadow would
satisfy the hypothesis — and the recolouring net refutes not the
donor's certificate but **every candidate rank at once**, pinning
that the demonic law-set's rank hypothesis carries real content at
colour. -/

namespace CspnDemonicControls

open FinCISPN CispnControls

/-- **The refutation by supply.**  At the red-only vanishing marking
the blue selection of the sole immediate transition is unsupplied, so
its branch row is the zero-time self-loop and no rank is
branch-Zeno-free for `cnet₁`'s automaton.  The uncoloured shadow of
this net has one action, enabled at every vanishing marking: the
refutation is manufactured entirely by colour selection. -/
theorem cnet₁_not_branchZenoFree (r : cnet₁.Vanishing → ℕ) :
    ¬ cnet₁.toFinMA.BranchZenoFree r :=
  cnet₁.not_branchZenoFree_of_disabled
    (i := i20) (a := ⟨0, ιb⟩) (by decide) r

/-- **The refutation by guard.**  At the mixed marking the blue
token is *present* — the blue selection is supplied — and the guard
cylinder alone refuses it.  The same disabled-pair self-loop follows:
the guard-cylinder mechanism, which the flattening's per-vector guard
rows identify, is independently sufficient to refute the branch-level
certificate. -/
theorem cnet₁_not_branchZenoFree_guard (r : cnet₁.Vanishing → ℕ) :
    ¬ cnet₁.toFinMA.BranchZenoFree r :=
  cnet₁.not_branchZenoFree_of_disabled
    (i := i11) (a := ⟨0, ιb⟩) (by decide) r

/-- The uniform-over-pairs scheduler is a member of `cnet₁`'s arena —
the subclass is inhabited at the concrete coloured net. -/
def cnet₁_uniformResp : cnet₁.RespScheduler := cnet₁.uniformResp

/-- The uniform member's tangible path law is in `cnet₁`'s demonic
law-set: the community's randomization over pairs is one adversary
among the quantified family. -/
theorem cnet₁_uniform_mem (k : ℕ) :
    cnet₁.demonicTangibleLaws cnet₁_rank k
      (cnet₁.tangiblePathLaw cnet₁.uniformPolicy r₁
        (cnet₁.respZenoFree cnet₁_rank cnet₁.uniformResp) k) :=
  ⟨cnet₁.uniformResp, singletonC_self _⟩

/-- The compiled demonic reading admits the uniform member's law at
`cnet₁` — the square's positive face, concretely at colour. -/
theorem cnet₁_demonicC_uniform (k : ℕ) :
    cnet₁.cispnDemonicC (absFuel r₁) k
      (cnet₁.tangiblePathLaw cnet₁.uniformPolicy r₁
        (cnet₁.respZenoFree cnet₁_rank cnet₁.uniformResp) k) :=
  cnet₁.cispnDemonicC_uniform cnet₁_rank k

/-! ### The recolouring net: rank refutation and colour-conflict
plurality -/

/-- The blue-only marking is vanishing for the recolouring net: its
blue selection is supplied and unguarded. -/
def j02 : cnet₂.Vanishing := ⟨m02, by decide⟩

/-- The red firing of the recolouring net's sole transition consumes
the red token and deposits a blue one: the mixed marking steps to the
(vanishing) blue-only marking. -/
theorem cnet₂_fire_red :
    cnet₂.toSum (cnet₂.ifire ⟨0, ιr⟩ j11.1) = Sum.inr j02 := by
  rw [show cnet₂.ifire ⟨0, ιr⟩ j11.1 = m02 from by decide]
  exact dif_pos (by decide)

/-- The blue firing deposits a red token: the blue-only marking steps
back to the (vanishing) mixed marking — the recolouring cycle. -/
theorem cnet₂_fire_blue :
    cnet₂.toSum (cnet₂.ifire ⟨0, ιb⟩ j02.1) = Sum.inr j11 := by
  rw [show cnet₂.ifire ⟨0, ιb⟩ j02.1 = m11 from by decide]
  exact dif_pos (by decide)

/-- **The recolouring net admits no cascade rank**: red recolours to
blue, blue recolours to red, and the two vanishing markings cycle —
every candidate rank would have to strictly decrease around a loop.
The demonic law-set correctly refuses to form on this net (Zeno
honesty), while the arena below still exists: membership needs no
rank. -/
theorem cnet₂_no_cascadeRank (r : cnet₂.Vanishing → ℕ) :
    ¬ cnet₂.CascadeRank r := by
  intro hr
  exact absurd
    ((hr j11 ⟨0, ιr⟩ (by decide) j02 cnet₂_fire_red).trans
      (hr j02 ⟨0, ιb⟩ (by decide) j11 cnet₂_fire_blue))
    (lt_irrefl _)

/-- **The colour-preferring adversary**: all mass on the red
selection wherever it is enabled; the uniform split elsewhere.  A
scheduler that resolves the pure *colour* conflict deterministically —
a choice no transitions-only adversary can express. -/
def preferRed : Policy cnet₂.Vanishing cnet₂.IAct where
  choice i a :=
    if cnet₂.IEnabled ⟨0, ιr⟩ i.1
    then (if a = ⟨0, ιr⟩ then 1 else 0)
    else cnet₂.uniformPolicy.choice i a
  nonneg i a := by
    by_cases h : cnet₂.IEnabled ⟨0, ιr⟩ i.1
    · simp only [if_pos h]
      split <;> norm_num
    · simp only [if_neg h]
      exact cnet₂.uniformPolicy.nonneg i a
  row_sum i := by
    by_cases h : cnet₂.IEnabled ⟨0, ιr⟩ i.1
    · simp only [if_pos h]
      rw [Finset.sum_ite_eq' univ (⟨0, ιr⟩ : cnet₂.IAct)
        fun _ => (1 : ℚ)]
      simp
    · simp only [if_neg h]
      exact cnet₂.uniformPolicy.row_sum i

/-- The colour-preferring adversary respects enabling: where it
prefers, the preferred pair is enabled; elsewhere it is the uniform
member. -/
theorem preferRed_respects : cnet₂.RespectsEnabling preferRed := by
  intro i a h
  by_cases hr : cnet₂.IEnabled ⟨0, ιr⟩ i.1
  · have hne : (if a = (⟨0, ιr⟩ : cnet₂.IAct) then (1 : ℚ) else 0) ≠ 0 := by
      simpa only [preferRed, if_pos hr] using h
    have ha : a = ⟨0, ιr⟩ := by
      by_contra hcon
      exact hne (if_neg hcon)
    rw [ha]
    exact hr
  · have hu : cnet₂.uniformPolicy.choice i a ≠ 0 := by
      simpa only [preferRed, if_neg hr] using h
    exact cnet₂.uniformPolicy_respects i a hu

/-- The colour-preferring adversary, as an arena member. -/
def preferRedResp : cnet₂.RespScheduler :=
  ⟨preferRed, preferRed_respects⟩

/-- **The arena is genuinely plural at a pure colour conflict.**  At
the mixed marking both selections of the sole transition are enabled;
the uniform member splits the conflict evenly over the two *pairs*,
and the colour-preferring member does not.  The demon's choices at
colour genuinely include which tokens fire — plurality that the
uncoloured shadow (one transition, one action) cannot express. -/
theorem arena_plural_by_colour :
    (cnet₂.uniformResp : cnet₂.RespScheduler).1.choice j11 ⟨0, ιr⟩
      ≠ preferRedResp.1.choice j11 ⟨0, ιr⟩ := by
  have h1 : (cnet₂.uniformResp : cnet₂.RespScheduler).1.choice
      j11 ⟨0, ιr⟩ = 2⁻¹ := cnet₂_pair_split
  have h2 : preferRedResp.1.choice j11 ⟨0, ιr⟩ = 1 := by
    show (if cnet₂.IEnabled ⟨0, ιr⟩ j11.1
      then (if (⟨0, ιr⟩ : cnet₂.IAct) = ⟨0, ιr⟩ then (1 : ℚ) else 0)
      else cnet₂.uniformPolicy.choice j11 ⟨0, ιr⟩) = 1
    rw [if_pos (by decide : cnet₂.IEnabled ⟨0, ιr⟩ j11.1), if_pos rfl]
  rw [h1, h2]
  norm_num

end CspnDemonicControls

end Adequacy
end SuFunctor
