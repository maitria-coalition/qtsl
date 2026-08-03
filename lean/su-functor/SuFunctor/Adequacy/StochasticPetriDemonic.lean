import SuFunctor.Adequacy.StochasticPetriCascade
import SuFunctor.Adequacy.MaDemonic

/-! # Adequacy: stochastic Petri frames, demonic (scheduler-quantified) face

The scheduler-quantification face of the stochastic-Petri cascade
square — the net-level sibling of the demonic Markov-automaton square
(`SuFunctor.Adequacy.MaDemonic`), and the last set-valued face of the
immediate/cascade species.  The fixed-scheduler square
(`SuFunctor.Adequacy.StochasticPetriCascade`) closes a net at a
*declared* memoryless randomized scheduler and lands a singleton
credal constraint; this module quantifies the demon and lands a
set-valued one.

**The obstruction, and why this face is not a transport.**  The
natural move — instantiate the donor `ma_demonic_adequacy` at
`compileIspn` through the landed dictionary triangle
`compile_ispn_comm` — is *unavailable*, and unavailable for a reason
worth stating rather than routing around.  The donor's hypothesis is
`FinMA.BranchZenoFree`: a rank strictly decreasing along **every**
branch row, scheduler-blind.  A net's automaton `FinISPN.toFinMA`
sends a *disabled* immediate transition to the honest zero-time no-op —
a point mass at the source (`toFinMA_branch`, the else-branch).  So at
any vanishing marking `i` with a disabled immediate `u`, the branch row
`branch i u (Sum.inr i) = 1 ≠ 0`, and `BranchZenoFree` demands
`r i < r i`.  **False.**  Not merely unproven: refutable, for every
rank at once, on any net possessing one disabled immediate at one
vanishing marking — which is essentially every net with more than one
immediate transition, and in particular the control net `net₁` this
species already ships (`net₁_not_branchZenoFree`, discharged at the
capacity-blocked marking `i11`).

The fixed-scheduler face already named the shape of the repair in its
own docstring (`zenoFree_of_cascadeRank`: the branch-level condition
"cannot apply verbatim here").  This module is where the
scheduler-*quantified* face meets it, and the repair is the one the
cascade square's own logic dictates: **quantify the demon over
enabling-respecting schedulers**.  `RespectsEnabling` (landed) is
exactly the class for which `CascadeRank` certifies Zeno-freedom; it
is the class the community's randomizations all inhabit (a scheduler
weighting a disabled transition would sit still in zero time, which is
Zeno behaviour the rank machinery refuses rather than papers over);
and it is inhabited, `uniformPolicy` being the shipped member.  The
demon here is therefore a *subclass* demon, and the subclass is
load-bearing rather than decorative — the mutant that drops it fails
at `zenoFree_of_cascadeRank`'s hypothesis, not at bookkeeping.

**What is claimed.**  The set-valued square
`ispn_demonic_adequacy`: in `Crd (Traj N.Tangible k)`, the demonic
reading of the compiled, scheduler-free net rows — admitted by *some*
well-formed scheduler-row mechanism whose assembled policy respects
enabling, at the cascade rank's working fuel — is isomorphic, by an
invertible globular cell, to the set-valued inclusion of the net's
demonic tangible law-set.  Compile-then-denote agrees with
interpret-then-include, where interpretation now yields a set of
closed tangible laws, one per enabling-respecting adversary.  The
proof is six-storey engine reuse: the dictionary triangle rewrites the
compiled rows into the automaton compilation, the fixed-scheduler
cascade square supplies each member, and the enabling-respect side
condition travels on the scheduler-row well-formedness.  Zero new
inductions.

**The compiled side carries the subclass explicitly.**  `PolicyRows`
stores probabilities and nothing about enabling, so the assembled
`PolicyRows.toPolicy` is not enabling-respecting in general; the
honest compiled-side quantifier is therefore over well-formed rows
*whose assembled policy respects enabling*
(`FinISPN.RespectingRows`), and the module says so in the statement
rather than smuggling it through a definitional coincidence.  This is
a strengthening of the compiled admission predicate, named as such.

**Scope fences.**  The coloured stratum, guard transitions, the
set-firing (simultaneous composite) stratum R1/R3, and the
infinite-horizon extension are untouched, exactly as for the
fixed-scheduler face.  The adversary is memoryless randomized over
immediate choices, matching the donor's scheduler class; history-
dependent adversaries are a different stratum and are not claimed.  No
certificate rows are minted. -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open SuFunctor.Universe (SpecDnf)
open Finset

variable {P T U : Type} [Fintype P] [DecidableEq P] [Fintype T]
  [Fintype U] [DecidableEq U] {B : ℕ}

namespace FinISPN

variable (N : FinISPN P T U B)

/-! ## The obstruction: the donor's hypothesis is refutable at nets -/

/-- **The disabled-action self-loop refutes the branch-level
certificate.**  If some vanishing marking `i` of `N` has a *disabled*
immediate transition `u`, then no rank whatsoever is branch-Zeno-free
for `N`'s automaton: the disabled branch is the zero-time no-op, a
point mass at `i`, so the certificate would demand `r i < r i`.

This is the honest reason the demonic face of this species quantifies
over a scheduler *subclass* rather than transporting the donor square
on the nose. -/
theorem not_branchZenoFree_of_disabled {i : N.Vanishing} {u : U}
    (h : ¬ N.IEnabled u i.1) (r : N.Vanishing → ℕ) :
    ¬ N.toFinMA.BranchZenoFree r := by
  intro hb
  have hne : N.toFinMA.branch i u (Sum.inr i) ≠ 0 := by
    rw [toFinMA_branch, if_neg h, if_pos rfl]
    norm_num
  exact absurd (hb i u i hne) (lt_irrefl _)

/-! ## The scheduler subclass: enabling-respecting adversaries -/

/-- **The demon's arena**: memoryless randomized schedulers that
respect enabling.  The community's conflict randomizations all live
here; the rank certificate `CascadeRank` certifies Zeno-freedom for
exactly this class, and `uniformPolicy` witnesses that it is
inhabited. -/
def RespScheduler : Type :=
  {σ : Policy N.Vanishing U // N.RespectsEnabling σ}

/-- A cascade rank certifies Zeno-freedom at every member of the
arena — the subclass's defining service. -/
theorem respZenoFree {r : N.Vanishing → ℕ} (hr : N.CascadeRank r)
    (σ : N.RespScheduler) :
    ZenoFree (N.toFinMA.imStep σ.1) r :=
  N.zenoFree_of_cascadeRank σ.1 σ.2 hr

/-- The uniform scheduler is a member: the arena is inhabited. -/
def uniformResp : N.RespScheduler :=
  ⟨N.uniformPolicy, N.uniformPolicy_respects⟩

instance : Nonempty N.RespScheduler := ⟨N.uniformResp⟩

/-! ## The classical objects: the demonic tangible law-set -/

/-- **The demonic semantics of a cascade-certified net**, per jump
horizon: the set of tangible path laws over all enabling-respecting
adversaries, as a set-valued constraint.  The community's randomized
conflict resolution is one member; the set dominates every particular
randomization at once. -/
def demonicTangibleLaws {r : N.Vanishing → ℕ} (hr : N.CascadeRank r)
    (k : ℕ) : SubPMF (Traj N.Tangible k) → Prop :=
  unionSingletons fun σ : N.RespScheduler =>
    N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k

/-- The credal presentation of the net's demonic face: the union of
the members' rays. -/
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
policy** — the compiled-side face of the arena.  `PolicyRows` stores
probabilities and nothing about enabling, so the subclass must be
carried explicitly; this is the named strengthening of the compiled
admission predicate, not a definitional coincidence. -/
structure RespectingRows where
  /-- The stored scheduler rows. -/
  rows : PolicyRows N.Vanishing U
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

/-- **The demonic reading of the compiled net rows**: the rows carry
no scheduler, and the demon's choice is the existentially quantified
*respecting* scheduler-row mechanism — `μ` is admitted exactly when
some such mechanism closes the compiled rows, at absorption fuel `n`,
onto a chain diagram that `μ` satisfies. -/
noncomputable def ispnDemonicC (n k : ℕ) :
    SubPMF (Traj N.Tangible k) → Prop :=
  fun μ => ∃ σr : N.RespectingRows,
    looseConj (atoms (jumpRows
      (closeMaRows N.compileIspn σr.rows n)) k) μ

/-- The ray-closure of the compiled demonic reading. -/
noncomputable def ispnDemonicCredalC (n k : ℕ) :
    SubPMF (Traj N.Tangible k) → Prop :=
  fun ν => ∃ μ, N.ispnDemonicC n k μ ∧ rayC μ ν

/-! ## The feeding lemma and the square -/

/-- **The pointwise demonic equivalence at the net level**: a
subprobability mass function is admitted by the compiled net rows
under some respecting scheduler-row mechanism, at the cascade rank's
working fuel, exactly when it is a member of the demonic tangible
law-set.

Each direction is the fixed-scheduler engine at the appropriate arena
member, reached through the dictionary triangle `compile_ispn_comm`:
the stored rows assemble a respecting policy whose closure the
rate-closure and jump triangles collapse to a compiled chain the chain
engine pins; conversely every arena member compiles to a witnessing
respecting row set.  The cascade certificate is spent exactly once on
the compiled side, supplying Zeno-freedom for whichever member the
demon stored. -/
theorem ispnDemonicC_iff {r : N.Vanishing → ℕ} (hr : N.CascadeRank r)
    (k : ℕ) (μ : SubPMF (Traj N.Tangible k)) :
    N.ispnDemonicC (absFuel r) k μ ↔ N.demonicTangibleLaws hr k μ := by
  classical
  constructor
  · rintro ⟨σr, hsat⟩
    refine ⟨σr.toResp, ?_⟩
    have hrows : closeMaRows N.compileIspn σr.rows (absFuel r)
        = compileCtmc (N.toFinMA.close σr.toResp.1 r
            (N.respZenoFree hr σr.toResp)) := by
      rw [compile_ispn_comm, ← compile_closeMa_comm N.toFinMA
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
      (closeMaRows N.compileIspn (compilePolicy σ.1) (absFuel r))) k) μ
    rw [compile_ispn_comm, compile_closeMa_comm N.toFinMA σ.1 r
        (N.respZenoFree hr σ), compile_jump_comm,
      satAtoms_iff (compile_wf (N.toFinMA.close σ.1 r
        (N.respZenoFree hr σ)).jumpChain) μ,
      compile_rowsLaw]
    exact (singletonC_iff _ _).mp hσ

/-- **Adequacy of the stochastic-Petri compilation, demonic face** —
the set-valued square at the net level.

In the double category `Crd (Traj N.Tangible k)`: the demonic reading
of the compiled, scheduler-free net rows — timed rows in the unordered
convention with the compiler-owned dictionary, immediate rows
action-keyed, admitted by *some* respecting scheduler-row mechanism at
the cascade rank's working fuel — is isomorphic, by an invertible
globular cell, to the set-valued inclusion of the net's demonic
tangible law-set.  Compile-then-denote agrees with
interpret-then-include, where interpretation now yields a set of
closed tangible laws, one per enabling-respecting adversary. -/
theorem ispn_demonic_adequacy {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ α : Cell (N.ispnDemonicC (absFuel r) k : Loose a a)
        (N.demonicTangibleLaws hr k) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  Crd.looseIso_ofIff (N.ispnDemonicC_iff hr k)

/-- The feeding lemma at the credal stratum. -/
theorem ispnDemonicCredalC_iff {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ) (ν : SubPMF (Traj N.Tangible k)) :
    N.ispnDemonicCredalC (absFuel r) k ν ↔
      N.demonicTangibleCredal hr k ν := by
  constructor
  · rintro ⟨μ, hμ, hray⟩
    obtain ⟨σ, hσ⟩ := (N.ispnDemonicC_iff hr k μ).mp hμ
    exact ⟨σ, (singletonC_iff _ _).mp hσ ▸ hray⟩
  · rintro ⟨σ, hray⟩
    exact ⟨N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k,
      (N.ispnDemonicC_iff hr k _).mpr ⟨σ, singletonC_self _⟩, hray⟩

/-! ## The slice: credal presentation reconciled with the law-set -/

/-- **The demonic slice at the net level**: the radially maximal slice
of the demonic credal set is exactly the demonic law-set — the
equal-mass reconciliation at `m = 1`, every tangible path law having
full mass. -/
theorem ispn_demonic_maxSlice {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ) (ν : SubPMF (Traj N.Tangible k)) :
    maxSlice (N.demonicTangibleCredal hr k) ν ↔
      N.demonicTangibleLaws hr k ν :=
  maxSlice_unionRays
    (fun σ : N.RespScheduler =>
      N.toFinMA.pathLaw_mass σ.1 r (N.respZenoFree hr σ) k)
    one_ne_zero ν

/-- The demonic reconciliation at the net level, packaged as loose
arrows. -/
theorem ispn_demonic_ray_singleton_reconciliation
    {r : N.Vanishing → ℕ} (hr : N.CascadeRank r) (k : ℕ)
    {a : Crd (Traj N.Tangible k)} :
    ∃ α : Cell (maxSlice (N.demonicTangibleCredal hr k) : Loose a a)
        (N.demonicTangibleLaws hr k) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  Crd.looseIso_ofIff (N.ispn_demonic_maxSlice hr k)

/-! ## The verdicts: uniform-over-adversary bounds at both polarities -/

/-- **The demonic lower verdict is the uniform-over-adversaries
bound**: a lower-kind constraint holds of the net's demonic credal set
exactly when it holds of every enabling-respecting adversary's
tangible law. -/
theorem satCredal_lower_ispnDemonicCredal {r : N.Vanishing → ℕ}
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
theorem satCredal_upper_ispnDemonicCredal {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ)
    {c : SubPMF (Traj N.Tangible k) → Prop} (hc : DownClosed c) :
    SatCredal .upper (N.demonicTangibleCredal hr k) c ↔
      ∀ σ : N.RespScheduler,
        c (N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k) :=
  satCredal_upper_unionRays hc

/-! ## The semantic-universe wiring (in-module, per the standing
precedent) -/

/-- The compiled net's demonic presentation in the semantic universe's
fibre: the set-valued reading, as a constraint on ideal points. -/
noncomputable def ispnDemonicSet {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ) : SubPMF (Traj N.Tangible k) → Prop :=
  N.demonicTangibleLaws hr k

/-- **The demonic square, at the uniform member**: the tangible path
law of any enabling-respecting adversary is admitted by the compiled
demonic reading — the positive face, at the arena's shipped member. -/
theorem ispnDemonicC_uniform {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ) :
    N.ispnDemonicC (absFuel r) k
      (N.tangiblePathLaw N.uniformPolicy r
        (N.respZenoFree hr N.uniformResp) k) :=
  (N.ispnDemonicC_iff hr k _).mpr ⟨N.uniformResp, singletonC_self _⟩

/-- Every member of the demonic law-set is some adversary's tangible
path law — the set is exactly the adversary-indexed family. -/
theorem demonicTangibleLaws_iff {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ) (μ : SubPMF (Traj N.Tangible k)) :
    N.demonicTangibleLaws hr k μ ↔
      ∃ σ : N.RespScheduler,
        μ = N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k :=
  Iff.rfl

/-! ## The semantic-universe wiring (in-module, per the standing
precedent for squares landing while the shared wiring file is hot) -/

/-- The compiled net's demonic presentation in the semantic universe's
fibre: the scheduler-free rows with the existentially quantified
enabling-respecting scheduler-row mechanism at the working fuel, as a
one-atom projection — the set-valued face presents as a single wall
atom, so finite presentation is untouched by the arena's infinitude,
exactly as at the demonic automaton corner. -/
noncomputable def ispnDemonicDnf (n k : ℕ) :
    SpecDnf (Plain.Joint (Traj N.Tangible k)) :=
  diagramDnf [N.ispnDemonicC n k]

/-- **The demonic net square, wired to the semantic universe**: the
ideal point of a law models the compiled demonic presentation, at the
certificate's working fuel, exactly when the law is a member of the
demonic tangible law-set. -/
theorem su_ispn_demonic_adequacy {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ) (μ : SubPMF (Traj N.Tangible k)) :
    idealPoint μ ∈ (N.ispnDemonicDnf (absFuel r) k).modelClass
      ↔ N.demonicTangibleLaws hr k μ := by
  have h := idealPoint_mem_diagramDnf_iff [N.ispnDemonicC (absFuel r) k] μ
  constructor
  · intro hm
    obtain ⟨h1, -⟩ := h.mp hm
    exact (N.ispnDemonicC_iff hr k μ).mp h1
  · intro hd
    exact h.mpr ⟨(N.ispnDemonicC_iff hr k μ).mpr hd, trivial⟩

/-- The positive face: every arena member's tangible path law models
the compiled demonic presentation. -/
theorem su_ispn_demonic_mem {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (σ : N.RespScheduler) (k : ℕ) :
    idealPoint (N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k)
      ∈ (N.ispnDemonicDnf (absFuel r) k).modelClass :=
  (N.su_ispn_demonic_adequacy hr k _).mpr
    ((N.demonicTangibleLaws_iff hr k _).mpr ⟨σ, rfl⟩)

/-- Ex falso at the demonic net corner. -/
theorem su_ispn_demonic_bottom (n k : ℕ) :
    (⊤ : Plain.Pen (Traj N.Tangible k))
      ∉ (N.ispnDemonicDnf n k).modelClass :=
  top_notMem_diagramDnf _

/-- The credal reading at the demonic net corner: membership at the
semantic universe's judgment is exactly radial maximality in the
union-of-rays credal object — the equal-mass reconciliation consumed
whole, at the net level. -/
theorem su_ispn_demonic_slice {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ) (ν : SubPMF (Traj N.Tangible k)) :
    idealPoint ν ∈ (N.ispnDemonicDnf (absFuel r) k).modelClass
      ↔ maxSlice (N.demonicTangibleCredal hr k) ν :=
  (N.su_ispn_demonic_adequacy hr k ν).trans
    (N.ispn_demonic_maxSlice hr k ν).symm

end FinISPN

/-! ## Controls

Second witnesses at the designed mutant loci, reusing the cascade
face's shipped control net.  The headline control is the
**refutation**: the donor's branch-level hypothesis fails on the very
net this species ships, which is what makes the subclass repair
necessary rather than fastidious. -/

namespace SpnDemonicControls

open FinISPN SpnCascadeControls

/-- **The refutation, concretely.**  `net₁` refutes the donor's
branch-level Zeno certificate *for every rank at once*: at the
capacity-blocked marking `i11` the move transition is disabled, so its
branch row is the zero-time self-loop and no rank can strictly
decrease along it.

This is the leg's honest headline: `ma_demonic_adequacy` is not merely
unproven at `compileIspn`, it is inapplicable — its hypothesis is
false on the shipped example. -/
theorem net₁_not_branchZenoFree (r : net₁.Vanishing → ℕ) :
    ¬ net₁.toFinMA.BranchZenoFree r :=
  net₁.not_branchZenoFree_of_disabled
    (i := i11) (u := 1) (by decide) r

/-- The uniform scheduler is a member of `net₁`'s arena — the
subclass is inhabited at the concrete net. -/
def net₁_uniformResp : net₁.RespScheduler := net₁.uniformResp

/-- The uniform member's tangible path law is in `net₁`'s demonic
law-set: the community's randomization is one adversary among the
quantified family. -/
theorem net₁_uniform_mem (k : ℕ) :
    net₁.demonicTangibleLaws net₁_rank k
      (net₁.tangiblePathLaw net₁.uniformPolicy r₁
        (net₁.respZenoFree net₁_rank net₁.uniformResp) k) :=
  ⟨net₁.uniformResp, singletonC_self _⟩

/-- The compiled demonic reading admits the uniform member's law at
`net₁` — the square's positive face, concretely. -/
theorem net₁_demonicC_uniform (k : ℕ) :
    net₁.ispnDemonicC (absFuel r₁) k
      (net₁.tangiblePathLaw net₁.uniformPolicy r₁
        (net₁.respZenoFree net₁_rank net₁.uniformResp) k) :=
  net₁.ispnDemonicC_uniform net₁_rank k

/-- **The arena is genuinely plural at `net₁`.**  At the conflict
marking `i10` both immediates are enabled, so the deterministic
"always discard" scheduler is a second, distinct member of the arena —
the demon has a real choice, and the set-valued face is not a
singleton in disguise.

The scheduler: at `i10` put all mass on the discard (action `0`); at
`i11` the discard is the only enabled action anyway. -/
def discardPolicy : Policy net₁.Vanishing (Fin 2) where
  choice _ u := if u = 0 then 1 else 0
  nonneg _ u := by by_cases h : u = 0 <;> simp [h]
  row_sum i := by
    rw [Fin.sum_univ_two]
    norm_num

theorem discardPolicy_respects : net₁.RespectsEnabling discardPolicy := by
  intro i u h
  have hu : u = 0 := by
    by_contra hne
    exact h (if_neg hne)
  subst hu
  fin_cases i <;> decide

/-- The always-discard adversary, as an arena member. -/
def discardResp : net₁.RespScheduler :=
  ⟨discardPolicy, discardPolicy_respects⟩

/-- The two adversaries differ as *schedulers*: the uniform one splits
the `i10` conflict evenly, the discard one does not.  (Whether their
closed path laws differ at a given horizon is a separate computation;
what this control pins is that the quantified family is indexed by a
genuinely plural arena, so the union is not a singleton by
construction.) -/
theorem arena_plural :
    (net₁.uniformResp : net₁.RespScheduler).1.choice i10 1
      ≠ discardResp.1.choice i10 1 := by
  rw [show (net₁.uniformResp : net₁.RespScheduler).1.choice i10 1
      = 2⁻¹ from by
    show (if net₁.IEnabled 1 i10.1
      then ((net₁.enabledCount i10 : ℕ) : ℚ)⁻¹ else 0) = 2⁻¹
    rw [if_pos (by decide),
      show net₁.enabledCount i10 = 2 from by decide]
    norm_num]
  show (2 : ℚ)⁻¹ ≠ (if (1 : Fin 2) = 0 then 1 else 0)
  rw [if_neg (by decide)]
  norm_num

/-- The discard adversary's law is also a member of the demonic
law-set — the second point of the set. -/
theorem net₁_discard_mem (k : ℕ) :
    net₁.demonicTangibleLaws net₁_rank k
      (net₁.tangiblePathLaw discardPolicy r₁
        (net₁.respZenoFree net₁_rank discardResp) k) :=
  ⟨discardResp, singletonC_self _⟩

end SpnDemonicControls

end Adequacy
end SuFunctor
