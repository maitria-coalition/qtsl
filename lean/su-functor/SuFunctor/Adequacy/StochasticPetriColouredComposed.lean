import SuFunctor.Adequacy.StochasticPetriColouredCascade
import SuFunctor.Adequacy.StochasticPetriFlattenAgreement

/-! # Adequacy: the coloured composed corollary of the flattening triangle

The flattening story at the **coloured** grain — premise rows, the
commuting-triangle cell, the flattening construction, and the composed
community-to-community corollary, over coloured nets with immediate
transitions (`FinCISPN`: per-place finite colour boxes, per-class
capacity, colour-dependent rates, guard cylinders, Dirac firing
measures).  The coloured companion of the uncoloured
`StochasticPetriFlatten` / `StochasticPetriComposed` /
`StochasticPetriFlattenAgreement` strata, folded into one module: the
left square (`cispn_cascade_adequacy`) was landed with its statement
shape identical to the uncoloured face precisely so that the pasting
below could consume it verbatim.

**The grain, honestly.**  At this stratum colours are static between
jumps and the colour boxes are finite, so the flattened object of a
coloured net *is* a finite continuous-time chain over tangible coloured
markings, and the execution-side square of the pasting is
`ctmc_jump_adequacy`, exactly as in the uncoloured corollary.  What is
genuinely coloured is the *content* of the transported atoms: the
compiled rate rows carry the per-colour-class census and multiplicity
dictionary, the colour-dependent rates `D_T(c)`, the guard cylinders
(through enabledness), and the Dirac firing measures (through the fired
marking) — the controls pin a branch probability that is *nothing but*
the colour dependence of a rate flowing through the flattening.

**The interface tier** states every face against a flattened
presentation on an **abstract mode carrier** with a declared mode
identification (`Mode ≃ N.Tangible`), agreement hypothesized at the
compiled atom roster of this fragment (initial rows and rate rows —
holding-time, boundary-guard, and kernel-reset atoms live at strata
this fragment does not compile).  That carrier interface is the socket
for the hybrid-side carrier identification (lex-sorted colour vectors
read as chart points of a hybrid-state space) — a consumer plugs in
there without reopening this module.

**The constructed tier** discharges the hypotheses outright: the
flattening of a coloured net, in the flattened formalism's own shape
([EB10b]'s construction at this grain) — one flattened transition per
delay transition **per colour vector**, jump intensity the coloured
ordered census times the colour-dependent rate, reset the
cascade-closed firing kernel, initial row the net's own at tangible
markings (a distribution under the initial-tangibility premise, which
carries real load exactly as in the uncoloured module).  The agreement
law is derived for every net and every declared scheduler
(`flattenChain_agree_off`, `flattenChain_agree_init`), and the
composed corollary (`flatten_composed_triangle`) — token-game community
object ≅ flattened-execution community object, by the pasted invertible
globular cell — holds with no agreement hypothesis.

**The premise rows at colour.**  `TangibleInit` and the invariant
token bound (`TokenBound`, witness-vector idiom with **colour-indexed
weights**) carry over from the uncoloured module; the per-place
colour-box premise of the community's flattening theorem — finiteness
of the colour state spaces — is carried *by the formation itself* at
this fragment (the boxes are finite types by construction), so the one
premise the uncoloured module could only name is discharged
definitionally here.  `FlattenPremises` bundles the rows; entry points
consume the bundle whole.

**The grade, stated exactly**: the composed corollary extends the
uncoloured G4-free finite-jump-skeleton analogue of Everdij–Blom's
transport theorem to the coloured grain, *with its own restriction
clause*: Dirac firing measures (the v1 slice — kernel-valued firing
measures are the named extension), finite colour boxes, colours static
between jumps.  Different conclusion, different observational grain
from the community's process-level bisimulation; neither implies the
other, exactly as the uncoloured module states its own boundary.

**Deliberately separate, named** (the honest-partial boundary):
(i) the hybrid-grain reading of the flattened object — continuous
colour spaces with colour flow between jumps, the lex-sorted
colour-vector/chart-point identification with its padded or
mode-indexed dimensions, and the martingale-problem square on the
execution side — consumes this module's interface tier when its own
ingredients land, and nothing here entrenches against it;
(ii) kernel-valued firing measures (the finite-mixture donor lives
with the hybrid development); (iii) coloured demonic/angelic directed
composed faces — the coloured demonic arena is its own module's row,
and the directed tier lands beside it; (iv) the TIME-indexed
comparison, exactly as the uncoloured corollary ships it: the
exit-rate *data* agrees here, the transient reads live with the killed
time-indexed development. -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Finset

variable {P T U : Type} [Fintype P] [DecidableEq P] [Fintype T]
  [Fintype U] {K : P → Type} [∀ p, Fintype (K p)]
  [∀ p, DecidableEq (K p)] {B : ℕ}

/-! ## The consumed-block/demand comparison

The consumed block of a colour vector is a sub-block of its full arc
demand, per colour class — the coloured face of "the reservation
includes the consumption". -/

namespace Coloured

omit [Fintype P] [DecidableEq P] [∀ p, Fintype (K p)] in
/-- The consumed-block count is bounded by the full class demand: the
consumed arcs embed into all arcs by the block inclusion. -/
theorem consCount_le_vecDemand {pre rd : P → ℕ}
    (κ : ∀ p, Fin (pre p + rd p) → K p) (p : P) (c : K p) :
    consCount κ p c ≤ vecDemand κ p c := by
  unfold consCount vecDemand
  refine Finset.card_le_card_of_injOn (Fin.castAdd (rd p))
    (fun j hj => Finset.mem_filter.mpr
      ⟨mem_univ _, (Finset.mem_filter.mp hj).2⟩)
    (fun x _ y _ h => ?_)
  have hv := congrArg Fin.val h
  exact Fin.ext hv

end Coloured

/-! ## The coloured weighted token count -/

/-- The weighted token count of a coloured marking under a
colour-indexed place weighting. -/
def cwsum (w : ∀ p, K p → ℕ) (m : CMarking P K B) : ℕ :=
  ∑ p, ∑ c, w p c * (m p c : ℕ)

namespace FinCISPN

variable (N : FinCISPN P T U K B)

/-! ## Premise row: initial tangibility -/

/-- **The initial-tangibility premise** at colour ([EB10b] Thm 5.2's
"no immediate transition enabled initially", at the initial-support
grain): vanishing coloured markings carry no initial mass.  Decidable,
so concrete nets discharge it by computation. -/
def TangibleInit : Prop :=
  ∀ m : CMarking P K B, N.IsVanishing m → N.delay.init m = 0

instance : Decidable N.TangibleInit :=
  inferInstanceAs
    (Decidable (∀ m, N.IsVanishing m → N.delay.init m = 0))

/-- Under the initial-tangibility premise the closed chain's initial
distribution is the net's on the nose — the landed receipt, consumed
at the premise row. -/
theorem tangibleChain_init_eq_of_tangibleInit (h : N.TangibleInit)
    (σ : Policy N.Vanishing N.IAct) (r : N.Vanishing → ℕ)
    (hr : ZenoFree (N.toFinMA.imStep σ) r) (s : N.Tangible) :
    (N.tangibleChain σ r hr).init s = N.delay.init s.1 :=
  N.tangibleChain_init_of_tangible σ r hr h s

/-! ## Premise row: the invariant token bound, witness-vector idiom

Colour-indexed weights: the certificate may count a red token
differently from a blue one, and the step conditions read the
consumed and produced colour counts of each transition *at each
colour vector* — decidable arithmetic on the arc data, as in the
uncoloured module. -/

/-- **The invariant-bounded-token-count premise at colour, as a
certificate**: a positive colour-indexed place weighting under which
no transition of either species increases the weighted token count,
at any colour vector. -/
structure TokenBound (N : FinCISPN P T U K B) where
  /-- The witness vector: a weight per place and colour. -/
  w : ∀ p, K p → ℕ
  /-- Positivity: every colour class is genuinely counted. -/
  pos : ∀ p c, 0 < w p c
  /-- Delay transitions do not increase the weighted count, at any
  colour vector. -/
  delay_le : ∀ (t : T) (κ : N.delay.CVec t),
    (∑ p, ∑ c, w p c * Coloured.prodCount (N.delay.reset t κ) p c)
      ≤ ∑ p, ∑ c, w p c * Coloured.consCount κ p c
  /-- Immediate transitions do not increase the weighted count, at
  any colour vector. -/
  imm_le : ∀ a : N.IAct,
    (∑ p, ∑ c, w p c * Coloured.prodCount (N.ireset a.1 a.2) p c)
      ≤ ∑ p, ∑ c, w p c * Coloured.consCount a.2 p c

omit [Fintype T] [Fintype U] in
/-- The fired marking's count at a place and colour, under
enabledness: the capacity truncation is inert, and the outcome is the
exact per-class arithmetic one. -/
theorem fire_val_of_enabled (t : T) (κ : N.delay.CVec t)
    (m : CMarking P K B) (ht : N.delay.Enabled t κ m) (p : P)
    (c : K p) :
    (N.delay.fire t κ m p c : ℕ)
      = (m p c : ℕ) - Coloured.consCount κ p c
        + Coloured.prodCount (N.delay.reset t κ) p c := by
  show min (Coloured.outAt κ (N.delay.reset t κ) m p c) B = _
  rw [min_eq_left (ht.1 p c).2]
  rfl

omit [Fintype T] [Fintype U] in
/-- The immediate twin. -/
theorem ifire_val_of_enabled (a : N.IAct) (m : CMarking P K B)
    (ha : N.IEnabled a m) (p : P) (c : K p) :
    (N.ifire a m p c : ℕ)
      = (m p c : ℕ) - Coloured.consCount a.2 p c
        + Coloured.prodCount (N.ireset a.1 a.2) p c := by
  show min (Coloured.outAt a.2 (N.ireset a.1 a.2) m p c) B = _
  rw [min_eq_left (ha.1 p c).2]
  rfl

omit [Fintype T] [Fintype U] in
/-- **Step soundness, delay species**: an enabled delay firing does
not increase the weighted token count.  Enabledness is load-bearing
twice — it keeps the truncation inert and the reservation supplied,
per colour class. -/
theorem cwsum_fire_le (tb : N.TokenBound) (t : T)
    (κ : N.delay.CVec t) (m : CMarking P K B)
    (ht : N.delay.Enabled t κ m) :
    cwsum tb.w (N.delay.fire t κ m) ≤ cwsum tb.w m := by
  have hcons : ∀ p c, Coloured.consCount κ p c ≤ (m p c : ℕ) :=
    fun p c => le_trans (Coloured.consCount_le_vecDemand κ p c)
      (ht.1 p c).1
  calc cwsum tb.w (N.delay.fire t κ m)
      = (∑ p, ∑ c, tb.w p c * ((m p c : ℕ) - Coloured.consCount κ p c))
          + ∑ p, ∑ c,
              tb.w p c * Coloured.prodCount (N.delay.reset t κ) p c := by
        unfold cwsum
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [N.fire_val_of_enabled t κ m ht p c, Nat.mul_add]
    _ ≤ (∑ p, ∑ c, tb.w p c * ((m p c : ℕ) - Coloured.consCount κ p c))
          + ∑ p, ∑ c, tb.w p c * Coloured.consCount κ p c :=
        Nat.add_le_add_left (tb.delay_le t κ) _
    _ = cwsum tb.w m := by
        unfold cwsum
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← Nat.mul_add, Nat.sub_add_cancel (hcons p c)]

omit [Fintype T] [Fintype U] in
/-- **Step soundness, immediate species.** -/
theorem cwsum_ifire_le (tb : N.TokenBound) (a : N.IAct)
    (m : CMarking P K B) (ha : N.IEnabled a m) :
    cwsum tb.w (N.ifire a m) ≤ cwsum tb.w m := by
  have hcons : ∀ p c, Coloured.consCount a.2 p c ≤ (m p c : ℕ) :=
    fun p c => le_trans (Coloured.consCount_le_vecDemand a.2 p c)
      (ha.1 p c).1
  calc cwsum tb.w (N.ifire a m)
      = (∑ p, ∑ c, tb.w p c * ((m p c : ℕ) - Coloured.consCount a.2 p c))
          + ∑ p, ∑ c,
              tb.w p c * Coloured.prodCount (N.ireset a.1 a.2) p c := by
        unfold cwsum
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [N.ifire_val_of_enabled a m ha p c, Nat.mul_add]
    _ ≤ (∑ p, ∑ c, tb.w p c * ((m p c : ℕ) - Coloured.consCount a.2 p c))
          + ∑ p, ∑ c, tb.w p c * Coloured.consCount a.2 p c :=
        Nat.add_le_add_left (tb.imm_le a) _
    _ = cwsum tb.w m := by
        unfold cwsum
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← Nat.mul_add, Nat.sub_add_cancel (hcons p c)]

/-- Reachability by enabled firings of either species, at colour. -/
inductive Reach (N : FinCISPN P T U K B) (m : CMarking P K B) :
    CMarking P K B → Prop
  | refl : Reach N m m
  | delay {m' : CMarking P K B} (t : T) (κ : N.delay.CVec t)
      (h : Reach N m m') (ht : N.delay.Enabled t κ m') :
      Reach N m (N.delay.fire t κ m')
  | imm {m' : CMarking P K B} (a : N.IAct) (h : Reach N m m')
      (ha : N.IEnabled a m') : Reach N m (N.ifire a m')

omit [Fintype T] [Fintype U] in
/-- The weighted count is non-increasing along reachability. -/
theorem cwsum_le_of_reach (tb : N.TokenBound) {m m' : CMarking P K B}
    (h : N.Reach m m') : cwsum tb.w m' ≤ cwsum tb.w m := by
  induction h with
  | refl => exact le_rfl
  | delay t κ h ht ih => exact le_trans (N.cwsum_fire_le tb t κ _ ht) ih
  | imm a h ha ih => exact le_trans (N.cwsum_ifire_le tb a _ ha) ih

omit [Fintype T] [Fintype U] in
/-- **The intrinsic per-class token bound**: every reachable marking's
count at every place and colour is bounded by the initial weighted
count — the witness vector and the initial marking alone, no declared
capacity consulted.  This is the clause a finite mode roster consumes
at an unbounded-count grain. -/
theorem count_le_of_reach (tb : N.TokenBound) {m m' : CMarking P K B}
    (h : N.Reach m m') (p : P) (c : K p) :
    (m' p c : ℕ) ≤ cwsum tb.w m :=
  le_trans
    (le_trans (Nat.le_mul_of_pos_left _ (tb.pos p c))
      (le_trans
        (Finset.single_le_sum (f := fun d => tb.w p d * (m' p d : ℕ))
          (fun _ _ => Nat.zero_le _) (mem_univ c))
        (Finset.single_le_sum
          (f := fun q => ∑ d, tb.w q d * (m' q d : ℕ))
          (fun _ _ => Nat.zero_le _) (mem_univ p))))
    (N.cwsum_le_of_reach tb h)

/-! ## The premise bundle -/

/-- **The flattening's definedness premises, bundled, at colour**:
initial tangibility, the invariant token bound, and cascade
termination.  The community's remaining premise — per-place colour-box
discharge — is carried by the formation itself at this fragment: the
colour boxes are finite types by construction, so the one row the
uncoloured module could only name is discharged definitionally
here. -/
structure FlattenPremises (N : FinCISPN P T U K B) where
  /-- No initial mass on vanishing markings. -/
  init_tangible : N.TangibleInit
  /-- The invariant token bound, colour-indexed witness-vector
  idiom. -/
  bound : N.TokenBound
  /-- The cascade rank. -/
  rank : N.Vanishing → ℕ
  /-- Cascade termination, certified by the rank. -/
  cascade : N.CascadeRank rank

/-! ## The interface tier: the triangle and its composed faces, from
agreement

Every statement takes the flattened presentation on an abstract mode
carrier with a declared identification `e : Mode ≃ N.Tangible`, and
the atom-transport agreement at this fragment's compiled atom roster
(initial rows and rate rows) as hypotheses `hoff`/`hinit` — the socket
the hybrid-side carrier identification plugs into. -/

/-- **The commuting triangle, packaged from agreement, at colour**: if
the flat presentation, transported along the mode identification,
agrees with the scheduler-closed net off-diagonally and initially,
then the net-compiled reading and the flatten-compiled reading denote
isomorphic constraints — an invertible globular cell of
`Crd (Traj N.Tangible k)`, at every jump horizon. -/
theorem flatten_triangle_of_agree (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ r hr).rate s s')
    (hinit : (flat.relabel e).init = (N.toFinMA.close σ r hr).init)
    (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ α : Cell
        (looseConj (atoms (jumpRows
          (closeMaRows N.compileCispn (compilePolicy σ) (absFuel r))) k) :
          Loose a a)
        (looseConj (atoms (jumpRows (compileCtmc (flat.relabel e))) k))
        (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  refine Crd.looseIso_ofIff fun μ => ?_
  rw [N.compile_cispn_comm, compile_closeMa_comm N.toFinMA σ r hr,
    compile_jump_comm (N.toFinMA.close σ r hr),
    compile_jump_comm (flat.relabel e),
    satAtoms_iff (compile_wf (N.toFinMA.close σ r hr).jumpChain) μ,
    satAtoms_iff (compile_wf (flat.relabel e).jumpChain) μ]
  show μ = (N.toFinMA.close σ r hr).jumpLaw k
    ↔ μ = (flat.relabel e).jumpLaw k
  rw [FinCTMC.jumpLaw_diag_blind (flat.relabel e)
    (N.toFinMA.close σ r hr) hoff hinit k]

/-- **The killed-jump-skeleton agreement from agreement** — the
law-level face: the flattened presentation's community law *is* the
net's tangible path law, at every jump horizon; diagonal-blindness
and nothing else. -/
theorem flatten_skeleton_agreement_of_agree
    (σ : Policy N.Vanishing N.IAct) (r : N.Vanishing → ℕ)
    (hr : ZenoFree (N.toFinMA.imStep σ) r)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ r hr).rate s s')
    (hinit : (flat.relabel e).init = (N.toFinMA.close σ r hr).init)
    (k : ℕ) :
    (flat.relabel e).jumpLaw k = N.tangiblePathLaw σ r hr k :=
  FinCTMC.jumpLaw_diag_blind _ _ hoff hinit k

/-- **The composed corollary of the flattening triangle at colour,
precise face, from agreement**: the token-game community object and
the flattened-execution community object are isomorphic by an
invertible globular cell, at every jump horizon.

The proof is a *pasting*, never a re-derivation: the coloured net
square's cascade face, the triangle cell, and the flattened object's
jump-chain square, composed as entailments in the thin double
category, both directions; invertibility is thinness. -/
theorem flatten_composed_triangle_of_agree
    (σ : Policy N.Vanishing N.IAct) (r : N.Vanishing → ℕ)
    (hr : ZenoFree (N.toFinMA.imStep σ) r)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ r hr).rate s s')
    (hinit : (flat.relabel e).init = (N.toFinMA.close σ r hr).init)
    (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ α : Cell
        (singletonC (N.tangiblePathLaw σ r hr k) : Loose a a)
        (singletonC ((flat.relabel e).jumpLaw k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  obtain ⟨α₁, β₁, -, -⟩ := N.cispn_cascade_adequacy σ r hr k (a := a)
  obtain ⟨α₂, β₂, -, -⟩ :=
    N.flatten_triangle_of_agree σ r hr e flat hoff hinit k (a := a)
  obtain ⟨α₃, β₃, -, -⟩ := ctmc_jump_adequacy (flat.relabel e) k (a := a)
  exact ⟨Crd.cellOfEntails fun μ h =>
      Crd.entailsOfCell α₃ μ (Crd.entailsOfCell α₂ μ
        (Crd.entailsOfCell β₁ μ h)),
    Crd.cellOfEntails fun μ h =>
      Crd.entailsOfCell α₁ μ (Crd.entailsOfCell β₂ μ
        (Crd.entailsOfCell β₃ μ h)),
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- **The connector face from agreement**: the two community-vocabulary
trajectory constructions — the net's observed tangible process and the
flattened chain's jump chain, each through the standard monadic
construction — agree, at every jump horizon. -/
theorem flatten_connector_agreement_of_agree
    (σ : Policy N.Vanishing N.IAct) (r : N.Vanishing → ℕ)
    (hr : ZenoFree (N.toFinMA.imStep σ) r)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ r hr).rate s s')
    (hinit : (flat.relabel e).init = (N.toFinMA.close σ r hr).init)
    (k : ℕ) :
    (N.tangibleChain σ r hr).jumpTrajPMF k
      = (flat.relabel e).jumpTrajPMF k := by
  have hlaw : (flat.relabel e).jumpLaw k
      = (N.tangibleChain σ r hr).jumpLaw k :=
    FinCTMC.jumpLaw_diag_blind _ _ hoff hinit k
  refine PMF.ext fun ω => ?_
  rw [FinCTMC.jumpTrajPMF_eq, FinCTMC.jumpTrajPMF_eq, hlaw]

/-- **The semantic-universe face from agreement**: a law's ideal point
models the flattened compiled presentation exactly when it models the
coloured net's compiled presentation — the pasting read at the
judgment stratum. -/
theorem su_flatten_composed_of_agree (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ r hr).rate s s')
    (hinit : (flat.relabel e).init = (N.toFinMA.close σ r hr).init)
    (k : ℕ) (μ : SubPMF (Traj N.Tangible k)) :
    idealPoint μ
        ∈ (ctmcJumpDnf (compileCtmc (flat.relabel e)) k).modelClass
      ↔ idealPoint μ ∈ (N.cispnDnf σ r k).modelClass := by
  rw [su_ctmc_jump_adequacy (flat.relabel e) k μ,
    N.su_cispn_cascade_adequacy σ r hr k μ,
    N.flatten_skeleton_agreement_of_agree σ r hr e flat hoff hinit k]

/-- **Exit-rate agreement from agreement** — the honest time-content
at this grain: the flattened chain and the closed net chain carry the
same exit-rate family, so the holding-time *data* of the two readings
coincide.  Data-level agreement, never analysis. -/
theorem flatten_exitRate_agree_of_agree (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ r hr).rate s s')
    (s : N.Tangible) :
    (flat.relabel e).exitRate s
      = (N.tangibleChain σ r hr).exitRate s := by
  unfold FinCTMC.exitRate
  refine Finset.sum_congr rfl fun s' _ => ?_
  by_cases h : s = s'
  · rw [h, FinCTMC.offRate_diag, FinCTMC.offRate_diag]
  · rw [FinCTMC.offRate_of_ne _ h, FinCTMC.offRate_of_ne _ h]
    exact hoff s s' h

/-! ## The flattening, constructed -/

/-- **The flattened chain of a coloured net, constructed** — the
community's flattening in the flattened formalism's own shape at
colour: one flattened transition per delay transition **per colour
vector**, each contributing its race intensity (coloured ordered
census × colour-dependent rate) through the cascade-closed reset
(absorption of its Dirac-fired marking under the declared scheduler,
within the rank's working fuel); the initial row is the net's own,
read at the tangible markings — a distribution by the
initial-tangibility premise.  The stored diagonal is construction data
the jump law never reads. -/
def flattenChain (σ : Policy N.Vanishing N.IAct) (r : N.Vanishing → ℕ)
    (hti : N.TangibleInit) : FinCTMC N.Tangible where
  rate s s' := ∑ t, ∑ κ : N.delay.CVec t,
    if N.delay.Enabled t κ s.1
    then (N.delay.raceCount t κ s.1 : ℚ) * N.delay.rate t κ
      * N.toFinMA.absorb σ r (N.toSum (N.delay.fire t κ s.1)) s'
    else 0
  init s := N.delay.init s.1
  rate_nonneg s s' _ := Finset.sum_nonneg fun t _ =>
    Finset.sum_nonneg fun κ _ => by
      by_cases h : N.delay.Enabled t κ s.1
      · rw [if_pos h]
        exact mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (N.delay.rate_nonneg t κ))
          (N.toFinMA.absorb_nonneg σ r _ s')
      · rw [if_neg h]
  init_nonneg s := N.delay.init_nonneg s.1
  init_sum := by
    have hz : ∀ i : N.Vanishing,
        N.delay.init (N.ofSum (Sum.inr i)) = 0 :=
      fun i => hti i.1 i.2
    have h : ∑ x : N.Tangible ⊕ N.Vanishing,
        N.delay.init (N.ofSum x) = 1 :=
      (Equiv.sum_comp N.markingEquiv N.delay.init).trans
        N.delay.init_sum
    rw [Fintype.sum_sum_type,
      Finset.sum_congr rfl fun i _ => hz i, Finset.sum_const_zero,
      add_zero] at h
    exact h

@[simp] theorem flattenChain_rate (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hti : N.TangibleInit) (s s' : N.Tangible) :
    (N.flattenChain σ r hti).rate s s'
      = ∑ t, ∑ κ : N.delay.CVec t,
          if N.delay.Enabled t κ s.1
          then (N.delay.raceCount t κ s.1 : ℚ) * N.delay.rate t κ
            * N.toFinMA.absorb σ r (N.toSum (N.delay.fire t κ s.1)) s'
          else 0 := rfl

@[simp] theorem flattenChain_init (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hti : N.TangibleInit) (s : N.Tangible) :
    (N.flattenChain σ r hti).init s = N.delay.init s.1 := rfl

/-! ## The agreement law, derived

Rate rows: the house closure sums races grouped by intermediate
marking; the flattening sums them per (transition, colour vector).
Off-diagonally the regrouping is exact — each enabled pair's indicator
collapses at its own fired marking, and the diagonal guard separating
the two reads is invisible because the hit kernel sends direct-return
mass to the diagonal only.  Initial rows: the landed
initial-tangibility receipt, consumed not re-proved. -/

/-- **The rate-row atom transport, derived from the construction, at
colour**: off-diagonally, the constructed flattening's rate is the
scheduler-closed net's — for every coloured net, scheduler, and rank.
The `hoff` obligation of every interface-tier theorem, discharged. -/
theorem flattenChain_agree_off (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (hti : N.TangibleInit) :
    ∀ s s' : N.Tangible, s ≠ s' →
      (N.flattenChain σ r hti).rate s s'
        = (N.toFinMA.close σ r hr).rate s s' := by
  intro s s' hne
  rw [FinMA.close_rate]
  have habs_diag : N.toFinMA.absorb σ r (Sum.inl s) s' = 0 := by
    show absorbIter (N.toFinMA.imStep σ) (absFuel r) (Sum.inl s) s' = 0
    rw [absorbIter_inl, hitMass_inl, if_neg hne]
  have hstep1 : ∀ x : N.Tangible ⊕ N.Vanishing,
      N.toFinMA.offRate s x * N.toFinMA.absorb σ r x s'
        = N.delay.raceRate s.1 (N.ofSum x)
            * N.toFinMA.absorb σ r x s' := by
    intro x
    by_cases hx : Sum.inl s = x
    · rw [← hx, FinMA.offRate_diag, habs_diag, zero_mul, mul_zero]
    · rw [N.toFinMA.offRate_of_ne hx, toFinMA_rate]
  have hexpand : ∀ x : N.Tangible ⊕ N.Vanishing,
      N.delay.raceRate s.1 (N.ofSum x) * N.toFinMA.absorb σ r x s'
        = ∑ t, ∑ κ : N.delay.CVec t,
            if N.delay.Enabled t κ s.1
                ∧ N.delay.fire t κ s.1 = N.ofSum x
            then (N.delay.raceCount t κ s.1 : ℚ) * N.delay.rate t κ
              * N.toFinMA.absorb σ r x s'
            else 0 := by
    intro x
    show (∑ t, ∑ κ : N.delay.CVec t,
        if N.delay.Enabled t κ s.1 ∧ N.delay.fire t κ s.1 = N.ofSum x
        then (N.delay.raceCount t κ s.1 : ℚ) * N.delay.rate t κ
        else 0)
        * N.toFinMA.absorb σ r x s' = _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [ite_mul, zero_mul]
  have hcollapse : ∀ (t : T) (κ : N.delay.CVec t),
      (∑ x : N.Tangible ⊕ N.Vanishing,
        if N.delay.Enabled t κ s.1 ∧ N.delay.fire t κ s.1 = N.ofSum x
        then (N.delay.raceCount t κ s.1 : ℚ) * N.delay.rate t κ
          * N.toFinMA.absorb σ r x s'
        else 0)
      = if N.delay.Enabled t κ s.1
        then (N.delay.raceCount t κ s.1 : ℚ) * N.delay.rate t κ
          * N.toFinMA.absorb σ r (N.toSum (N.delay.fire t κ s.1)) s'
        else 0 := by
    intro t κ
    by_cases hen : N.delay.Enabled t κ s.1
    · have hiff : ∀ x : N.Tangible ⊕ N.Vanishing,
          (N.delay.Enabled t κ s.1 ∧ N.delay.fire t κ s.1 = N.ofSum x)
            ↔ N.toSum (N.delay.fire t κ s.1) = x := by
        intro x
        constructor
        · rintro ⟨-, hfx⟩
          rw [hfx, toSum_ofSum]
        · rintro rfl
          exact ⟨hen, (N.ofSum_toSum _).symm⟩
      rw [if_pos hen,
        Finset.sum_congr rfl fun x _ => if_congr (hiff x) rfl rfl,
        Finset.sum_ite_eq univ (N.toSum (N.delay.fire t κ s.1))
          (fun x => (N.delay.raceCount t κ s.1 : ℚ) * N.delay.rate t κ
            * N.toFinMA.absorb σ r x s'),
        if_pos (mem_univ _)]
    · rw [if_neg hen]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [if_neg fun h => hen h.1]
  calc (N.flattenChain σ r hti).rate s s'
      = ∑ t, ∑ κ : N.delay.CVec t,
          if N.delay.Enabled t κ s.1
          then (N.delay.raceCount t κ s.1 : ℚ) * N.delay.rate t κ
            * N.toFinMA.absorb σ r (N.toSum (N.delay.fire t κ s.1)) s'
          else 0 := rfl
    _ = ∑ t, ∑ κ : N.delay.CVec t, ∑ x : N.Tangible ⊕ N.Vanishing,
          if N.delay.Enabled t κ s.1 ∧ N.delay.fire t κ s.1 = N.ofSum x
          then (N.delay.raceCount t κ s.1 : ℚ) * N.delay.rate t κ
            * N.toFinMA.absorb σ r x s'
          else 0 :=
        Finset.sum_congr rfl fun t _ =>
          Finset.sum_congr rfl fun κ _ => (hcollapse t κ).symm
    _ = ∑ t, ∑ x : N.Tangible ⊕ N.Vanishing, ∑ κ : N.delay.CVec t,
          if N.delay.Enabled t κ s.1 ∧ N.delay.fire t κ s.1 = N.ofSum x
          then (N.delay.raceCount t κ s.1 : ℚ) * N.delay.rate t κ
            * N.toFinMA.absorb σ r x s'
          else 0 :=
        Finset.sum_congr rfl fun t _ => Finset.sum_comm
    _ = ∑ x : N.Tangible ⊕ N.Vanishing, ∑ t, ∑ κ : N.delay.CVec t,
          if N.delay.Enabled t κ s.1 ∧ N.delay.fire t κ s.1 = N.ofSum x
          then (N.delay.raceCount t κ s.1 : ℚ) * N.delay.rate t κ
            * N.toFinMA.absorb σ r x s'
          else 0 := Finset.sum_comm
    _ = ∑ x : N.Tangible ⊕ N.Vanishing,
          N.delay.raceRate s.1 (N.ofSum x)
            * N.toFinMA.absorb σ r x s' :=
        Finset.sum_congr rfl fun x _ => (hexpand x).symm
    _ = ∑ x : N.Tangible ⊕ N.Vanishing,
          N.toFinMA.offRate s x * N.toFinMA.absorb σ r x s' :=
        Finset.sum_congr rfl fun x _ => (hstep1 x).symm

/-- **The initial-row atom transport, derived from the construction**:
the constructed flattening's initial row is the scheduler-closed
net's — the landed initial-tangibility receipt, consumed at the
premise row.  The `hinit` obligation of every interface-tier theorem,
discharged. -/
theorem flattenChain_agree_init (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (hti : N.TangibleInit) :
    (N.flattenChain σ r hti).init = (N.toFinMA.close σ r hr).init := by
  funext s
  exact (N.tangibleChain_init_of_tangible σ r hr hti s).symm

/-! ## The discharged tier

Every interface-tier statement, instantiated at the constructed
flattening with the agreement supplied — the carrier identification is
the identity enumeration, and transport along it is definitionally
invisible. -/

/-- **The commuting triangle at colour, kernel-checked outright**: the
net-compiled reading and the constructed flattening's compiled reading
denote isomorphic constraints — no agreement hypothesis. -/
theorem flatten_triangle (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (hti : N.TangibleInit) (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ α : Cell
        (looseConj (atoms (jumpRows
          (closeMaRows N.compileCispn (compilePolicy σ) (absFuel r))) k) :
          Loose a a)
        (looseConj (atoms (jumpRows
          (compileCtmc (N.flattenChain σ r hti))) k))
        (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  N.flatten_triangle_of_agree σ r hr (Equiv.refl _)
    (N.flattenChain σ r hti)
    (N.flattenChain_agree_off σ r hr hti)
    (N.flattenChain_agree_init σ r hr hti) k

/-- **The killed-jump-skeleton agreement, kernel-checked outright**:
the constructed flattening's community law *is* the coloured net's
tangible path law, at every jump horizon. -/
theorem flatten_skeleton_agreement (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (hti : N.TangibleInit) (k : ℕ) :
    (N.flattenChain σ r hti).jumpLaw k = N.tangiblePathLaw σ r hr k :=
  N.flatten_skeleton_agreement_of_agree σ r hr (Equiv.refl _)
    (N.flattenChain σ r hti)
    (N.flattenChain_agree_off σ r hr hti)
    (N.flattenChain_agree_init σ r hr hti) k

/-- **The coloured composed corollary, kernel-checked outright**:
token-game community object and flattened-execution community object,
isomorphic by the pasted invertible cell, on the constructed
flattening — the coloured extension of the G4-free
finite-jump-skeleton analogue, at the Dirac slice, with zero
hypotheses on the constructed object. -/
theorem flatten_composed_triangle (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (hti : N.TangibleInit) (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ α : Cell
        (singletonC (N.tangiblePathLaw σ r hr k) : Loose a a)
        (singletonC ((N.flattenChain σ r hti).jumpLaw k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  N.flatten_composed_triangle_of_agree σ r hr (Equiv.refl _)
    (N.flattenChain σ r hti)
    (N.flattenChain_agree_off σ r hr hti)
    (N.flattenChain_agree_init σ r hr hti) k

/-- The connector face on the constructed flattening. -/
theorem flatten_connector_agreement (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (hti : N.TangibleInit) (k : ℕ) :
    (N.tangibleChain σ r hr).jumpTrajPMF k
      = (N.flattenChain σ r hti).jumpTrajPMF k :=
  N.flatten_connector_agreement_of_agree σ r hr (Equiv.refl _)
    (N.flattenChain σ r hti)
    (N.flattenChain_agree_off σ r hr hti)
    (N.flattenChain_agree_init σ r hr hti) k

/-- The semantic-universe face on the constructed flattening. -/
theorem su_flatten_composed (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (hti : N.TangibleInit) (k : ℕ) (μ : SubPMF (Traj N.Tangible k)) :
    idealPoint μ
        ∈ (ctmcJumpDnf (compileCtmc (N.flattenChain σ r hti))
            k).modelClass
      ↔ idealPoint μ ∈ (N.cispnDnf σ r k).modelClass :=
  N.su_flatten_composed_of_agree σ r hr (Equiv.refl _)
    (N.flattenChain σ r hti)
    (N.flattenChain_agree_off σ r hr hti)
    (N.flattenChain_agree_init σ r hr hti) k μ

/-- The holding-time data agreement on the constructed flattening. -/
theorem flatten_exitRate_agree (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (hti : N.TangibleInit) (s : N.Tangible) :
    (N.flattenChain σ r hti).exitRate s
      = (N.tangibleChain σ r hr).exitRate s :=
  N.flatten_exitRate_agree_of_agree σ r hr (Equiv.refl _)
    (N.flattenChain σ r hti)
    (N.flattenChain_agree_off σ r hr hti) s

/-! ## The premise-bundle entry points

The community's premise set, consumed whole, for any
enabling-respecting scheduler — the coloured demonic arena's packaged
scheduler subtype is that module's own row; here the respecting
hypothesis is taken bare. -/

/-- The killed-jump-skeleton agreement from the premise bundle. -/
theorem flatten_skeleton_agreement_of_premises
    (prem : N.FlattenPremises) (σ : Policy N.Vanishing N.IAct)
    (hσ : N.RespectsEnabling σ) (k : ℕ) :
    (N.flattenChain σ prem.rank prem.init_tangible).jumpLaw k
      = N.tangiblePathLaw σ prem.rank
          (N.zenoFree_of_cascadeRank σ hσ prem.cascade) k :=
  N.flatten_skeleton_agreement σ prem.rank
    (N.zenoFree_of_cascadeRank σ hσ prem.cascade) prem.init_tangible k

/-- The composed corollary from the premise bundle. -/
theorem flatten_composed_triangle_of_premises
    (prem : N.FlattenPremises) (σ : Policy N.Vanishing N.IAct)
    (hσ : N.RespectsEnabling σ) (k : ℕ)
    {a : Crd (Traj N.Tangible k)} :
    ∃ α : Cell
        (singletonC (N.tangiblePathLaw σ prem.rank
          (N.zenoFree_of_cascadeRank σ hσ prem.cascade) k) : Loose a a)
        (singletonC ((N.flattenChain σ prem.rank
          prem.init_tangible).jumpLaw k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  N.flatten_composed_triangle σ prem.rank
    (N.zenoFree_of_cascadeRank σ hσ prem.cascade) prem.init_tangible k

end FinCISPN

/-! ## Controls: the colour-dependent rate through the flattening

A coloured net no uncoloured formation can express, end-to-end: one
place, red and blue at capacity two; a delay transition consuming one
token and depositing the *opposite* colour, racing at rate `2` on red
selections and `3` on blue; an immediate transition consuming a **blue
pair** under an all-blue guard cylinder and depositing one red.  The
classification reads colours three ways (guard-blocked mixed pairs,
class-undersupplied blue pairs, and one *capacity*-tangible marking);
the flattening closes a genuinely coloured cascade; and the flattened
jump chain's branch split at the one-of-each marking is `2/5` against
`3/5` — **nothing but** the colour-dependence of the rate, flowing
through the flattening into the community law, where it is consumed
as a token-game verdict by transport.  Proofs ride `decide` at the
marking grain and `Finset.sum_eq_single_of_mem` + `norm_num` at the
rational grain, per the standing kernel note. -/

namespace CspnComposedWitness

open FinCISPN

/-- Two colours on one place: `0` is red, `1` is blue. -/
abbrev Col : Fin 1 → Type := fun _ => Fin 2

/-- The marking with `a` red and `b` blue tokens (capacity 2). -/
def mc (a b : Fin 3) : CMarking (Fin 1) Col 2 :=
  fun _ c => if c = 0 then a else b

/-- The witness net: opposite-colour delay flips at colour-dependent
rates; a blue-pair immediate (all-blue guard cylinder) deposits one
red; initial mass on two red. -/
def cwnet : FinCISPN (Fin 1) (Fin 1) (Fin 1) Col 2 where
  delay :=
    { pre := fun _ _ => 1
      read := fun _ _ => 0
      post := fun _ _ => 1
      guard := fun _ _ => True
      guard_dec := fun _ _ => inferInstance
      rate := fun _ κ => if κ 0 0 = 0 then 2 else 3
      rate_nonneg := fun _ κ => by split <;> norm_num
      reset := fun _ κ _ _ => if κ 0 0 = 0 then 1 else 0
      init := fun m => if m = mc 2 0 then 1 else 0
      init_nonneg := fun m => by by_cases h : m = mc 2 0 <;> simp [h]
      init_sum :=
        Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (mem_univ _)) }
  ipre := fun _ _ => 2
  iread := fun _ _ => 0
  ipost := fun _ _ => 1
  iguard := fun _ κ => ∀ j, κ 0 j = 1
  iguard_dec := fun _ _ => inferInstance
  ireset := fun _ _ _ _ => 0

/-- The red selection vector of the delay transition. -/
def κr : cwnet.delay.CVec 0 := fun _ _ => 0

/-- The blue selection vector of the delay transition. -/
def κb : cwnet.delay.CVec 0 := fun _ _ => 1

/-- The blue-pair selection vector of the immediate transition. -/
def κbb : cwnet.IVec 0 := fun _ _ => 1

/-! ### The coloured classification -/

/-- Two blue vanish: the blue pair is supplied, in capacity, and
guard-passed. -/
theorem cwnet_v02 : cwnet.IsVanishing (mc 0 2) := by decide

/-- One red two blue vanish likewise. -/
theorem cwnet_v12 : cwnet.IsVanishing (mc 1 2) := by decide

/-- The one-of-each marking is tangible: the blue pair is
class-undersupplied and every mixed pair is guard-blocked — though
total supply would satisfy an uncoloured demand of two. -/
theorem cwnet_t11 : ¬ cwnet.IsVanishing (mc 1 1) := by decide

/-- **The capacity-tangible marking**: at two-of-each, the blue pair
is supplied and guard-passed but its red deposit would overflow the
red class — tangible by capacity alone. -/
theorem cwnet_t22 : ¬ cwnet.IsVanishing (mc 2 2) := by decide

/-- The classified elements the controls name. -/
def T00 : cwnet.Tangible := ⟨mc 0 0, by decide⟩
def T10 : cwnet.Tangible := ⟨mc 1 0, by decide⟩
def T20 : cwnet.Tangible := ⟨mc 2 0, by decide⟩
def T11 : cwnet.Tangible := ⟨mc 1 1, by decide⟩
def V02 : cwnet.Vanishing := ⟨mc 0 2, by decide⟩

/-! ### Cascade termination: the rank is a blue census -/

/-- The coloured cascade rank: the blue-token count. -/
def rC : cwnet.Vanishing → ℕ := fun i => (i.1 0 1 : ℕ)

/-- The rank certificate, by direct argument: the guard pins every
arc's selection blue, supply forces the blue count to the capacity,
and the Dirac deposit is red-only — so the blue census strictly
drops. -/
theorem cwnet_rank : cwnet.CascadeRank rC := by
  intro i a ha j hj
  obtain ⟨u, κ⟩ := a
  obtain ⟨hsup, hg⟩ := ha
  have hall : ∀ x : Fin (cwnet.ipre u 0 + cwnet.iread u 0),
      κ 0 x = 1 := hg
  have hvd : Coloured.vecDemand κ 0 (1 : Fin 2) = 2 := by
    unfold Coloured.vecDemand
    rw [Finset.filter_true_of_mem fun x _ => hall x, Finset.card_univ,
      Fintype.card_fin]
    rfl
  have hdem : 2 ≤ (i.1 0 1 : ℕ) := by
    have h := (hsup 0 1).1
    rwa [hvd] at h
  have hcc : Coloured.consCount κ 0 (1 : Fin 2) = 2 := by
    unfold Coloured.consCount
    rw [Finset.filter_true_of_mem fun x _ => hall _, Finset.card_univ,
      Fintype.card_fin]
    rfl
  have hpc : Coloured.prodCount (cwnet.ireset u κ) 0 (1 : Fin 2) = 0 := by
    unfold Coloured.prodCount
    rw [Finset.filter_false_of_mem, Finset.card_empty]
    intro x _
    show ¬ (0 : Fin 2) = 1
    decide
  have hval : j.1 = cwnet.ifire ⟨u, κ⟩ i.1 := cwnet.toSum_inr_val hj
  show (j.1 0 1 : ℕ) < (i.1 0 1 : ℕ)
  rw [hval]
  show min (Coloured.outAt κ (cwnet.ireset u κ) i.1 0 1) 2
    < (i.1 0 1 : ℕ)
  unfold Coloured.outAt
  rw [hcc, hpc, add_zero]
  exact lt_of_le_of_lt (min_le_left _ _)
    (Nat.sub_lt (lt_of_lt_of_le (by norm_num) hdem) (by norm_num))

theorem cwnet_zenoFree :
    ZenoFree (cwnet.toFinMA.imStep cwnet.uniformPolicy) rC :=
  cwnet.zenoFree_uniform cwnet_rank

/-- Initial tangibility: the two-red marking is tangible, and it
carries all the mass. -/
theorem cwnet_tangibleInit : cwnet.TangibleInit := by
  intro m hm
  have hne : m ≠ mc 2 0 := by
    rintro rfl
    exact (by decide : ¬ cwnet.IsVanishing (mc 2 0)) hm
  show (if m = mc 2 0 then (1 : ℚ) else 0) = 0
  rw [if_neg hne]

/-- The colour-indexed token bound: unit weights — both species
consume at least as many tokens as they deposit. -/
def cwnet_bound : cwnet.TokenBound where
  w := fun _ _ => 1
  pos := fun _ _ => one_pos
  delay_le := by decide
  imm_le := by decide

/-- The premise bundle at the witness. -/
def cwnet_premises : cwnet.FlattenPremises :=
  ⟨cwnet_tangibleInit, cwnet_bound, rC, cwnet_rank⟩

/-! ### The flattened object, computed -/

/-- The constructed flattening of the witness net under the uniform
scheduler. -/
def fchain : FinCTMC cwnet.Tangible :=
  cwnet.flattenChain cwnet.uniformPolicy rC cwnet_tangibleInit

/-- Absorption from a tangible start is the hit mass. -/
theorem absorb_inl (x s' : cwnet.Tangible) :
    cwnet.toFinMA.absorb cwnet.uniformPolicy rC (Sum.inl x) s'
      = if x = s' then 1 else 0 := by
  show absorbIter (cwnet.toFinMA.imStep cwnet.uniformPolicy)
    (absFuel rC) (Sum.inl x) s' = _
  rw [absorbIter_inl, hitMass_inl]

/-- Only the blue pair is enabled at two blue. -/
theorem cwnet_only_bb_02 : ∀ κ : cwnet.IVec 0, κ ≠ κbb →
    ¬ cwnet.IEnabled ⟨0, κ⟩ V02.1 := by decide

/-- The scheduler at two blue: the sole enabled pair takes the whole
mass. -/
theorem cwnet_choice_02 :
    cwnet.uniformPolicy.choice V02 ⟨0, κbb⟩ = 1 := by
  show (if cwnet.IEnabled ⟨0, κbb⟩ V02.1
    then ((cwnet.enabledCount V02 : ℕ) : ℚ)⁻¹ else 0) = 1
  rw [if_pos (by decide : cwnet.IEnabled ⟨0, κbb⟩ V02.1),
    show cwnet.enabledCount V02 = 1 from by decide]
  norm_num

/-- The blue-pair firing at two blue lands in the tangible one-red
marking — the coloured cascade step. -/
theorem ifire_02 :
    cwnet.toSum (cwnet.ifire ⟨0, κbb⟩ V02.1) = Sum.inl T10 := by
  rw [show cwnet.ifire ⟨0, κbb⟩ V02.1 = mc 1 0 from by decide]
  exact dif_neg (by decide)

/-- The mixed immediate kernel at two blue: the whole mass rides the
blue-pair firing to one red. -/
theorem cwnet_imStep_02 (y : cwnet.Tangible ⊕ cwnet.Vanishing) :
    cwnet.toFinMA.imStep cwnet.uniformPolicy V02 y
      = if (Sum.inl T10 : cwnet.Tangible ⊕ cwnet.Vanishing) = y
        then 1 else 0 := by
  show (∑ a : cwnet.IAct, cwnet.uniformPolicy.choice V02 a
      * cwnet.toFinMA.branch V02 a y) = _
  refine (Fintype.sum_sigma _).trans ?_
  rw [Fin.sum_univ_one]
  refine (Finset.sum_eq_single_of_mem κbb (mem_univ _)
    fun κ _ hκ => ?_).trans ?_
  · show (if cwnet.IEnabled ⟨0, κ⟩ V02.1
      then ((cwnet.enabledCount V02 : ℕ) : ℚ)⁻¹ else 0) * _ = 0
    rw [if_neg (cwnet_only_bb_02 κ hκ), zero_mul]
  · rw [cwnet_choice_02, one_mul]
    show (if cwnet.IEnabled ⟨0, κbb⟩ V02.1
      then (if cwnet.toSum (cwnet.ifire ⟨0, κbb⟩ V02.1) = y
        then 1 else 0)
      else (if Sum.inr V02 = y then 1 else 0)) = _
    rw [if_pos (by decide : cwnet.IEnabled ⟨0, κbb⟩ V02.1), ifire_02]

/-- Absorption from two blue: one zero-time blue-pair firing, then
absorption at one red. -/
theorem absorb_inr_02 (s' : cwnet.Tangible) :
    cwnet.toFinMA.absorb cwnet.uniformPolicy rC (Sum.inr V02) s'
      = if T10 = s' then 1 else 0 := by
  show absorbIter (cwnet.toFinMA.imStep cwnet.uniformPolicy)
    (absFuel rC) (Sum.inr V02) s' = _
  rw [show absFuel rC = 2 + 1 from by decide, absorbIter_succ_inr]
  simp only [cwnet_imStep_02, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq univ
    (Sum.inl T10 : cwnet.Tangible ⊕ cwnet.Vanishing)
    (fun y => absorbIter
      (cwnet.toFinMA.imStep cwnet.uniformPolicy) 2 y s'),
    if_pos (mem_univ _), absorbIter_inl, hitMass_inl]

/-! ### The flattened rate rows -/

/-- Away from the red selection, nothing is enabled at two red — the
blue selection is class-undersupplied. -/
theorem cwnet_side_20 : ∀ κ : cwnet.delay.CVec 0, κ ≠ κr →
    ¬ cwnet.delay.Enabled 0 κ T20.1 := by decide

/-- The delay selection vectors, enumerated. -/
theorem cvec_univ :
    (univ : Finset (cwnet.delay.CVec 0)) = {κr, κb} := by decide

/-- The red flip from two red lands at one-of-each (tangible). -/
theorem fire_20_r :
    cwnet.toSum (cwnet.delay.fire 0 κr T20.1) = Sum.inl T11 := by
  rw [show cwnet.delay.fire 0 κr T20.1 = mc 1 1 from by decide]
  exact dif_neg (by decide)

/-- The red flip from one-of-each lands at two blue (vanishing). -/
theorem fire_11_r :
    cwnet.toSum (cwnet.delay.fire 0 κr T11.1) = Sum.inr V02 := by
  rw [show cwnet.delay.fire 0 κr T11.1 = mc 0 2 from by decide]
  exact dif_pos (by decide)

/-- The blue flip from one-of-each lands back at two red
(tangible). -/
theorem fire_11_b :
    cwnet.toSum (cwnet.delay.fire 0 κb T11.1) = Sum.inl T20 := by
  rw [show cwnet.delay.fire 0 κb T11.1 = mc 2 0 from by decide]
  exact dif_neg (by decide)

/-- The flattened rate row at two red: one edge, to one-of-each, at
census `2` times the red rate `2`. -/
theorem frate_20 (s' : cwnet.Tangible) :
    fchain.rate T20 s' = if T11 = s' then 4 else 0 := by
  show (∑ t : Fin 1, ∑ κ : cwnet.delay.CVec t,
      if cwnet.delay.Enabled t κ T20.1
      then (cwnet.delay.raceCount t κ T20.1 : ℚ) * cwnet.delay.rate t κ
        * cwnet.toFinMA.absorb cwnet.uniformPolicy rC
            (cwnet.toSum (cwnet.delay.fire t κ T20.1)) s'
      else 0) = _
  rw [Fin.sum_univ_one]
  refine (Finset.sum_eq_single_of_mem κr (mem_univ _)
    fun κ _ hκ => if_neg (cwnet_side_20 κ hκ)).trans ?_
  rw [if_pos (by decide : cwnet.delay.Enabled 0 κr T20.1),
    show cwnet.delay.raceCount 0 κr T20.1 = 2 from by decide,
    show cwnet.delay.rate 0 κr = 2 from rfl,
    fire_20_r, absorb_inl]
  simp only [mul_ite, mul_one, mul_zero]
  split <;> norm_num

/-- The flattened rate row at one-of-each: the red flip reaches one
red *through the cascade* at rate `1 · 2`; the blue flip reaches two
red directly at rate `1 · 3` — the colour-dependent rate, visible as
edge data. -/
theorem frate_11 (s' : cwnet.Tangible) :
    fchain.rate T11 s'
      = (if T10 = s' then 2 else 0) + (if T20 = s' then 3 else 0) := by
  show (∑ t : Fin 1, ∑ κ : cwnet.delay.CVec t,
      if cwnet.delay.Enabled t κ T11.1
      then (cwnet.delay.raceCount t κ T11.1 : ℚ) * cwnet.delay.rate t κ
        * cwnet.toFinMA.absorb cwnet.uniformPolicy rC
            (cwnet.toSum (cwnet.delay.fire t κ T11.1)) s'
      else 0) = _
  rw [Fin.sum_univ_one, cvec_univ, Finset.sum_insert (by decide),
    Finset.sum_singleton]
  rw [if_pos (by decide : cwnet.delay.Enabled 0 κr T11.1),
    if_pos (by decide : cwnet.delay.Enabled 0 κb T11.1),
    show cwnet.delay.raceCount 0 κr T11.1 = 1 from by decide,
    show cwnet.delay.raceCount 0 κb T11.1 = 1 from by decide,
    show cwnet.delay.rate 0 κr = 2 from rfl,
    show cwnet.delay.rate 0 κb = 3 from rfl,
    fire_11_r, fire_11_b, absorb_inr_02, absorb_inl]
  simp only [mul_ite, mul_one, mul_zero]
  congr 1 <;> · split <;> norm_num

/-- The flattened initial row: all mass at two red. -/
theorem finit_20 : fchain.init T20 = 1 := by
  show (if T20.1 = mc 2 0 then (1 : ℚ) else 0) = 1
  exact if_pos rfl

/-! ### The flattened-side certificate -/

/-- The exit rate at two red is `4`. -/
theorem fexit_20 : fchain.exitRate T20 = 4 := by
  have hoff : ∀ s' : cwnet.Tangible,
      fchain.offRate T20 s' = if T11 = s' then 4 else 0 := by
    intro s'
    by_cases h : T20 = s'
    · rw [← h, FinCTMC.offRate_diag,
        if_neg (show ¬ T11 = T20 from by decide)]
    · rw [FinCTMC.offRate_of_ne _ h, frate_20]
  show (∑ s', fchain.offRate T20 s') = 4
  rw [Finset.sum_congr rfl fun s' _ => hoff s',
    Finset.sum_ite_eq univ T11 (fun _ => (4 : ℚ)),
    if_pos (mem_univ _)]

/-- The exit rate at one-of-each is `2 + 3 = 5` — the two
colour-resolved races. -/
theorem fexit_11 : fchain.exitRate T11 = 5 := by
  have hoff : ∀ s' : cwnet.Tangible,
      fchain.offRate T11 s'
        = (if T10 = s' then 2 else 0) + (if T20 = s' then 3 else 0) := by
    intro s'
    by_cases h : T11 = s'
    · rw [← h, FinCTMC.offRate_diag,
        if_neg (show ¬ T10 = T11 from by decide),
        if_neg (show ¬ T20 = T11 from by decide)]
      norm_num
    · rw [FinCTMC.offRate_of_ne _ h, frate_11]
  show (∑ s', fchain.offRate T11 s') = 5
  rw [Finset.sum_congr rfl fun s' _ => hoff s',
    Finset.sum_add_distrib,
    Finset.sum_ite_eq univ T10 (fun _ => (2 : ℚ)),
    Finset.sum_ite_eq univ T20 (fun _ => (3 : ℚ)),
    if_pos (mem_univ _), if_pos (mem_univ _)]
  norm_num

/-- The jump chain leaves two red for one-of-each with probability
one. -/
theorem fstep_20_11 : fchain.jumpChain.step T20 T11 = 1 := by
  rw [FinCTMC.jumpChain_step,
    if_neg (show ¬ fchain.exitRate T20 = 0 from by
      rw [fexit_20]; norm_num),
    FinCTMC.offRate_of_ne _ (show T20 ≠ T11 from by decide),
    frate_20, if_pos rfl, fexit_20]
  norm_num

/-- **The red branch**: one-of-each drains to one red with probability
`2/5` — the red rate over the colour-resolved exit rate. -/
theorem fstep_11_10 : fchain.jumpChain.step T11 T10 = 2/5 := by
  rw [FinCTMC.jumpChain_step,
    if_neg (show ¬ fchain.exitRate T11 = 0 from by
      rw [fexit_11]; norm_num),
    FinCTMC.offRate_of_ne _ (show T11 ≠ T10 from by decide),
    frate_11, if_pos rfl,
    if_neg (show ¬ T20 = T10 from by decide), fexit_11]
  norm_num

/-- **The blue branch**: one-of-each flips back to two red with
probability `3/5`.  With the red branch, this pins that the branch
split is exactly the colour-dependence of the rate: the two
selections differ *only* in the colour their vectors read. -/
theorem fstep_11_20 : fchain.jumpChain.step T11 T20 = 3/5 := by
  rw [FinCTMC.jumpChain_step,
    if_neg (show ¬ fchain.exitRate T11 = 0 from by
      rw [fexit_11]; norm_num),
    FinCTMC.offRate_of_ne _ (show T11 ≠ T20 from by decide),
    frate_11, if_neg (show ¬ T10 = T20 from by decide),
    if_pos rfl, fexit_11]
  norm_num

/-- The drain trajectory: two red, one-of-each, one red. -/
def ωd : Traj cwnet.Tangible 2 :=
  fun i => if i = 0 then T20 else if i = 1 then T11 else T10

theorem ωd_0 : ωd 0 = T20 := if_pos rfl

theorem ωd_1 : ωd 1 = T11 := by
  show (if (1 : Fin 3) = 0 then T20
    else if (1 : Fin 3) = 1 then T11 else T10) = T11
  rw [if_neg (by decide), if_pos rfl]

theorem ωd_2 : ωd 2 = T10 := by
  show (if (2 : Fin 3) = 0 then T20
    else if (2 : Fin 3) = 1 then T11 else T10) = T10
  rw [if_neg (by decide), if_neg (by decide)]

/-- The flip trajectory: two red, one-of-each, two red. -/
def ωf : Traj cwnet.Tangible 2 :=
  fun i => if i = 0 then T20 else if i = 1 then T11 else T20

theorem ωf_0 : ωf 0 = T20 := if_pos rfl

theorem ωf_1 : ωf 1 = T11 := by
  show (if (1 : Fin 3) = 0 then T20
    else if (1 : Fin 3) = 1 then T11 else T20) = T11
  rw [if_neg (by decide), if_pos rfl]

theorem ωf_2 : ωf 2 = T20 := by
  show (if (2 : Fin 3) = 0 then T20
    else if (2 : Fin 3) = 1 then T11 else T20) = T20
  rw [if_neg (by decide), if_neg (by decide)]

/-- **The flattened-side certificate**: the flattened execution law
gives the drain trajectory weight `2/5` — computed on the flattened
object alone. -/
theorem fdrain_weight : ((fchain.jumpLaw 2).wt ωd) = 2/5 := by
  show chainWt fchain.jumpChain.init fchain.jumpChain.step ωd = 2/5
  unfold chainWt
  rw [Fin.prod_univ_two]
  simp only [Fin.castSucc_zero, Fin.castSucc_one,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rw [ωd_0, ωd_1, ωd_2, FinCTMC.jumpChain_init, finit_20,
    fstep_20_11, fstep_11_10]
  norm_num

/-- The flip control: weight `3/5`, same computation through the blue
branch. -/
theorem fflip_weight : ((fchain.jumpLaw 2).wt ωf) = 3/5 := by
  show chainWt fchain.jumpChain.init fchain.jumpChain.step ωf = 3/5
  unfold chainWt
  rw [Fin.prod_univ_two]
  simp only [Fin.castSucc_zero, Fin.castSucc_one,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rw [ωf_0, ωf_1, ωf_2, FinCTMC.jumpChain_init, finit_20,
    fstep_20_11, fstep_11_20]
  norm_num

/-! ### The consumption: flattened certificate in, net verdicts out -/

/-- **The certificate consumed at the token game**: the coloured net's
own community law gives the drain trajectory weight `2/5` — by
transport through the skeleton agreement, never by recomputation on
the net side.  The `2/5`-against-`3/5` split *is* `D_T(c)`: red races
at `2`, blue at `3`, and nothing else distinguishes the branches. -/
theorem witness_token_game_drain :
    (cwnet.tangiblePathLaw cwnet.uniformPolicy rC
      cwnet_zenoFree 2).wt ωd = 2/5 := by
  rw [← cwnet.flatten_skeleton_agreement cwnet.uniformPolicy rC
    cwnet_zenoFree cwnet_tangibleInit 2]
  exact fdrain_weight

/-- The flip control at the token game. -/
theorem witness_token_game_flip :
    (cwnet.tangiblePathLaw cwnet.uniformPolicy rC
      cwnet_zenoFree 2).wt ωf = 3/5 := by
  rw [← cwnet.flatten_skeleton_agreement cwnet.uniformPolicy rC
    cwnet_zenoFree cwnet_tangibleInit 2]
  exact fflip_weight

/-- **The coloured composed corollary at the witness**: token-game
community object and flattened-execution community object, isomorphic
by the pasted invertible cell, zero hypotheses. -/
theorem witness_composed_triangle (k : ℕ)
    {a : Crd (Traj cwnet.Tangible k)} :
    ∃ α : Cell
        (singletonC (cwnet.tangiblePathLaw cwnet.uniformPolicy rC
          cwnet_zenoFree k) : Loose a a)
        (singletonC ((cwnet.flattenChain cwnet.uniformPolicy rC
          cwnet_tangibleInit).jumpLaw k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  cwnet.flatten_composed_triangle cwnet.uniformPolicy rC
    cwnet_zenoFree cwnet_tangibleInit k

/-- The composed corollary from the premise bundle, at the witness:
the community's premise set consumed whole. -/
theorem witness_composed_of_premises (k : ℕ)
    {a : Crd (Traj cwnet.Tangible k)} :
    ∃ α : Cell
        (singletonC (cwnet.tangiblePathLaw cwnet.uniformPolicy
          cwnet_premises.rank
          (cwnet.zenoFree_of_cascadeRank cwnet.uniformPolicy
            cwnet.uniformPolicy_respects cwnet_premises.cascade) k) :
          Loose a a)
        (singletonC ((cwnet.flattenChain cwnet.uniformPolicy
          cwnet_premises.rank
          cwnet_premises.init_tangible).jumpLaw k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  cwnet.flatten_composed_triangle_of_premises cwnet_premises
    cwnet.uniformPolicy cwnet.uniformPolicy_respects k

end CspnComposedWitness

end Adequacy
end SuFunctor
