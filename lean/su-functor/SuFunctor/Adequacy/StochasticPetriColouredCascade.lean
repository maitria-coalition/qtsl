import SuFunctor.Adequacy.StochasticPetriColoured
import SuFunctor.Adequacy.StochasticPetriCascade

/-! # Adequacy: coloured stochastic Petri frames, immediate/cascade face

The immediate-transition face of the coloured stochastic-Petri story —
the coloured companion of `SuFunctor.Adequacy.StochasticPetriCascade`,
and the left square the coloured flattening triangle consumes.  One
more reuse of the landed Markov-automaton square, on the nose.

**The fragment.**  The coloured delay fragment of
`SuFunctor.Adequacy.StochasticPetriColoured` (finite colour boxes,
capacity per colour class, colour-dependent rates, guard cylinders,
Dirac firing measures), extended by **coloured immediate
transitions**: transitions that fire in zero time with priority over
the delay species, each carrying arcs, a guard cylinder on its colour
vector, and a Dirac firing measure — no rate and no weight, exactly
the community presentation at its deterministic slice ([EB10a]
arXiv:1003.4812 pp. 233–234).  Inhibitors do not exist, by formation,
as before.

**Actions are (transition, colour-vector) pairs.**  At the coloured
grain a conflict is resolved not only *which* immediate transition
fires but *which tokens it selects*: the compiled automaton's action
type is `Σ u, IVec u` — one action per transition per colour vector —
and the declared scheduler weighs both at once.  The uniform instance
below is the single-firing shadow of the community's randomization at
this grain: uniform among the enabled *pairs*.  (Weighting selections
by their census multiplicity is another legitimate instance; the
square is scheduler-generic and never depends on the choice.)

**Vanishing is now a coloured judgment.**  A marking is vanishing
when some *pair* is enabled — supply per colour class, capacity, and
the guard cylinder all participate — so the tangible/vanishing split
genuinely reads colours: a red token may vanish where a blue one
rests.  The controls pin exactly this (`cnet₁_blue_tangible`).  As in
the uncoloured face, the split is carried by the type, a delay row at
a vanishing marking is unrepresentable, and the cascade is the
automaton square's absorbing closure at the working fuel of a
declared `CascadeRank` — whose coloured witness below is a *colour
census* (the red-token count), not a token count.

**The square** (`cispn_cascade_adequacy`): compile the net's rows —
timed rows in the unordered convention with the coloured dictionary,
immediate branch rows action-keyed by pairs, initial rows — close
through the compiled scheduler rows, jump-close, denote; and this
agrees, by an invertible globular cell, with interpreting the net as
its Markov automaton, closing classically, and including the tangible
path law.  Five-storey engine reuse; the one net-shaped obligation is
the compile triangle (`compile_cispn_comm`), the coloured dictionary
rowwise on the timed component and definitional on the immediate and
initial rows.  Zero new inductions.

**No initial-tangibility premise**, exactly as the uncoloured face:
the closure pushes vanishing initial mass through the cascade, and
`tangibleChain_init_of_tangible` is the receipt that the community's
premise recovers the untouched initial distribution.

**Deliberately separate, named**: kernel-valued immediate firing
measures (v2 — the branches here are point masses at Dirac outcomes,
and nothing entrenches a kernel encoding); composite set-firings of
non-conflicting immediates at colour (the set-action face's coloured
lift); coloured demonic/angelic instruments; boundary-hitting guard
transitions; the flattening cell and carrier identification (the
triangle's own legs). -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open SuFunctor.Universe (SpecDnf)
open Finset

variable {P T U : Type} [Fintype P] [DecidableEq P] [Fintype T]
  [Fintype U] {K : P → Type} [∀ p, Fintype (K p)]
  [∀ p, DecidableEq (K p)] {B : ℕ}

/-! ## The fragment: a coloured net with immediate transitions -/

/-- A coloured stochastic Petri net with immediate transitions: the
delay layer is a `FinCSPN` (carrying the net's initial distribution),
and each immediate transition carries ordinary input arcs, enabling
arcs, output arcs, a guard cylinder on its colour vector, and a Dirac
firing measure — no rate and no weight.  No inhibitor field exists on
either species. -/
structure FinCISPN (P T U : Type) [Fintype P] [DecidableEq P]
    (K : P → Type) [∀ p, Fintype (K p)] [∀ p, DecidableEq (K p)]
    (B : ℕ) where
  /-- The delay layer: coloured delay transitions and the initial
  distribution over coloured markings. -/
  delay : FinCSPN P T K B
  /-- Ordinary input arcs per immediate transition and place. -/
  ipre : U → P → ℕ
  /-- Enabling arcs per immediate transition and place. -/
  iread : U → P → ℕ
  /-- Ordinary output arcs per immediate transition and place. -/
  ipost : U → P → ℕ
  /-- The immediate guard: a decidable cylinder on colour vectors. -/
  iguard : (u : U) → (∀ p, Fin (ipre u p + iread u p) → K p) → Prop
  /-- The immediate guard's decision procedure, carried as data. -/
  iguard_dec : ∀ u κ, Decidable (iguard u κ)
  /-- The immediate Dirac firing measure. -/
  ireset : (u : U) → (∀ p, Fin (ipre u p + iread u p) → K p) →
    ∀ p, Fin (ipost u p) → K p

namespace FinCISPN

variable (N : FinCISPN P T U K B)

/-- The colour vectors of an immediate transition. -/
abbrev IVec (u : U) : Type := ∀ p, Fin (N.ipre u p + N.iread u p) → K p

/-- The action type of the compiled automaton: one action per
immediate transition *per colour vector* — conflict resolution at the
coloured grain weighs token selections, not just transitions. -/
abbrev IAct : Type := Σ u : U, N.IVec u

instance (u : U) (κ : N.IVec u) : Decidable (N.iguard u κ) :=
  N.iguard_dec u κ

/-- Enabledness of an immediate pair: the colour-classed reservation
is supplied, the outcome respects the capacity, and the colour vector
passes the guard. -/
def IEnabled (a : N.IAct) (m : CMarking P K B) : Prop :=
  Coloured.Supplied a.2 (N.ireset a.1 a.2) m ∧ N.iguard a.1 a.2

instance (a : N.IAct) (m : CMarking P K B) :
    Decidable (N.IEnabled a m) :=
  inferInstanceAs (Decidable
    (Coloured.Supplied a.2 (N.ireset a.1 a.2) m ∧ N.iguard a.1 a.2))

/-- The immediate firing (truncated at capacity for totality; under
`IEnabled` the truncation is inert). -/
def ifire (a : N.IAct) (m : CMarking P K B) : CMarking P K B :=
  Coloured.fireAt a.2 (N.ireset a.1 a.2) m

/-! ## Vanishing and tangible markings -/

/-- A marking is **vanishing** when it enables some immediate pair —
a coloured judgment: supply per colour class, capacity, and the guard
cylinder all participate. -/
def IsVanishing (m : CMarking P K B) : Prop := ∃ a, N.IEnabled a m

instance (m : CMarking P K B) : Decidable (N.IsVanishing m) :=
  inferInstanceAs (Decidable (∃ a, N.IEnabled a m))

/-- The tangible markings: the Markovian sort of the compiled
automaton. -/
abbrev Tangible := {m : CMarking P K B // ¬ N.IsVanishing m}

/-- The vanishing markings: the instantaneous sort of the compiled
automaton. -/
abbrev Vanishing := {m : CMarking P K B // N.IsVanishing m}

/-- Forget the classification. -/
def ofSum : N.Tangible ⊕ N.Vanishing → CMarking P K B :=
  Sum.elim Subtype.val Subtype.val

/-- Classify a marking as tangible or vanishing. -/
def toSum (m : CMarking P K B) : N.Tangible ⊕ N.Vanishing :=
  if h : N.IsVanishing m then Sum.inr ⟨m, h⟩ else Sum.inl ⟨m, h⟩

omit [Fintype T] [Fintype U] in
@[simp] theorem ofSum_inl (s : N.Tangible) :
    N.ofSum (Sum.inl s) = s.1 := rfl

omit [Fintype T] [Fintype U] in
@[simp] theorem ofSum_inr (i : N.Vanishing) :
    N.ofSum (Sum.inr i) = i.1 := rfl

omit [Fintype T] in
@[simp] theorem ofSum_toSum (m : CMarking P K B) :
    N.ofSum (N.toSum m) = m := by
  unfold toSum
  split <;> rfl

omit [Fintype T] in
@[simp] theorem toSum_ofSum (x : N.Tangible ⊕ N.Vanishing) :
    N.toSum (N.ofSum x) = x := by
  cases x with
  | inl s => rw [ofSum_inl]; exact dif_neg s.2
  | inr i => rw [ofSum_inr]; exact dif_pos i.2

omit [Fintype T] in
/-- Landing in the instantaneous sort determines the marking — the
inversion the direct rank arguments consume. -/
theorem toSum_inr_val {m : CMarking P K B} {j : N.Vanishing}
    (h : N.toSum m = Sum.inr j) : j.1 = m := by
  unfold toSum at h
  split at h
  · exact (congrArg Subtype.val (Sum.inr.inj h)).symm
  · simp at h

/-- The classification is a bijection: tangible-or-vanishing markings
are all the markings — the community's state-space split, as an
equivalence. -/
def markingEquiv : (N.Tangible ⊕ N.Vanishing) ≃ CMarking P K B where
  toFun := N.ofSum
  invFun := N.toSum
  left_inv := N.toSum_ofSum
  right_inv := N.ofSum_toSum

/-! ## The Markov automaton of the net

Maximal progress is *structure* here, exactly as in the uncoloured
face: the automaton's rate field takes tangible sources only, so a
delay row at a vanishing marking is unrepresentable rather than
linted. -/

/-- The Markov-automaton reading of the coloured net: tangible
markings are the Markovian states (their timed rows are the coloured
delay layer's race intensities); vanishing markings are the
instantaneous states, with one action per immediate *pair* — an
enabled pair is a point mass at the Dirac-fired marking, a disabled
pair is the honest zero-time no-op (a point mass at the source; a
scheduler that chooses it sits still in zero time, which the rank
machinery refuses rather than this definition papering over). -/
def toFinMA : FinMA N.Tangible N.Vanishing N.IAct where
  rate s x := N.delay.raceRate s.1 (N.ofSum x)
  branch i a x :=
    if N.IEnabled a i.1
    then (if N.toSum (N.ifire a i.1) = x then 1 else 0)
    else (if Sum.inr i = x then 1 else 0)
  init x := N.delay.init (N.ofSum x)
  rate_nonneg s x _ := N.delay.raceRate_nonneg s.1 (N.ofSum x)
  branch_nonneg i a x := by
    split <;> split <;> norm_num
  branch_row_sum i a := by
    by_cases h : N.IEnabled a i.1
    · simp only [if_pos h]
      rw [Finset.sum_ite_eq univ (N.toSum (N.ifire a i.1))
        fun _ => (1 : ℚ)]
      simp
    · simp only [if_neg h]
      rw [Finset.sum_ite_eq univ (Sum.inr i : N.Tangible ⊕ N.Vanishing)
        fun _ => (1 : ℚ)]
      simp
  init_nonneg x := N.delay.init_nonneg (N.ofSum x)
  init_sum := (Equiv.sum_comp N.markingEquiv N.delay.init).trans
    N.delay.init_sum

@[simp] theorem toFinMA_rate (s : N.Tangible)
    (x : N.Tangible ⊕ N.Vanishing) :
    N.toFinMA.rate s x = N.delay.raceRate s.1 (N.ofSum x) := rfl

@[simp] theorem toFinMA_branch (i : N.Vanishing) (a : N.IAct)
    (x : N.Tangible ⊕ N.Vanishing) :
    N.toFinMA.branch i a x
      = if N.IEnabled a i.1
          then (if N.toSum (N.ifire a i.1) = x then 1 else 0)
          else (if Sum.inr i = x then 1 else 0) := rfl

@[simp] theorem toFinMA_init (x : N.Tangible ⊕ N.Vanishing) :
    N.toFinMA.init x = N.delay.init (N.ofSum x) := rfl

/-! ## The community scheduler and the cascade-termination
certificate -/

/-- The number of immediate pairs enabled at a vanishing marking. -/
def enabledCount (i : N.Vanishing) : ℕ :=
  (univ.filter fun a : N.IAct => N.IEnabled a i.1).card

omit [Fintype T] in
theorem enabledCount_pos (i : N.Vanishing) : 0 < N.enabledCount i := by
  obtain ⟨a, ha⟩ := i.2
  exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨mem_univ a, ha⟩⟩

/-- The community's conflict resolution at the coloured single-firing
stratum: uniform choice among the enabled immediate *pairs* — both
which transition and which token selection.  The square never depends
on this particular scheduler (it is proven for every declared one);
this is the concrete instance the controls pin. -/
def uniformPolicy : Policy N.Vanishing N.IAct where
  choice i a :=
    if N.IEnabled a i.1 then (N.enabledCount i : ℚ)⁻¹ else 0
  nonneg i a := by
    split
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl
  row_sum i := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
      add_zero, nsmul_eq_mul]
    exact mul_inv_cancel₀
      (Nat.cast_ne_zero.mpr (N.enabledCount_pos i).ne')

/-- A scheduler **respects enabling** when it never weights a
disabled pair. -/
def RespectsEnabling (σ : Policy N.Vanishing N.IAct) : Prop :=
  ∀ i a, σ.choice i a ≠ 0 → N.IEnabled a i.1

omit [Fintype T] in
theorem uniformPolicy_respects : N.RespectsEnabling N.uniformPolicy := by
  intro i a h
  by_contra hne
  exact h (if_neg hne)

/-- **Cascade termination as a ranking certificate**, at colour: a
rank on vanishing markings that strictly decreases along every
enabled immediate firing landing in a vanishing marking.  Decidable
at concrete nets (the instance below); at colour the natural
witnesses are colour censuses (the controls' rank is a red-token
count), and the controls discharge the certificate by direct
argument, which at colour is also the stronger specimen. -/
def CascadeRank (r : N.Vanishing → ℕ) : Prop :=
  ∀ (i : N.Vanishing) (a : N.IAct), N.IEnabled a i.1 →
    ∀ j : N.Vanishing, N.toSum (N.ifire a i.1) = Sum.inr j → r j < r i

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
instance (r : N.Vanishing → ℕ) : Decidable (N.CascadeRank r) := by
  letI : DecidableEq (N.Tangible ⊕ N.Vanishing) := inferInstance
  letI : Fintype N.Vanishing := inferInstance
  letI : Fintype N.IAct := inferInstance
  exact inferInstanceAs
    (Decidable (∀ (i : N.Vanishing) (a : N.IAct), N.IEnabled a i.1 →
      ∀ j : N.Vanishing, N.toSum (N.ifire a i.1) = Sum.inr j →
        r j < r i))

/-- A cascade rank certifies Zeno-freedom for every scheduler that
respects enabling — the policy-aware analogue of the automaton
square's branch-level sufficient condition, exactly as in the
uncoloured face: the disabled-pair stay rows would demand `r i < r i`,
and it is the scheduler's enabling-respect that keeps them out of the
mixture's support. -/
theorem zenoFree_of_cascadeRank (σ : Policy N.Vanishing N.IAct)
    (hσ : N.RespectsEnabling σ) {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) : ZenoFree (N.toFinMA.imStep σ) r := by
  intro i j hne
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hen : N.IEnabled a i.1 := hσ i a (left_ne_zero_of_mul ha)
  have hb : N.toFinMA.branch i a (Sum.inr j) ≠ 0 :=
    right_ne_zero_of_mul ha
  rw [toFinMA_branch, if_pos hen] at hb
  refine hr i a hen j ?_
  by_contra hns
  exact hb (if_neg hns)

/-- The uniform scheduler inherits Zeno-freedom from any cascade
rank. -/
theorem zenoFree_uniform {r : N.Vanishing → ℕ} (hr : N.CascadeRank r) :
    ZenoFree (N.toFinMA.imStep N.uniformPolicy) r :=
  N.zenoFree_of_cascadeRank N.uniformPolicy N.uniformPolicy_respects hr

/-! ## The observed process: the tangible chain -/

/-- **The reduced tangible chain**: the community's observed process
on non-vanishing coloured markings — the fixed-scheduler closure of
the net's automaton, by the landed absorbing computation. -/
def tangibleChain (σ : Policy N.Vanishing N.IAct) (r : N.Vanishing → ℕ)
    (hr : ZenoFree (N.toFinMA.imStep σ) r) : FinCTMC N.Tangible :=
  N.toFinMA.close σ r hr

theorem tangibleChain_eq (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r) :
    N.tangibleChain σ r hr = N.toFinMA.close σ r hr := rfl

/-- The time-abstract semantics of the net under the declared
scheduler: the tangible chain's jump-chain path law at jump horizon
`k`. -/
noncomputable def tangiblePathLaw (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (k : ℕ) : SubPMF (Traj N.Tangible k) :=
  N.toFinMA.pathLaw σ r hr k

theorem tangiblePathLaw_eq (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (k : ℕ) :
    N.tangiblePathLaw σ r hr k = N.toFinMA.pathLaw σ r hr k := rfl

/-- **The initial-tangibility receipt**: when no vanishing marking
carries initial mass, the initial distribution passes through the
closure untouched — the community's premise recovered, never
inherited. -/
theorem tangibleChain_init_of_tangible (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (hsupp : ∀ m : CMarking P K B, N.IsVanishing m → N.delay.init m = 0)
    (s : N.Tangible) :
    (N.tangibleChain σ r hr).init s = N.delay.init s.1 := by
  show (∑ x, N.toFinMA.init x * N.toFinMA.absorb σ r x s) = _
  rw [Fintype.sum_sum_type]
  have h2 : ∀ i : N.Vanishing,
      N.toFinMA.init (Sum.inr i) * N.toFinMA.absorb σ r (Sum.inr i) s
        = 0 := by
    intro i
    rw [toFinMA_init, ofSum_inr, hsupp i.1 i.2, zero_mul]
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_const_zero,
    add_zero]
  have h1 : ∀ m' : N.Tangible,
      N.toFinMA.init (Sum.inl m') * N.toFinMA.absorb σ r (Sum.inl m') s
        = if m' = s then N.delay.init m'.1 else 0 := by
    intro m'
    have habs : N.toFinMA.absorb σ r (Sum.inl m') s
        = hitMass (Sum.inl m' : N.Tangible ⊕ N.Vanishing) s :=
      absorbIter_inl _ _ m' s
    rw [habs, hitMass_inl, toFinMA_init, ofSum_inl]
    by_cases h : m' = s <;> simp [h]
  rw [Finset.sum_congr rfl fun m' _ => h1 m']
  rw [Finset.sum_ite_eq' univ s fun m' => N.delay.init m'.1]
  simp

/-! ## The compiled rows: the unordered convention, both species -/

/-- **Compilation in the house convention**: timed rows in the
unordered grain — the coloured dictionary times the per-colour-class
unordered count times the colour-dependent rate, guard-gated, at the
automaton row grain; immediate branch rows keyed by (transition,
colour-vector) pairs; initial rows read off the delay layer. -/
noncomputable def compileCispn :
    MaRows N.Tangible N.Vanishing N.IAct where
  rateRow := Finsupp.onFinset univ
    (fun q => ∑ t, ∑ κ : N.delay.CVec t,
      if N.delay.Enabled t κ q.1.1.1
          ∧ N.delay.fire t κ q.1.1.1 = N.ofSum q.1.2
      then ((N.delay.dict t κ * N.delay.selCount t κ q.1.1.1 : ℕ) : ℚ)
        * N.delay.rate t κ
      else 0)
    (fun _ _ => mem_univ _)
  branchRow := Finsupp.onFinset univ
    (fun p =>
      if N.IEnabled p.2.1 p.1.1
      then (if N.toSum (N.ifire p.2.1 p.1.1) = p.2.2 then 1 else 0)
      else (if Sum.inr p.1 = p.2.2 then 1 else 0))
    (fun _ _ => mem_univ _)
  initRow := Finsupp.onFinset univ (fun x => N.delay.init (N.ofSum x))
    (fun _ _ => mem_univ _)

/-- **The compile-commutes triangle — the coloured dictionary, one
storey up**: the compiled rows are the compilation of the net's
automaton.  Deliberately not definitional on the timed component (the
coloured dictionary theorem rowwise, under the colour-vector sum);
definitional on the immediate and initial components. -/
theorem compile_cispn_comm : N.compileCispn = compileMa N.toFinMA := by
  have ext3 : ∀ X Y : MaRows N.Tangible N.Vanishing N.IAct,
      X.rateRow = Y.rateRow → X.branchRow = Y.branchRow →
      X.initRow = Y.initRow → X = Y := by
    rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h1 h2 h3
    cases h1; cases h2; cases h3; rfl
  refine ext3 _ _ (Finsupp.ext fun q => ?_) rfl rfl
  show (∑ t, ∑ κ : N.delay.CVec t,
      if N.delay.Enabled t κ q.1.1.1
          ∧ N.delay.fire t κ q.1.1.1 = N.ofSum q.1.2
      then ((N.delay.dict t κ * N.delay.selCount t κ q.1.1.1 : ℕ) : ℚ)
        * N.delay.rate t κ
      else 0)
    = N.delay.raceRate q.1.1.1 (N.ofSum q.1.2)
  refine Finset.sum_congr rfl fun t _ => ?_
  refine Finset.sum_congr rfl fun κ _ => ?_
  by_cases hc : N.delay.Enabled t κ q.1.1.1
      ∧ N.delay.fire t κ q.1.1.1 = N.ofSum q.1.2
  · rw [if_pos hc, if_pos hc]
    congr 1
    exact_mod_cast congrArg (Nat.cast (R := ℚ))
      (N.delay.raceCount_eq_dict t κ q.1.1.1).symm
  · rw [if_neg hc, if_neg hc]

/-- The compiled rows are well-formed — through the triangle, from
the automaton compilation. -/
theorem compileCispn_wf : N.compileCispn.WF :=
  N.compile_cispn_comm ▸ compileMa_wf N.toFinMA

/-! ## The square -/

/-- **Adequacy of the coloured stochastic-Petri compilation,
immediate/cascade face.**

In the double category `Crd (Traj N.Tangible k)` of per-element
credal constraints over jump-horizon-`k` trajectories of tangible
coloured markings: the loose-arrow diagram denoted by the *jump
closure of the scheduler closure* of the net's compiled rows — timed
rows in the unordered convention with the coloured dictionary,
immediate rows keyed by (transition, colour-vector) pairs, closed at
the working fuel of the declared cascade rank — is isomorphic, by an
invertible globular cell, to the singleton-credal inclusion of the
net's tangible path law under the declared scheduler.
Compile-close-close-denote agrees with interpret-then-include, at the
time-abstract stratum; scheduler-generic, hence dominating the
community's randomized conflict resolution at the coloured grain.

The statement's shape is the uncoloured face's exactly, so the
composed-triangle pasting consumes this square verbatim at the
coloured carrier.  The proof is five-storey engine reuse: the
coloured dictionary triangle rewrites the compiled rows into the
automaton compilation, and `ma_adequacy` finishes.  Zero new
inductions. -/
theorem cispn_cascade_adequacy (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ α : Cell
        (looseConj (atoms (jumpRows
          (closeMaRows N.compileCispn (compilePolicy σ) (absFuel r))) k) :
          Loose a a)
        (singletonC (N.tangiblePathLaw σ r hr k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  rw [compile_cispn_comm]
  exact ma_adequacy N.toFinMA σ r hr k

/-! ## The semantic-universe wiring (in-module, per the standing
precedent) -/

/-- The compiled coloured net's presentation in the semantic
universe's fibre over jump-horizon-`k` tangible trajectories. -/
noncomputable def cispnDnf (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (k : ℕ) :
    SpecDnf (Plain.Joint (Traj N.Tangible k)) :=
  maDnf N.compileCispn (compilePolicy σ) (absFuel r) k

/-- **The coloured cascade square, wired to the semantic universe**:
the ideal point of a law models the compiled net-and-scheduler
presentation exactly when the law is the tangible path law. -/
theorem su_cispn_cascade_adequacy (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (k : ℕ) (μ : SubPMF (Traj N.Tangible k)) :
    idealPoint μ ∈ (N.cispnDnf σ r k).modelClass
      ↔ μ = N.tangiblePathLaw σ r hr k := by
  unfold cispnDnf
  rw [compile_cispn_comm]
  exact su_ma_adequacy N.toFinMA σ r hr k μ

/-- The positive face: the tangible path law models the compiled
net. -/
theorem su_cispn_pathLaw_mem (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (k : ℕ) :
    idealPoint (N.tangiblePathLaw σ r hr k)
      ∈ (N.cispnDnf σ r k).modelClass :=
  (N.su_cispn_cascade_adequacy σ r hr k _).mpr rfl

/-- Ex falso at the net corner. -/
theorem su_cispn_bottom (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (k : ℕ) :
    (⊤ : Plain.Pen (Traj N.Tangible k))
      ∉ (N.cispnDnf σ r k).modelClass := by
  unfold cispnDnf maDnf ctmcJumpDnf
  exact top_notMem_diagramDnf _

/-- A tangible path law is never the bottom law. -/
theorem tangiblePathLaw_ne_zero (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (k : ℕ) :
    N.tangiblePathLaw σ r hr k ≠ SubPMF.zero (Traj N.Tangible k) :=
  N.toFinMA.pathLaw_ne_zero σ r hr k

/-- The credal reading at the net corner, through the slice. -/
theorem su_cispn_slice (σ : Policy N.Vanishing N.IAct)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (k : ℕ) (μ : SubPMF (Traj N.Tangible k)) :
    idealPoint μ ∈ (N.cispnDnf σ r k).modelClass
      ↔ maxSlice (rayC (N.tangiblePathLaw σ r hr k)) μ :=
  (N.su_cispn_cascade_adequacy σ r hr k μ).trans
    (maxSlice_rayC (N.tangiblePathLaw_ne_zero σ r hr k) μ).symm

end FinCISPN

/-! ## Controls

Concrete closed forms pinning what no uncoloured net can express: a
tangible/vanishing classification that reads colours (red vanishes
where blue rests), a colour-flipping two-step cascade whose rank is a
red-token census, the guard-blocked stay convention, and the uniform
split over (transition, colour-vector) *pairs*.  Proofs deliberately
independent of the lemmas they guard; rational values ride
`Finset.sum_eq_single_of_mem` + `norm_num`, per the standing kernel
note. -/

namespace CispnControls

open FinCISPN

/-- Two colours on one place: `0` is red, `1` is blue. -/
abbrev Col : Fin 1 → Type := fun _ => Fin 2

/-- Two red tokens (capacity 2). -/
def m20 : CMarking (Fin 1) Col 2 := fun _ c => if c = 0 then 2 else 0

/-- One red, one blue. -/
def m11 : CMarking (Fin 1) Col 2 := fun _ _ => 1

/-- No red, two blue. -/
def m02 : CMarking (Fin 1) Col 2 := fun _ c => if c = 0 then 0 else 2

/-- One red, two blue — immediate-side capacity block. -/
def m12 : CMarking (Fin 1) Col 2 := fun _ c => if c = 0 then 1 else 2

/-- The red selection vector of a one-arc immediate. -/
def ιr : Fin 1 → Fin 1 → Fin 2 := fun _ _ => 0

/-- The blue selection vector of a one-arc immediate. -/
def ιb : Fin 1 → Fin 1 → Fin 2 := fun _ _ => 1

/-- The inert coloured delay layer the cascade controls share: no
arcs, rate zero, initial mass on the two-red marking (vanishing —
exercising the no-initial-tangibility widening). -/
def inertDelay : FinCSPN (Fin 1) (Fin 1) Col 2 where
  pre := fun _ _ => 0
  read := fun _ _ => 0
  post := fun _ _ => 0
  guard := fun _ _ => True
  guard_dec := fun _ _ => inferInstance
  rate := fun _ _ => 0
  rate_nonneg := fun _ _ => le_rfl
  reset := fun _ _ _ j => j.elim0
  init := fun m => if m = m20 then 1 else 0
  init_nonneg := fun m => by by_cases h : m = m20 <;> simp [h]
  init_sum := Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (mem_univ _))

/-- One place, two colours, capacity 2; one immediate transition
consuming one token under a **red-only guard** and depositing the
opposite colour — the coloured cascade specimen: from two red, the
cascade flips red to blue twice through a vanishing intermediate. -/
def cnet₁ : FinCISPN (Fin 1) (Fin 1) (Fin 1) Col 2 where
  delay := inertDelay
  ipre := fun _ _ => 1
  iread := fun _ _ => 0
  ipost := fun _ _ => 1
  iguard := fun _ κ => κ 0 0 = 0
  iguard_dec := fun _ _ => inferInstance
  ireset := fun _ κ _ _ => if κ 0 0 = 0 then 1 else 0

/-- Two red tokens vanish: the red pair is enabled. -/
theorem cnet₁_red_vanishing : cnet₁.IsVanishing m20 := by decide

/-- The mixed marking vanishes: a red token is present. -/
theorem cnet₁_mixed_vanishing : cnet₁.IsVanishing m11 := by decide

/-- **The coloured classification**: the blue-only marking is
tangible — the red selection is colour-under-supplied (though total
supply abounds) and the blue selection is guard-blocked.  No
uncoloured formation expresses this split. -/
theorem cnet₁_blue_tangible : ¬ cnet₁.IsVanishing m02 := by decide

/-- The immediate-side capacity gate: with one red and two blue, the
red firing would overflow the blue class — tangible by capacity. -/
theorem cnet₁_cap_tangible : ¬ cnet₁.IsVanishing m12 := by decide

/-- The classified elements of `cnet₁`, named for the controls. -/
def i20 : cnet₁.Vanishing := ⟨m20, by decide⟩
def i11 : cnet₁.Vanishing := ⟨m11, by decide⟩
def t02 : cnet₁.Tangible := ⟨m02, by decide⟩

/-- The red firing from two red lands in the (vanishing) mixed
marking. -/
theorem cnet₁_fire_20 :
    cnet₁.toSum (cnet₁.ifire ⟨0, ιr⟩ i20.1) = Sum.inr i11 := by
  rw [show cnet₁.ifire ⟨0, ιr⟩ i20.1 = m11 from by decide]
  exact dif_pos (by decide)

/-- The red firing from the mixed marking lands in the (tangible)
blue-only marking. -/
theorem cnet₁_fire_11 :
    cnet₁.toSum (cnet₁.ifire ⟨0, ιr⟩ i11.1) = Sum.inl t02 := by
  rw [show cnet₁.ifire ⟨0, ιr⟩ i11.1 = m02 from by decide]
  exact dif_neg (by decide)

/-- **The stay convention, pinned at colour**: at the mixed marking
the blue pair is guard-blocked, and its branch row is the point mass
at the source — the zero-time no-op, not a firing. -/
theorem cnet₁_stay :
    cnet₁.toFinMA.branch i11 ⟨0, ιb⟩ (Sum.inr i11) = 1 := by
  show (if cnet₁.IEnabled ⟨0, ιb⟩ i11.1
    then (if cnet₁.toSum (cnet₁.ifire ⟨0, ιb⟩ i11.1) = Sum.inr i11
      then 1 else 0)
    else (if (Sum.inr i11 : cnet₁.Tangible ⊕ cnet₁.Vanishing)
      = Sum.inr i11 then 1 else 0)) = 1
  rw [if_neg (by decide : ¬ cnet₁.IEnabled ⟨0, ιb⟩ i11.1), if_pos rfl]

/-- **The coloured cascade rank is a colour census**: the red-token
count strictly decreases along every enabled immediate firing. -/
def r₁ : cnet₁.Vanishing → ℕ := fun i => (i.1 0 0 : ℕ)

/-- The rank certificate, discharged by direct argument — and the
argument is the better specimen: it holds for *every* enabled pair at
*every* vanishing marking at once (the guard pins the selection to
red, supply bounds the red count below, the Dirac outcome deposits
only blue, so the red census strictly drops), where an enumeration
would have merely checked the four cases.  (A whole-certificate
`decide` is unavailable here: evaluating the composite instance at
this coloured carrier sticks on a proof-irrelevant transport — the
findings file carries the mechanism.) -/
theorem cnet₁_rank : cnet₁.CascadeRank r₁ := by
  intro i a ha j hj
  obtain ⟨u, κ⟩ := a
  unfold FinCISPN.IEnabled at ha
  obtain ⟨hsup, hg⟩ := ha
  -- the guard pins every arc's selection colour to red (the sole arc
  -- index is reached through `Fin.eq_zero`, whose zero carries its own
  -- numeral instance — `cnet₁`'s projections are opaque to reducible
  -- numeral synthesis)
  have hall : ∀ x : Fin (cnet₁.ipre u 0 + cnet₁.iread u 0),
      κ 0 x = 0 := by
    intro x
    rw [Fin.eq_zero x]
    exact hg
  have hvd : Coloured.vecDemand κ 0 (0 : Fin 2) = 1 := by
    unfold Coloured.vecDemand
    rw [Finset.filter_true_of_mem fun x _ => hall x, Finset.card_univ,
      Fintype.card_fin]
    rfl
  have hdem : 1 ≤ (i.1 0 0 : ℕ) := by
    have h := (hsup 0 0).1
    rwa [hvd] at h
  have hcc : Coloured.consCount κ 0 (0 : Fin 2) = 1 := by
    unfold Coloured.consCount
    rw [Finset.filter_true_of_mem fun x _ => hall _, Finset.card_univ,
      Fintype.card_fin]
    rfl
  have hpc : Coloured.prodCount (cnet₁.ireset u κ) 0 (0 : Fin 2) = 0 := by
    unfold Coloured.prodCount
    rw [Finset.filter_false_of_mem, Finset.card_empty]
    intro x _
    show ¬ (if κ 0 ⟨0, Nat.zero_lt_one⟩ = (0 : Fin 2)
      then (1 : Fin 2) else 0) = 0
    rw [if_pos (hall ⟨0, Nat.zero_lt_one⟩)]
    decide
  have hval : j.1 = cnet₁.ifire ⟨u, κ⟩ i.1 := cnet₁.toSum_inr_val hj
  show (j.1 0 0 : ℕ) < (i.1 0 0 : ℕ)
  rw [hval]
  show min (Coloured.outAt κ (cnet₁.ireset u κ) i.1 0 0) 2
    < (i.1 0 0 : ℕ)
  unfold Coloured.outAt
  rw [hcc, hpc, add_zero]
  exact lt_of_le_of_lt (min_le_left _ _)
    (Nat.sub_lt (lt_of_lt_of_le one_pos hdem) one_pos)

theorem cnet₁_zenoFree :
    ZenoFree (cnet₁.toFinMA.imStep cnet₁.uniformPolicy) r₁ :=
  cnet₁.zenoFree_uniform cnet₁_rank

/-- Only the red selection is enabled at two red — stated at the
colour-vector grain (the action's second component), which is where
the fact is decidable by evaluation. -/
theorem cnet₁_only_red_20 : ∀ κ : cnet₁.IVec 0, κ ≠ ιr →
    ¬ cnet₁.IEnabled ⟨0, κ⟩ i20.1 := by decide

/-- Only the red selection is enabled at the mixed marking. -/
theorem cnet₁_only_red_11 : ∀ κ : cnet₁.IVec 0, κ ≠ ιr →
    ¬ cnet₁.IEnabled ⟨0, κ⟩ i11.1 := by decide

/-- The scheduler at two red: the sole enabled pair takes the whole
mass. -/
theorem cnet₁_choice_20 :
    cnet₁.uniformPolicy.choice i20 ⟨0, ιr⟩ = 1 := by
  show (if cnet₁.IEnabled ⟨0, ιr⟩ i20.1
    then ((cnet₁.enabledCount i20 : ℕ) : ℚ)⁻¹ else 0) = 1
  rw [if_pos (by decide : cnet₁.IEnabled ⟨0, ιr⟩ i20.1),
    show cnet₁.enabledCount i20 = 1 from by decide]
  norm_num

/-- The scheduler at the mixed marking: likewise. -/
theorem cnet₁_choice_11 :
    cnet₁.uniformPolicy.choice i11 ⟨0, ιr⟩ = 1 := by
  show (if cnet₁.IEnabled ⟨0, ιr⟩ i11.1
    then ((cnet₁.enabledCount i11 : ℕ) : ℚ)⁻¹ else 0) = 1
  rw [if_pos (by decide : cnet₁.IEnabled ⟨0, ιr⟩ i11.1),
    show cnet₁.enabledCount i11 = 1 from by decide]
  norm_num

/-- The mixed immediate kernel at two red: the whole mass rides the
red flip to the vanishing intermediate. -/
theorem cnet₁_imStep_20 (y : cnet₁.Tangible ⊕ cnet₁.Vanishing) :
    cnet₁.toFinMA.imStep cnet₁.uniformPolicy i20 y
      = if (Sum.inr i11 : cnet₁.Tangible ⊕ cnet₁.Vanishing) = y
        then 1 else 0 := by
  show (∑ a : cnet₁.IAct, cnet₁.uniformPolicy.choice i20 a
      * cnet₁.toFinMA.branch i20 a y) = _
  refine (Fintype.sum_sigma _).trans ?_
  rw [Fin.sum_univ_one]
  refine (Finset.sum_eq_single_of_mem ιr (mem_univ _)
    fun κ _ hκ => ?_).trans ?_
  · show (if cnet₁.IEnabled ⟨0, κ⟩ i20.1
      then ((cnet₁.enabledCount i20 : ℕ) : ℚ)⁻¹ else 0) * _ = 0
    rw [if_neg (cnet₁_only_red_20 κ hκ), zero_mul]
  · rw [cnet₁_choice_20, one_mul]
    show (if cnet₁.IEnabled ⟨0, ιr⟩ i20.1
      then (if cnet₁.toSum (cnet₁.ifire ⟨0, ιr⟩ i20.1) = y then 1 else 0)
      else (if Sum.inr i20 = y then 1 else 0)) = _
    rw [if_pos (by decide : cnet₁.IEnabled ⟨0, ιr⟩ i20.1), cnet₁_fire_20]

/-- The mixed immediate kernel at the mixed marking: the whole mass
rides the red flip to the tangible blue-only marking. -/
theorem cnet₁_imStep_11 (y : cnet₁.Tangible ⊕ cnet₁.Vanishing) :
    cnet₁.toFinMA.imStep cnet₁.uniformPolicy i11 y
      = if (Sum.inl t02 : cnet₁.Tangible ⊕ cnet₁.Vanishing) = y
        then 1 else 0 := by
  show (∑ a : cnet₁.IAct, cnet₁.uniformPolicy.choice i11 a
      * cnet₁.toFinMA.branch i11 a y) = _
  refine (Fintype.sum_sigma _).trans ?_
  rw [Fin.sum_univ_one]
  refine (Finset.sum_eq_single_of_mem ιr (mem_univ _)
    fun κ _ hκ => ?_).trans ?_
  · show (if cnet₁.IEnabled ⟨0, κ⟩ i11.1
      then ((cnet₁.enabledCount i11 : ℕ) : ℚ)⁻¹ else 0) * _ = 0
    rw [if_neg (cnet₁_only_red_11 κ hκ), zero_mul]
  · rw [cnet₁_choice_11, one_mul]
    show (if cnet₁.IEnabled ⟨0, ιr⟩ i11.1
      then (if cnet₁.toSum (cnet₁.ifire ⟨0, ιr⟩ i11.1) = y then 1 else 0)
      else (if Sum.inr i11 = y then 1 else 0)) = _
    rw [if_pos (by decide : cnet₁.IEnabled ⟨0, ιr⟩ i11.1), cnet₁_fire_11]

/-- The second cascade step, one fuel short of the working fuel: from
the vanishing mixed marking, one red flip absorbs in the blue-only
marking. -/
theorem cnet₁_absorb_mid :
    absorbIter (cnet₁.toFinMA.imStep cnet₁.uniformPolicy) 2
      (Sum.inr i11) t02 = 1 := by
  refine (absorbIter_succ_inr _ 1 i11 t02).trans ?_
  simp only [cnet₁_imStep_11, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq univ
    (Sum.inl t02 : cnet₁.Tangible ⊕ cnet₁.Vanishing)
    (fun y => absorbIter
      (cnet₁.toFinMA.imStep cnet₁.uniformPolicy) 1 y t02),
    if_pos (mem_univ _), absorbIter_inl, hitMass_inl, if_pos rfl]

/-- **The colour-flipping two-step cascade absorbs whole**: from two
red, absorption reaches the blue-only marking with mass 1 — two
zero-time flips through the vanishing mixed marking, the rank (a red
census) counting them down. -/
theorem cnet₁_cascade_absorb :
    cnet₁.toFinMA.absorb cnet₁.uniformPolicy r₁
      (Sum.inr i20) t02 = 1 := by
  show absorbIter (cnet₁.toFinMA.imStep cnet₁.uniformPolicy)
    (absFuel r₁) (Sum.inr i20) t02 = 1
  rw [show absFuel r₁ = 2 + 1 from by decide, absorbIter_succ_inr]
  simp only [cnet₁_imStep_20, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq univ
    (Sum.inr i11 : cnet₁.Tangible ⊕ cnet₁.Vanishing)
    (fun y => absorbIter
      (cnet₁.toFinMA.imStep cnet₁.uniformPolicy) 2 y t02),
    if_pos (mem_univ _)]
  exact cnet₁_absorb_mid

/-- The unguarded variant: both colour selections of the sole
immediate pass, so the conflict at the mixed marking is between two
*pairs* of one transition. -/
def cnet₂ : FinCISPN (Fin 1) (Fin 1) (Fin 1) Col 2 where
  delay := inertDelay
  ipre := fun _ _ => 1
  iread := fun _ _ => 0
  ipost := fun _ _ => 1
  iguard := fun _ _ => True
  iguard_dec := fun _ _ => inferInstance
  ireset := fun _ κ _ _ => if κ 0 0 = 0 then 1 else 0

def j11 : cnet₂.Vanishing := ⟨m11, by decide⟩

/-- Both pairs of the sole transition are enabled at the mixed
marking. -/
theorem cnet₂_count : cnet₂.enabledCount j11 = 2 := by decide

/-- **The uniform split is over pairs**: with a single immediate
transition whose two colour selections are both enabled, each pair
gets `½` — a transitions-only scheduler would have assigned the sole
transition the whole mass.  This is the control that pins the action
grain. -/
theorem cnet₂_pair_split :
    cnet₂.uniformPolicy.choice j11 ⟨0, ιr⟩ = 2⁻¹ := by
  show (if cnet₂.IEnabled ⟨0, ιr⟩ j11.1
    then ((cnet₂.enabledCount j11 : ℕ) : ℚ)⁻¹ else 0) = 2⁻¹
  rw [if_pos (by decide : cnet₂.IEnabled ⟨0, ιr⟩ j11.1), cnet₂_count]
  norm_num

end CispnControls

end Adequacy
end SuFunctor
