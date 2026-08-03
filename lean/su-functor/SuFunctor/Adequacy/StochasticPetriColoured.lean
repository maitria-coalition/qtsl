import SuFunctor.Adequacy.StochasticPetri

/-! # Adequacy: coloured stochastic Petri frames, delay-race face

The coloured formation of the stochastic-Petri dynamics story — the
"FinCSPN coloured compile" the row ledger named as missing — and its
delay-race adequacy square, at the finite time-abstract stratum.  The
companion of `SuFunctor.Adequacy.StochasticPetri`, one colour grain up;
the statics square (`SuFunctor.TokenGame`) was coloured-general from
birth and is consumed unchanged.

**The fragment.**  Coloured nets with per-place **finite colour boxes**
`K : P → Type` — the finite time-abstract materialization of the
founding formalism's per-place colour types ([EB10a] arXiv:1003.4812,
Definition 2.1): at this stratum colours are *static between jumps*
(the colour flow is the hybrid-process side of the flattening
triangle, not this square), so a finite box is the honest carrier.
Markings count tokens per place *and colour*
(`CMarking P K B := ∀ p, K p → Fin (B + 1)`), with the declared
capacity `B` gating **per colour class** — the fragment's convention,
chosen so the `Unit`-colour instance recovers the uncoloured fragment
on the nose (`FinSPN.toColoured`, the degeneracy theorems below).
Each delay transition carries, per **colour vector** (an assignment of
a colour to each of its input arcs, consumed block first, read block
reserving without removal):

* a **colour-dependent rate** `rate t κ` — the `D_T(c)` of the
  community's delay species; at this exact-rational grain a rate map
  is data, and the state-dependent-thinning reading of rates (the
  measure-weighted jump tier) is its measure-theoretic face, cited
  not imported;
* a **guard** `guard t κ` — a decidable predicate on colour vectors,
  which at the finite grain *is* a finite union of per-vector
  cylinders, the flattening memo's own phrase; kept as separate data
  (not folded into the rate) so guard rows compile as gates.  The
  boundary-*hitting* guard species stays deliberately separate: with
  colours static between jumps there is no motion to hit a boundary
  with — what materializes here is the guard's cylinder face;
* a **Dirac firing measure** `reset t κ` — produced colours a
  function of the reserved colour vector: the founding formalism's
  firing measure at its deterministic slice (the v1 restriction of
  the flattening design; kernel-valued firing measures are the named
  v2 delta, not entrenched here — nothing below mints a kernel
  encoding).

Inhibitor arcs do not exist, by formation, as everywhere in this
story; the statics module's `enabled_mono` is the exclusion's warrant.

**The community semantics** ([EB10a] delay-transition execution, at
colour): each pre-enabled *ordered assignment of distinct tokens to
input arcs* races its own exponential clock, at the rate the assigned
colours determine, guard permitting.  Ordered assignments realizing
the same colour vector are counted by the **coloured census**
(`Coloured.census`): per place and per colour class, the falling
factorial of the token count over the number of arcs assigned that
colour — under-supply in *any* colour class vanishes the census, so
pre-enabling is built into the count, colour-classwise.  The
community object is the coloured race chain `raceCtmc : FinCTMC` over
coloured markings.

**The compiled side** carries the house convention at the coloured
grain: rate rows in the **unordered** grain, one selection per token
*multiset per colour class*, with the arc-multiplicity dictionary now
`∏ₚ ∏ᵪ (arcs of colour c)!` — owned by the compiler, per colour
class.  The compile-commutes triangle (`compile_race_comm`) is again
*not* `rfl`: it **is** the coloured multiplicity-dictionary theorem
(`raceCount_eq_dict`), applied rowwise under the double product.

**The square** (`cspn_delay_adequacy`): compile the coloured net's
rows, close to jump rows, denote — and this agrees, by an invertible
globular cell, with interpreting the net as the coloured race chain
and including its jump-chain path law.  The proof is the
continuous-time square instantiated at the coloured race chain,
through the dictionary triangle — engine reuse, zero new inductions.

**Degeneracy, as theorems**: `FinSPN.toColoured` embeds the
uncoloured fragment at `Unit` colours, and the census, dictionary,
enabledness, firing, race intensities, and initial data all agree on
the nose (`toColoured_raceRate` and kin) — the coloured formation
*contains* the landed uncoloured one, so every uncoloured control is
inherited rather than re-run.

**Deliberately separate, named**: kernel-valued firing measures (v2;
the finite-leg mixture donor lives with the hybrid development);
boundary-hitting guard transitions (the crossing-budget lane);
coloured demonic/angelic/set-firing/supervision faces (each lands
beside its uncoloured module, consuming this formation); the
lex-sorted colour-vector carrier identification ρ and the flattening
cell (the triangle's own legs); the exponential time-law stratum,
exactly as for the uncoloured face. -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open SuFunctor.Universe (SpecDnf)
open Finset

/-! ## Coloured markings -/

/-- Coloured bounded markings: per place and colour, a token count at
most `B` — the capacity gate is per colour class, the fragment's
declared convention. -/
abbrev CMarking (P : Type) (K : P → Type) (B : ℕ) :=
  ∀ p, K p → Fin (B + 1)

variable {P T : Type} [Fintype P] [DecidableEq P] [Fintype T]
  {K : P → Type} [∀ p, Fintype (K p)] [∀ p, DecidableEq (K p)] {B : ℕ}

/-! ## The coloured census layer

Stated over bare arc-count data — the shared grain of the delay and
immediate species, in the house tradition of `jumpStep` and
`ZenoFree`: one census, one dictionary, one firing computation, read
by both. -/

namespace Coloured

/-- The per-colour arc demand of a colour vector at a place: how many
of the transition's arcs there are assigned colour `c`. -/
def vecDemand {a : P → ℕ} (κ : ∀ p, Fin (a p) → K p) (p : P)
    (c : K p) : ℕ :=
  (univ.filter fun j => κ p j = c).card

/-- **The coloured ordered census**: the number of ordered assignments
of distinct tokens to the input arcs realizing the colour vector —
per place and colour class, the falling factorial of the count over
the class demand.  `descFactorial` vanishes exactly on under-supply,
per colour class, so pre-enabling is built into the count. -/
def census {a : P → ℕ} (κ : ∀ p, Fin (a p) → K p)
    (m : CMarking P K B) : ℕ :=
  ∏ p, ∏ c, ((m p c : ℕ)).descFactorial (vecDemand κ p c)

/-- The unordered selection count: one selection per token multiset,
per colour class. -/
def selCount {a : P → ℕ} (κ : ∀ p, Fin (a p) → K p)
    (m : CMarking P K B) : ℕ :=
  ∏ p, ∏ c, ((m p c : ℕ)).choose (vecDemand κ p c)

/-- The coloured arc-multiplicity dictionary: per place and colour
class, the factorial of the class demand. -/
def dict {a : P → ℕ} (κ : ∀ p, Fin (a p) → K p) : ℕ :=
  ∏ p, ∏ c, (vecDemand κ p c).factorial

omit [DecidableEq P] in
/-- The census counts actual selection objects: per colour class, the
ordered assignments are the embeddings of that class's arc indices
into its tokens — the counting shadow of the statics' exchange-orbit
selection families, colour-classwise. -/
theorem census_eq_card_embeddings {a : P → ℕ}
    (κ : ∀ p, Fin (a p) → K p) (m : CMarking P K B) :
    census κ m
      = ∏ p, ∏ c,
          Fintype.card (Fin (vecDemand κ p c) ↪ Fin (m p c : ℕ)) := by
  refine Finset.prod_congr rfl fun p _ => ?_
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Fintype.card_embedding_eq]
  simp

omit [DecidableEq P] in
/-- **The coloured multiplicity dictionary, as a theorem**: the
ordered census factors as the dictionary times the unordered
selection count — `∏ₚ ∏ᵪ (class demand)!`, the compiler-owned
convention, verified against the community's ordered races per colour
class. -/
theorem census_eq_dict {a : P → ℕ} (κ : ∀ p, Fin (a p) → K p)
    (m : CMarking P K B) :
    census κ m = dict κ * selCount κ m := by
  unfold census dict selCount
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun c _ =>
    Nat.descFactorial_eq_factorial_mul_choose _ _

/-- The consumed-block demand: how many *ordinary* input arcs at `p`
are assigned colour `c` — the first block of the colour vector; the
read block reserves without removal. -/
def consCount {pre rd : P → ℕ} (κ : ∀ p, Fin (pre p + rd p) → K p)
    (p : P) (c : K p) : ℕ :=
  (univ.filter fun j : Fin (pre p) =>
    κ p (Fin.castAdd (rd p) j) = c).card

/-- The produced count: how many output arcs deposit colour `c` under
the Dirac firing outcome `ρ`. -/
def prodCount {po : P → ℕ} (ρ : ∀ p, Fin (po p) → K p) (p : P)
    (c : K p) : ℕ :=
  (univ.filter fun j : Fin (po p) => ρ p j = c).card

/-- The outcome count at a place and colour. -/
def outAt {pre rd po : P → ℕ} (κ : ∀ p, Fin (pre p + rd p) → K p)
    (ρ : ∀ p, Fin (po p) → K p) (m : CMarking P K B) (p : P)
    (c : K p) : ℕ :=
  (m p c : ℕ) - consCount κ p c + prodCount ρ p c

/-- Supply in the coloured capacity fragment: per place and colour
class, the reservation is supplied and the outcome respects the
capacity — firing blocks at capacity, colour-classwise. -/
def Supplied {pre rd po : P → ℕ} (κ : ∀ p, Fin (pre p + rd p) → K p)
    (ρ : ∀ p, Fin (po p) → K p) (m : CMarking P K B) : Prop :=
  ∀ p, ∀ c, vecDemand κ p c ≤ (m p c : ℕ) ∧ outAt κ ρ m p c ≤ B

instance {pre rd po : P → ℕ} (κ : ∀ p, Fin (pre p + rd p) → K p)
    (ρ : ∀ p, Fin (po p) → K p) (m : CMarking P K B) :
    Decidable (Supplied κ ρ m) :=
  inferInstanceAs (Decidable (∀ p, ∀ c,
    vecDemand κ p c ≤ (m p c : ℕ) ∧ outAt κ ρ m p c ≤ B))

/-- The fired marking (truncated at capacity for totality; under
`Supplied` the truncation is inert). -/
def fireAt {pre rd po : P → ℕ} (κ : ∀ p, Fin (pre p + rd p) → K p)
    (ρ : ∀ p, Fin (po p) → K p) (m : CMarking P K B) :
    CMarking P K B :=
  fun p c => ⟨min (outAt κ ρ m p c) B,
    Nat.lt_succ_of_le (min_le_right _ _)⟩

end Coloured

/-! ## The formation -/

/-- A coloured stochastic Petri net with per-place finite colour
boxes, declared capacity `B` per colour class, and delay transitions
whose rates, guards, and Dirac firing measures all read the reserved
colour vector: ordinary input arcs (`pre`, consumed), enabling arcs
(`read` — reserved, never removed), output arcs (`post`), and an
initial distribution over coloured markings.  No inhibitor field
exists — the formation restriction of the statics fragment,
unchanged.  Kernel-valued firing measures are deliberately
unrepresentable at this formation (the v1 Dirac slice). -/
structure FinCSPN (P T : Type) [Fintype P] [DecidableEq P]
    (K : P → Type) [∀ p, Fintype (K p)] [∀ p, DecidableEq (K p)]
    (B : ℕ) where
  /-- Ordinary input arcs per transition and place. -/
  pre : T → P → ℕ
  /-- Enabling arcs per transition and place. -/
  read : T → P → ℕ
  /-- Ordinary output arcs per transition and place. -/
  post : T → P → ℕ
  /-- The guard: a decidable predicate on colour vectors — at this
  finite grain, a finite union of per-vector cylinders. -/
  guard : (t : T) → (∀ p, Fin (pre t p + read t p) → K p) → Prop
  /-- The guard's decision procedure, carried as data so enabledness
  stays decidable at concrete nets. -/
  guard_dec : ∀ t κ, Decidable (guard t κ)
  /-- The colour-dependent delay rate `D_T(c)`. -/
  rate : (t : T) → (∀ p, Fin (pre t p + read t p) → K p) → ℚ
  rate_nonneg : ∀ t κ, 0 ≤ rate t κ
  /-- The Dirac firing measure: produced colours as a function of the
  reserved colour vector. -/
  reset : (t : T) → (∀ p, Fin (pre t p + read t p) → K p) →
    ∀ p, Fin (post t p) → K p
  /-- Initial-distribution mass at a coloured marking. -/
  init : CMarking P K B → ℚ
  init_nonneg : ∀ m, 0 ≤ init m
  init_sum : ∑ m, init m = 1

namespace FinCSPN

variable (N : FinCSPN P T K B)

/-- The colour vectors of a transition: one colour per input arc,
consumed block first. -/
abbrev CVec (t : T) : Type := ∀ p, Fin (N.pre t p + N.read t p) → K p

instance (t : T) (κ : N.CVec t) : Decidable (N.guard t κ) :=
  N.guard_dec t κ

/-- The coloured ordered census at a transition (the layer's census,
at the transition's colour vector). -/
abbrev raceCount (t : T) (κ : N.CVec t) (m : CMarking P K B) : ℕ :=
  Coloured.census κ m

/-- The unordered selection count at a transition. -/
abbrev selCount (t : T) (κ : N.CVec t) (m : CMarking P K B) : ℕ :=
  Coloured.selCount κ m

/-- The coloured arc-multiplicity dictionary at a transition. -/
abbrev dict (t : T) (κ : N.CVec t) : ℕ :=
  Coloured.dict κ

omit [Fintype T] in
/-- The coloured dictionary theorem, at the species: ordered census =
dictionary × unordered count. -/
theorem raceCount_eq_dict (t : T) (κ : N.CVec t) (m : CMarking P K B) :
    N.raceCount t κ m = N.dict t κ * N.selCount t κ m :=
  Coloured.census_eq_dict κ m

omit [Fintype T] in
/-- The census-to-embeddings tie, at the species. -/
theorem raceCount_eq_card_embeddings (t : T) (κ : N.CVec t)
    (m : CMarking P K B) :
    N.raceCount t κ m
      = ∏ p, ∏ c, Fintype.card
          (Fin (Coloured.vecDemand κ p c) ↪ Fin (m p c : ℕ)) :=
  Coloured.census_eq_card_embeddings κ m

/-- Enabledness in the coloured capacity fragment: the colour-classed
reservation is supplied, the outcome respects the capacity, and the
colour vector passes the guard. -/
def Enabled (t : T) (κ : N.CVec t) (m : CMarking P K B) : Prop :=
  Coloured.Supplied κ (N.reset t κ) m ∧ N.guard t κ

instance (t : T) (κ : N.CVec t) (m : CMarking P K B) :
    Decidable (N.Enabled t κ m) :=
  inferInstanceAs
    (Decidable (Coloured.Supplied κ (N.reset t κ) m ∧ N.guard t κ))

/-- The fired marking: consumed colours removed, reset colours
deposited (truncated at capacity for totality; under `Enabled` the
truncation is inert). -/
def fire (t : T) (κ : N.CVec t) (m : CMarking P K B) :
    CMarking P K B :=
  Coloured.fireAt κ (N.reset t κ) m

/-! ## The community object: the coloured race chain -/

/-- The total race intensity between coloured markings: every ordered
assignment races its own clock at the rate its colour vector
determines, guard permitting — the intensity to a target marking is
the census-weighted, colour-resolved rate sum. -/
def raceRate (m m' : CMarking P K B) : ℚ :=
  ∑ t, ∑ κ : N.CVec t,
    if N.Enabled t κ m ∧ N.fire t κ m = m'
    then (N.raceCount t κ m : ℚ) * N.rate t κ else 0

theorem raceRate_nonneg (m m' : CMarking P K B) :
    0 ≤ N.raceRate m m' :=
  Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun κ _ => by
    by_cases h : N.Enabled t κ m ∧ N.fire t κ m = m'
    · rw [if_pos h]
      exact mul_nonneg (Nat.cast_nonneg _) (N.rate_nonneg t κ)
    · rw [if_neg h]

/-- A marking at which nothing is enabled emits no race intensity —
the shared skeleton of the guard-gate and capacity controls. -/
theorem raceRate_eq_zero_of_not_enabled {m : CMarking P K B}
    (h : ∀ t κ, ¬ N.Enabled t κ m) (m' : CMarking P K B) :
    N.raceRate m m' = 0 :=
  Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun κ _ =>
    if_neg fun hc => h t κ hc.1

/-- **The community semantics of the fragment**: the coloured race
chain — the finite continuous-time Markov chain over coloured
markings whose off-diagonal rates are the colour-resolved race
intensities and whose initial distribution is the net's. -/
def raceCtmc (N : FinCSPN P T K B) : FinCTMC (CMarking P K B) where
  rate := N.raceRate
  init := N.init
  rate_nonneg := fun m m' _ => N.raceRate_nonneg m m'
  init_nonneg := N.init_nonneg
  init_sum := N.init_sum

/-! ## The compiled rows: the unordered convention, coloured -/

/-- **Compilation in the house convention**: rate rows in the
unordered grain — the coloured dictionary times the per-colour-class
unordered selection count times the colour-dependent rate, guard
rows gating — and the initial-distribution rows.  The off-diagonal
key type is inherited from the continuous-time row grain: a
self-loop firing is unrepresentable rather than linted (the thinning
convention). -/
noncomputable def compileCspn (N : FinCSPN P T K B) :
    CtmcRows (CMarking P K B) where
  rateRow := Finsupp.onFinset univ
    (fun q => ∑ t, ∑ κ : N.CVec t,
      if N.Enabled t κ q.1.1 ∧ N.fire t κ q.1.1 = q.1.2
      then ((N.dict t κ * N.selCount t κ q.1.1 : ℕ) : ℚ) * N.rate t κ
      else 0)
    (fun _ _ => mem_univ _)
  initRow := Finsupp.onFinset univ N.init (fun _ _ => mem_univ _)

/-- **The compile-commutes triangle — the coloured dictionary,
applied**: the unordered-convention rows are the compilation of the
community's coloured race chain.  Deliberately not definitional: the
two conventions genuinely differ by the per-colour-class
arc-multiplicity dictionary, and this triangle is
`raceCount_eq_dict` rowwise under the colour-vector sum. -/
theorem compile_race_comm (N : FinCSPN P T K B) :
    compileCspn N = compileCtmc (raceCtmc N) := by
  have ext2 : ∀ X Y : CtmcRows (CMarking P K B),
      X.rateRow = Y.rateRow → X.initRow = Y.initRow → X = Y := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h1 h2
    cases h1
    cases h2
    rfl
  refine ext2 _ _ (Finsupp.ext fun q => ?_) rfl
  show (∑ t, ∑ κ : N.CVec t,
      if N.Enabled t κ q.1.1 ∧ N.fire t κ q.1.1 = q.1.2
      then ((N.dict t κ * N.selCount t κ q.1.1 : ℕ) : ℚ) * N.rate t κ
      else 0)
    = N.raceRate q.1.1 q.1.2
  refine Finset.sum_congr rfl fun t _ => ?_
  refine Finset.sum_congr rfl fun κ _ => ?_
  by_cases hc : N.Enabled t κ q.1.1 ∧ N.fire t κ q.1.1 = q.1.2
  · rw [if_pos hc, if_pos hc]
    congr 1
    exact_mod_cast congrArg (Nat.cast (R := ℚ))
      (N.raceCount_eq_dict t κ q.1.1).symm
  · rw [if_neg hc, if_neg hc]

/-! ## The square -/

/-- **Adequacy of the coloured stochastic-Petri compilation,
delay-race face.**

In the double category `Crd (Traj (CMarking P K B) k)` of per-element
credal constraints over jump-horizon-`k` coloured-marking
trajectories: the loose-arrow diagram denoted by the jump closure of
the net's compiled rate rows — emitted in the unordered convention
with the compiler-owned coloured multiplicity dictionary, guard rows
gating, Dirac resets resolving targets — is isomorphic, by an
invertible globular cell, to the singleton-credal inclusion of the
coloured race chain's jump-chain path law.  Compile-close-denote
agrees with interpret-then-include, at the time-abstract stratum; the
compiled init rows carry the initial-marking face on the same ride.

The proof is the continuous-time square instantiated at the coloured
race chain, through the dictionary triangle — engine reuse, zero new
inductions. -/
theorem cspn_delay_adequacy (N : FinCSPN P T K B) (k : ℕ)
    {a : Crd (Traj (CMarking P K B) k)} :
    ∃ α : Cell
        (looseConj (atoms (jumpRows (compileCspn N)) k) : Loose a a)
        (singletonC ((raceCtmc N).jumpLaw k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  rw [compile_race_comm]
  exact ctmc_jump_adequacy (raceCtmc N) k

/-- **The thinning receipt**: coloured nets whose race intensities
agree between *distinct* markings (and whose initial distributions
agree) have equal jump-chain laws — a firing whose Dirac outcome
returns the source marking contributes only to the diagonal, which
the off-diagonal grain thins away. -/
theorem cspn_jumpLaw_thinning {T' : Type} [Fintype T']
    (N : FinCSPN P T K B) (N' : FinCSPN P T' K B)
    (hoff : ∀ m m', m ≠ m' → N.raceRate m m' = N'.raceRate m m')
    (hinit : N.init = N'.init) (k : ℕ) :
    (raceCtmc N).jumpLaw k = (raceCtmc N').jumpLaw k :=
  FinCTMC.jumpLaw_diag_blind _ _ hoff hinit k

/-! ## The semantic-universe wiring (in-module, per the standing
precedent for squares landing while the shared wiring file is hot) -/

/-- The compiled coloured net's presentation in the semantic
universe's fibre over jump-horizon-`k` coloured-marking
trajectories. -/
noncomputable def cspnDnf (N : FinCSPN P T K B) (k : ℕ) :
    SpecDnf (Plain.Joint (Traj (CMarking P K B) k)) :=
  ctmcJumpDnf (compileCspn N) k

/-- **The coloured delay-race square, wired to the semantic
universe**: the ideal point of a law models the compiled net's
presentation exactly when the law is the coloured race chain's
jump-chain path law. -/
theorem su_cspn_delay_adequacy (N : FinCSPN P T K B) (k : ℕ)
    (μ : SubPMF (Traj (CMarking P K B) k)) :
    idealPoint μ ∈ (cspnDnf N k).modelClass
      ↔ μ = (raceCtmc N).jumpLaw k := by
  unfold cspnDnf
  rw [compile_race_comm]
  exact su_ctmc_jump_adequacy (raceCtmc N) k μ

/-- The positive face: the coloured race chain's jump law models the
compiled net. -/
theorem su_cspn_jumpLaw_mem (N : FinCSPN P T K B) (k : ℕ) :
    idealPoint ((raceCtmc N).jumpLaw k) ∈ (cspnDnf N k).modelClass :=
  (su_cspn_delay_adequacy N k _).mpr rfl

/-- Ex falso at the net corner. -/
theorem su_cspn_bottom (N : FinCSPN P T K B) (k : ℕ) :
    (⊤ : Plain.Pen (Traj (CMarking P K B) k))
      ∉ (cspnDnf N k).modelClass := by
  unfold cspnDnf ctmcJumpDnf
  exact top_notMem_diagramDnf _

/-- The credal reading at the net corner, through the slice. -/
theorem su_cspn_slice (N : FinCSPN P T K B) (k : ℕ)
    (μ : SubPMF (Traj (CMarking P K B) k)) :
    idealPoint μ ∈ (cspnDnf N k).modelClass
      ↔ maxSlice (rayC ((raceCtmc N).jumpLaw k)) μ :=
  (su_cspn_delay_adequacy N k μ).trans
    (maxSlice_rayC (FinCTMC.jumpLaw_ne_zero _ k) μ).symm

end FinCSPN

/-! ## Degeneracy: the uncoloured fragment at `Unit` colours

The coloured formation contains the landed uncoloured one on the
nose.  Stated at field level (census, enabledness, firing, race
intensities, initial data); the law-level relabel packaging rides the
carrier-identification leg of the flattening triangle, where it is
needed. -/

/-- Unit-coloured markings are bounded markings. -/
def unitMarkingEquiv (P : Type) [Fintype P] [DecidableEq P] (B : ℕ) :
    BMarking P B ≃ CMarking P (fun _ => Unit) B where
  toFun m := fun p _ => m p
  invFun m := fun p => m p ()
  left_inv _ := rfl
  right_inv _ := rfl

namespace FinSPN

/-- The unit-colouring of an uncoloured net: guard everywhere true,
rates constant on the unique colour vector, unit resets, initial data
transported along the marking identification. -/
def toColoured (N : FinSPN P T B) :
    FinCSPN P T (fun _ => Unit) B where
  pre := N.pre
  read := N.read
  post := N.post
  guard := fun _ _ => True
  guard_dec := fun _ _ => inferInstance
  rate := fun t _ => N.rate t
  rate_nonneg := fun t _ => N.rate_nonneg t
  reset := fun _ _ _ _ => ()
  init := fun m => N.init fun p => m p ()
  init_nonneg := fun _ => N.init_nonneg _
  init_sum :=
    (Equiv.sum_comp (unitMarkingEquiv P B).symm N.init).trans N.init_sum

variable (N : FinSPN P T B)

omit [Fintype T] in
/-- At `Unit` colours the sole colour class carries the whole arc
demand. -/
theorem toColoured_vecDemand (t : T) (κ : N.toColoured.CVec t) (p : P)
    (c : Unit) :
    Coloured.vecDemand κ p c = N.demand t p := by
  unfold Coloured.vecDemand
  rw [Finset.filter_true_of_mem fun j _ => Subsingleton.elim _ _,
    Finset.card_univ, Fintype.card_fin]
  rfl

omit [Fintype T] in
/-- At `Unit` colours the consumed block is the ordinary arc count. -/
theorem toColoured_consCount (t : T) (κ : N.toColoured.CVec t) (p : P)
    (c : Unit) :
    Coloured.consCount κ p c = N.pre t p := by
  unfold Coloured.consCount
  rw [Finset.filter_true_of_mem fun j _ => Subsingleton.elim _ _,
    Finset.card_univ, Fintype.card_fin]
  rfl

omit [Fintype T] in
/-- At `Unit` colours every output arc deposits the sole colour. -/
theorem toColoured_prodCount (t : T) (κ : N.toColoured.CVec t) (p : P)
    (c : Unit) :
    Coloured.prodCount (N.toColoured.reset t κ) p c = N.post t p := by
  unfold Coloured.prodCount
  rw [Finset.filter_true_of_mem fun j _ => Subsingleton.elim _ _,
    Finset.card_univ, Fintype.card_fin]
  rfl

omit [Fintype T] in
/-- The outcome counts agree along the marking identification. -/
theorem toColoured_outAt (t : T) (κ : N.toColoured.CVec t)
    (m : BMarking P B) (p : P) (c : Unit) :
    Coloured.outAt κ (N.toColoured.reset t κ) (unitMarkingEquiv P B m)
        p c
      = N.outAt t m p := by
  unfold Coloured.outAt FinSPN.outAt
  rw [toColoured_consCount, toColoured_prodCount]
  rfl

omit [Fintype T] in
/-- The censuses agree along the marking identification. -/
theorem toColoured_raceCount (t : T) (κ : N.toColoured.CVec t)
    (m : BMarking P B) :
    N.toColoured.raceCount t κ (unitMarkingEquiv P B m)
      = N.raceCount t m := by
  show Coloured.census κ (unitMarkingEquiv P B m) = N.raceCount t m
  unfold Coloured.census FinSPN.raceCount
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Fintype.prod_unique]
  rw [toColoured_vecDemand]
  rfl

omit [Fintype T] in
/-- The dictionaries agree. -/
theorem toColoured_dict (t : T) (κ : N.toColoured.CVec t) :
    N.toColoured.dict t κ = N.dict t := by
  show Coloured.dict κ = N.dict t
  unfold Coloured.dict FinSPN.dict
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Fintype.prod_unique, toColoured_vecDemand]

omit [Fintype T] in
/-- Enabledness agrees along the marking identification: the guard is
everywhere true and the sole colour class carries the uncoloured
supply-and-capacity gate. -/
theorem toColoured_enabled_iff (t : T) (κ : N.toColoured.CVec t)
    (m : BMarking P B) :
    N.toColoured.Enabled t κ (unitMarkingEquiv P B m)
      ↔ N.Enabled t m := by
  unfold FinCSPN.Enabled Coloured.Supplied FinSPN.Enabled
  constructor
  · rintro ⟨hs, -⟩ p
    have hc := hs p ()
    rwa [toColoured_vecDemand, toColoured_outAt] at hc
  · intro h
    refine ⟨fun p c => ?_, trivial⟩
    rw [toColoured_vecDemand, toColoured_outAt]
    exact h p

omit [Fintype T] in
/-- The firings agree along the marking identification. -/
theorem toColoured_fire (t : T) (κ : N.toColoured.CVec t)
    (m : BMarking P B) :
    N.toColoured.fire t κ (unitMarkingEquiv P B m)
      = unitMarkingEquiv P B (N.fire t m) := by
  funext p c
  exact Fin.ext (by
    show min (Coloured.outAt κ (N.toColoured.reset t κ)
        (unitMarkingEquiv P B m) p c) B
      = min (N.outAt t m p) B
    rw [toColoured_outAt])

omit [Fintype T] in
/-- The initial data agree along the marking identification. -/
theorem toColoured_init (m : BMarking P B) :
    N.toColoured.init (unitMarkingEquiv P B m) = N.init m := rfl

/-- **The degeneracy theorem**: the coloured race intensities restrict
to the uncoloured ones along the marking identification — the
coloured formation contains the landed uncoloured fragment on the
nose. -/
theorem toColoured_raceRate (m m' : BMarking P B) :
    N.toColoured.raceRate (unitMarkingEquiv P B m)
        (unitMarkingEquiv P B m')
      = N.raceRate m m' := by
  unfold FinCSPN.raceRate FinSPN.raceRate
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Fintype.sum_unique]
  by_cases h : N.Enabled t m ∧ N.fire t m = m'
  · rw [if_pos ⟨(N.toColoured_enabled_iff t default m).mpr h.1, by
      rw [toColoured_fire, h.2]⟩, if_pos h, toColoured_raceCount]
    rfl
  · rw [if_neg (fun hc => h ⟨(N.toColoured_enabled_iff t default m).mp
      hc.1, (unitMarkingEquiv P B).injective (by
        rw [← toColoured_fire]
        exact hc.2)⟩), if_neg h]

end FinSPN

/-! ## Controls

Concrete closed forms pinning the coloured census and dictionary, the
guard gate, the colour-dependent rates, the Dirac reset flow, and the
per-colour-class capacity gate — with proofs deliberately independent
of the lemmas they guard (decidability, not rewriting): second
witnesses at the designed mutant loci.  Rational-valued controls
evaluate their finite sums via `Finset.sum_eq_single_of_mem` and
close with `norm_num`, per the standing kernel note (the kernel does
not reduce rational arithmetic). -/

namespace CspnControls

/-- Two colours on one place: `0` is red, `1` is blue. -/
abbrev Col : Fin 1 → Type := fun _ => Fin 2

/-- Two red tokens, no blue (capacity 2). -/
def m20 : CMarking (Fin 1) Col 2 := fun _ c => if c = 0 then 2 else 0

/-- One red, one blue. -/
def m11 : CMarking (Fin 1) Col 2 := fun _ _ => 1

/-- No red, two blue. -/
def m02 : CMarking (Fin 1) Col 2 := fun _ c => if c = 0 then 0 else 2

/-- Two of each — the full marking. -/
def m22 : CMarking (Fin 1) Col 2 := fun _ _ => 2

/-- The red colour vector of a one-arc transition. -/
def κr : Fin 1 → Fin 1 → Fin 2 := fun _ _ => 0

/-- The blue colour vector of a one-arc transition. -/
def κb : Fin 1 → Fin 1 → Fin 2 := fun _ _ => 1

/-- One place, two colours, capacity 2; one delay transition
consuming one token and producing one of the *opposite* colour (the
Dirac reset genuinely reads the colour vector), with colour-dependent
rate: red selections race at 2, blue at 3; no guard. -/
def cnetR : FinCSPN (Fin 1) (Fin 1) Col 2 where
  pre := fun _ _ => 1
  read := fun _ _ => 0
  post := fun _ _ => 1
  guard := fun _ _ => True
  guard_dec := fun _ _ => inferInstance
  rate := fun _ κ => if κ 0 0 = 0 then 2 else 3
  rate_nonneg := fun _ κ => by split <;> norm_num
  reset := fun _ κ _ _ => if κ 0 0 = 0 then 1 else 0
  init := fun m => if m = m20 then 1 else 0
  init_nonneg := fun m => by by_cases h : m = m20 <;> simp [h]
  init_sum := Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (mem_univ _))

/-- One red token among two: the red census is the falling factorial
`1`, the blue census `1` — the mixed marking's red-selection census. -/
example : cnetR.raceCount 0 κr m11 = 1 := by decide

/-- Two red tokens, red selection: census `2`. -/
example : cnetR.raceCount 0 κr m20 = 2 := by decide

/-- The blue selection at the red-only marking vanishes — per-class
under-supply kills the census even though total supply abounds. -/
example : cnetR.raceCount 0 κb m20 = 0 := by decide

/-- The Dirac reset genuinely moves colour: firing the red selection
at the mixed marking consumes red, deposits blue. -/
theorem cnetR_fire_flip : cnetR.fire 0 κr m11 = m02 := by decide

/-- Everything is capacity-blocked at the full marking: producing the
opposite colour would exceed the per-class capacity. -/
theorem cnetR_full_blocked :
    ∀ (t : Fin 1) (κ : cnetR.CVec t), ¬ cnetR.Enabled t κ m22 := by
  decide

/-- **The per-colour-class capacity gate has teeth**: no race
intensity leaves the full marking. -/
theorem cnetR_capacity (m' : CMarking (Fin 1) Col 2) :
    cnetR.raceRate m22 m' = 0 :=
  cnetR.raceRate_eq_zero_of_not_enabled cnetR_full_blocked m'

/-- Away from the red selection, nothing fires from the mixed marking
toward the blue-heavy target. -/
theorem cnetR_side02 : ∀ κ : cnetR.CVec 0, κ ≠ κr →
    ¬ (cnetR.Enabled 0 κ m11 ∧ cnetR.fire 0 κ m11 = m02) := by
  decide

/-- Away from the blue selection, nothing fires from the mixed
marking toward the red-heavy target. -/
theorem cnetR_side20 : ∀ κ : cnetR.CVec 0, κ ≠ κb →
    ¬ (cnetR.Enabled 0 κ m11 ∧ cnetR.fire 0 κ m11 = m20) := by
  decide

/-- **The colour-dependent rate, red leg**: the race intensity from
the mixed marking to the blue-heavy target is the red census times
the red rate — `1 · 2`. -/
theorem cnetR_rate_red : cnetR.raceRate m11 m02 = 2 := by
  show (∑ t : Fin 1, ∑ κ : cnetR.CVec t,
      if cnetR.Enabled t κ m11 ∧ cnetR.fire t κ m11 = m02
      then (cnetR.raceCount t κ m11 : ℚ) * cnetR.rate t κ else 0) = 2
  rw [Fin.sum_univ_one]
  refine (Finset.sum_eq_single_of_mem κr (mem_univ _)
    (fun κ _ hκ => if_neg (cnetR_side02 κ hκ))).trans ?_
  rw [if_pos ⟨by decide, by decide⟩,
    show cnetR.raceCount 0 κr m11 = 1 from by decide,
    show cnetR.rate 0 κr = 2 from rfl]
  norm_num

/-- **The colour-dependent rate, blue leg**: to the red-heavy target,
the blue census times the blue rate — `1 · 3`.  With the red leg,
this pins that the rate map genuinely reads the colour vector. -/
theorem cnetR_rate_blue : cnetR.raceRate m11 m20 = 3 := by
  show (∑ t : Fin 1, ∑ κ : cnetR.CVec t,
      if cnetR.Enabled t κ m11 ∧ cnetR.fire t κ m11 = m20
      then (cnetR.raceCount t κ m11 : ℚ) * cnetR.rate t κ else 0) = 3
  rw [Fin.sum_univ_one]
  refine (Finset.sum_eq_single_of_mem κb (mem_univ _)
    (fun κ _ hκ => if_neg (cnetR_side20 κ hκ))).trans ?_
  rw [if_pos ⟨by decide, by decide⟩,
    show cnetR.raceCount 0 κb m11 = 1 from by decide,
    show cnetR.rate 0 κb = 3 from rfl]
  norm_num

/-- The guarded variant: same net, but only red selections pass the
guard. -/
def cnetG : FinCSPN (Fin 1) (Fin 1) Col 2 where
  pre := fun _ _ => 1
  read := fun _ _ => 0
  post := fun _ _ => 1
  guard := fun _ κ => κ 0 0 = 0
  guard_dec := fun _ _ => inferInstance
  rate := fun _ _ => 5
  rate_nonneg := fun _ _ => by norm_num
  reset := fun _ κ _ _ => if κ 0 0 = 0 then 1 else 0
  init := fun m => if m = m20 then 1 else 0
  init_nonneg := fun m => by by_cases h : m = m20 <;> simp [h]
  init_sum := Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (mem_univ _))

/-- At the blue-only marking nothing is enabled: the red selection is
colour-under-supplied, the blue selection is guard-blocked — supply
alone would licence it. -/
theorem cnetG_blue_blocked :
    ∀ (t : Fin 1) (κ : cnetG.CVec t), ¬ cnetG.Enabled t κ m02 := by
  decide

/-- **The guard gate has teeth**: a supplied selection whose colour
vector fails the guard contributes nothing — no race intensity leaves
the blue-only marking. -/
theorem cnetG_gate (m' : CMarking (Fin 1) Col 2) :
    cnetG.raceRate m02 m' = 0 :=
  cnetG.raceRate_eq_zero_of_not_enabled cnetG_blue_blocked m'

/-- The demand-2 net: one transition consuming two tokens, producing
none — the dictionary's nontrivial witness. -/
def cnetD : FinCSPN (Fin 1) (Fin 1) Col 2 where
  pre := fun _ _ => 2
  read := fun _ _ => 0
  post := fun _ _ => 0
  guard := fun _ _ => True
  guard_dec := fun _ _ => inferInstance
  rate := fun _ _ => 1
  rate_nonneg := fun _ _ => zero_le_one
  reset := fun _ _ _ j => j.elim0
  init := fun m => if m = m20 then 1 else 0
  init_nonneg := fun m => by by_cases h : m = m20 <;> simp [h]
  init_sum := Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (mem_univ _))

/-- The both-red vector of the demand-2 transition. -/
def κrr : Fin 1 → Fin 2 → Fin 2 := fun _ _ => 0

/-- The mixed vector of the demand-2 transition: first arc red,
second blue. -/
def κrb : Fin 1 → Fin 2 → Fin 2 := fun _ j => j

/-- Two red tokens on two red arcs: the ordered census is the falling
factorial `2 · 1 = 2` — not `2² = 4`; ordered assignments are of
*distinct* tokens. -/
example : cnetD.raceCount 0 κrr m20 = 2 := by decide

/-- The same count through the coloured dictionary:
`2! · C(2,2) = 2 · 1`. -/
example : cnetD.dict 0 κrr * cnetD.selCount 0 κrr m20 = 2 := by decide

/-- The mixed vector at the red-only marking: the blue class is
under-supplied, so the census vanishes — while total supply (two
tokens for two arcs) would suffice. -/
example : cnetD.raceCount 0 κrb m20 = 0 := by decide

/-- The mixed vector at the mixed marking: one choice per class,
census `1`, dictionary `1!·1! = 1`. -/
example : cnetD.raceCount 0 κrb m11 = 1 := by decide

example : cnetD.dict 0 κrb = 1 := by decide

end CspnControls

end Adequacy
end SuFunctor
