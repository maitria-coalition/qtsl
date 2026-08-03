import SuFunctor.Adequacy.StochasticPetriDemonic

/-! # Adequacy: stochastic Petri frames, flattening premises and the
commuting-triangle instance

The flattening bridge of the stochastic-Petri adequacy story: the net
formalism and the flattened mode-indexed formalism each carry their own
compiled reading into the semantic universe, and the translation
between *presentations* — one mode per reachable tangible marking, jump
intensities through the multiplicity dictionary and the cascade-closed
resets ([EB10b]'s construction, at this fragment's grain) — bridges the
two compiled readings by an invertible globular cell.  The flattening
is apparatus of the triangle: it is **not** an edge of either adequacy
square and not a definition of anything — the flattened object is
combinatorially large in the net (one mode per reachable marking), so
the net-side compile remains the structural semantics and the triangle
is what makes the two readings interchangeable *as claims*.

**The premise rows.**  The flattening is a partial translation, defined
under the community's premise set ([EB10b] Thm 5.2 and its kin), and
this module carries those premises as certificate-shaped objects at the
uncoloured grain:

* `TangibleInit` — no immediate transition is enabled at the initial
  support (decidable); under it the closed chain's initial distribution
  is the net's on the nose (`tangibleChain_init_eq_of_tangibleInit`,
  consuming the landed initial-tangibility receipt).
* `TokenBound` — the invariant-bounded-token-count premise in the
  witness-vector idiom: a positive place-weighting under which no
  transition of either species increases the weighted token count.
  Soundness is the step pair `wsum_fire_le`/`wsum_ifire_le` (the
  capacity truncation is inert under enabledness, and read arcs return
  their reservation), closed under reachability (`wsum_le_of_reach`)
  with the per-place corollary `count_le_of_reach` — a bound intrinsic
  to the witness vector and the initial marking, independent of the
  declared capacity.  This is the clause a flattening at the unbounded
  grain consumes for the finiteness of its mode roster.  The row has
  teeth: a token-creating control net admits *no* witness vector
  (`netC_tokenBound_isEmpty`).
* `CascadeRank` — cascade termination, consumed from the landed
  immediate/cascade face, not re-proved.
* `FlattenPremises` bundles the three.  The remaining community
  premise — per-place colour-box discharge — and the guard/boundary
  row identification are **coloured-stratum** obligations: the
  uncoloured formation has neither colour boxes nor guards, so neither
  admits a non-vacuous statement here; both are named for the coloured
  successor rather than silently dropped.

**The multiplicity dictionary** is already a theorem of this tree
(`raceCount_eq_dict`, with its rate-level faces `compile_race_comm` and
`compile_ispn_comm`); this module adds the second witnesses the landed
controls lack — an arity-3 census and a heterogeneous two-place census —
pinning the factorial beyond arity 2 and the per-place product
structure (`SpnDictControls`).

**The triangle.**  `flatten_triangle_of_agree` is the statement
skeleton at this grain: for any net, declared scheduler, and rank
certificate, and any flat presentation on an abstract mode carrier
identified with the tangible markings, IF the transported flat
presentation agrees with the scheduler-closed net off-diagonally and
initially — the atom-transport obligations at this fragment's compiled
atom roster (initial rows and rate rows; holding-time, guard, and
coloured-reset atoms live at strata this fragment does not compile) —
THEN the net-compiled reading and the flatten-compiled reading are
isomorphic by an invertible globular cell of `Crd (Traj N.Tangible k)`,
packaged by `Crd.looseIso_ofIff` exactly as every landed square is.
Both sides are house compiles; no community semantics and no process
construction enter the cell.  The carrier identification at this grain
is a finite mode enumeration (`FinCTMC.relabel` along an equivalence);
at the coloured grain it becomes the lex-sorted colour-vector/chart
identification, which is the successor's obligation, not this
module's.

**The instance** (`SpnFlattenWitness`): the drain-net-plus-counter's
uncoloured jump-skeleton shadow — two places (a supply place and a
counter), an arity-2 delay transition at rate 3 whose fired marking
cascades through two immediate steps (the flattened edge's rate 6
carries the dictionary factor 2! and the cascade-closed reset), an
arity-1 delay transition at rate 1, and a point initial distribution at
a tangible marking.  The flat presentation `flatWitness` is hand-written
[EB10b]-construction data on the mode roster `Fin 3` with literal
rational rates; the agreement obligations are discharged by explicit
finite computation, and the compiled closure is thereby the check on
the hand construction.  `witness_triangle` is the invertible cell;
`witness_demonic_directed` packages the membership lemma — the
flattened law is admitted by the compiled demonic reading, so
universally-quantified demonic verdicts transfer *to* it (the sound
direction only; no envelope equality is stated, and at this net the
enabling-respecting arena is a singleton — one immediate transition —
so the directed cell demonstrates the mechanism while arena plurality
stays pinned by the demonic face's own control net).

**Deliberately separate, named**: the coloured instance (colour boxes,
drift/diffusion segment data, boundary-slab guards, the padding or
mode-indexed-dimension carrier identifications); kernel-valued firing
measures (this fragment's resets are Dirac by construction); the
angelic directed face (landed in the angelic module).  The former-level
triangle at THIS grain is discharged in
`StochasticPetriFlattenAgreement` — the flattening constructed for
every net and the agreement derived from it; the abstract-shape-roster
generality beyond the uncoloured grain rides the coloured successor. -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Finset

variable {P T U : Type} [Fintype P] [DecidableEq P] [Fintype T]
  [Fintype U] {B : ℕ}

/-! ## Transport of a chain presentation along a carrier bijection

The carrier identification's action at the presentation level: rates
and initial masses precompose with the inverse.  This is what
"transporting the flattened diagram along the mode identification"
means for row-compiled chain presentations. -/

/-- Relabel a finite continuous-time chain along an equivalence of
state spaces. -/
def FinCTMC.relabel {S S' : Type} [Fintype S] [Fintype S'] (e : S ≃ S')
    (M : FinCTMC S) : FinCTMC S' where
  rate x y := M.rate (e.symm x) (e.symm y)
  init x := M.init (e.symm x)
  rate_nonneg := fun _ _ h =>
    M.rate_nonneg _ _ fun hc => h (e.symm.injective hc)
  init_nonneg := fun _ => M.init_nonneg _
  init_sum := (Equiv.sum_comp e.symm M.init).trans M.init_sum

@[simp] theorem FinCTMC.relabel_rate {S S' : Type} [Fintype S]
    [Fintype S'] (e : S ≃ S') (M : FinCTMC S) (x y : S') :
    (M.relabel e).rate x y = M.rate (e.symm x) (e.symm y) := rfl

@[simp] theorem FinCTMC.relabel_init {S S' : Type} [Fintype S]
    [Fintype S'] (e : S ≃ S') (M : FinCTMC S) (x : S') :
    (M.relabel e).init x = M.init (e.symm x) := rfl

/-! ## The weighted token count -/

/-- The weighted token count of a bounded marking under a place
weighting. -/
def wsum (w : P → ℕ) (m : BMarking P B) : ℕ := ∑ p, w p * (m p : ℕ)

namespace FinISPN

variable (N : FinISPN P T U B)

/-! ## Premise row: initial tangibility -/

/-- **The initial-tangibility premise** ([EB10b] Thm 5.2's "no
immediate transition enabled initially", at the initial-support
grain): vanishing markings carry no initial mass.  Decidable, so
concrete nets discharge it by computation. -/
def TangibleInit : Prop :=
  ∀ m : BMarking P B, N.IsVanishing m → N.delay.init m = 0

instance : Decidable N.TangibleInit :=
  inferInstanceAs
    (Decidable (∀ m, N.IsVanishing m → N.delay.init m = 0))

/-- Under the initial-tangibility premise the closed chain's initial
distribution is the net's on the nose — the landed initial-tangibility
receipt, consumed at the premise row. -/
theorem tangibleChain_init_eq_of_tangibleInit (h : N.TangibleInit)
    (σ : Policy N.Vanishing U) (r : N.Vanishing → ℕ)
    (hr : ZenoFree (N.toFinMA.imStep σ) r) (s : N.Tangible) :
    (N.tangibleChain σ r hr).init s = N.delay.init s.1 :=
  N.tangibleChain_init_of_tangible σ r hr h s

/-! ## Premise row: the invariant token bound, witness-vector idiom -/

/-- **The invariant-bounded-token-count premise, as a certificate**: a
positive place weighting under which no transition of either species
increases the weighted token count.  The conditions are decidable
per-transition arithmetic on the arc data — the checker's side of the
witness-vector idiom. -/
structure TokenBound (N : FinISPN P T U B) where
  /-- The witness vector: a weight per place. -/
  w : P → ℕ
  /-- Positivity: every place is genuinely counted. -/
  pos : ∀ p, 0 < w p
  /-- Delay transitions do not increase the weighted count. -/
  delay_le : ∀ t : T,
    ∑ p, w p * N.delay.post t p ≤ ∑ p, w p * N.delay.pre t p
  /-- Immediate transitions do not increase the weighted count. -/
  imm_le : ∀ u : U, ∑ p, w p * N.ipost u p ≤ ∑ p, w p * N.ipre u p

omit [Fintype T] [Fintype U] in
/-- The fired marking's count at a place, under enabledness: the
capacity truncation is inert, and the outcome is the exact arithmetic
one. -/
theorem fire_val_of_enabled (t : T) (m : BMarking P B)
    (ht : N.delay.Enabled t m) (p : P) :
    (N.delay.fire t m p : ℕ)
      = (m p : ℕ) - N.delay.pre t p + N.delay.post t p := by
  show min (N.delay.outAt t m p) B = _
  rw [min_eq_left (ht p).2]
  rfl

omit [Fintype T] [Fintype U] in
/-- The immediate twin. -/
theorem ifire_val_of_enabled (u : U) (m : BMarking P B)
    (hu : N.IEnabled u m) (p : P) :
    (N.ifire u m p : ℕ) = (m p : ℕ) - N.ipre u p + N.ipost u p := by
  show min (N.iOutAt u m p) B = _
  rw [min_eq_left (hu p).2]
  rfl

omit [Fintype T] [Fintype U] in
/-- **Step soundness, delay species**: an enabled delay firing does
not increase the weighted token count.  Enabledness is load-bearing
twice — it keeps the truncation inert and the reservation supplied. -/
theorem wsum_fire_le (tb : N.TokenBound) (t : T) (m : BMarking P B)
    (ht : N.delay.Enabled t m) :
    wsum tb.w (N.delay.fire t m) ≤ wsum tb.w m := by
  have hpre : ∀ p, N.delay.pre t p ≤ (m p : ℕ) := fun p =>
    le_trans (Nat.le_add_right _ _) (ht p).1
  calc wsum tb.w (N.delay.fire t m)
      = (∑ p, tb.w p * ((m p : ℕ) - N.delay.pre t p))
          + ∑ p, tb.w p * N.delay.post t p := by
        unfold wsum
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [N.fire_val_of_enabled t m ht p, Nat.mul_add]
    _ ≤ (∑ p, tb.w p * ((m p : ℕ) - N.delay.pre t p))
          + ∑ p, tb.w p * N.delay.pre t p :=
        Nat.add_le_add_left (tb.delay_le t) _
    _ = wsum tb.w m := by
        unfold wsum
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Nat.mul_add, Nat.sub_add_cancel (hpre p)]

omit [Fintype T] [Fintype U] in
/-- **Step soundness, immediate species.** -/
theorem wsum_ifire_le (tb : N.TokenBound) (u : U) (m : BMarking P B)
    (hu : N.IEnabled u m) :
    wsum tb.w (N.ifire u m) ≤ wsum tb.w m := by
  have hpre : ∀ p, N.ipre u p ≤ (m p : ℕ) := fun p =>
    le_trans (Nat.le_add_right _ _) (hu p).1
  calc wsum tb.w (N.ifire u m)
      = (∑ p, tb.w p * ((m p : ℕ) - N.ipre u p))
          + ∑ p, tb.w p * N.ipost u p := by
        unfold wsum
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [N.ifire_val_of_enabled u m hu p, Nat.mul_add]
    _ ≤ (∑ p, tb.w p * ((m p : ℕ) - N.ipre u p))
          + ∑ p, tb.w p * N.ipre u p :=
        Nat.add_le_add_left (tb.imm_le u) _
    _ = wsum tb.w m := by
        unfold wsum
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Nat.mul_add, Nat.sub_add_cancel (hpre p)]

/-- Reachability by enabled firings of either species. -/
inductive Reach (N : FinISPN P T U B) (m : BMarking P B) :
    BMarking P B → Prop
  | refl : Reach N m m
  | delay {m' : BMarking P B} (t : T) (h : Reach N m m')
      (ht : N.delay.Enabled t m') : Reach N m (N.delay.fire t m')
  | imm {m' : BMarking P B} (u : U) (h : Reach N m m')
      (hu : N.IEnabled u m') : Reach N m (N.ifire u m')

omit [Fintype T] [Fintype U] in
/-- The weighted count is non-increasing along reachability. -/
theorem wsum_le_of_reach (tb : N.TokenBound) {m m' : BMarking P B}
    (h : N.Reach m m') : wsum tb.w m' ≤ wsum tb.w m := by
  induction h with
  | refl => exact le_rfl
  | delay t h ht ih => exact le_trans (N.wsum_fire_le tb t _ ht) ih
  | imm u h hu ih => exact le_trans (N.wsum_ifire_le tb u _ hu) ih

omit [Fintype T] [Fintype U] in
/-- **The intrinsic per-place token bound**: every reachable marking's
count at every place is bounded by the initial weighted count — the
witness vector and the initial marking alone, no declared capacity
consulted.  This is the clause the flattening's finite mode roster
consumes at the unbounded grain. -/
theorem count_le_of_reach (tb : N.TokenBound) {m m' : BMarking P B}
    (h : N.Reach m m') (p : P) : (m' p : ℕ) ≤ wsum tb.w m :=
  le_trans
    (le_trans (Nat.le_mul_of_pos_left _ (tb.pos p))
      (Finset.single_le_sum
        (f := fun q => tb.w q * (m' q : ℕ))
        (fun _ _ => Nat.zero_le _) (mem_univ p)))
    (N.wsum_le_of_reach tb h)

/-! ## The premise bundle -/

/-- **The flattening's definedness premises, bundled** at the
uncoloured grain: initial tangibility, the invariant token bound, and
cascade termination (the landed rank certificate).  The remaining
community premise — per-place colour-box discharge via exit guards —
and the guard-row identification are coloured-stratum obligations with
no non-vacuous uncoloured statement; they are the coloured successor's
rows, named here rather than silently dropped. -/
structure FlattenPremises (N : FinISPN P T U B) where
  /-- No initial mass on vanishing markings. -/
  init_tangible : N.TangibleInit
  /-- The invariant token bound, witness-vector idiom. -/
  bound : N.TokenBound
  /-- The cascade rank. -/
  rank : N.Vanishing → ℕ
  /-- Cascade termination, certified by the rank. -/
  cascade : N.CascadeRank rank

/-! ## The triangle, statement skeleton at this grain

Both sides are house compiles.  The flat presentation is data on an
abstract mode carrier; the agreement hypotheses are the atom-transport
obligations at this fragment's compiled atom roster (initial rows and
rate rows).  No process is constructed inside the cell: the pointwise
equivalence runs through the landed compile-commutes triangles and the
diagonal-blindness of the jump law. -/

/-- **The commuting triangle, packaged from agreement**: if the flat
presentation, transported along the mode identification, agrees with
the scheduler-closed net off-diagonally and initially, then the
net-compiled reading and the flatten-compiled reading denote
isomorphic constraints — an invertible globular cell of
`Crd (Traj N.Tangible k)`, at every jump horizon. -/
theorem flatten_triangle_of_agree (σ : Policy N.Vanishing U)
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
          (closeMaRows N.compileIspn (compilePolicy σ) (absFuel r))) k) :
          Loose a a)
        (looseConj (atoms (jumpRows (compileCtmc (flat.relabel e))) k))
        (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  refine Crd.looseIso_ofIff fun μ => ?_
  rw [compile_ispn_comm, compile_closeMa_comm N.toFinMA σ r hr,
    compile_jump_comm (N.toFinMA.close σ r hr),
    compile_jump_comm (flat.relabel e),
    satAtoms_iff (compile_wf (N.toFinMA.close σ r hr).jumpChain) μ,
    satAtoms_iff (compile_wf (flat.relabel e).jumpChain) μ]
  show μ = (N.toFinMA.close σ r hr).jumpLaw k
    ↔ μ = (flat.relabel e).jumpLaw k
  rw [FinCTMC.jumpLaw_diag_blind (flat.relabel e)
    (N.toFinMA.close σ r hr) hoff hinit k]

variable [DecidableEq U]

/-- **The demonic directed face, packaged from agreement**: the
transported flat presentation's compiled reading *entails* the
compiled demonic reading — the flattened law is one arena member's
law, so every universally-quantified demonic verdict transfers to it.
A directed cell, sound direction only; the reverse entailment is not
claimed (the demonic set quantifies over adversaries the flattening
never sees). -/
theorem flatten_demonic_directed_of_agree {r : N.Vanishing → ℕ}
    (hrk : N.CascadeRank r) (σ : N.RespScheduler)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).rate s s')
    (hinit : (flat.relabel e).init
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).init)
    (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ _α : Cell
        (looseConj (atoms (jumpRows (compileCtmc (flat.relabel e))) k) :
          Loose a a)
        (N.ispnDemonicC (absFuel r) k) (𝟙 a) (𝟙 a), True := by
  refine ⟨Crd.cellOfEntails fun μ hμ => ?_, trivial⟩
  rw [compile_jump_comm (flat.relabel e),
    satAtoms_iff (compile_wf (flat.relabel e).jumpChain) μ] at hμ
  have hμ' : μ = (flat.relabel e).jumpLaw k := hμ
  have hlaw : (flat.relabel e).jumpLaw k
      = N.tangiblePathLaw σ.1 r (N.respZenoFree hrk σ) k :=
    FinCTMC.jumpLaw_diag_blind _ _ hoff hinit k
  rw [hμ', hlaw]
  exact (N.ispnDemonicC_iff hrk k _).mpr ⟨σ, singletonC_self _⟩

end FinISPN

/-! ## Controls: the dictionary beyond arity 2

The multiplicity dictionary is the landed theorem `raceCount_eq_dict`;
these controls are its second witnesses past the landed ones — the
factorial at arity 3 and the per-place product on a heterogeneous
two-place demand — with proofs deliberately independent of the lemma
they guard (decidability, not rewriting). -/

namespace SpnDictControls

/-- One place, one transition, capacity `3`: demand three tokens. -/
def race₃ : FinSPN (Fin 1) (Fin 1) 3 where
  pre := fun _ _ => 3
  read := fun _ _ => 0
  post := fun _ _ => 0
  rate := fun _ => 1
  rate_nonneg := fun _ => zero_le_one
  init := fun m => if m = fun _ => (3 : Fin 4) then 1 else 0
  init_nonneg := fun m => by
    by_cases h : m = fun _ => (3 : Fin 4) <;> simp [h]
  init_sum := Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (mem_univ _))

/-- Three tokens, demand three: the ordered census is `3! = 6`. -/
theorem race₃_census :
    race₃.raceCount 0 (fun _ => (3 : Fin 4)) = 6 := by decide

/-- The dictionary factor at arity 3 is the full factorial. -/
theorem race₃_dict : race₃.dict 0 = 6 := by decide

/-- The same census through the dictionary: `3! · C(3,3) = 6 · 1`. -/
theorem race₃_factor :
    race₃.raceCount 0 (fun _ => (3 : Fin 4))
      = race₃.dict 0 * race₃.selCount 0 (fun _ => (3 : Fin 4)) := by
  decide

/-- The marking with supplies `(3, 2)`. -/
def m₃₂ : BMarking (Fin 2) 3 := fun p => if p = 0 then 3 else 2

/-- Two places, one transition, capacity `3`: heterogeneous demands —
two tokens from place `0`, one from place `1`. -/
def race₂₁ : FinSPN (Fin 2) (Fin 1) 3 where
  pre := fun _ p => if p = 0 then 2 else 1
  read := fun _ _ => 0
  post := fun _ _ => 0
  rate := fun _ => 1
  rate_nonneg := fun _ => zero_le_one
  init := fun m => if m = m₃₂ then 1 else 0
  init_nonneg := fun m => by by_cases h : m = m₃₂ <;> simp [h]
  init_sum := Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (mem_univ _))

/-- The heterogeneous ordered census: `(3·2) · 2 = 12`. -/
theorem race₂₁_census : race₂₁.raceCount 0 m₃₂ = 12 := by decide

/-- The per-place dictionary product: `2! · 1! = 2`. -/
theorem race₂₁_dict : race₂₁.dict 0 = 2 := by decide

/-- The unordered selection count: `C(3,2) · C(2,1) = 6`. -/
theorem race₂₁_sel : race₂₁.selCount 0 m₃₂ = 6 := by decide

/-- The census through the dictionary, heterogeneous: `12 = 2 · 6`. -/
theorem race₂₁_factor :
    race₂₁.raceCount 0 m₃₂ = race₂₁.dict 0 * race₂₁.selCount 0 m₃₂ := by
  decide

end SpnDictControls

/-! ## Controls: the token-bound refusal -/

namespace SpnBoundControls

/-- A one-place token-creating net: one delay transition producing a
token from nothing (no immediate species). -/
def netC : FinISPN (Fin 1) (Fin 1) (Fin 0) 2 where
  delay :=
    { pre := fun _ _ => 0
      read := fun _ _ => 0
      post := fun _ _ => 1
      rate := fun _ => 1
      rate_nonneg := fun _ => zero_le_one
      init := fun m => if m = fun _ => (0 : Fin 3) then 1 else 0
      init_nonneg := fun m => by
        by_cases h : m = fun _ => (0 : Fin 3) <;> simp [h]
      init_sum :=
        Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (mem_univ _)) }
  ipre := fun u => u.elim0
  iread := fun u => u.elim0
  ipost := fun u => u.elim0

/-- **The refusal**: the token-creating net admits no witness vector —
any candidate would need a non-positive weight at the created place.
The premise row has teeth. -/
theorem netC_tokenBound_isEmpty : IsEmpty netC.TokenBound := by
  refine ⟨fun tb => ?_⟩
  have h := tb.delay_le 0
  rw [Fin.sum_univ_one, Fin.sum_univ_one,
    show netC.delay.post 0 0 = 1 from rfl,
    show netC.delay.pre 0 0 = 0 from rfl] at h
  have hp := tb.pos 0
  omega

end SpnBoundControls

/-! ## The instance: the drain-net skeleton and its flattening -/

namespace SpnFlattenWitness

open FinISPN

/-- Marking constructor on two places at capacity 2. -/
def mk2 (a b : Fin 3) : BMarking (Fin 2) 2 :=
  fun p => if p = 0 then a else b

/-- **The witness net** — the drain-net-plus-counter's uncoloured
jump-skeleton shadow.  Place `0` is the supply, place `1` the counter;
delay transition `0` (the drain) consumes two supply tokens (arity 2 —
the dictionary factor is genuinely `2!`) and produces two counter
tokens at rate `3`; delay transition `1` (evaporation) consumes one
supply token at rate `1`; the immediate transition consumes one
counter token, so counter-positive markings are vanishing and the
drain's fired marking cascades in two immediate steps.  Initial
distribution: a point mass at two supply tokens — tangible. -/
def wnet : FinISPN (Fin 2) (Fin 2) (Fin 1) 2 where
  delay :=
    { pre := fun t p =>
        if t = 0 then (if p = 0 then 2 else 0)
        else (if p = 0 then 1 else 0)
      read := fun _ _ => 0
      post := fun t p => if t = 0 ∧ p = 1 then 2 else 0
      rate := fun t => if t = 0 then 3 else 1
      rate_nonneg := fun t => by
        by_cases h : t = 0
        · rw [if_pos h]; norm_num
        · rw [if_neg h]; norm_num
      init := fun m => if m = mk2 2 0 then 1 else 0
      init_nonneg := fun m => by by_cases h : m = mk2 2 0 <;> simp [h]
      init_sum :=
        Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (mem_univ _)) }
  ipre := fun _ p => if p = 1 then 1 else 0
  iread := fun _ _ => 0
  ipost := fun _ _ => 0

/-- The tangible markings, named: counter empty. -/
def T00 : wnet.Tangible := ⟨mk2 0 0, by decide⟩
def T10 : wnet.Tangible := ⟨mk2 1 0, by decide⟩
def T20 : wnet.Tangible := ⟨mk2 2 0, by decide⟩

/-- The vanishing markings, named: counter positive. -/
def V01 : wnet.Vanishing := ⟨mk2 0 1, by decide⟩
def V02 : wnet.Vanishing := ⟨mk2 0 2, by decide⟩
def V11 : wnet.Vanishing := ⟨mk2 1 1, by decide⟩
def V12 : wnet.Vanishing := ⟨mk2 1 2, by decide⟩
def V21 : wnet.Vanishing := ⟨mk2 2 1, by decide⟩
def V22 : wnet.Vanishing := ⟨mk2 2 2, by decide⟩

theorem tangible_univ :
    (univ : Finset wnet.Tangible) = {T00, T10, T20} := by decide

theorem vanishing_univ :
    (univ : Finset wnet.Vanishing)
      = {V01, V02, V11, V12, V21, V22} := by decide

/-- Every tangible marking is one of the three named ones. -/
theorem tangible_cases (s : wnet.Tangible) :
    s = T00 ∨ s = T10 ∨ s = T20 := by
  have h := Finset.mem_univ s
  rw [tangible_univ] at h
  simpa using h

/-! ### The premises, discharged -/

/-- The cascade rank: the counter count. -/
def rW : wnet.Vanishing → ℕ := fun i => (i.1 1 : ℕ)

/-- Every vanishing marking is one of the six named ones. -/
theorem vanishing_cases (i : wnet.Vanishing) :
    i = V01 ∨ i = V02 ∨ i = V11 ∨ i = V12 ∨ i = V21 ∨ i = V22 := by
  have h := Finset.mem_univ i
  rw [vanishing_univ] at h
  simpa using h

/-- The counter's firing outcomes, classified once for the rank. -/
theorem fire_V01 : wnet.toSum (wnet.ifire 0 V01.1) = Sum.inl T00 := by
  rw [show wnet.ifire 0 V01.1 = mk2 0 0 from by decide]
  exact dif_neg (by decide)

theorem fire_V02 : wnet.toSum (wnet.ifire 0 V02.1) = Sum.inr V01 := by
  rw [show wnet.ifire 0 V02.1 = mk2 0 1 from by decide]
  exact dif_pos (by decide)

theorem fire_V11 : wnet.toSum (wnet.ifire 0 V11.1) = Sum.inl T10 := by
  rw [show wnet.ifire 0 V11.1 = mk2 1 0 from by decide]
  exact dif_neg (by decide)

theorem fire_V12 : wnet.toSum (wnet.ifire 0 V12.1) = Sum.inr V11 := by
  rw [show wnet.ifire 0 V12.1 = mk2 1 1 from by decide]
  exact dif_pos (by decide)

theorem fire_V21 : wnet.toSum (wnet.ifire 0 V21.1) = Sum.inl T20 := by
  rw [show wnet.ifire 0 V21.1 = mk2 2 0 from by decide]
  exact dif_neg (by decide)

theorem fire_V22 : wnet.toSum (wnet.ifire 0 V22.1) = Sum.inr V21 := by
  rw [show wnet.ifire 0 V22.1 = mk2 2 1 from by decide]
  exact dif_pos (by decide)

/-- The counter count is a cascade rank: each immediate step drains
one counter token, and a step landing in a vanishing marking strictly
descends. -/
theorem wnet_rank : wnet.CascadeRank rW := by
  intro i u _hu j hj
  obtain rfl : u = 0 := Subsingleton.elim u 0
  rcases vanishing_cases i with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [fire_V01] at hj
    simp at hj
  · rw [fire_V02] at hj
    obtain rfl : V01 = j := by simpa using hj
    decide
  · rw [fire_V11] at hj
    simp at hj
  · rw [fire_V12] at hj
    obtain rfl : V11 = j := by simpa using hj
    decide
  · rw [fire_V21] at hj
    simp at hj
  · rw [fire_V22] at hj
    obtain rfl : V21 = j := by simpa using hj
    decide

theorem wnet_zenoFree :
    ZenoFree (wnet.toFinMA.imStep wnet.uniformPolicy) rW :=
  wnet.zenoFree_uniform wnet_rank

/-- The witness vector `(1, 1)`: the drain trades two supply tokens
for two counter tokens, evaporation destroys, the immediate destroys —
all non-increasing. -/
def tbW : wnet.TokenBound where
  w := fun _ => 1
  pos := fun _ => Nat.one_pos
  delay_le := by decide
  imm_le := by decide

/-- Initial tangibility: the point initial mass sits at a tangible
marking. -/
theorem wnet_tangibleInit : wnet.TangibleInit := by
  intro m hv
  have hne : m ≠ mk2 2 0 := by
    rintro rfl
    exact absurd hv (by decide)
  exact if_neg hne

/-- The premise bundle for the witness net. -/
def premisesW : wnet.FlattenPremises where
  init_tangible := wnet_tangibleInit
  bound := tbW
  rank := rW
  cascade := wnet_rank

/-! ### The flat presentation, as construction data

Modes `0, 1, 2` are the tangible markings with `0, 1, 2` supply
tokens.  The rates are the flattening construction's, written as
literals: the drain edge `2 → 0` carries `2! · C(2,2) · 3 = 6` (the
dictionary) *through the two-step cascade-closed reset*; the
evaporation edges carry the arity-1 censuses. -/

/-- The flattened chain on the mode roster `Fin 3`. -/
def flatWitness : FinCTMC (Fin 3) where
  rate i j :=
    if i = 2 ∧ j = 0 then 6
    else if i = 2 ∧ j = 1 then 2
    else if i = 1 ∧ j = 0 then 1
    else 0
  init i := if i = 2 then 1 else 0
  rate_nonneg := fun i j _ => by split_ifs <;> norm_num
  init_nonneg := fun i => by by_cases h : i = 2 <;> simp [h]
  init_sum := Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (mem_univ _))

/-- The carrier identification: the mode enumeration. -/
def rho : Fin 3 ≃ wnet.Tangible where
  toFun i := if i = 0 then T00 else if i = 1 then T10 else T20
  invFun s := if s = T00 then 0 else if s = T10 then 1 else 2
  left_inv := by decide
  right_inv := by decide

/-! ### The race intensities of the delay layer -/

/-- Race intensities vanish where neither transition fires to the
target. -/
theorem race_zero {m m' : BMarking (Fin 2) 2}
    (h0 : ¬(wnet.delay.Enabled 0 m ∧ wnet.delay.fire 0 m = m'))
    (h1 : ¬(wnet.delay.Enabled 1 m ∧ wnet.delay.fire 1 m = m')) :
    wnet.delay.raceRate m m' = 0 := by
  show (∑ t : Fin 2,
      if wnet.delay.Enabled t m ∧ wnet.delay.fire t m = m'
      then (wnet.delay.raceCount t m : ℚ) * wnet.delay.rate t
      else 0) = 0
  rw [Fin.sum_univ_two, if_neg h0, if_neg h1, add_zero]

/-- The drain's race out of the full supply: census `2` (the ordered
assignments of two tokens to two arcs) at rate `3`. -/
theorem race_m20_m02 :
    wnet.delay.raceRate (mk2 2 0) (mk2 0 2) = 6 := by
  show (∑ t : Fin 2,
      if wnet.delay.Enabled t (mk2 2 0)
          ∧ wnet.delay.fire t (mk2 2 0) = mk2 0 2
      then (wnet.delay.raceCount t (mk2 2 0) : ℚ) * wnet.delay.rate t
      else 0) = 6
  rw [Fin.sum_univ_two, if_pos ⟨by decide, by decide⟩,
    if_neg (by decide),
    show wnet.delay.raceCount 0 (mk2 2 0) = 2 from by decide,
    show wnet.delay.rate 0 = 3 from rfl]
  norm_num

/-- Evaporation's race out of the full supply: census `2` at rate
`1`. -/
theorem race_m20_m10 :
    wnet.delay.raceRate (mk2 2 0) (mk2 1 0) = 2 := by
  show (∑ t : Fin 2,
      if wnet.delay.Enabled t (mk2 2 0)
          ∧ wnet.delay.fire t (mk2 2 0) = mk2 1 0
      then (wnet.delay.raceCount t (mk2 2 0) : ℚ) * wnet.delay.rate t
      else 0) = 2
  rw [Fin.sum_univ_two, if_neg (by decide),
    if_pos ⟨by decide, by decide⟩,
    show wnet.delay.raceCount 1 (mk2 2 0) = 2 from by decide,
    show wnet.delay.rate 1 = 1 from rfl]
  norm_num

/-- Evaporation's race out of one supply token. -/
theorem race_m10_m00 :
    wnet.delay.raceRate (mk2 1 0) (mk2 0 0) = 1 := by
  show (∑ t : Fin 2,
      if wnet.delay.Enabled t (mk2 1 0)
          ∧ wnet.delay.fire t (mk2 1 0) = mk2 0 0
      then (wnet.delay.raceCount t (mk2 1 0) : ℚ) * wnet.delay.rate t
      else 0) = 1
  rw [Fin.sum_univ_two, if_neg (by decide),
    if_pos ⟨by decide, by decide⟩,
    show wnet.delay.raceCount 1 (mk2 1 0) = 1 from by decide,
    show wnet.delay.rate 1 = 1 from rfl]
  norm_num

/-! ### The cascade absorption -/

/-- One absorption step from an instantaneous state whose mixed kernel
is a point mass. -/
theorem absorbIter_succ_point {S I : Type} [Fintype S] [Fintype I]
    [DecidableEq S] [DecidableEq I]
    {f : I → S ⊕ I → ℚ} {i : I} {y₀ : S ⊕ I}
    (h : ∀ y, f i y = if y = y₀ then 1 else 0) (n : ℕ) (s : S) :
    absorbIter f (n + 1) (Sum.inr i) s = absorbIter f n y₀ s := by
  rw [absorbIter_succ_inr]
  have hterm : ∀ y, f i y * absorbIter f n y s
      = if y = y₀ then absorbIter f n y s else 0 := by
    intro y
    rw [h y, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_congr rfl fun y _ => hterm y,
    Finset.sum_ite_eq' univ y₀ (fun y => absorbIter f n y s)]
  simp

/-- The uniform scheduler gives the sole immediate transition the
whole mass at every vanishing marking of the witness net. -/
theorem uniform_choice_one (i : wnet.Vanishing) :
    wnet.uniformPolicy.choice i 0 = 1 := by
  show (if wnet.IEnabled 0 i.1
    then ((wnet.enabledCount i : ℕ) : ℚ)⁻¹ else 0) = 1
  have hen : wnet.IEnabled 0 i.1 := by
    obtain ⟨u, hu⟩ := i.2
    have : u = 0 := Subsingleton.elim u 0
    rwa [this] at hu
  rw [if_pos hen,
    show wnet.enabledCount i = 1 from by
      have h := Finset.mem_univ i
      rw [vanishing_univ] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide]
  norm_num

/-- The mixed immediate kernel at the two-counter marking: a point
mass at the one-counter marking. -/
theorem imStep_V02 (y : wnet.Tangible ⊕ wnet.Vanishing) :
    wnet.toFinMA.imStep wnet.uniformPolicy V02 y
      = if y = Sum.inr V01 then 1 else 0 := by
  show (∑ u : Fin 1, wnet.uniformPolicy.choice V02 u
      * wnet.toFinMA.branch V02 u y) = _
  rw [Fin.sum_univ_one, uniform_choice_one V02, one_mul,
    toFinMA_branch, if_pos (show wnet.IEnabled 0 V02.1 by decide),
    fire_V02]
  by_cases hy : (Sum.inr V01 : wnet.Tangible ⊕ wnet.Vanishing) = y
  · rw [if_pos hy, if_pos hy.symm]
  · rw [if_neg hy, if_neg fun h => hy h.symm]

/-- The mixed immediate kernel at the one-counter marking: a point
mass at the empty tangible marking. -/
theorem imStep_V01 (y : wnet.Tangible ⊕ wnet.Vanishing) :
    wnet.toFinMA.imStep wnet.uniformPolicy V01 y
      = if y = Sum.inl T00 then 1 else 0 := by
  show (∑ u : Fin 1, wnet.uniformPolicy.choice V01 u
      * wnet.toFinMA.branch V01 u y) = _
  rw [Fin.sum_univ_one, uniform_choice_one V01, one_mul,
    toFinMA_branch, if_pos (show wnet.IEnabled 0 V01.1 by decide),
    fire_V01]
  by_cases hy : (Sum.inl T00 : wnet.Tangible ⊕ wnet.Vanishing) = y
  · rw [if_pos hy, if_pos hy.symm]
  · rw [if_neg hy, if_neg fun h => hy h.symm]

/-- Absorption from a tangible state is the point mass. -/
theorem absorb_inl (t s : wnet.Tangible) :
    wnet.toFinMA.absorb wnet.uniformPolicy rW (Sum.inl t) s
      = if t = s then 1 else 0 := by
  show absorbIter (wnet.toFinMA.imStep wnet.uniformPolicy)
    (absFuel rW) (Sum.inl t) s = _
  rw [absorbIter_inl, hitMass_inl]

theorem absorb_inl_self (t : wnet.Tangible) :
    wnet.toFinMA.absorb wnet.uniformPolicy rW (Sum.inl t) t = 1 := by
  rw [absorb_inl, if_pos rfl]

theorem absorb_inl_ne {t s : wnet.Tangible} (h : t ≠ s) :
    wnet.toFinMA.absorb wnet.uniformPolicy rW (Sum.inl t) s = 0 := by
  rw [absorb_inl, if_neg h]

/-- **The two-step cascade absorbs whole**: from the two-counter
marking, absorption is the point mass at the empty tangible marking —
two zero-time steps through the one-counter intermediate, within the
rank's working fuel. -/
theorem absorb_V02 (s : wnet.Tangible) :
    wnet.toFinMA.absorb wnet.uniformPolicy rW (Sum.inr V02) s
      = if T00 = s then 1 else 0 := by
  show absorbIter (wnet.toFinMA.imStep wnet.uniformPolicy)
    (absFuel rW) (Sum.inr V02) s = _
  rw [show absFuel rW = 1 + 1 + 1 from by decide,
    absorbIter_succ_point imStep_V02,
    absorbIter_succ_point imStep_V01,
    absorbIter_inl, hitMass_inl]

theorem absorb_V02_T00 :
    wnet.toFinMA.absorb wnet.uniformPolicy rW (Sum.inr V02) T00 = 1 := by
  rw [absorb_V02, if_pos rfl]

theorem absorb_V02_T10 :
    wnet.toFinMA.absorb wnet.uniformPolicy rW (Sum.inr V02) T10 = 0 := by
  rw [absorb_V02, if_neg (by decide)]

theorem absorb_V02_T20 :
    wnet.toFinMA.absorb wnet.uniformPolicy rW (Sum.inr V02) T20 = 0 := by
  rw [absorb_V02, if_neg (by decide)]

/-! ### The closed rates, computed -/

/-- The timed row read out of the full-supply marking, at each of the
nine automaton states. -/
theorem off_T20_inl_T00 :
    wnet.toFinMA.offRate T20 (Sum.inl T00) = 0 := by
  rw [wnet.toFinMA.offRate_of_ne (by decide)]
  exact race_zero (by decide) (by decide)

theorem off_T20_inl_T10 :
    wnet.toFinMA.offRate T20 (Sum.inl T10) = 2 := by
  rw [wnet.toFinMA.offRate_of_ne (by decide)]
  exact race_m20_m10

theorem off_T20_inl_T20 :
    wnet.toFinMA.offRate T20 (Sum.inl T20) = 0 :=
  wnet.toFinMA.offRate_diag T20

theorem off_T20_inr_V01 :
    wnet.toFinMA.offRate T20 (Sum.inr V01) = 0 := by
  rw [wnet.toFinMA.offRate_of_ne (by decide)]
  exact race_zero (by decide) (by decide)

theorem off_T20_inr_V02 :
    wnet.toFinMA.offRate T20 (Sum.inr V02) = 6 := by
  rw [wnet.toFinMA.offRate_of_ne (by decide)]
  exact race_m20_m02

theorem off_T20_inr_V11 :
    wnet.toFinMA.offRate T20 (Sum.inr V11) = 0 := by
  rw [wnet.toFinMA.offRate_of_ne (by decide)]
  exact race_zero (by decide) (by decide)

theorem off_T20_inr_V12 :
    wnet.toFinMA.offRate T20 (Sum.inr V12) = 0 := by
  rw [wnet.toFinMA.offRate_of_ne (by decide)]
  exact race_zero (by decide) (by decide)

theorem off_T20_inr_V21 :
    wnet.toFinMA.offRate T20 (Sum.inr V21) = 0 := by
  rw [wnet.toFinMA.offRate_of_ne (by decide)]
  exact race_zero (by decide) (by decide)

theorem off_T20_inr_V22 :
    wnet.toFinMA.offRate T20 (Sum.inr V22) = 0 := by
  rw [wnet.toFinMA.offRate_of_ne (by decide)]
  exact race_zero (by decide) (by decide)

/-- The timed row read out of the one-supply marking. -/
theorem off_T10_inl_T00 :
    wnet.toFinMA.offRate T10 (Sum.inl T00) = 1 := by
  rw [wnet.toFinMA.offRate_of_ne (by decide)]
  exact race_m10_m00

theorem off_T10_inl_T10 :
    wnet.toFinMA.offRate T10 (Sum.inl T10) = 0 :=
  wnet.toFinMA.offRate_diag T10

theorem off_T10_inl_T20 :
    wnet.toFinMA.offRate T10 (Sum.inl T20) = 0 := by
  rw [wnet.toFinMA.offRate_of_ne (by decide)]
  exact race_zero (by decide) (by decide)

theorem off_T10_inr_V01 :
    wnet.toFinMA.offRate T10 (Sum.inr V01) = 0 := by
  rw [wnet.toFinMA.offRate_of_ne (by decide)]
  exact race_zero (by decide) (by decide)

theorem off_T10_inr_V02 :
    wnet.toFinMA.offRate T10 (Sum.inr V02) = 0 := by
  rw [wnet.toFinMA.offRate_of_ne (by decide)]
  exact race_zero (by decide) (by decide)

theorem off_T10_inr_V11 :
    wnet.toFinMA.offRate T10 (Sum.inr V11) = 0 := by
  rw [wnet.toFinMA.offRate_of_ne (by decide)]
  exact race_zero (by decide) (by decide)

theorem off_T10_inr_V12 :
    wnet.toFinMA.offRate T10 (Sum.inr V12) = 0 := by
  rw [wnet.toFinMA.offRate_of_ne (by decide)]
  exact race_zero (by decide) (by decide)

theorem off_T10_inr_V21 :
    wnet.toFinMA.offRate T10 (Sum.inr V21) = 0 := by
  rw [wnet.toFinMA.offRate_of_ne (by decide)]
  exact race_zero (by decide) (by decide)

theorem off_T10_inr_V22 :
    wnet.toFinMA.offRate T10 (Sum.inr V22) = 0 := by
  rw [wnet.toFinMA.offRate_of_ne (by decide)]
  exact race_zero (by decide) (by decide)

/-- The empty-supply marking is rate-absorbing: no transition is
enabled, so every closed rate out of it vanishes. -/
theorem close_T00 (s' : wnet.Tangible) :
    (wnet.toFinMA.close wnet.uniformPolicy rW wnet_zenoFree).rate
      T00 s' = 0 := by
  show (∑ x, wnet.toFinMA.offRate T00 x
      * wnet.toFinMA.absorb wnet.uniformPolicy rW x s') = 0
  refine Finset.sum_eq_zero fun x _ => ?_
  have h0 : wnet.toFinMA.offRate T00 x = 0 := by
    rcases x with s | i
    · by_cases hd : T00 = s
      · subst hd
        exact wnet.toFinMA.offRate_diag T00
      · rw [wnet.toFinMA.offRate_of_ne
          (fun hc => hd (Sum.inl_injective hc))]
        exact race_zero (fun h => absurd h.1 (by decide))
          (fun h => absurd h.1 (by decide))
    · rw [wnet.toFinMA.offRate_of_ne (Sum.inl_ne_inr)]
      exact race_zero (fun h => absurd h.1 (by decide))
        (fun h => absurd h.1 (by decide))
  rw [h0, zero_mul]

/-- The closed drain edge: rate `6` from full supply to empty — the
dictionary-weighted race through the two-step cascade-closed reset. -/
theorem close_T20_T00 :
    (wnet.toFinMA.close wnet.uniformPolicy rW wnet_zenoFree).rate
      T20 T00 = 6 := by
  show (∑ x, wnet.toFinMA.offRate T20 x
      * wnet.toFinMA.absorb wnet.uniformPolicy rW x T00) = 6
  rw [Fintype.sum_sum_type, tangible_univ, vanishing_univ,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, off_T20_inl_T00, off_T20_inl_T10,
    off_T20_inl_T20, off_T20_inr_V01, off_T20_inr_V02,
    off_T20_inr_V11, off_T20_inr_V12, off_T20_inr_V21,
    off_T20_inr_V22, absorb_inl_ne (show T10 ≠ T00 by decide),
    absorb_V02_T00]
  norm_num

/-- The closed evaporation edge out of full supply: rate `2`, no
cascade. -/
theorem close_T20_T10 :
    (wnet.toFinMA.close wnet.uniformPolicy rW wnet_zenoFree).rate
      T20 T10 = 2 := by
  show (∑ x, wnet.toFinMA.offRate T20 x
      * wnet.toFinMA.absorb wnet.uniformPolicy rW x T10) = 2
  rw [Fintype.sum_sum_type, tangible_univ, vanishing_univ,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, off_T20_inl_T00, off_T20_inl_T10,
    off_T20_inl_T20, off_T20_inr_V01, off_T20_inr_V02,
    off_T20_inr_V11, off_T20_inr_V12, off_T20_inr_V21,
    off_T20_inr_V22, absorb_inl_self T10, absorb_V02_T10]
  norm_num

/-- The closed evaporation edge out of one supply token: rate `1`. -/
theorem close_T10_T00 :
    (wnet.toFinMA.close wnet.uniformPolicy rW wnet_zenoFree).rate
      T10 T00 = 1 := by
  show (∑ x, wnet.toFinMA.offRate T10 x
      * wnet.toFinMA.absorb wnet.uniformPolicy rW x T00) = 1
  rw [Fintype.sum_sum_type, tangible_univ, vanishing_univ,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, off_T10_inl_T00, off_T10_inl_T10,
    off_T10_inl_T20, off_T10_inr_V01, off_T10_inr_V02,
    off_T10_inr_V11, off_T10_inr_V12, off_T10_inr_V21,
    off_T10_inr_V22, absorb_inl_self T00]
  norm_num

/-- No closed edge climbs from one supply token to two. -/
theorem close_T10_T20 :
    (wnet.toFinMA.close wnet.uniformPolicy rW wnet_zenoFree).rate
      T10 T20 = 0 := by
  show (∑ x, wnet.toFinMA.offRate T10 x
      * wnet.toFinMA.absorb wnet.uniformPolicy rW x T20) = 0
  rw [Fintype.sum_sum_type, tangible_univ, vanishing_univ,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, off_T10_inl_T00, off_T10_inl_T10,
    off_T10_inl_T20, off_T10_inr_V01, off_T10_inr_V02,
    off_T10_inr_V11, off_T10_inr_V12, off_T10_inr_V21,
    off_T10_inr_V22, absorb_inl_ne (show T00 ≠ T20 by decide)]
  norm_num

/-! ### The agreement — the instance's atom-transport obligations -/

/-- **Off-diagonal agreement**: the transported flat presentation's
rates are the scheduler-closed net's, entry by entry — the hand-written
construction data checked against the compiled closure. -/
theorem flat_agree_off : ∀ s s' : wnet.Tangible, s ≠ s' →
    (flatWitness.relabel rho).rate s s'
      = (wnet.toFinMA.close wnet.uniformPolicy rW wnet_zenoFree).rate
          s s' := by
  intro s s' hne
  rcases tangible_cases s with rfl | rfl | rfl <;>
    rcases tangible_cases s' with rfl | rfl | rfl
  · exact absurd rfl hne
  · rw [close_T00, FinCTMC.relabel_rate,
      show rho.symm T00 = 0 from by decide,
      show rho.symm T10 = 1 from by decide]
    show (if (0 : Fin 3) = 2 ∧ (1 : Fin 3) = 0 then (6 : ℚ)
      else if (0 : Fin 3) = 2 ∧ (1 : Fin 3) = 1 then 2
      else if (0 : Fin 3) = 1 ∧ (1 : Fin 3) = 0 then 1 else 0) = 0
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  · rw [close_T00, FinCTMC.relabel_rate,
      show rho.symm T00 = 0 from by decide,
      show rho.symm T20 = 2 from by decide]
    show (if (0 : Fin 3) = 2 ∧ (2 : Fin 3) = 0 then (6 : ℚ)
      else if (0 : Fin 3) = 2 ∧ (2 : Fin 3) = 1 then 2
      else if (0 : Fin 3) = 1 ∧ (2 : Fin 3) = 0 then 1 else 0) = 0
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  · rw [close_T10_T00, FinCTMC.relabel_rate,
      show rho.symm T10 = 1 from by decide,
      show rho.symm T00 = 0 from by decide]
    show (if (1 : Fin 3) = 2 ∧ (0 : Fin 3) = 0 then (6 : ℚ)
      else if (1 : Fin 3) = 2 ∧ (0 : Fin 3) = 1 then 2
      else if (1 : Fin 3) = 1 ∧ (0 : Fin 3) = 0 then 1 else 0) = 1
    rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  · exact absurd rfl hne
  · rw [close_T10_T20, FinCTMC.relabel_rate,
      show rho.symm T10 = 1 from by decide,
      show rho.symm T20 = 2 from by decide]
    show (if (1 : Fin 3) = 2 ∧ (2 : Fin 3) = 0 then (6 : ℚ)
      else if (1 : Fin 3) = 2 ∧ (2 : Fin 3) = 1 then 2
      else if (1 : Fin 3) = 1 ∧ (2 : Fin 3) = 0 then 1 else 0) = 0
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  · rw [close_T20_T00, FinCTMC.relabel_rate,
      show rho.symm T20 = 2 from by decide,
      show rho.symm T00 = 0 from by decide]
    show (if (2 : Fin 3) = 2 ∧ (0 : Fin 3) = 0 then (6 : ℚ)
      else if (2 : Fin 3) = 2 ∧ (0 : Fin 3) = 1 then 2
      else if (2 : Fin 3) = 1 ∧ (0 : Fin 3) = 0 then 1 else 0) = 6
    rw [if_pos (by decide)]
  · rw [close_T20_T10, FinCTMC.relabel_rate,
      show rho.symm T20 = 2 from by decide,
      show rho.symm T10 = 1 from by decide]
    show (if (2 : Fin 3) = 2 ∧ (1 : Fin 3) = 0 then (6 : ℚ)
      else if (2 : Fin 3) = 2 ∧ (1 : Fin 3) = 1 then 2
      else if (2 : Fin 3) = 1 ∧ (1 : Fin 3) = 0 then 1 else 0) = 2
    rw [if_neg (by decide), if_pos (by decide)]
  · exact absurd rfl hne

/-- **Initial agreement**: through the initial-tangibility premise the
closed initial row is the net's, and the flat presentation's point
mass sits at the matching mode. -/
theorem flat_agree_init :
    (flatWitness.relabel rho).init
      = (wnet.toFinMA.close wnet.uniformPolicy rW wnet_zenoFree).init := by
  funext s
  rw [show (wnet.toFinMA.close wnet.uniformPolicy rW
        wnet_zenoFree).init s = wnet.delay.init s.1 from
    wnet.tangibleChain_init_of_tangible wnet.uniformPolicy rW
      wnet_zenoFree wnet_tangibleInit s]
  rcases tangible_cases s with rfl | rfl | rfl
  · rw [FinCTMC.relabel_init, show rho.symm T00 = 0 from by decide]
    show (if (0 : Fin 3) = 2 then (1 : ℚ) else 0)
      = (if mk2 0 0 = mk2 2 0 then (1 : ℚ) else 0)
    rw [if_neg (by decide), if_neg (by decide)]
  · rw [FinCTMC.relabel_init, show rho.symm T10 = 1 from by decide]
    show (if (1 : Fin 3) = 2 then (1 : ℚ) else 0)
      = (if mk2 1 0 = mk2 2 0 then (1 : ℚ) else 0)
    rw [if_neg (by decide), if_neg (by decide)]
  · rw [FinCTMC.relabel_init, show rho.symm T20 = 2 from by decide]
    show (if (2 : Fin 3) = 2 then (1 : ℚ) else 0)
      = (if mk2 2 0 = mk2 2 0 then (1 : ℚ) else 0)
    rw [if_pos rfl, if_pos rfl]

/-! ### The triangle at the instance -/

/-- **The commuting-triangle instance, precise face**: the witness
net's compiled reading and its hand-flattened presentation's compiled
reading, transported along the mode enumeration, are isomorphic by an
invertible globular cell — at every jump horizon. -/
theorem witness_triangle (k : ℕ) {a : Crd (Traj wnet.Tangible k)} :
    ∃ α : Cell
        (looseConj (atoms (jumpRows (closeMaRows wnet.compileIspn
          (compilePolicy wnet.uniformPolicy) (absFuel rW))) k) :
          Loose a a)
        (looseConj (atoms (jumpRows
          (compileCtmc (flatWitness.relabel rho))) k))
        (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  wnet.flatten_triangle_of_agree wnet.uniformPolicy rW wnet_zenoFree
    rho flatWitness flat_agree_off flat_agree_init k

/-- **The demonic directed face at the instance**: the flattened
presentation's compiled reading entails the compiled demonic reading —
the membership lemma packaged as a directed cell.  At this net the
enabling-respecting arena is a singleton (one immediate transition),
so this demonstrates the mechanism; arena plurality is pinned by the
demonic face's own control net. -/
theorem witness_demonic_directed (k : ℕ)
    {a : Crd (Traj wnet.Tangible k)} :
    ∃ _α : Cell
        (looseConj (atoms (jumpRows
          (compileCtmc (flatWitness.relabel rho))) k) : Loose a a)
        (wnet.ispnDemonicC (absFuel rW) k) (𝟙 a) (𝟙 a), True :=
  wnet.flatten_demonic_directed_of_agree wnet_rank wnet.uniformResp
    rho flatWitness flat_agree_off flat_agree_init k

/-- The flattened law models the compiled net-and-scheduler
presentation in the semantic universe — the wired positive face at the
instance. -/
theorem su_witness_flat (k : ℕ) :
    idealPoint ((flatWitness.relabel rho).jumpLaw k)
      ∈ (wnet.ispnDnf wnet.uniformPolicy rW k).modelClass := by
  rw [show (flatWitness.relabel rho).jumpLaw k
      = wnet.tangiblePathLaw wnet.uniformPolicy rW wnet_zenoFree k from
    FinCTMC.jumpLaw_diag_blind _ _ flat_agree_off flat_agree_init k]
  exact wnet.su_ispn_pathLaw_mem wnet.uniformPolicy rW wnet_zenoFree k

end SpnFlattenWitness

end Adequacy
end SuFunctor
