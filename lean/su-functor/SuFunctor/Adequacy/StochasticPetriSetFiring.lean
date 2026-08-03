import SuFunctor.Adequacy.StochasticPetriCascade

/-! # Adequacy: stochastic Petri frames, set-firing face (simultaneous
composite firings)

The conflict-resolution face the cascade module deliberately left
separate and named: **simultaneous composite firings of
non-conflicting immediates** — rules R1 and R3 of the founding
formalism ([EB10a] arXiv:1003.4812, pp. 233–234).  R1: one transition
enabled by several token sets whose firings do not disable one
another fires all of them at the same instant.  R3: several
transitions enabled simultaneously and non-disabling fire at the same
instant.  Both rules live in one vocabulary here: the composite is a
**multiset** of immediate transitions — R1 is a replicated singleton
(`Multiset.replicate`), R3 a multiset of support two or more.

**The face's engine is one value identity.**  A scheduler realizes a
composite as a zero-time *chain* of single firings (`chainFire`); a
chain whose every step is enabled is *exact* — no truncation fires,
by the enabledness conventions of the fragment — so its result
satisfies

  `result + (ordinary-input total) = source + (ordinary-output total)`

per place (`chainFire_val`), and the right-hand data depend on the
multiset alone.  Everything the community's rules assert then falls
out arithmetically, with **no diamond induction and no permutation
induction**:

* **Order-invariance** (`chainFire_eq_of_enabled`): two enabled
  enumerations of one multiset land the same marking — the value is
  pinned by the identity.  On the non-conflicting locus the
  community's randomization (rules R2/R4) has nothing left to choose
  between; the pairwise diamond (`ifire_comm`) is the two-element
  corollary.

* **Composite = chain** (`chainFire_eq_compositeFire`): the
  simultaneous composite firing — remove every ordinary-input token
  at once, then produce, the community's own firing order
  (`compositeFire`, monus-first) — equals the chain, in every enabled
  order, under **joint supply** (`Supplied`: the ordinary-input total
  is available at the source).  Joint supply is load-bearing in the
  statement, not the proof: without it the composite genuinely
  diverges from every chain (control `c3` below — two swap-tokens
  through one token chain to the same marking, while the monus
  composite reads two).

* **The reservation precondition** (`JointReservation`): the
  community's R1/R3 side condition at the counting stratum — every
  member individually enabled, ordinary consumption jointly supplied,
  every member's enabling-arc reads fitting the *untouched* pool (a
  read token consumed by a sibling's set is a disabled set, hence
  conflict, hence R2/R4 territory), and the composite outcome within
  capacity.

* **The scope condition made explicit**
  (`chainEnabled_of_headroom` / `setNonConflicting_of_headroom`): a
  composite reduces to per-firing rows only when the *intermediate*
  markings stay in scope — intermediate counts do not interpolate
  between endpoints (one firing may add what the next removes).  In
  the capacity fragment the cheap sufficient condition is headroom:
  `source + (output total) ≤ capacity`.  Control `c4` shows the gap
  is real: a three-element composite whose reservation holds and
  whose endpoints respect capacity, with a producer-first order that
  blocks mid-chain.  Under reservation + headroom, *every* order is
  enabled (`SetNonConflicting`), all orders agree, and each equals
  the composite (`r1r3_composite_adequacy` — the packaged face).
  A pleasing redundancy, proved rather than assumed: under supply,
  reads, and headroom, the members' individual enabledness is
  derivable (`iEnabled_of_reservation`) — the community states it as
  part of the rule ("become enabled at exactly the same time"), and
  the fragment agrees from the other clauses.

**Connection to the landed cascade square — no new closure
mathematics.**  An enabled immediate's branch row in the compiled
Markov automaton is a point mass at its firing
(`toFinMA_branch_ifire`), so an enabled chain is an absorption path
of the cascade closure exactly as already built; the observed
tangible process cannot distinguish the community's one-instant
composite from any scheduler's zero-time chain, because both absorb
through the same rows to the same tangible marking.  The face adds
precisely what the closure did not carry: that on the non-conflicting
locus the chain's *value* is order-free and equals the community's
simultaneous composite.

**Deliberately separate, named**: coloured composite firings (the
kernel-presentation seam, exactly as for the single-firing faces);
guard-transition simultaneity (positive-probability coincidence under
degenerate colour dynamics — the guard face's own stratum); the
community's randomization *distribution* over maximal non-conflicting
combinations (rules R2/R4 — dominated by the scheduler-generic and
demonic faces of the cascade square, as there). -/

namespace SuFunctor
namespace Adequacy
namespace FinISPN

section SetFiring

variable {P T U : Type} [Fintype P] [DecidableEq P] {B : ℕ}
variable (N : FinISPN P T U B)

/-! ## Chains: a scheduler's zero-time realization of a composite -/

/-- The zero-time chain of single immediate firings along a list. -/
def chainFire : List U → BMarking P B → BMarking P B
  | [], m => m
  | u :: l, m => chainFire l (N.ifire u m)

@[simp] theorem chainFire_nil (m : BMarking P B) : N.chainFire [] m = m := rfl

@[simp] theorem chainFire_cons (u : U) (l : List U) (m : BMarking P B) :
    N.chainFire (u :: l) m = N.chainFire l (N.ifire u m) := rfl

/-- Every step of the chain is enabled at its intermediate marking —
the per-firing rows' scope hypotheses, held along the whole chain. -/
def ChainEnabled : List U → BMarking P B → Prop
  | [], _ => True
  | u :: l, m => N.IEnabled u m ∧ ChainEnabled l (N.ifire u m)

@[simp] theorem chainEnabled_nil (m : BMarking P B) :
    N.ChainEnabled [] m := trivial

theorem chainEnabled_cons {u : U} {l : List U} {m : BMarking P B} :
    N.ChainEnabled (u :: l) m
      ↔ N.IEnabled u m ∧ N.ChainEnabled l (N.ifire u m) := Iff.rfl

/-- Chain-enabledness is decidable (the controls' instrument). -/
def decChainEnabled : (l : List U) → (m : BMarking P B) →
    Decidable (N.ChainEnabled l m)
  | [], _ => .isTrue trivial
  | u :: l, m =>
    have : Decidable (N.ChainEnabled l (N.ifire u m)) :=
      decChainEnabled l (N.ifire u m)
    inferInstanceAs (Decidable (N.IEnabled u m ∧ N.ChainEnabled l (N.ifire u m)))

instance (l : List U) (m : BMarking P B) : Decidable (N.ChainEnabled l m) :=
  N.decChainEnabled l m

/-! ## The composite's per-place arc totals -/

/-- The ordinary-input total of a composite at a place. -/
def preSum (S : Multiset U) (p : P) : ℕ := (S.map fun u => N.ipre u p).sum

/-- The ordinary-output total of a composite at a place. -/
def postSum (S : Multiset U) (p : P) : ℕ := (S.map fun u => N.ipost u p).sum

@[simp] theorem preSum_zero (p : P) : N.preSum 0 p = 0 := rfl

@[simp] theorem postSum_zero (p : P) : N.postSum 0 p = 0 := rfl

@[simp] theorem preSum_cons (u : U) (S : Multiset U) (p : P) :
    N.preSum (u ::ₘ S) p = N.ipre u p + N.preSum S p := by
  simp [preSum]

@[simp] theorem postSum_cons (u : U) (S : Multiset U) (p : P) :
    N.postSum (u ::ₘ S) p = N.ipost u p + N.postSum S p := by
  simp [postSum]

@[simp] theorem preSum_coe_cons (u : U) (l : List U) (p : P) :
    N.preSum ↑(u :: l) p = N.ipre u p + N.preSum ↑l p :=
  N.preSum_cons u ↑l p

@[simp] theorem postSum_coe_cons (u : U) (l : List U) (p : P) :
    N.postSum ↑(u :: l) p = N.ipost u p + N.postSum ↑l p :=
  N.postSum_cons u ↑l p

/-- Joint ordinary-token supply: the counting shadow of the
community's disjoint token reservation across the composite's sets. -/
def Supplied (S : Multiset U) (m : BMarking P B) : Prop :=
  ∀ p, N.preSum S p ≤ (m p : ℕ)

instance (S : Multiset U) (m : BMarking P B) : Decidable (N.Supplied S m) :=
  inferInstanceAs (Decidable (∀ p, N.preSum S p ≤ (m p : ℕ)))

/-! ## Exactness: enabledness makes every firing arithmetic -/

/-- Under enabledness the capacity truncation is inert and the firing
is exact per-place arithmetic. -/
theorem ifire_val {u : U} {m : BMarking P B} (hu : N.IEnabled u m) (p : P) :
    (N.ifire u m p : ℕ) = (m p : ℕ) - N.ipre u p + N.ipost u p := by
  show min (N.iOutAt u m p) B = _
  rw [min_eq_left (hu p).2]
  rfl

/-- The demand bound, spelled for arithmetic use: an enabled
transition's ordinary and enabling arcs are jointly supplied. -/
theorem iEnabled_demand {u : U} {m : BMarking P B} (hu : N.IEnabled u m)
    (p : P) : N.ipre u p + N.iread u p ≤ (m p : ℕ) :=
  (hu p).1

/-- **The chain value identity — the face's engine.**  A chain whose
every step is enabled is exact, so its result satisfies
`result + input-total = source + output-total` per place: the value
depends on the firing multiset alone, not the order. -/
theorem chainFire_val : ∀ (l : List U) (m : BMarking P B),
    N.ChainEnabled l m → ∀ p : P,
    (N.chainFire l m p : ℕ) + N.preSum ↑l p
      = (m p : ℕ) + N.postSum ↑l p
  | [], m, _, p => by simp
  | u :: l, m, h, p => by
    obtain ⟨hu, hl⟩ := h
    have hval := N.ifire_val hu p
    have hdem := N.iEnabled_demand hu p
    have hrec := chainFire_val l (N.ifire u m) hl p
    rw [chainFire_cons, preSum_coe_cons, postSum_coe_cons]
    omega

/-- **Order-invariance**: two enabled enumerations of one firing
multiset land the same marking.  On the non-conflicting locus the
community's randomization (R2/R4) has nothing left to choose
between. -/
theorem chainFire_eq_of_enabled {l₁ l₂ : List U} {m : BMarking P B}
    (h₁ : N.ChainEnabled l₁ m) (h₂ : N.ChainEnabled l₂ m)
    (hml : (↑l₁ : Multiset U) = ↑l₂) :
    N.chainFire l₁ m = N.chainFire l₂ m := by
  funext p
  have v₁ := N.chainFire_val l₁ m h₁ p
  have v₂ := N.chainFire_val l₂ m h₂ p
  rw [hml] at v₁
  exact Fin.ext (by omega)

/-- The pairwise diamond, as the two-element corollary of the value
identity: enabled in both orders, two firings commute. -/
theorem ifire_comm {u v : U} {m : BMarking P B}
    (hu : N.IEnabled u m) (hv : N.IEnabled v m)
    (hvu : N.IEnabled v (N.ifire u m)) (huv : N.IEnabled u (N.ifire v m)) :
    N.ifire v (N.ifire u m) = N.ifire u (N.ifire v m) := by
  have h₁ : N.ChainEnabled [u, v] m := ⟨hu, hvu, trivial⟩
  have h₂ : N.ChainEnabled [v, u] m := ⟨hv, huv, trivial⟩
  have h := N.chainFire_eq_of_enabled h₁ h₂ (Multiset.cons_swap u v 0)
  simpa using h

/-! ## The simultaneous composite firing -/

/-- The composite outcome count: remove every ordinary-input token at
once, then produce — the community's own firing order, at the
composite. -/
def compositeOut (S : Multiset U) (m : BMarking P B) (p : P) : ℕ :=
  (m p : ℕ) - N.preSum S p + N.postSum S p

/-- The simultaneous composite firing (truncated at capacity for
totality, as the single firing is; under joint supply and capacity
the truncation is inert). -/
def compositeFire (S : Multiset U) (m : BMarking P B) : BMarking P B :=
  fun p => ⟨min (N.compositeOut S m p) B, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- Under joint supply the remove-first and produce-first spellings of
the composite outcome agree — the monus-first form is the faithful
one, and it costs nothing on the supplied locus. -/
theorem compositeOut_add_first {S : Multiset U} {m : BMarking P B}
    (h : N.Supplied S m) (p : P) :
    N.compositeOut S m p = (m p : ℕ) + N.postSum S p - N.preSum S p := by
  have := h p
  unfold compositeOut
  omega

/-- **Composite = chain**: under joint supply, the simultaneous
composite firing equals the zero-time chain, in every enabled order.
Joint supply is load-bearing in the *statement*: without it the monus
composite genuinely diverges from every chain (control `c3`). -/
theorem chainFire_eq_compositeFire {l : List U} {m : BMarking P B}
    (h : N.ChainEnabled l m) (hsup : N.Supplied ↑l m) :
    N.chainFire l m = N.compositeFire ↑l m := by
  funext p
  have hval := N.chainFire_val l m h p
  have hs := hsup p
  have hle : (N.chainFire l m p : ℕ) ≤ B := Fin.is_le _
  have hout : N.compositeOut ↑l m p = (N.chainFire l m p : ℕ) := by
    unfold compositeOut
    omega
  apply Fin.ext
  show (N.chainFire l m p : ℕ) = min (N.compositeOut ↑l m p) B
  rw [hout, min_eq_left hle]

/-- Rule R1's replicated form, spelled: one transition, `k` token
sets, one composite — the multiset vocabulary carries multiplicity
natively. -/
theorem replicate_composite {k : ℕ} {u : U} {m : BMarking P B}
    (h : N.ChainEnabled (List.replicate k u) m)
    (hsup : N.Supplied ↑(List.replicate k u) m) :
    N.chainFire (List.replicate k u) m
      = N.compositeFire (Multiset.replicate k u) m := by
  have := N.chainFire_eq_compositeFire h hsup
  rwa [Multiset.coe_replicate] at this

/-! ## The reservation precondition and the scope condition -/

/-- **The community's R1/R3 side condition at the counting stratum**:
every member individually enabled ("become enabled at exactly the
same time"), ordinary consumption jointly supplied (disjoint token
sets exist), every member's enabling-arc reads fitting the pool no
sibling consumes (a read token consumed by a sibling's set is a
disabled set — conflict, not simultaneity), and the composite outcome
within capacity. -/
def JointReservation (S : Multiset U) (m : BMarking P B) : Prop :=
  (∀ u ∈ S, N.IEnabled u m) ∧ N.Supplied S m
    ∧ (∀ u ∈ S, ∀ p, N.iread u p ≤ (m p : ℕ) - N.preSum S p)
    ∧ (∀ p, N.compositeOut S m p ≤ B)

instance (S : Multiset U) (m : BMarking P B) :
    Decidable (N.JointReservation S m) := by
  unfold JointReservation
  infer_instance

/-- Non-conflict, closed under iteration: **every** firing order of
the composite keeps every step enabled — the house rendering of "the
firing of any one will not disable the others", including the scope
of every intermediate marking. -/
def SetNonConflicting (S : Multiset U) (m : BMarking P B) : Prop :=
  ∀ l : List U, (↑l : Multiset U) = S → N.ChainEnabled l m

/-- Individual enabledness is derivable from supply, reads, and
headroom — the reservation's `members` clause is the community's own
wording, and the fragment agrees with it from the other clauses. -/
theorem iEnabled_of_reservation {S : Multiset U} {m : BMarking P B} {u : U}
    (hu : u ∈ S) (hsup : N.Supplied S m)
    (hreads : ∀ v ∈ S, ∀ p, N.iread v p ≤ (m p : ℕ) - N.preSum S p)
    (hcap : ∀ p, (m p : ℕ) + N.postSum S p ≤ B) :
    N.IEnabled u m := by
  intro p
  have hpre : N.ipre u p ≤ N.preSum S p :=
    Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _
      (Multiset.mem_map_of_mem _ hu)
  have hpost : N.ipost u p ≤ N.postSum S p :=
    Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _
      (Multiset.mem_map_of_mem _ hu)
  have hr := hreads u hu p
  have hs := hsup p
  have hc := hcap p
  constructor
  · show N.ipre u p + N.iread u p ≤ _
    omega
  · show (m p : ℕ) - N.ipre u p + N.ipost u p ≤ B
    omega

/-- **The scope condition, discharged by headroom** (the list form):
under joint supply, pool-fitting reads, and headroom
(`source + output-total ≤ capacity`), every firing order is enabled —
the reservation clauses propagate along a fired head.  Headroom is
load-bearing: intermediate counts do not interpolate between
endpoints (control `c4` — a reservation-respecting composite whose
producer-first order blocks at capacity mid-chain). -/
theorem chainEnabled_of_headroom : ∀ (l : List U) (m : BMarking P B),
    N.Supplied ↑l m →
    (∀ u ∈ l, ∀ p, N.iread u p ≤ (m p : ℕ) - N.preSum ↑l p) →
    (∀ p, (m p : ℕ) + N.postSum ↑l p ≤ B) →
    N.ChainEnabled l m
  | [], _, _, _, _ => trivial
  | u :: l, m, hsup, hreads, hcap => by
    have hu : N.IEnabled u m :=
      N.iEnabled_of_reservation (Multiset.mem_coe.mpr (List.mem_cons_self ..))
        hsup (fun v hv => hreads v (Multiset.mem_coe.mp hv)) hcap
    refine ⟨hu, chainEnabled_of_headroom l (N.ifire u m) ?_ ?_ ?_⟩
    · intro p
      have := hsup p
      have := N.ifire_val hu p
      have := N.preSum_coe_cons u l p
      omega
    · intro v hv p
      have := hreads v (List.mem_cons_of_mem u hv) p
      have := hsup p
      have := N.ifire_val hu p
      have := N.preSum_coe_cons u l p
      omega
    · intro p
      have := hcap p
      have := hsup p
      have := N.ifire_val hu p
      have := N.postSum_coe_cons u l p
      have := N.preSum_coe_cons u l p
      omega

/-- The scope condition at the multiset: joint reservation plus
headroom makes the composite non-conflicting — every order of the
community's simultaneous firing is a valid scheduler chain. -/
theorem setNonConflicting_of_headroom {S : Multiset U} {m : BMarking P B}
    (hJ : N.JointReservation S m)
    (hcap : ∀ p, (m p : ℕ) + N.postSum S p ≤ B) :
    N.SetNonConflicting S m := by
  intro l hl
  subst hl
  exact N.chainEnabled_of_headroom l m hJ.2.1
    (fun u hu => hJ.2.2.1 u (Multiset.mem_coe.mpr hu)) hcap

/-- **The packaged R1/R3 face**: under joint reservation and
headroom, every enumeration of the composite is an enabled chain, all
enumerations agree, and each equals the simultaneous composite firing
— the community's one-instant rule is order-free and scheduler-free
at the marking stratum. -/
theorem r1r3_composite_adequacy {S : Multiset U} {m : BMarking P B}
    (hJ : N.JointReservation S m)
    (hcap : ∀ p, (m p : ℕ) + N.postSum S p ≤ B) :
    ∀ l : List U, (↑l : Multiset U) = S →
      N.ChainEnabled l m ∧ N.chainFire l m = N.compositeFire S m := by
  intro l hl
  subst hl
  have hen : N.ChainEnabled l m :=
    N.chainEnabled_of_headroom l m hJ.2.1
      (fun u hu => hJ.2.2.1 u (Multiset.mem_coe.mpr hu)) hcap
  exact ⟨hen, N.chainFire_eq_compositeFire hen hJ.2.1⟩

end SetFiring

/-! ## The connective to the landed cascade square -/

section Automaton

variable {P T U : Type} [Fintype P] [DecidableEq P] [Fintype T] [Fintype U]
  {B : ℕ}
variable (N : FinISPN P T U B)

/-- An enabled immediate's branch row in the compiled Markov automaton
is a point mass at its firing: an enabled chain is an absorption path
of the cascade closure exactly as already built — the observed
tangible process cannot distinguish the community's one-instant
composite from any scheduler's zero-time chain. -/
theorem toFinMA_branch_ifire (i : N.Vanishing) (u : U)
    (hu : N.IEnabled u i.1) :
    N.toFinMA.branch i u (N.toSum (N.ifire u i.1)) = 1 := by
  rw [toFinMA_branch, if_pos hu, if_pos rfl]

end Automaton

end FinISPN

/-! ## Controls

Concrete refutation witnesses at the designed mutant loci, proofs
deliberately independent of the lemmas they guard (decidability, not
rewriting).  All controls are ℕ/`Fin` markings on one place — no
rational arithmetic, so `decide` discharges everything. -/

namespace SpnSetFiringControls

open FinISPN

/-- A trivial delay layer: no arcs, rate zero, initial mass at the
empty marking (the controls exercise the immediate layer only). -/
def pointDelay (B : ℕ) : FinSPN (Fin 1) (Fin 1) B where
  pre _ _ := 0
  read _ _ := 0
  post _ _ := 0
  rate _ := 0
  rate_nonneg _ := le_refl 0
  init m := if m = (fun _ => 0) then 1 else 0
  init_nonneg m := by by_cases h : m = (fun _ => 0) <;> simp [h]
  init_sum := (Finset.sum_ite_eq' _ _ _).trans (if_pos (Finset.mem_univ _))

/-! ### c1 — a genuinely non-conflicting pair

A consumer and a producer on one place, capacity 2, one token: both
orders are enabled, agree, and equal the composite. -/

/-- Consumer (`0`: pre 1) and producer (`1`: post 1), capacity 2. -/
def cnet₁ : FinISPN (Fin 1) (Fin 1) (Fin 2) 2 where
  delay := pointDelay 2
  ipre u _ := if u = 0 then 1 else 0
  iread _ _ := 0
  ipost u _ := if u = 1 then 1 else 0

def c1m : BMarking (Fin 1) 2 := fun _ => 1

theorem c1_both_orders :
    cnet₁.ChainEnabled [0, 1] c1m ∧ cnet₁.ChainEnabled [1, 0] c1m := by
  decide

theorem c1_orders_agree :
    cnet₁.chainFire [0, 1] c1m = cnet₁.chainFire [1, 0] c1m := by
  decide

theorem c1_composite :
    cnet₁.chainFire [0, 1] c1m = cnet₁.compositeFire ↑[(0 : Fin 2), 1] c1m := by
  decide

/-! ### c2/c6 — the read/consume conflict pair

Transition `0` reads the one token that transition `1` consumes
(capacity 1, one token).  The read-first order is enabled; the
consume-first order is not — this is conflict (R2/R4 territory), and
it is exactly the reservation's *reads* clause that fails: supply,
headroom, and both members' individual enabledness all hold. -/

/-- Reader (`0`: read 1) and consumer (`1`: pre 1), capacity 1. -/
def cnet₂ : FinISPN (Fin 1) (Fin 1) (Fin 2) 1 where
  delay := pointDelay 1
  ipre u _ := if u = 1 then 1 else 0
  iread u _ := if u = 0 then 1 else 0
  ipost _ _ := 0

def c2m : BMarking (Fin 1) 1 := fun _ => 1

theorem c2_read_first_enabled : cnet₂.ChainEnabled [0, 1] c2m := by decide

theorem c2_consume_first_blocked : ¬ cnet₂.ChainEnabled [1, 0] c2m := by
  decide

theorem c2_not_setNonConflicting :
    ¬ cnet₂.SetNonConflicting ↑[(0 : Fin 2), 1] c2m := fun h =>
  (by decide : ¬ cnet₂.ChainEnabled [1, 0] c2m)
    (h [1, 0] (Multiset.cons_swap 1 0 0))

/-- c6 (the reads clause is the failing one — mutant locus `m4`):
supply, headroom, and members hold on the conflict pair… -/
theorem c6_other_clauses_hold :
    cnet₂.Supplied ↑[(0 : Fin 2), 1] c2m
      ∧ (∀ p, (c2m p : ℕ) + cnet₂.postSum ↑[(0 : Fin 2), 1] p ≤ 1)
      ∧ (∀ u ∈ (↑[(0 : Fin 2), 1] : Multiset (Fin 2)),
          cnet₂.IEnabled u c2m) := by
  decide

/-- …and the reads clause refuses, correctly: the reader's token is
the consumer's token. -/
theorem c6_reads_clause_fails :
    ¬ (∀ u ∈ (↑[(0 : Fin 2), 1] : Multiset (Fin 2)), ∀ p,
        cnet₂.iread u p ≤ (c2m p : ℕ) - cnet₂.preSum ↑[(0 : Fin 2), 1] p) := by
  decide

/-! ### c3 — joint supply is load-bearing in the statement (mutant
locus `m1`)

Two swap-tokens (pre 1, post 1) through one token: the unique chain
is enabled and lands 1 — each firing returns what it takes — but the
monus composite removes two tokens from one and reads 2.  Without
`Supplied` the composite ≠ every chain: the community would classify
the pair as conflicting (both sets reserve the same token), so the
composite never forms there, and the theorem's hypothesis carves
exactly that boundary. -/

/-- One swap-token transition (pre 1, post 1), capacity 2. -/
def cnet₃ : FinISPN (Fin 1) (Fin 1) (Fin 1) 2 where
  delay := pointDelay 2
  ipre _ _ := 1
  iread _ _ := 0
  ipost _ _ := 1

def c3m : BMarking (Fin 1) 2 := fun _ => 1

theorem c3_chain_enabled : cnet₃.ChainEnabled [0, 0] c3m := by decide

theorem c3_supply_fails : ¬ cnet₃.Supplied ↑[(0 : Fin 1), 0] c3m := by
  decide

theorem c3_composite_diverges :
    cnet₃.chainFire [0, 0] c3m ≠ cnet₃.compositeFire ↑[(0 : Fin 1), 0] c3m := by
  decide

/-! ### c4 — headroom is load-bearing: intermediates do not
interpolate (mutant locus `m3`)

Two producers and a consumer at one token, capacity 2: the
reservation holds (supply 1 ≤ 1, composite outcome 2 ≤ 2, members all
enabled, no reads) — but the producers-first order blocks at capacity
mid-chain.  Headroom (`1 + 2 ≤ 2`) correctly refuses. -/

/-- Producers (`0`,`1`: post 1) and a consumer (`2`: pre 1),
capacity 2. -/
def cnet₄ : FinISPN (Fin 1) (Fin 1) (Fin 3) 2 where
  delay := pointDelay 2
  ipre u _ := if u = 2 then 1 else 0
  iread _ _ := 0
  ipost u _ := if u = 2 then 0 else 1

def c4m : BMarking (Fin 1) 2 := fun _ => 1

theorem c4_reservation_holds :
    cnet₄.JointReservation ↑[(0 : Fin 3), 1, 2] c4m := by decide

theorem c4_producers_first_blocked :
    ¬ cnet₄.ChainEnabled [0, 1, 2] c4m := by decide

theorem c4_not_setNonConflicting :
    ¬ cnet₄.SetNonConflicting ↑[(0 : Fin 3), 1, 2] c4m := fun h =>
  (by decide : ¬ cnet₄.ChainEnabled [0, 1, 2] c4m) (h [0, 1, 2] rfl)

theorem c4_headroom_fails :
    ¬ (∀ p, (c4m p : ℕ) + cnet₄.postSum ↑[(0 : Fin 3), 1, 2] p ≤ 2) := by
  decide

/-! ### c5 — the value identity needs enabledness (mutant locus `m2`)

A disabled step clips: at the empty marking a swap-token's truncated
firing produces without consuming, and the value identity fails. -/

def c5m : BMarking (Fin 1) 2 := fun _ => 0

theorem c5_not_enabled : ¬ cnet₃.ChainEnabled [0] c5m := by decide

theorem c5_value_identity_fails :
    ¬ ((cnet₃.chainFire [0] c5m 0 : ℕ) + cnet₃.preSum ↑[(0 : Fin 1)] 0
        = (c5m 0 : ℕ) + cnet₃.postSum ↑[(0 : Fin 1)] 0) := by
  decide

/-! ### c7 — one-sided enabledness does not give order-invariance
(mutant locus `m5`)

A swap-token and a double-consumer at two tokens: the swap-first
order is enabled and lands 0; the consume-first order disables the
swap and its truncated chain lands 1.  Both hypotheses of
`chainFire_eq_of_enabled` are load-bearing. -/

/-- Swap-token (`0`: pre 1, post 1) and double-consumer (`1`: pre 2),
capacity 2. -/
def cnet₇ : FinISPN (Fin 1) (Fin 1) (Fin 2) 2 where
  delay := pointDelay 2
  ipre u _ := if u = 0 then 1 else 2
  iread _ _ := 0
  ipost u _ := if u = 0 then 1 else 0

def c7m : BMarking (Fin 1) 2 := fun _ => 2

theorem c7_swap_first_enabled : cnet₇.ChainEnabled [0, 1] c7m := by decide

theorem c7_consume_first_blocked : ¬ cnet₇.ChainEnabled [1, 0] c7m := by
  decide

theorem c7_same_multiset :
    (↑[(0 : Fin 2), 1] : Multiset (Fin 2)) = ↑[(1 : Fin 2), 0] :=
  Multiset.cons_swap 0 1 0

theorem c7_values_diverge :
    cnet₇.chainFire [0, 1] c7m ≠ cnet₇.chainFire [1, 0] c7m := by
  decide

end SpnSetFiringControls

end Adequacy
end SuFunctor
