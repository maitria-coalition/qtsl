import SuFunctor.Adequacy.StochasticPetriCascade

/-! # Supervision: control through enablement, at the uncoloured stratum

The composition-pattern face of supervisory control over stochastic
Petri frames, rendered with **the formalism's own enabling arcs** and
nothing else: a supervising policy is an ordinary jump-only mechanism
that owns *places*; a gated transition carries an ordinary enabling
arc (read-no-consume) from its gate place; enable is minting the gate
token and disable is draining it — both the policy's own firings.  No
new arc kind, bind class, or judgment form exists here to define,
because the gating mechanism has been first-class in every stratum of
the stochastic-Petri story since its statics square:
`NetTransition.read` (statics), `FinSPN.read` (delay-race face),
`FinISPN.iread` (immediate/cascade face).

What this module adds on top of the landed faces:

* **The gating lemmas** — the semantics the reduction predicts, read
  off the landed definitions: a closed gate zeroes the ordered race
  census (`raceCount_eq_zero_of_closed_gate` — `descFactorial`
  vanishes on undersupply, so pre-enabling was always in the count);
  a weight-1 gate place is a *multiplicative factor* of the census
  (`raceCount_gate_factor`: `descFactorial g 1 = g` — whence
  ℕ-graded throttling is native: `k` gate tokens multiply the race
  intensity by `k`); a closed gate disables an immediate transition
  (`not_IEnabled_of_closed_gate` — `iread` enters `iDemand` enters
  `IEnabled`, so the tangible/vanishing classification reads gate
  coordinates); and plant firings fix every gate coordinate
  (`fire_gate_fixed`/`ifire_gate_fixed` — read-no-consume *is* the
  zero-order hold, structure rather than lemma).

* **The `Supervise` package census** (`Supervise.ArcSeparation`): the
  ownership split (which places, which updates are the policy's) plus
  the one formation check the reduction genuinely demands, row-level
  and decidable — plant transitions touch policy places through
  declared read arcs only (no ordinary in/out arcs, in *either*
  direction: a plant transition producing into a gate place would be
  plant-side control of the policy's state), and policy updates carry
  no arcs on plant places at all (the policy acts through enablement
  only).  The derived gate rosters (`gatedDelay`/`gatedImmediate`)
  are computed from the split, not declared.  Raw rows remain lawful
  with the census as admission check — the same two-door structure as
  the pattern inventory's other packaged rows.

* **The Boolean gate discipline** (`Supervise.BooleanGates`): gates
  read as switches under a capacity-1 declaration (structural when
  the net's declared capacity is 1), and plant firings preserve the
  discipline because they cannot move gate tokens at all.  Omitting
  the discipline is meaningful, not unsound: the census lemma above
  gives token-count throttling.

* **The micro-instances** (`SuperviseControls`): a delay-gated net
  pinning closed/open/graded race intensities as values and the
  read-no-consume survival of the gate token across a firing; an
  immediate-gated net with a one-update policy whose wake is a
  *cascade step* — the mint rides `CascadeRank`'s own quantification,
  `zenoFree_of_cascadeRank` discharges non-Zeno for it unmodified,
  and absorption computes through the policy's update — together
  with census-teeth refusals (a plant write to a gate place; a
  policy read of a plant place) and the empty-policy specimen
  (deliberate idling: a gate-closed marking is tangible and inert,
  which is exactly why liveness is unprovable over the unrestricted
  policy family).  The capstone control applies the landed cascade
  adequacy square **to** the supervised composite: the composite is
  again a net of the same fragment, so the fixed-policy square is an
  instance, not an extension.

Deliberately not here, with their strata named: observables and
adaptedness (the observation interface lives at the coloured
record-lens stratum); event-subscription wiring (the event-port
fusion stratum — at this uncoloured stratum the policy's wake is
modelled by its own arcs); the box-discharge lint for gated guard
transitions (guard species are not in this fragment; the obligation
is certificate-stratum content, stated with the pattern's catalogue
entry); the package-as-data expansion, the collapsed fixed-policy
square at package generality, and the demonic gate-envelope face —
all in `SuFunctor.Adequacy.StochasticPetriSuperviseDemonic`. -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Finset

variable {P T U : Type} [Fintype P] [DecidableEq P] [Fintype T]
  [Fintype U] {B : ℕ}

/-! ## Gating lemmas: the delay-race face -/

namespace FinSPN

variable (N : FinSPN P T B)

omit [Fintype T] in
/-- The ordered census vanishes on undersupply at any single place:
`descFactorial` is zero exactly below the demand, so one
under-supplied place kills every ordered assignment. -/
theorem raceCount_eq_zero_of_undersupplied (t : T) (m : BMarking P B)
    (p : P) (h : (m p : ℕ) < N.demand t p) : N.raceCount t m = 0 :=
  Finset.prod_eq_zero (mem_univ p)
    (Nat.descFactorial_eq_zero_iff_lt.mpr h)

omit [Fintype T] in
/-- **A closed gate kills the race**: any enabling arc from an empty
place zeroes the transition's ordered census — pre-enabling was
always inside the count. -/
theorem raceCount_eq_zero_of_closed_gate (t : T) (m : BMarking P B)
    (g : P) (hread : N.read t g ≠ 0) (hm : m g = 0) :
    N.raceCount t m = 0 := by
  refine N.raceCount_eq_zero_of_undersupplied t m g ?_
  have hdef : N.demand t g = N.pre t g + N.read t g := rfl
  have hval : (m g : ℕ) = 0 := by rw [hm]; rfl
  omega

omit [Fintype T] in
/-- **The gate factor**: a weight-1 pure enabling arc contributes its
place's token count as a multiplicative factor of the ordered census
(`descFactorial g 1 = g`).  This is ℕ-graded throttling, native: `k`
gate tokens multiply the race intensity by `k`; the Boolean gate is
the capacity-1 special case. -/
theorem raceCount_gate_factor (t : T) (m : BMarking P B) (g : P)
    (hpre : N.pre t g = 0) (hread : N.read t g = 1) :
    N.raceCount t m
      = (m g : ℕ) * ∏ p ∈ univ.erase g,
          ((m p : ℕ)).descFactorial (N.demand t p) := by
  have hd : N.demand t g = 1 := by
    show N.pre t g + N.read t g = 1
    rw [hpre, hread]
  show (∏ p, ((m p : ℕ)).descFactorial (N.demand t p)) = _
  rw [← Finset.mul_prod_erase univ _ (mem_univ g), hd,
    Nat.descFactorial_one]

omit [Fintype T] in
/-- **Read-no-consume, as marking arithmetic**: a firing with no
ordinary arcs at a place leaves that place's count unchanged — in
particular, the fired marking *keeps* every gate token it read.  This
is the zero-order hold of supervisory gating, as structure: token
presence has no drift, and no plant firing can move a gate token. -/
theorem fire_gate_fixed (t : T) (m : BMarking P B) (g : P)
    (hpre : N.pre t g = 0) (hpost : N.post t g = 0) :
    N.fire t m g = m g := by
  apply Fin.ext
  show min (N.outAt t m g) B = ((m g : ℕ))
  have hout : N.outAt t m g = (m g : ℕ) := by
    show (m g : ℕ) - N.pre t g + N.post t g = _
    rw [hpre, hpost]
    omega
  rw [hout]
  exact min_eq_left (m g).is_le

end FinSPN

/-! ## Gating lemmas: the immediate/cascade face -/

namespace FinISPN

variable (N : FinISPN P T U B)

omit [Fintype T] [Fintype U] in
/-- **A closed gate disables an immediate transition**: `iread`
enters `iDemand` enters `IEnabled`, so the tangible/vanishing
classification is a function of the whole marking, gate coordinates
included. -/
theorem not_IEnabled_of_closed_gate (u : U) (m : BMarking P B) (g : P)
    (hread : N.iread u g ≠ 0) (hm : m g = 0) :
    ¬ N.IEnabled u m := by
  intro h
  have h1 := (h g).1
  have hdef : N.iDemand u g = N.ipre u g + N.iread u g := rfl
  have hval : (m g : ℕ) = 0 := by rw [hm]; rfl
  omega

omit [Fintype T] [Fintype U] in
/-- The immediate twin of `FinSPN.fire_gate_fixed`: an immediate
firing with no ordinary arcs at a place fixes that place's count. -/
theorem ifire_gate_fixed (u : U) (m : BMarking P B) (g : P)
    (hpre : N.ipre u g = 0) (hpost : N.ipost u g = 0) :
    N.ifire u m g = m g := by
  apply Fin.ext
  show min (N.iOutAt u m g) B = ((m g : ℕ))
  have hout : N.iOutAt u m g = (m g : ℕ) := by
    show (m g : ℕ) - N.ipre u g + N.ipost u g = _
    rw [hpre, hpost]
    omega
  rw [hout]
  exact min_eq_left (m g).is_le

end FinISPN

/-! ## The Supervise package: ownership split, census, discipline

The package's structural content at this stratum is *bookkeeping over
existing rows*: which places and which immediate transitions are the
policy's.  The census is the one formation check the enabling-arc
rendering demands; everything it consumes is already on the net's
rows, so it binds however the composite was wired — package or
hand-rolled — the two-door structure of the pattern inventory. -/

namespace Supervise

variable [DecidableEq U]

/-- **The arc-separation census** for a supervised net with
policy-owned places `gates` and policy update transitions `upd`
(the policy is jump-only, so the delay layer is wholly the plant's):

* *plant-delay clause* — no delay transition carries an ordinary arc
  at a gate place, in either direction (read arcs are free: they are
  the gating);
* *plant-immediate clause* — likewise for the plant's immediate
  transitions (a plant transition producing into a gate place would
  be plant-side control of the policy's state — refused);
* *policy-confinement clause* — a policy update carries **no arc at
  all** on plant places: the policy acts on the plant through
  enablement only (its information channel lives at the observation
  and event strata, not on arcs).

Row-level and decidable; the census reads output arcs as well as
inputs. -/
def ArcSeparation (N : FinISPN P T U B) (gates : Finset P)
    (upd : Finset U) : Prop :=
  (∀ t : T, ∀ p ∈ gates, N.delay.pre t p = 0 ∧ N.delay.post t p = 0)
    ∧ (∀ u : U, u ∉ upd → ∀ p ∈ gates,
        N.ipre u p = 0 ∧ N.ipost u p = 0)
    ∧ (∀ u ∈ upd, ∀ p : P, p ∉ gates →
        N.ipre u p = 0 ∧ N.iread u p = 0 ∧ N.ipost u p = 0)

instance (N : FinISPN P T U B) (gates : Finset P) (upd : Finset U) :
    Decidable (ArcSeparation N gates upd) :=
  inferInstanceAs (Decidable
    ((∀ t : T, ∀ p ∈ gates, N.delay.pre t p = 0 ∧ N.delay.post t p = 0)
      ∧ (∀ u : U, u ∉ upd → ∀ p ∈ gates,
          N.ipre u p = 0 ∧ N.ipost u p = 0)
      ∧ (∀ u ∈ upd, ∀ p : P, p ∉ gates →
          N.ipre u p = 0 ∧ N.iread u p = 0 ∧ N.ipost u p = 0)))

/-- The derived gate roster, delay species: which (transition, place)
pairs are gated — computed from the ownership split, never declared.
The family quantification of the demonic face reads this roster. -/
def gatedDelay (N : FinISPN P T U B) (gates : Finset P) :
    Finset (T × P) :=
  univ.filter fun tp => tp.2 ∈ gates ∧ N.delay.read tp.1 tp.2 ≠ 0

/-- The derived gate roster, immediate species. -/
def gatedImmediate (N : FinISPN P T U B) (gates : Finset P) :
    Finset (U × P) :=
  univ.filter fun up => up.2 ∈ gates ∧ N.iread up.1 up.2 ≠ 0

omit [Fintype T] [Fintype U] [DecidableEq U] in
/-- **The hold, packaged** (delay species): under arc separation, no
plant delay firing moves any gate coordinate. -/
theorem gate_hold_delay {N : FinISPN P T U B} {gates : Finset P}
    {upd : Finset U} (h : ArcSeparation N gates upd) (t : T)
    (m : BMarking P B) {g : P} (hg : g ∈ gates) :
    N.delay.fire t m g = m g :=
  N.delay.fire_gate_fixed t m g (h.1 t g hg).1 (h.1 t g hg).2

omit [Fintype T] [Fintype U] [DecidableEq U] in
/-- **The hold, packaged** (immediate species): under arc separation,
no plant immediate firing moves any gate coordinate. -/
theorem gate_hold_immediate {N : FinISPN P T U B} {gates : Finset P}
    {upd : Finset U} (h : ArcSeparation N gates upd) {u : U}
    (hu : u ∉ upd) (m : BMarking P B) {g : P} (hg : g ∈ gates) :
    N.ifire u m g = m g :=
  N.ifire_gate_fixed u m g (h.2.1 u hu g hg).1 (h.2.1 u hu g hg).2

/-- **The Boolean gate discipline**: every gate place carries at most
one token — gates read as switches.  A declaration plus an
obligation, not vocabulary; deliberately omittable (`k` tokens then
throttle the race by `k`, per `FinSPN.raceCount_gate_factor`). -/
def BooleanGates (gates : Finset P) (m : BMarking P B) : Prop :=
  ∀ p ∈ gates, (m p : ℕ) ≤ 1

omit [Fintype P] [DecidableEq P] in
/-- At declared capacity 1 the Boolean discipline is structural:
every marking satisfies it everywhere. -/
theorem booleanGates_of_B_le_one (hB : B ≤ 1) (gates : Finset P)
    (m : BMarking P B) : BooleanGates gates m :=
  fun p _ => le_trans (m p).is_le hB

omit [Fintype T] [Fintype U] [DecidableEq U] in
/-- Plant delay firings preserve the Boolean discipline — they cannot
move gate tokens at all. -/
theorem booleanGates_preserved_delay {N : FinISPN P T U B}
    {gates : Finset P} {upd : Finset U}
    (h : ArcSeparation N gates upd) (t : T) {m : BMarking P B}
    (hm : BooleanGates gates m) :
    BooleanGates gates (N.delay.fire t m) := fun p hp => by
  rw [gate_hold_delay h t m hp]
  exact hm p hp

omit [Fintype T] [Fintype U] [DecidableEq U] in
/-- Plant immediate firings preserve the Boolean discipline. -/
theorem booleanGates_preserved_immediate {N : FinISPN P T U B}
    {gates : Finset P} {upd : Finset U}
    (h : ArcSeparation N gates upd) {u : U} (hu : u ∉ upd)
    {m : BMarking P B} (hm : BooleanGates gates m) :
    BooleanGates gates (N.ifire u m) := fun p hp => by
  rw [gate_hold_immediate h hu m hp]
  exact hm p hp

end Supervise

/-! ## Controls

Concrete closed forms pinning the gating semantics and the census —
proofs deliberately independent of the lemmas they guard
(decidability, not rewriting): second witnesses at the designed
mutant loci. -/

namespace SuperviseControls

open FinISPN SpnCascadeControls

/-! ### The delay-gated net: closed, open, graded

Place 0 is the plant's queue; place 1 is the gate, policy-owned.  One
delay transition consumes a queue token, reads the gate, at rate 5;
capacity 2, so the gate place can hold two tokens and the graded
semantics is visible. -/

/-- One queue token, gate closed. -/
def q10 : BMarking (Fin 2) 2 := fun p => if p = 0 then 1 else 0

/-- One queue token, gate open. -/
def q11 : BMarking (Fin 2) 2 := fun _ => 1

/-- Queue empty, gate open — the fired image of `q11`. -/
def q01 : BMarking (Fin 2) 2 := fun p => if p = 1 then 1 else 0

/-- One queue token, gate at 2 (Boolean discipline deliberately
omitted). -/
def q12 : BMarking (Fin 2) 2 := fun p => if p = 0 then 1 else 2

/-- Queue empty, gate at 2. -/
def q02 : BMarking (Fin 2) 2 := fun p => if p = 0 then 0 else 2

/-- The delay-gated net: consume one queue token, read the gate,
rate 5. -/
def gnet₁ : FinSPN (Fin 2) (Fin 1) 2 where
  pre := fun _ p => if p = 0 then 1 else 0
  read := fun _ p => if p = 1 then 1 else 0
  post := fun _ _ => 0
  rate := fun _ => 5
  rate_nonneg := fun _ => by norm_num
  init := fun m => if m = q11 then 1 else 0
  init_nonneg := fun m => by by_cases h : m = q11 <;> simp [h]
  init_sum := Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (mem_univ _))

/-- Closed gate: the ordered census vanishes. -/
theorem gnet₁_census_closed : gnet₁.raceCount 0 q10 = 0 := by decide

/-- Open gate: census 1 (one token, one gate token, weight-1 arcs). -/
theorem gnet₁_census_open : gnet₁.raceCount 0 q11 = 1 := by decide

/-- Gate at 2: the census doubles — `descFactorial 2 1 = 2`. -/
theorem gnet₁_census_graded : gnet₁.raceCount 0 q12 = 2 := by decide

/-- **Read-no-consume, pinned**: the firing keeps the gate token —
the fired marking still has the gate open. -/
theorem gnet₁_fire_keeps_gate : gnet₁.fire 0 q11 = q01 := by decide

/-- Closed gate: zero race intensity to every target. -/
theorem gnet₁_rate_closed (m' : BMarking (Fin 2) 2) :
    gnet₁.raceRate q10 m' = 0 := by
  show (∑ t : Fin 1, if gnet₁.Enabled t q10 ∧ gnet₁.fire t q10 = m'
      then (gnet₁.raceCount t q10 : ℚ) * gnet₁.rate t else 0) = 0
  rw [Fin.sum_univ_one, if_neg]
  rintro ⟨he, -⟩
  exact absurd he (by decide)

/-- Open gate: the full rate flows, and the gate survives the
firing. -/
theorem gnet₁_rate_open : gnet₁.raceRate q11 q01 = 5 := by
  show (∑ t : Fin 1, if gnet₁.Enabled t q11 ∧ gnet₁.fire t q11 = q01
      then (gnet₁.raceCount t q11 : ℚ) * gnet₁.rate t else 0) = 5
  rw [Fin.sum_univ_one, if_pos ⟨by decide, by decide⟩,
    show gnet₁.raceCount 0 q11 = 1 from by decide,
    show gnet₁.rate 0 = 5 from rfl]
  norm_num

/-- **Graded throttling, pinned as a value**: two gate tokens, twice
the rate — `k` tokens = rate × `k`.  The Boolean capacity-1
discipline is exactly what rules this reading out where switches are
meant. -/
theorem gnet₁_rate_graded : gnet₁.raceRate q12 q02 = 10 := by
  show (∑ t : Fin 1, if gnet₁.Enabled t q12 ∧ gnet₁.fire t q12 = q02
      then (gnet₁.raceCount t q12 : ℚ) * gnet₁.rate t else 0) = 10
  rw [Fin.sum_univ_one, if_pos ⟨by decide, by decide⟩,
    show gnet₁.raceCount 0 q12 = 2 from by decide,
    show gnet₁.rate 0 = 5 from rfl]
  norm_num

/-! ### The immediate-gated net with a one-update policy

Place 0 the plant's queue, place 1 the gate; capacity 1.  Immediate
transition 0 is the plant's gated dispatch (consume a queue token,
read the gate); immediate transition 1 is the policy's single update
(mint the gate token — capacity blocks re-minting at an open gate).
Ownership split: gates = {1}, policy updates = {1}. -/

/-- The supervised micro-composite. -/
def gnet₂ : FinISPN (Fin 2) (Fin 1) (Fin 2) 1 where
  delay :=
    { pre := fun _ _ => 0
      read := fun _ _ => 0
      post := fun _ _ => 0
      rate := fun _ => 0
      rate_nonneg := fun _ => le_rfl
      init := fun m => if m = m10 then 1 else 0
      init_nonneg := fun m => by by_cases h : m = m10 <;> simp [h]
      init_sum := Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (mem_univ _)) }
  ipre := fun u p => if u = 0 ∧ p = 0 then 1 else 0
  iread := fun u p => if u = 0 ∧ p = 1 then 1 else 0
  ipost := fun u p => if u = 1 ∧ p = 1 then 1 else 0

/-- The census passes on the well-formed supervised composite. -/
theorem gnet₂_census : Supervise.ArcSeparation gnet₂ {1} {1} := by
  decide

/-- Census teeth, plant-write direction: a plant immediate that
*produces* into the gate place is refused — the census reads output
arcs, not just inputs. -/
def gnet₂bad : FinISPN (Fin 2) (Fin 1) (Fin 2) 1 :=
  { gnet₂ with ipost := fun _ p => if p = 1 then 1 else 0 }

theorem gnet₂bad_refused :
    ¬ Supervise.ArcSeparation gnet₂bad {1} {1} := by decide

/-- Census teeth, policy-read direction: a policy update that reads a
plant place directly (an arc side channel around the observation
interface) is refused. -/
def gnet₂bad₂ : FinISPN (Fin 2) (Fin 1) (Fin 2) 1 :=
  { gnet₂ with iread := fun u p =>
      if (u = 0 ∧ p = 1) ∨ (u = 1 ∧ p = 0) then 1 else 0 }

theorem gnet₂bad₂_refused :
    ¬ Supervise.ArcSeparation gnet₂bad₂ {1} {1} := by decide

/-- Census teeth, delay direction: a delay transition producing into
the gate place is refused by the plant-delay clause. -/
def gnet₂bad₃ : FinISPN (Fin 2) (Fin 1) (Fin 2) 1 :=
  { gnet₂ with delay :=
    { pre := fun _ _ => 0
      read := fun _ _ => 0
      post := fun _ p => if p = 1 then 1 else 0
      rate := fun _ => 0
      rate_nonneg := fun _ => le_rfl
      init := fun m => if m = m10 then 1 else 0
      init_nonneg := fun m => by by_cases h : m = m10 <;> simp [h]
      init_sum := Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (mem_univ _)) } }

theorem gnet₂bad₃_refused :
    ¬ Supervise.ArcSeparation gnet₂bad₃ {1} {1} := by decide

/-- A delay-gated variant passes: read arcs are the sanctioned
channel (the gating itself), for either species. -/
def gnet₂delay : FinISPN (Fin 2) (Fin 1) (Fin 2) 1 :=
  { gnet₂ with delay :=
    { pre := fun _ p => if p = 0 then 1 else 0
      read := fun _ p => if p = 1 then 1 else 0
      post := fun _ _ => 0
      rate := fun _ => 5
      rate_nonneg := fun _ => by norm_num
      init := fun m => if m = m10 then 1 else 0
      init_nonneg := fun m => by by_cases h : m = m10 <;> simp [h]
      init_sum := Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (mem_univ _)) } }

theorem gnet₂delay_census : Supervise.ArcSeparation gnet₂delay {1} {1} := by
  decide

/-- Closed gate blocks the plant's dispatch. -/
theorem gnet₂_closed_blocks : ¬ gnet₂.IEnabled 0 m10 := by decide

/-- Open gate enables it. -/
theorem gnet₂_open_enables : gnet₂.IEnabled 0 m11 := by decide

/-- The wake is pending at the gate-closed marking: the policy's mint
is enabled, so the marking is vanishing — the policy's update is an
ordinary immediate transition of the composite. -/
theorem gnet₂_wake_pending : gnet₂.IsVanishing m10 := by decide

/-- The classified elements of `gnet₂`, named for the controls. -/
def tg01 : gnet₂.Tangible := ⟨m01, by decide⟩
def vg00 : gnet₂.Vanishing := ⟨m00, by decide⟩
def vg10 : gnet₂.Vanishing := ⟨m10, by decide⟩
def vg11 : gnet₂.Vanishing := ⟨m11, by decide⟩

theorem gnet₂_tangible_univ :
    (univ : Finset gnet₂.Tangible) = {tg01} := by decide

theorem gnet₂_vanishing_univ :
    (univ : Finset gnet₂.Vanishing) = {vg00, vg10, vg11} := by decide

/-- The mint's firing outcome: gate open, queue untouched — still
vanishing (the dispatch is now enabled). -/
theorem gnet₂_fire_mint :
    gnet₂.toSum (gnet₂.ifire 1 vg10.1) = Sum.inr vg11 := by
  rw [show gnet₂.ifire 1 vg10.1 = m11 from by decide]
  exact dif_pos (by decide)

/-- The dispatch's firing outcome: queue served, **gate token
retained** (read-no-consume) — tangible. -/
theorem gnet₂_fire_dispatch :
    gnet₂.toSum (gnet₂.ifire 0 vg11.1) = Sum.inl tg01 := by
  rw [show gnet₂.ifire 0 vg11.1 = m01 from by decide]
  exact dif_neg (by decide)

/-- The idle wake: minting at an empty queue absorbs immediately. -/
theorem gnet₂_fire_idle_mint :
    gnet₂.toSum (gnet₂.ifire 1 vg00.1) = Sum.inl tg01 := by
  rw [show gnet₂.ifire 1 vg00.1 = m01 from by decide]
  exact dif_neg (by decide)

/-- A cascade rank for the supervised composite: queue tokens waiting
at a closed gate.  The mint `(1,0) ↦ (1,1)` descends `1 ↦ 0`; every
other enabled firing absorbs.  **The policy's own update is inside
the rank's quantification** — the wake is a cascade step like any
other. -/
def rGate : gnet₂.Vanishing → ℕ :=
  fun i => (i.1 0 : ℕ) * (1 - (i.1 1 : ℕ))

theorem gnet₂_rank : gnet₂.CascadeRank rGate := by
  intro i u hu j hj
  have hi : i = vg00 ∨ i = vg10 ∨ i = vg11 := by
    have h := Finset.mem_univ i
    rw [gnet₂_vanishing_univ] at h
    simpa using h
  rcases hi with rfl | rfl | rfl
  · obtain rfl : u = 1 :=
      (by decide : ∀ v : Fin 2, gnet₂.IEnabled v vg00.1 → v = 1) u hu
    rw [gnet₂_fire_idle_mint] at hj
    simp at hj
  · obtain rfl : u = 1 :=
      (by decide : ∀ v : Fin 2, gnet₂.IEnabled v vg10.1 → v = 1) u hu
    rw [gnet₂_fire_mint] at hj
    obtain rfl : vg11 = j := by simpa using hj
    decide
  · obtain rfl : u = 0 :=
      (by decide : ∀ v : Fin 2, gnet₂.IEnabled v vg11.1 → v = 0) u hu
    rw [gnet₂_fire_dispatch] at hj
    simp at hj

/-- Rank teeth: the trivial rank is refused — the cascade genuinely
passes through a vanishing intermediate (the freshly-minted gate
enabling the dispatch within the same epoch). -/
theorem gnet₂_rank_teeth : ¬ gnet₂.CascadeRank (fun _ => 0) :=
  fun h =>
    Nat.lt_irrefl 0 (h vg10 1 (by decide) vg11 gnet₂_fire_mint)

theorem gnet₂_zenoFree :
    ZenoFree (gnet₂.toFinMA.imStep gnet₂.uniformPolicy) rGate :=
  gnet₂.zenoFree_uniform gnet₂_rank

/-- At the gate-closed marking only the mint is enabled: the uniform
scheduler gives it the whole mass. -/
theorem gnet₂_uniform_mint : gnet₂.uniformPolicy.choice vg10 1 = 1 := by
  show (if gnet₂.IEnabled 1 vg10.1
    then ((gnet₂.enabledCount vg10 : ℕ) : ℚ)⁻¹ else 0) = 1
  rw [if_pos (by decide), show gnet₂.enabledCount vg10 = 1 from by decide]
  norm_num

/-- The disabled dispatch gets zero scheduler mass at the closed
gate. -/
theorem gnet₂_uniform_blocked :
    gnet₂.uniformPolicy.choice vg10 0 = 0 := by
  show (if gnet₂.IEnabled 0 vg10.1
    then ((gnet₂.enabledCount vg10 : ℕ) : ℚ)⁻¹ else 0) = 0
  rw [if_neg (by decide)]

/-- The first cascade step — the policy's wake: the mint carries the
whole mass to the gate-open vanishing marking. -/
theorem gnet₂_imStep_mint :
    gnet₂.toFinMA.imStep gnet₂.uniformPolicy vg10 (Sum.inr vg11) = 1 := by
  show (∑ u : Fin 2, gnet₂.uniformPolicy.choice vg10 u
      * gnet₂.toFinMA.branch vg10 u (Sum.inr vg11)) = 1
  rw [Fin.sum_univ_two, gnet₂_uniform_blocked, gnet₂_uniform_mint]
  simp only [toFinMA_branch]
  rw [gnet₂_fire_mint, if_pos (show gnet₂.IEnabled 1 vg10.1 by decide),
    if_pos rfl]
  norm_num

/-- Off-path legs of the wake step carry no mass. -/
theorem gnet₂_imStep_mint_off (y : gnet₂.Tangible ⊕ gnet₂.Vanishing)
    (hy : y ≠ Sum.inr vg11) :
    gnet₂.toFinMA.imStep gnet₂.uniformPolicy vg10 y = 0 := by
  show (∑ u : Fin 2, gnet₂.uniformPolicy.choice vg10 u
      * gnet₂.toFinMA.branch vg10 u y) = 0
  rw [Fin.sum_univ_two, gnet₂_uniform_blocked, gnet₂_uniform_mint]
  simp only [toFinMA_branch]
  rw [gnet₂_fire_mint, if_pos (show gnet₂.IEnabled 1 vg10.1 by decide),
    if_neg (show ¬ (Sum.inr vg11 : gnet₂.Tangible ⊕ gnet₂.Vanishing) = y
      from fun h => hy h.symm)]
  norm_num

/-- The second cascade step: the freshly-enabled dispatch carries the
whole mass to the tangible marking — gate token retained. -/
theorem gnet₂_imStep_dispatch :
    gnet₂.toFinMA.imStep gnet₂.uniformPolicy vg11 (Sum.inl tg01) = 1 := by
  show (∑ u : Fin 2, gnet₂.uniformPolicy.choice vg11 u
      * gnet₂.toFinMA.branch vg11 u (Sum.inl tg01)) = 1
  rw [Fin.sum_univ_two,
    show gnet₂.uniformPolicy.choice vg11 0 = 1 from by
      show (if gnet₂.IEnabled 0 vg11.1
        then ((gnet₂.enabledCount vg11 : ℕ) : ℚ)⁻¹ else 0) = 1
      rw [if_pos (by decide),
        show gnet₂.enabledCount vg11 = 1 from by decide]
      norm_num,
    show gnet₂.uniformPolicy.choice vg11 1 = 0 from by
      show (if gnet₂.IEnabled 1 vg11.1
        then ((gnet₂.enabledCount vg11 : ℕ) : ℚ)⁻¹ else 0) = 0
      rw [if_neg (by decide)]]
  simp only [toFinMA_branch]
  rw [gnet₂_fire_dispatch, if_pos (show gnet₂.IEnabled 0 vg11.1 by decide),
    if_pos rfl]
  norm_num

/-- Off-path legs of the dispatch step carry no mass. -/
theorem gnet₂_imStep_dispatch_off (y : gnet₂.Tangible ⊕ gnet₂.Vanishing)
    (hy : y ≠ Sum.inl tg01) :
    gnet₂.toFinMA.imStep gnet₂.uniformPolicy vg11 y = 0 := by
  show (∑ u : Fin 2, gnet₂.uniformPolicy.choice vg11 u
      * gnet₂.toFinMA.branch vg11 u y) = 0
  rw [Fin.sum_univ_two,
    show gnet₂.uniformPolicy.choice vg11 0 = 1 from by
      show (if gnet₂.IEnabled 0 vg11.1
        then ((gnet₂.enabledCount vg11 : ℕ) : ℚ)⁻¹ else 0) = 1
      rw [if_pos (by decide),
        show gnet₂.enabledCount vg11 = 1 from by decide]
      norm_num,
    show gnet₂.uniformPolicy.choice vg11 1 = 0 from by
      show (if gnet₂.IEnabled 1 vg11.1
        then ((gnet₂.enabledCount vg11 : ℕ) : ℚ)⁻¹ else 0) = 0
      rw [if_neg (by decide)]]
  simp only [toFinMA_branch]
  rw [gnet₂_fire_dispatch, if_pos (show gnet₂.IEnabled 0 vg11.1 by decide),
    if_neg (show ¬ (Sum.inl tg01 : gnet₂.Tangible ⊕ gnet₂.Vanishing) = y
      from fun h => hy h.symm)]
  norm_num

/-- Absorption from the gate-open intermediate, one fuel short of the
working fuel: one dispatch step, then the Markovian point mass. -/
theorem gnet₂_absorb_mid :
    absorbIter (gnet₂.toFinMA.imStep gnet₂.uniformPolicy) 1
      (Sum.inr vg11) tg01 = 1 := by
  show absorbIter (gnet₂.toFinMA.imStep gnet₂.uniformPolicy) (0 + 1)
    (Sum.inr vg11) tg01 = 1
  rw [absorbIter_succ_inr, Fintype.sum_sum_type, gnet₂_tangible_univ,
    gnet₂_vanishing_univ, Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [absorbIter_zero, hitMass_inr]
  rw [show hitMass (Sum.inl tg01 : gnet₂.Tangible ⊕ gnet₂.Vanishing) tg01
        = 1 from by rw [hitMass_inl]; exact if_pos rfl,
    gnet₂_imStep_dispatch]
  norm_num

/-- **The supervised cascade absorbs whole, through the policy's own
update**: from the queue-waiting, gate-closed marking, absorption
reaches the served tangible marking with mass 1 — wake (mint), then
dispatch, two zero-time steps inside one cascade epoch. -/
theorem gnet₂_cascade_absorb :
    gnet₂.toFinMA.absorb gnet₂.uniformPolicy rGate
      (Sum.inr vg10) tg01 = 1 := by
  show absorbIter (gnet₂.toFinMA.imStep gnet₂.uniformPolicy)
    (absFuel rGate) (Sum.inr vg10) tg01 = 1
  rw [show absFuel rGate = 1 + 1 from by decide, absorbIter_succ_inr,
    Fintype.sum_sum_type, gnet₂_tangible_univ, gnet₂_vanishing_univ,
    Finset.sum_singleton, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    gnet₂_imStep_mint, gnet₂_absorb_mid,
    gnet₂_imStep_mint_off (Sum.inl tg01) (by decide),
    gnet₂_imStep_mint_off (Sum.inr vg00) (by decide),
    gnet₂_imStep_mint_off (Sum.inr vg10) (by decide)]
  norm_num

/-- **The collapse, as a control**: the supervised composite is again
a net of the same fragment, so its fixed-policy adequacy is the
landed cascade square *applied to it* — an instance, not an
extension; the pattern adds no vertical. -/
theorem gnet₂_supervised_adequacy (k : ℕ)
    {a : Crd (Traj gnet₂.Tangible k)} :
    ∃ α : Cell
        (looseConj (atoms (jumpRows
          (closeMaRows gnet₂.compileIspn
            (compilePolicy gnet₂.uniformPolicy) (absFuel rGate))) k) :
          Loose a a)
        (singletonC (gnet₂.tangiblePathLaw gnet₂.uniformPolicy rGate
          gnet₂_zenoFree k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  gnet₂.ispn_cascade_adequacy gnet₂.uniformPolicy rGate gnet₂_zenoFree k

/-! ### The empty policy: deliberate idling -/

/-- The plant of `gnet₂` with **no policy at all** — the empty
policy: no update transitions, gate never minted. -/
def gnet₃ : FinISPN (Fin 2) (Fin 1) (Fin 1) 1 where
  delay :=
    { pre := fun _ _ => 0
      read := fun _ _ => 0
      post := fun _ _ => 0
      rate := fun _ => 0
      rate_nonneg := fun _ => le_rfl
      init := fun m => if m = m10 then 1 else 0
      init_nonneg := fun m => by by_cases h : m = m10 <;> simp [h]
      init_sum := Finset.sum_ite_eq' _ _ _ |>.trans (if_pos (mem_univ _)) }
  ipre := fun _ p => if p = 0 then 1 else 0
  iread := fun _ p => if p = 1 then 1 else 0
  ipost := fun _ _ => 0

/-- The empty policy is well-formed: the census passes with an empty
update roster. -/
theorem gnet₃_census :
    Supervise.ArcSeparation gnet₃ {1} (∅ : Finset (Fin 1)) := by decide

/-- **Deliberate idling, pinned**: under the empty policy the
queue-waiting marking is *tangible* — the gated dispatch is blocked
and nothing will ever open the gate.  This is why liveness is
unprovable over the unrestricted policy family: never-minting is a
member. -/
theorem gnet₃_idles : ¬ gnet₃.IsVanishing m10 := by decide

end SuperviseControls

end Adequacy
end SuFunctor
