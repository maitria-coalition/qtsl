import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.FinCases

/-! # QWireComposeMarks — the cyclic liveness composition rule, discrete-relational tier

**Source spec**: `metanotation/QTSL-rules.toml` rule `QWireComposeMarks`
(the liveness sibling of `QWireCompose`); the cyclic AG design, r3
(premise-shaped liveness) + the r4 addendum this module's battery forced
(the pin rows); statements + mutant loci preregistered — committed before
these proofs were written.

This module is the **discrete-relational instance of the soundness
metatheorem** for the marks composition rule, plus its countermodel battery.
The model (`MarkNet`): `n` components over a wire alphabet `V`, each with
in-neighbours `dep`, a delivery lag `lag` (0 = instantaneous), an admitted-output
relation `F` reading one wire snapshot (memoryless v1), and an initial-segment
set `init`. A joint behaviour (`JointRun`) satisfies every component's
constraint at every stage; zero-lag cycles are algebraic loops, constrained
within the instant — precisely the configuration the acyclic rule's causality
walk makes unrepresentable, and the configuration this rule exists to admit.

## The kit, and what forced each row

- **`MarkFlowFeasible`** — the schedule walk, the ∃-dual of the causality
  walk: producer-supplied stage labels, checker-verified lag arithmetic.
  Formalized here at the exact-lag row shape (`t i = t j + lag i` per
  in-edge); the general difference-constraint species is the wire format's
  business. This Prop is the walk's *specification*; the executable checker
  is the geolog side-condition. Forced by the relay–delay loop (`z1Net`):
  without it the rule concludes marks a delay-pinned loop cannot realize
  (`z1_refutes_walkless`), and the walk refuses exactly that loop
  (`z1_walk_infeasible`) while admitting the all-ones relay loop
  (`allOnes_walk_feasible`).
- **`PinnedDelivery`** — the pin rows (mark membership + pointed delivery at
  a producer-supplied value per mark). Forced by the swap-loop countermodel
  (`z5Net`): the ∀∃ conditional-delivery premises, the walk, properness, and
  joint instant seriality can ALL hold while no joint run realizes the marks
  — each component maps the mark set into the mark set, but the loop's
  fixpoint equation only closes outside it (`z5_refutes_pinless`, the
  machine-checked defect-with-witness against the premise-only rule shape).
  The pin rows refuse that instance (`z5_no_pin`) and admit the relay loop.
- **`InstantClosure`** — stepwise joint properness relative to the schedule:
  the tier discharge of the W0-species rows for this construction. Bare
  composite nonemptiness is NOT enough (blocking components — admission
  constraining the input's future — leave a pinned instant with no admitted
  extension while an all-quiet run exists; and unpinned joint seriality is
  not enough either, since an instant subsystem's solvability can flip on
  the pinned coordinate's value). Both necessity witnesses are named in the
  preregistration (M3/M4); their formalization is a successor.
- **`ConditionalDelivery`** — the rule's premise judgment (the ∀∃
  conditional-delivery reading, memoryless instantiation): every
  mark-conforming input snapshot admits some own-mark output through it.
  Sufficient WITHOUT pins exactly where no zero-lag cycle bites:
  `pins_of_conditional_delivery` chains the premises into a pin along any
  topological order, so the premise-shaped rule is sound on acyclic-instant
  networks (`marks_of_conditional_delivery_acyclic`). On cycles, the walk's
  own arithmetic pins every cycle to total lag zero and one shared label, and
  the pin rows are the one value-level ingredient soundness then forces.

## The assembly engine

`marks_of_pinned_delivery`: pins + walk + seriality + instant closure yield a
joint run realizing every mark at its label. The joint object exists only
under the conclusion's binder — the construction (stage recursion; lagged
coordinates choose init/F/pin, instant coordinates close jointly via
`InstantClosure`, pinned constraints discharge through the pointed rows since
the walk aligns every in-neighbour of a marked component at its lagged label)
is performed by `build`, and nothing behaviour-sized appears among the
hypotheses.

Model honesty: memoryless `F` cannot express the design zoo's mode-memory
(Z3) or input-refusal-vacuity (Z4) members; those remain design-level battery
members. Everything here is classical and naturally noncomputable; nothing is
checker-facing (cf. `lean-conventions.md`).
-/

namespace BernsteinLogic.QtslCompose.Marks

open Classical

/-- A discrete relational network: `n` components over wire alphabet `V`.
Component `i` reads the wire snapshot at stage `k - lag i` (its in-neighbours
`dep i` are the coordinates it actually consumes) and emits one value per
stage; during the initial segment (`k < lag i`) its output is drawn from
`init i`. Zero lag means the constraint couples values *within* a stage. -/
structure MarkNet (n : ℕ) (V : Type*) where
  /-- in-neighbours: the wire coordinates component `i` reads -/
  dep : Fin n → Finset (Fin n)
  /-- delivery lag: `0` = instantaneous (algebraic), `≥ 1` = pipelined -/
  lag : Fin n → ℕ
  /-- admitted outputs, given the snapshot read at `k - lag i` -/
  F : Fin n → (Fin n → V) → Set V
  /-- admitted outputs during the initial segment (`k < lag i`) -/
  init : Fin n → Set V

variable {n : ℕ} {V : Type*}

/-- A joint behaviour of the network: at every stage, every component's
output is admitted — through its lagged snapshot once the pipe has filled,
from its initial set before that. -/
def JointRun (N : MarkNet n V) (ω : ℕ → Fin n → V) : Prop :=
  ∀ k i, (N.lag i ≤ k → ω k i ∈ N.F i (ω (k - N.lag i))) ∧
    (k < N.lag i → ω k i ∈ N.init i)

/-- Hygiene: `F i` reads only the `dep i` coordinates of its snapshot. -/
def DepLocal (N : MarkNet n V) : Prop :=
  ∀ i (w w' : Fin n → V), (∀ j ∈ N.dep i, w j = w' j) → N.F i w = N.F i w'

/-- Per-component seriality (the mechanism-presentation obligation of the
premise tier: a step relation that is its own causal strategy never blocks). -/
def Serial (N : MarkNet n V) : Prop :=
  (∀ i, (N.init i).Nonempty) ∧ ∀ i w, (N.F i w).Nonempty

/-- The MarkFlow schedule walk (exact-lag row shape): one stage label per
mark; every in-edge contributes the row `t i = t j + lag i`, and no delivery
precedes its pipe's fill. Feasibility ADMITS consistent cycles (the all-ones
loop: `t x = t y`) and refuses time-travel (`z1Net`: `t x = t y ∧ t y = t x + 1`).
No well-foundedness: this is difference-constraint consistency, not an
induction device. -/
def MarkFlowFeasible (N : MarkNet n V) (t : Fin n → ℕ) : Prop :=
  (∀ i, N.lag i ≤ t i) ∧ ∀ i, ∀ j ∈ N.dep i, t i = t j + N.lag i

/-- The pin rows: a producer-supplied delivered value per mark — mark
membership, plus pointed delivery (the pin is admitted through every snapshot
whose read coordinates sit at the neighbouring pins). The value-level
column of the schedule walk. -/
def PinnedDelivery (N : MarkNet n V) (mark : Fin n → Set V) (a : Fin n → V) : Prop :=
  ∀ i, a i ∈ mark i ∧ ∀ w : Fin n → V, (∀ j ∈ N.dep i, w j = a j) → a i ∈ N.F i w

/-- Unpinned joint instant closure: for any values of the pipelined
components, the instantaneous subsystem can close jointly. (Used to state the
pin-free rule shape that `z5Net` refutes; the assembly itself needs the
schedule-relative form below.) -/
def W0Serial (N : MarkNet n V) : Prop :=
  ∀ base : Fin n → V, ∃ cur : Fin n → V,
    (∀ i, N.lag i = 0 → cur i ∈ N.F i cur) ∧
    (∀ i, N.lag i ≠ 0 → cur i = base i)

/-- Schedule-relative joint instant closure (the W0-species tier discharge
this construction consumes): at every stage, with the schedule's pinned
instantaneous coordinates held at their pins and the pipelined coordinates
held at any given values, the remaining instantaneous coordinates close
jointly. The pinned coordinates' own admission is NOT this Prop's business —
it discharges through the pointed rows. -/
def InstantClosure (N : MarkNet n V) (a : Fin n → V) (t : Fin n → ℕ) : Prop :=
  ∀ (k : ℕ) (base : Fin n → V), ∃ cur : Fin n → V,
    (∀ i, N.lag i = 0 → t i = k → cur i = a i) ∧
    (∀ i, N.lag i = 0 → t i ≠ k → cur i ∈ N.F i cur) ∧
    (∀ i, N.lag i ≠ 0 → cur i = base i)

/-- The rule's premise judgment at this tier: conditional delivery, the
∀-conforming-∃-delivering reading — every input snapshot conforming to the
in-neighbours' marks admits some own-mark output through it. -/
def ConditionalDelivery (N : MarkNet n V) (mark : Fin n → Set V) (i : Fin n) : Prop :=
  ∀ w : Fin n → V, (∀ j ∈ N.dep i, w j ∈ mark j) → ∃ v ∈ N.F i w, v ∈ mark i

/-! ## The assembly engine (Theorem A of the preregistration) -/

section Assembly

variable [Nonempty V] {N : MarkNet n V} {mark : Fin n → Set V}
  {a : Fin n → V} {t : Fin n → ℕ}

/-- Stage-`k` values of the pipelined (`lag ≠ 0`) coordinates, given the
earlier stages: initial choice before the pipe fills, the pin at the mark's
label, otherwise any admitted output. (The `lag = 0` branch is a placeholder;
instantaneous coordinates are closed jointly, in `build`.) -/
noncomputable def laggedBody (hser : Serial N) (a : Fin n → V) (t : Fin n → ℕ)
    (k : ℕ) (prev : ∀ m, m < k → Fin n → V) (i : Fin n) : V :=
  if h0 : N.lag i = 0 then Classical.arbitrary V
  else if hk : k < N.lag i then (hser.1 i).some
  else if k = t i then a i
  else (hser.2 i (prev (k - N.lag i)
    (Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero h0) (Nat.le_of_not_lt hk))
      (Nat.pos_of_ne_zero h0)))).some

/-- The constructed joint behaviour: pipelined coordinates via `laggedBody`,
instantaneous coordinates closed jointly via `InstantClosure` at each stage. -/
noncomputable def build (hser : Serial N) (hclose : InstantClosure N a t) :
    ℕ → Fin n → V
  | k => fun i =>
      if N.lag i = 0 then
        (hclose k (laggedBody hser a t k fun m hm => build hser hclose m)).choose i
      else laggedBody hser a t k (fun m hm => build hser hclose m) i
  termination_by k => k
  decreasing_by all_goals first | exact hm | assumption | omega

/-- The stage-`k` pipelined-coordinate vector actually used by `build`. -/
noncomputable def laggedFn (hser : Serial N) (hclose : InstantClosure N a t)
    (k : ℕ) : Fin n → V :=
  laggedBody hser a t k fun m _ => build hser hclose m

theorem build_eq (hser : Serial N) (hclose : InstantClosure N a t) (k : ℕ) :
    build hser hclose k = fun i =>
      if N.lag i = 0 then (hclose k (laggedFn hser hclose k)).choose i
      else laggedFn hser hclose k i := by
  rw [build]
  rfl

theorem build_eq_apply (hser : Serial N) (hclose : InstantClosure N a t)
    (k : ℕ) (i : Fin n) :
    build hser hclose k i =
      if N.lag i = 0 then (hclose k (laggedFn hser hclose k)).choose i
      else laggedFn hser hclose k i :=
  congrFun (build_eq hser hclose k) i

variable {hser : Serial N} {hclose : InstantClosure N a t}

theorem laggedFn_marked (hfeas : MarkFlowFeasible N t) {k : ℕ} {i : Fin n}
    (h0 : N.lag i ≠ 0) (hk : k = t i) :
    laggedFn hser hclose k i = a i := by
  have hnl : ¬ k < N.lag i := by have := hfeas.1 i; omega
  unfold laggedFn laggedBody
  rw [dif_neg h0, dif_neg hnl, if_pos hk]

/-- The pin invariant: at its label, every coordinate carries its pin. -/
theorem build_pin (hfeas : MarkFlowFeasible N t) :
    ∀ k i, t i = k → build hser hclose k i = a i := by
  intro k i hti
  rw [build_eq_apply]
  by_cases h0 : N.lag i = 0
  · rw [if_pos h0]
    exact (hclose k (laggedFn hser hclose k)).choose_spec.1 i h0 hti
  · rw [if_neg h0]
    exact laggedFn_marked hfeas h0 hti.symm

/-- The stage vector IS the closure witness (the pipelined coordinates agree
by the closure's base clause). -/
theorem build_stage_eq_choose (k : ℕ) :
    build hser hclose k = (hclose k (laggedFn hser hclose k)).choose := by
  funext i
  rw [build_eq_apply]
  by_cases h0 : N.lag i = 0
  · rw [if_pos h0]
  · rw [if_neg h0]
    exact ((hclose k (laggedFn hser hclose k)).choose_spec.2.2 i h0).symm

/-- The constructed behaviour is a joint run. Pinned constraints discharge
through the pointed rows: the walk's rows put every in-neighbour of a marked
coordinate at its own label exactly one lag earlier, where the pin invariant
holds. -/
theorem build_run (hfeas : MarkFlowFeasible N t) (hpin : PinnedDelivery N mark a) :
    JointRun N (build hser hclose) := by
  intro k i
  constructor
  · intro hlag
    by_cases h0 : N.lag i = 0
    · -- instantaneous: the constraint reads the current stage
      rw [h0, Nat.sub_zero]
      by_cases hti : t i = k
      · -- pinned: pointed row; every in-neighbour shares the label, hence the pin
        rw [build_pin hfeas k i hti]
        refine (hpin i).2 _ fun j hj => ?_
        have hrow := hfeas.2 i j hj
        exact build_pin hfeas k j (by omega)
      · -- unpinned: the closure's own admission clause
        rw [build_stage_eq_choose]
        exact (hclose k (laggedFn hser hclose k)).choose_spec.2.1 i h0 hti
    · -- pipelined
      by_cases hti : k = t i
      · -- marked delivery: pointed row at the lagged snapshot, whose dep
        -- coordinates sit at their own labels (walk row), hence at their pins
        rw [build_pin hfeas k i hti.symm]
        refine (hpin i).2 _ fun j hj => ?_
        have hrow := hfeas.2 i j hj
        exact build_pin hfeas (k - N.lag i) j (by omega)
      · -- unmarked: any admitted output
        have hnl : ¬ k < N.lag i := not_lt.2 hlag
        rw [build_eq_apply, if_neg h0]
        unfold laggedFn laggedBody
        rw [dif_neg h0, dif_neg hnl, if_neg hti]
        exact Set.Nonempty.some_mem _
  · intro hklag
    have h0 : N.lag i ≠ 0 := by omega
    rw [build_eq_apply, if_neg h0]
    unfold laggedFn laggedBody
    rw [dif_neg h0, dif_pos hklag]
    exact Set.Nonempty.some_mem _

/-- **The assembly engine** (the soundness metatheorem's discrete-relational
instance, pinned form): pin rows + schedule walk + seriality + schedule-relative
instant closure produce a joint run realizing every mark at its label. The
joint behaviour exists only under this conclusion's binder. -/
theorem marks_of_pinned_delivery (hser : Serial N) (hfeas : MarkFlowFeasible N t)
    (hpin : PinnedDelivery N mark a) (hclose : InstantClosure N a t) :
    ∃ ω : ℕ → Fin n → V, JointRun N ω ∧ ∀ i, ω (t i) i ∈ mark i :=
  ⟨build hser hclose, build_run hfeas hpin, fun i => by
    rw [build_pin hfeas (t i) i rfl]; exact (hpin i).1⟩

end Assembly

/-! ## The chaining bridge (Theorem B): the premise-shaped rule is sound where
no instant cycle bites -/

section Chaining

variable [Nonempty V] {N : MarkNet n V} {mark : Fin n → Set V} {t : Fin n → ℕ}

/-- **Chaining**: on an acyclic network (any topological order of the
dependency graph), the ∀∃ conditional-delivery premises alone produce a pin —
each component's delivered value is chosen against its in-neighbours' already-
chosen deliveries, in topological order. This is why the premise-shaped rule
needs no value column on the wire in the acyclic case: the pin is derivable,
producer-side, from the premises it already cites. -/
theorem pins_of_conditional_delivery (hloc : DepLocal N) (ord : Fin n → ℕ)
    (hord : ∀ i, ∀ j ∈ N.dep i, ord j < ord i)
    (hdel : ∀ i, ConditionalDelivery N mark i) :
    ∃ a : Fin n → V, PinnedDelivery N mark a := by
  suffices h : ∀ m, ∃ a : Fin n → V, ∀ i, ord i < m →
      a i ∈ mark i ∧ ∀ w : Fin n → V, (∀ j ∈ N.dep i, w j = a j) → a i ∈ N.F i w by
    obtain ⟨a, ha⟩ := h (Finset.univ.sup ord + 1)
    exact ⟨a, fun i =>
      ha i (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i)))⟩
  intro m
  induction m with
  | zero =>
    exact ⟨fun _ => Classical.arbitrary V, fun i h => absurd h (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨b, hb⟩ := ih
    have hchoice : ∀ i, ord i = m →
        ∃ v, v ∈ N.F i (fun j => if j ∈ N.dep i then b j else Classical.arbitrary V) ∧
          v ∈ mark i := by
      intro i him
      refine hdel i _ fun j hj => ?_
      simp only [if_pos hj]
      exact (hb j (him ▸ hord i j hj)).1
    refine ⟨fun i => if h : ord i = m then (hchoice i h).choose else b i,
      fun i hi => ?_⟩
    by_cases him : ord i = m
    · obtain ⟨hF, hm⟩ := (hchoice i him).choose_spec
      simp only [dif_pos him]
      refine ⟨hm, fun w hw => ?_⟩
      have heq : N.F i w =
          N.F i (fun j => if j ∈ N.dep i then b j else Classical.arbitrary V) := by
        refine hloc i _ _ fun j hj => ?_
        have hjm : ord j ≠ m := by have := hord i j hj; omega
        rw [hw j hj]
        simp only [dif_neg hjm, if_pos hj]
      rw [heq]
      exact hF
    · have hi' : ord i < m := by omega
      obtain ⟨hm, hrow⟩ := hb i hi'
      simp only [dif_neg him]
      refine ⟨hm, fun w hw => ?_⟩
      refine hrow w fun j hj => ?_
      have hjm : ord j ≠ m := by have h1 := hord i j hj; omega
      have hwj := hw j hj
      rwa [dif_neg hjm] at hwj

/-- Acyclicity dissolves the joint instant solve: with a topological order,
seriality alone closes every instant, pins included — coordinate by
coordinate, in order. (Holds for ANY pin vector `a`; the pinned coordinates'
own admission is the pointed rows' business, not this closure's.) -/
theorem instantClosure_of_acyclic (hser : Serial N) (hloc : DepLocal N)
    (ord : Fin n → ℕ) (hord : ∀ i, ∀ j ∈ N.dep i, ord j < ord i)
    (a : Fin n → V) (t : Fin n → ℕ) :
    InstantClosure N a t := by
  intro k base
  suffices h : ∀ m, ∃ cur : Fin n → V,
      (∀ i, N.lag i = 0 → t i = k → cur i = a i) ∧
      (∀ i, N.lag i ≠ 0 → cur i = base i) ∧
      (∀ i, ord i < m → N.lag i = 0 → t i ≠ k → cur i ∈ N.F i cur) by
    obtain ⟨cur, h1, h2, h3⟩ := h (Finset.univ.sup ord + 1)
    exact ⟨cur, h1, fun i h0 ht =>
      h3 i (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))) h0 ht, h2⟩
  intro m
  induction m with
  | zero =>
    refine ⟨fun i => if N.lag i ≠ 0 then base i
        else if t i = k then a i else Classical.arbitrary V,
      fun i h0 htk => ?_, fun i h0 => ?_,
      fun i h => absurd h (Nat.not_lt_zero _)⟩
    · show (if N.lag i ≠ 0 then base i
        else if t i = k then a i else Classical.arbitrary V) = a i
      rw [if_neg (not_not_intro h0), if_pos htk]
    · show (if N.lag i ≠ 0 then base i
        else if t i = k then a i else Classical.arbitrary V) = base i
      rw [if_pos h0]
  | succ m ih =>
    obtain ⟨cur, h1, h2, h3⟩ := ih
    refine ⟨fun i => if ord i = m ∧ N.lag i = 0 ∧ t i ≠ k then
        (hser.2 i cur).some else cur i,
      fun i h0 htk => ?_, fun i h0 => ?_, fun i hi h0 htk => ?_⟩
    · show (if ord i = m ∧ N.lag i = 0 ∧ t i ≠ k then
        (hser.2 i cur).some else cur i) = a i
      rw [if_neg fun h => h.2.2 htk]
      exact h1 i h0 htk
    · show (if ord i = m ∧ N.lag i = 0 ∧ t i ≠ k then
        (hser.2 i cur).some else cur i) = base i
      rw [if_neg fun h => h0 h.2.1]
      exact h2 i h0
    · have hF_eq : N.F i (fun j => if ord j = m ∧ N.lag j = 0 ∧ t j ≠ k then
          (hser.2 j cur).some else cur j) = N.F i cur := by
        refine hloc i _ _ fun j hj => ?_
        have hji := hord i j hj
        exact if_neg fun h => by
          have he := h.1
          omega
      by_cases him : ord i = m
      · show (if ord i = m ∧ N.lag i = 0 ∧ t i ≠ k then
            (hser.2 i cur).some else cur i) ∈
          N.F i fun j => if ord j = m ∧ N.lag j = 0 ∧ t j ≠ k then
            (hser.2 j cur).some else cur j
        rw [if_pos ⟨him, h0, htk⟩, hF_eq]
        exact Set.Nonempty.some_mem _
      · show (if ord i = m ∧ N.lag i = 0 ∧ t i ≠ k then
            (hser.2 i cur).some else cur i) ∈
          N.F i fun j => if ord j = m ∧ N.lag j = 0 ∧ t j ≠ k then
            (hser.2 j cur).some else cur j
        rw [if_neg fun h => him h.1, hF_eq]
        exact h3 i (by omega) h0 htk

/-- **The premise-shaped rule, acyclic instance**: on a network with a
topological order, the ∀∃ conditional-delivery premises + the schedule walk +
seriality conclude — no pin appears among the hypotheses (it is derived).
This is the discrete face of the design's claim that the value column is
forced only by instant cycles. -/
theorem marks_of_conditional_delivery_acyclic (hser : Serial N) (hloc : DepLocal N)
    (ord : Fin n → ℕ) (hord : ∀ i, ∀ j ∈ N.dep i, ord j < ord i)
    (hfeas : MarkFlowFeasible N t) (hdel : ∀ i, ConditionalDelivery N mark i) :
    ∃ ω : ℕ → Fin n → V, JointRun N ω ∧ ∀ i, ω (t i) i ∈ mark i := by
  obtain ⟨a, hpin⟩ := pins_of_conditional_delivery hloc ord hord hdel
  exact marks_of_pinned_delivery hser hfeas hpin
    (instantClosure_of_acyclic hser hloc ord hord a t)

end Chaining

/-! ## The countermodel battery (the zoo, machine-checked members)

Each mutant is the assembly statement with exactly one hypothesis deleted,
refuted by a two-component loop. Labels follow the design's countermodel zoo. -/

section Zoo

/-- Z1's network: a relay (`x`, instantaneous) closed against a unit delay
initialized to `false` (`y`). The guard and initialization that rescue the
safety variant are exactly what kill the marks here. -/
def z1Net : MarkNet 2 Bool where
  dep := ![{1}, {0}]
  lag := ![0, 1]
  F := ![fun w => {w 1}, fun w => {w 0}]
  init := ![{false}, {false}]

/-- both marks: "hits `true`" -/
def boolMark : Fin 2 → Set Bool := ![{true}, {true}]

/-- The all-ones loop: two instantaneous relays. Same wiring shape as `z1Net`,
no delay — the design's positive example. -/
def allOnesNet : MarkNet 2 Bool where
  dep := ![{1}, {0}]
  lag := ![0, 0]
  F := ![fun w => {w 1}, fun w => {w 0}]
  init := ![{true}, {true}]

/-- The schedule walk REFUSES the relay–delay loop: its rows demand
`t 0 = t 1 ∧ t 1 = t 0 + 1`. -/
theorem z1_walk_infeasible : ¬ ∃ t : Fin 2 → ℕ, MarkFlowFeasible z1Net t := by
  rintro ⟨t, -, hrow⟩
  have h01 : t 0 = t 1 + z1Net.lag 0 := hrow 0 1 (by decide)
  have h10 : t 1 = t 0 + z1Net.lag 1 := hrow 1 0 (by decide)
  have e0 : z1Net.lag 0 = 0 := rfl
  have e1 : z1Net.lag 1 = 1 := rfl
  omega

/-- The schedule walk ADMITS the all-ones loop at the shared label `0`. -/
theorem allOnes_walk_feasible : MarkFlowFeasible allOnesNet ![0, 0] := by
  refine ⟨fun i => ?_, fun i j hj => ?_⟩
  · fin_cases i <;> exact Nat.le_refl 0
  · fin_cases i <;> fin_cases j
    · exact absurd hj (by decide)
    · rfl
    · rfl
    · exact absurd hj (by decide)

/-- Every joint run of the relay–delay loop is all-`false` (the delay's
initialization propagates around the cycle forever). -/
theorem z1_run_false {ω : ℕ → Fin 2 → Bool} (h : JointRun z1Net ω) :
    ∀ k i, ω k i = false := by
  have key : ∀ k, ω k 1 = false ∧ ω k 0 = false := by
    intro k
    induction k with
    | zero =>
      have hy : ω 0 1 = false := (h 0 1).2 (by decide)
      have hx : ω 0 0 = ω 0 1 := (h 0 0).1 (Nat.zero_le 0)
      exact ⟨hy, hx.trans hy⟩
    | succ k ih =>
      have hy : ω (k + 1) 1 = ω k 0 :=
        (h (k + 1) 1).1 (Nat.succ_le_succ (Nat.zero_le k))
      have hx : ω (k + 1) 0 = ω (k + 1) 1 := (h (k + 1) 0).1 (Nat.zero_le _)
      have hy' : ω (k + 1) 1 = false := hy.trans ih.2
      exact ⟨hy', hx.trans hy'⟩
  intro k i
  fin_cases i
  · exact (key k).2
  · exact (key k).1

/-- **M1 (the walk deleted): the pin-rowed rule WITHOUT the schedule walk is
unsound** — the relay–delay loop satisfies seriality, the pin rows, and the
instant closure, yet realizes no mark on any run at any stage. (The
design's forcing argument for MarkFlow, machine-checked; `z1_walk_infeasible`
shows the walk indeed refuses this instance.) -/
theorem z1_refutes_walkless :
    ¬ (∀ (m : ℕ) (W : Type) (_ : Nonempty W) (N : MarkNet m W)
        (mark : Fin m → Set W) (a : Fin m → W) (t : Fin m → ℕ),
        Serial N → PinnedDelivery N mark a → InstantClosure N a t →
        ∃ ω : ℕ → Fin m → W, JointRun N ω ∧ ∀ i, ∃ k, ω k i ∈ mark i) := by
  intro hrule
  have hser : Serial z1Net := by
    constructor
    · intro i
      fin_cases i
      · exact ⟨false, rfl⟩
      · exact ⟨false, rfl⟩
    · intro i w
      fin_cases i
      · exact ⟨w 1, rfl⟩
      · exact ⟨w 0, rfl⟩
  have hpin : PinnedDelivery z1Net boolMark ![true, true] := by
    intro i
    fin_cases i
    · exact ⟨rfl, fun w hw => (hw 1 (by decide)).symm⟩
    · exact ⟨rfl, fun w hw => (hw 0 (by decide)).symm⟩
  have hclose : InstantClosure z1Net ![true, true] ![0, 0] := by
    intro k base
    by_cases hk : k = 0
    · refine ⟨![true, base 1], fun i h0 htk => ?_, fun i h0 htk => ?_,
        fun i h0 => ?_⟩
      · fin_cases i
        · rfl
        · exact absurd h0 (by decide)
      · fin_cases i
        · exact absurd hk.symm htk
        · exact absurd h0 (by decide)
      · fin_cases i
        · exact absurd rfl h0
        · rfl
    · refine ⟨![base 1, base 1], fun i h0 htk => ?_, fun i h0 htk => ?_,
        fun i h0 => ?_⟩
      · fin_cases i
        · exact absurd htk.symm hk
        · exact absurd h0 (by decide)
      · fin_cases i
        · rfl
        · exact absurd h0 (by decide)
      · fin_cases i
        · exact absurd rfl h0
        · rfl
  obtain ⟨ω, hrun, hmark⟩ :=
    hrule 2 Bool ⟨true⟩ z1Net boolMark ![true, true] ![0, 0] hser hpin hclose
  obtain ⟨k, hk⟩ := hmark 0
  have hk' : ω k 0 = true := hk
  rw [z1_run_false hrun k 0] at hk'
  exact Bool.false_ne_true hk'

/-! ### Z5 — the swap loop with a swap-closed mark (the defect-with-witness
against the premise-only rule shape) -/

/-- the pointwise swap on `{0, 1, 2}`: fixes `0`, exchanges `1 ↔ 2` -/
def swap3 : Fin 3 → Fin 3 := ![0, 2, 1]

/-- Z5's network: a swap gate against a relay, both instantaneous. -/
def z5Net : MarkNet 2 (Fin 3) where
  dep := ![{1}, {0}]
  lag := ![0, 0]
  F := ![fun w => {swap3 (w 1)}, fun w => {w 0}]
  init := ![{0}, {0}]

/-- both marks: "hits a nonzero value" — a mark set CLOSED under the swap,
which is what defeats the ∀∃ premise's refusal. -/
def z5Mark : Fin 2 → Set (Fin 3) := ![{v | v ≠ 0}, {v | v ≠ 0}]

/-- Every joint run of the swap loop is all-`0`: around the cycle the loop
equation forces a fixpoint of the swap, and the only fixpoint is `0` —
outside the marks. -/
theorem z5_run_zero {ω : ℕ → Fin 2 → Fin 3} (h : JointRun z5Net ω) :
    ∀ k i, ω k i = 0 := by
  intro k i
  have hx : ω k 0 = swap3 (ω k 1) := (h k 0).1 (Nat.zero_le k)
  have hy : ω k 1 = ω k 0 := (h k 1).1 (Nat.zero_le k)
  rw [hy] at hx
  have hz : ω k 0 = 0 := (by decide : ∀ v : Fin 3, v = swap3 v → v = 0) _ hx
  fin_cases i
  · exact hz
  · exact hy.trans hz

/-- **M2 (the pins deleted): the premise-shaped rule without a value column is
unsound** — conditional delivery (∀∃) at every component, dep-locality,
a feasible schedule, unpinned joint instant closure, AND a nonempty composite
all hold for the swap loop with swap-closed marks, yet no joint run realizes
any mark: each component maps the mark set into the mark set (the premises
are true), but the loop's instant fixpoint lands outside it. The one
composite-level ingredient the stage arithmetic cannot see is the VALUE
consistency — the pin rows. -/
theorem z5_refutes_pinless :
    ¬ (∀ (m : ℕ) (W : Type) (_ : Nonempty W) (N : MarkNet m W)
        (mark : Fin m → Set W) (t : Fin m → ℕ),
        Serial N → DepLocal N → (∀ i, ConditionalDelivery N mark i) →
        MarkFlowFeasible N t → W0Serial N → (∃ ω, JointRun N ω) →
        ∃ ω : ℕ → Fin m → W, JointRun N ω ∧ ∀ i, ∃ k, ω k i ∈ mark i) := by
  intro hrule
  have hser : Serial z5Net := by
    constructor
    · intro i
      fin_cases i
      · exact ⟨0, rfl⟩
      · exact ⟨0, rfl⟩
    · intro i w
      fin_cases i
      · exact ⟨swap3 (w 1), rfl⟩
      · exact ⟨w 0, rfl⟩
  have hloc : DepLocal z5Net := by
    intro i w w' hw
    fin_cases i
    · have h1 : w 1 = w' 1 := hw 1 (by decide)
      show ({swap3 (w 1)} : Set (Fin 3)) = {swap3 (w' 1)}
      rw [h1]
    · have h0 : w 0 = w' 0 := hw 0 (by decide)
      show ({w 0} : Set (Fin 3)) = {w' 0}
      rw [h0]
  have hdel : ∀ i, ConditionalDelivery z5Net z5Mark i := by
    intro i w hw
    fin_cases i
    · have h1 : w 1 ≠ 0 := hw 1 (by decide)
      exact ⟨swap3 (w 1), rfl,
        (by decide : ∀ v : Fin 3, v ≠ 0 → swap3 v ≠ 0) _ h1⟩
    · have h0 : w 0 ≠ 0 := hw 0 (by decide)
      exact ⟨w 0, rfl, h0⟩
  have hfeas : MarkFlowFeasible z5Net ![0, 0] := by
    refine ⟨fun i => ?_, fun i j hj => ?_⟩
    · fin_cases i <;> exact Nat.le_refl 0
    · fin_cases i <;> fin_cases j
      · exact absurd hj (by decide)
      · rfl
      · rfl
      · exact absurd hj (by decide)
  have hw0 : W0Serial z5Net := by
    intro base
    refine ⟨![0, 0], fun i h0 => ?_, fun i h0 => ?_⟩
    · fin_cases i
      · rfl
      · rfl
    · fin_cases i
      · exact absurd rfl h0
      · exact absurd rfl h0
  have hprop : ∃ ω, JointRun z5Net ω := by
    refine ⟨fun _ => ![0, 0], fun k i => ?_⟩
    fin_cases i
    · exact ⟨fun _ => rfl, fun hlt => absurd hlt (Nat.not_lt_zero k)⟩
    · exact ⟨fun _ => rfl, fun hlt => absurd hlt (Nat.not_lt_zero k)⟩
  obtain ⟨ω, hrun, hmark⟩ :=
    hrule 2 (Fin 3) ⟨0⟩ z5Net z5Mark ![0, 0] hser hloc hdel hfeas hw0 hprop
  obtain ⟨k, hk⟩ := hmark 0
  exact hk (z5_run_zero hrun k 0)

/-- **The repair refuses Z5**: no pin exists — the pin rows demand a value
assignment with `a 0 = swap3 (a 1)` and `a 1 = a 0` inside the marks, and the
swap has no fixpoint there. (With `z5_refutes_pinless`: the pin rows are
exactly the ingredient that separates the swap loop from the all-ones loop,
which `allOnes_marks_realized` below certifies through the same engine.) -/
theorem z5_no_pin : ¬ ∃ a : Fin 2 → Fin 3, PinnedDelivery z5Net z5Mark a := by
  rintro ⟨a, ha⟩
  have hmem : a 0 ≠ 0 := (ha 0).1
  have hrow0 : a 0 = swap3 (a 1) := (ha 0).2 a fun j _ => rfl
  have hrow1 : a 1 = a 0 := (ha 1).2 a fun j _ => rfl
  rw [hrow1] at hrow0
  exact (by decide : ∀ v : Fin 3, v ≠ 0 → ¬ v = swap3 v) _ hmem hrow0

/-! ### The positive control: the all-ones loop through the engine -/

/-- **Positive control**: the assembly engine's full hypothesis kit is
satisfiable on the all-ones relay loop and concludes — both marks realized at
the shared label `0` (the design's Role-2 example, end-to-end: self-support
productive under the ∃-face). -/
theorem allOnes_marks_realized :
    ∃ ω : ℕ → Fin 2 → Bool, JointRun allOnesNet ω ∧
      ∀ i, ω ((![0, 0] : Fin 2 → ℕ) i) i ∈ boolMark i := by
  have hser : Serial allOnesNet := by
    constructor
    · intro i
      fin_cases i
      · exact ⟨true, rfl⟩
      · exact ⟨true, rfl⟩
    · intro i w
      fin_cases i
      · exact ⟨w 1, rfl⟩
      · exact ⟨w 0, rfl⟩
  have hpin : PinnedDelivery allOnesNet boolMark ![true, true] := by
    intro i
    fin_cases i
    · exact ⟨rfl, fun w hw => (hw 1 (by decide)).symm⟩
    · exact ⟨rfl, fun w hw => (hw 0 (by decide)).symm⟩
  have hclose : InstantClosure allOnesNet ![true, true] ![0, 0] := by
    intro k base
    refine ⟨![true, true], fun i h0 htk => ?_, fun i h0 htk => ?_,
      fun i h0 => ?_⟩
    · fin_cases i
      · rfl
      · rfl
    · fin_cases i
      · rfl
      · rfl
    · fin_cases i
      · exact absurd rfl h0
      · exact absurd rfl h0
  exact marks_of_pinned_delivery hser allOnes_walk_feasible hpin hclose

/-- The direct witness, independently of the engine: the all-ones behaviour. -/
theorem allOnes_direct : JointRun allOnesNet fun _ => ![true, true] := by
  intro k i
  fin_cases i
  · exact ⟨fun _ => rfl, fun hlt => absurd hlt (Nat.not_lt_zero k)⟩
  · exact ⟨fun _ => rfl, fun hlt => absurd hlt (Nat.not_lt_zero k)⟩

end Zoo

end BernsteinLogic.QtslCompose.Marks

/-! ## Axiom receipts -/

#print axioms BernsteinLogic.QtslCompose.Marks.marks_of_pinned_delivery
#print axioms BernsteinLogic.QtslCompose.Marks.pins_of_conditional_delivery
#print axioms BernsteinLogic.QtslCompose.Marks.instantClosure_of_acyclic
#print axioms BernsteinLogic.QtslCompose.Marks.marks_of_conditional_delivery_acyclic
#print axioms BernsteinLogic.QtslCompose.Marks.z1_walk_infeasible
#print axioms BernsteinLogic.QtslCompose.Marks.allOnes_walk_feasible
#print axioms BernsteinLogic.QtslCompose.Marks.z1_refutes_walkless
#print axioms BernsteinLogic.QtslCompose.Marks.z5_refutes_pinless
#print axioms BernsteinLogic.QtslCompose.Marks.z5_no_pin
#print axioms BernsteinLogic.QtslCompose.Marks.allOnes_marks_realized
