import QtslAux.QtslCompose.AGComposeMarks

/-! # QWireComposeMarks — tier adjudication: the walk fact, the M3 fork, the mixed engine

**Source spec**: the cyclic AG design (the carve round and its tier table);
statements preregistered — committed before these proofs, including the
pre-analysis this module resolves.

Three items, each a machine-checked adjudication of the r4 residue:

1. **The walk fact** (`walk_cycle_lag_zero`, `walk_cycle_instant`): the
   exact-lag rows compose along dependency chains, so around any dependency
   cycle the accumulated lag is zero — every walk-admitted cycle is
   INSTANTANEOUS and label-constant. (Used silently by the r4 engine; the r5
   findings asked for it crisp; here it is kernel-checked.) Downstream of
   this fact, stated once in this header and priced honestly: a
   walk-feasible exact-lag net carries NO recurrent memory — any lagged
   feedback makes the whole schedule infeasible — so the design zoo's Z6
   (blocking-after-delivery) is UNENCODABLE at this tier, joining Z3/Z4 in
   the relational module's model-honesty note. Z6's formalization home is the
   history-dependent tier of the design; its design-level lesson (the
   W0-species discharge is stepwise, not bare nonemptiness) is untouched.

2. **The M3 fork, resolved as derivability** (`instantClosure_of_w0Serial`):
   the r4 preregistration expected M3 (`InstantClosure` weakened to the unpinned
   `W0Serial`) to be refutable. At this tier it is NOT: under `DepLocal` and
   the walk, an unheld instant coordinate never reads a held one (instant
   dep edges force label equality), so the closure witness is the W0 witness
   with the held coordinates overridden to their pins. Consequence, stated
   as the finding it is: at the exact-lag memoryless tier the engine's
   schedule-relative closure hypothesis is DERIVABLE from the unpinned one
   (`marks_of_pinned_delivery_w0` is the citable engine form), and Z7's
   solvability-flip — the necessity witness for schedule-relativity — lives
   strictly ABOVE this tier (general difference-constraint walks with
   windows, where instant labels can differ along an edge — the design's
   history-dependent tier again).

3. **The mixed engine** (`PartialPins`, `pins_extend_partial`,
   `marks_of_partial_pins`): the rule's actual v1 wire shape — pins REQUIRED
   only on the zero-lag-cycle cores, ∀∃ conditional-delivery premises
   elsewhere (per the design: "the checker demands coverage of the zero-lag
   cycles and tolerates the rest") — was unproven in the earlier development, which
   machine-checked only the dial's two ends (total pins; total chaining on
   acyclic nets). Closed here: partial pins on a seed set extend to total
   pins by chaining along any order in which every non-seed coordinate's
   in-neighbours are seed-or-earlier, and the extended pins feed the existing
   assembly engine. The seed's pointed rows are the honest mixed rows: pointed
   through the seed's own pins, mark-conforming on non-seed reads.

Battery (preregistered as M-P1/M-P2): `seedRow_weakened_refuted` (a seed pointed row
that fixes its non-seed reads at specific values instead of tolerating every
mark-conforming read cannot extend) and `quotient_order_deleted_refuted`
(with the order deleted and the seed empty, the mixed rule degenerates to
exactly the pinless shape Z5 kills — same instance, at-label conclusion).

Everything here is classical event/relation algebra over the established model;
nothing is checker-facing (cf. `lean-conventions.md`).
-/

namespace BernsteinLogic.QtslCompose.Marks

open Classical

variable {n : ℕ} {V : Type*}

/-! ## 1 — the walk fact -/

/-- A dependency chain from `i` back to `k`, accumulating the lags of the
READING components along the way: `DepPath N i k ℓ` means `i` reaches `k`
through dep edges with total lag `ℓ` (each step `j ∈ N.dep i` contributes
`N.lag i`, the reader's lag — matching the walk row `t i = t j + lag i`). -/
inductive DepPath (N : MarkNet n V) : Fin n → Fin n → ℕ → Prop
  | refl (i : Fin n) : DepPath N i i 0
  | step {i j k : Fin n} {ℓ : ℕ} (hj : j ∈ N.dep i) (hp : DepPath N j k ℓ) :
      DepPath N i k (N.lag i + ℓ)

/-- Labels compose along dependency chains: the walk rows telescope. -/
theorem DepPath.label_eq {N : MarkNet n V} {t : Fin n → ℕ}
    (hfeas : MarkFlowFeasible N t) :
    ∀ {i k : Fin n} {ℓ : ℕ}, DepPath N i k ℓ → t i = t k + ℓ := by
  intro i k ℓ hp
  induction hp with
  | refl i => simp
  | step hj hp ih =>
    have hrow := hfeas.2 _ _ hj
    omega

/-- **The walk fact**: around any dependency cycle the accumulated lag is
zero — every walk-admitted cycle is instantaneous. -/
theorem walk_cycle_lag_zero {N : MarkNet n V} {t : Fin n → ℕ}
    (hfeas : MarkFlowFeasible N t) {i : Fin n} {ℓ : ℕ}
    (hp : DepPath N i i ℓ) : ℓ = 0 := by
  have := hp.label_eq hfeas
  omega

/-- The edge form: a dep edge that closes into a cycle is instantaneous and
label-constant. -/
theorem walk_cycle_instant {N : MarkNet n V} {t : Fin n → ℕ}
    (hfeas : MarkFlowFeasible N t) {i j : Fin n} {ℓ : ℕ}
    (hj : j ∈ N.dep i) (hback : DepPath N j i ℓ) :
    N.lag i = 0 ∧ t i = t j := by
  have h0 := walk_cycle_lag_zero hfeas (DepPath.step hj hback)
  have hlag : N.lag i = 0 := by omega
  have hrow := hfeas.2 i j hj
  exact ⟨hlag, by omega⟩

/-! ## 2 — the M3 fork, resolved as derivability -/

/-- **The M3 resolution (derivability, not refutation)**: at the exact-lag
tier, the schedule-relative instant closure follows from the UNPINNED joint
closure, for every pin vector — take the W0 witness and override the held
coordinates to their pins; no unheld instant coordinate reads a held one,
because an instant dep edge forces label equality (`t i = t j + 0`), so the
override is invisible to every admission clause that still has to hold. -/
theorem instantClosure_of_w0Serial {N : MarkNet n V} {t : Fin n → ℕ}
    (hloc : DepLocal N) (hfeas : MarkFlowFeasible N t) (hw0 : W0Serial N)
    (a : Fin n → V) : InstantClosure N a t := by
  intro k base
  obtain ⟨cur₀, hadm, hbase⟩ := hw0 base
  refine ⟨fun i => if N.lag i = 0 ∧ t i = k then a i else cur₀ i,
    fun i h0 htk => ?_, fun i h0 htk => ?_, fun i h0 => ?_⟩
  · exact if_pos ⟨h0, htk⟩
  · show (if N.lag i = 0 ∧ t i = k then a i else cur₀ i)
      ∈ N.F i (fun j => if N.lag j = 0 ∧ t j = k then a j else cur₀ j)
    rw [if_neg (fun h : N.lag i = 0 ∧ t i = k => htk h.2)]
    have hF : N.F i (fun j => if N.lag j = 0 ∧ t j = k then a j else cur₀ j)
        = N.F i cur₀ := by
      refine hloc i _ _ fun j hj => ?_
      refine if_neg fun hcon : N.lag j = 0 ∧ t j = k => ?_
      have hrow := hfeas.2 i j hj
      have h2 := hcon.2
      omega
    rw [hF]
    exact hadm i h0
  · show (if N.lag i = 0 ∧ t i = k then a i else cur₀ i) = base i
    rw [if_neg (fun h : N.lag i = 0 ∧ t i = k => h0 h.1)]
    exact hbase i h0

/-- The engine at the derived closure: at this tier, `W0Serial` (+ dep
locality) suffices wherever the assembly engine asked for the
schedule-relative closure — the citable mixed-hypothesis form. -/
theorem marks_of_pinned_delivery_w0 [Nonempty V] {N : MarkNet n V}
    {mark : Fin n → Set V} {a : Fin n → V} {t : Fin n → ℕ}
    (hser : Serial N) (hloc : DepLocal N) (hfeas : MarkFlowFeasible N t)
    (hpin : PinnedDelivery N mark a) (hw0 : W0Serial N) :
    ∃ ω : ℕ → Fin n → V, JointRun N ω ∧ ∀ i, ω (t i) i ∈ mark i :=
  marks_of_pinned_delivery hser hfeas hpin
    (instantClosure_of_w0Serial hloc hfeas hw0 a)

/-! ## 3 — the mixed engine (partial pins + chaining) -/

/-- Partial pin rows on a seed set `S` (the zero-lag-cycle cores, in the
rule's use): mark membership, plus pointed delivery through every snapshot
that carries the seed's own pins on seed reads and ANY mark-conforming
values on non-seed reads. The tolerance clause is load-bearing: the
extension chooses the non-seed pins, and the seed must deliver through
whatever mark-members it chooses (`seedRow_weakened_refuted`). -/
def PartialPins (N : MarkNet n V) (mark : Fin n → Set V) (S : Finset (Fin n))
    (a₀ : Fin n → V) : Prop :=
  ∀ i ∈ S, a₀ i ∈ mark i ∧ ∀ w : Fin n → V,
    (∀ j ∈ N.dep i, j ∈ S → w j = a₀ j) →
    (∀ j ∈ N.dep i, j ∉ S → w j ∈ mark j) → a₀ i ∈ N.F i w

/-- **The mixed extension**: partial pins on a seed set + ∀∃ conditional
delivery off the seed + an order in which every non-seed coordinate's
in-neighbours are seed-or-earlier produce TOTAL pin rows agreeing with the
seed. This is why the wire's value column covers only the zero-lag cycles:
everywhere else the pin is producer-derivable from the premises the
certificate already cites. -/
theorem pins_extend_partial [Nonempty V] {N : MarkNet n V}
    {mark : Fin n → Set V} (hloc : DepLocal N) {S : Finset (Fin n)}
    {a₀ : Fin n → V} (hseed : PartialPins N mark S a₀) (ord : Fin n → ℕ)
    (hord : ∀ i ∉ S, ∀ j ∈ N.dep i, j ∈ S ∨ ord j < ord i)
    (hdel : ∀ i ∉ S, ConditionalDelivery N mark i) :
    ∃ a : Fin n → V, PinnedDelivery N mark a ∧ ∀ i ∈ S, a i = a₀ i := by
  -- chain the non-seed pins by ord-induction, seed pins fixed throughout
  suffices h : ∀ m, ∃ a : Fin n → V, (∀ i ∈ S, a i = a₀ i) ∧
      ∀ i ∉ S, ord i < m →
        a i ∈ mark i ∧ ∀ w : Fin n → V,
          (∀ j ∈ N.dep i, w j = a j) → a i ∈ N.F i w by
    obtain ⟨a, haS, ha⟩ := h (Finset.univ.sup ord + 1)
    refine ⟨a, fun i => ?_, haS⟩
    by_cases hiS : i ∈ S
    · -- seed coordinate: its own mixed row, fed the completed extension
      obtain ⟨hm, hrow⟩ := hseed i hiS
      have hai : a i = a₀ i := haS i hiS
      refine ⟨by rw [hai]; exact hm, fun w hw => ?_⟩
      have hF := hrow w
        (fun j hj hjS => by rw [hw j hj]; exact haS j hjS)
        (fun j hj hjS => by
          rw [hw j hj]
          exact (ha j hjS
            (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ j)))).1)
      rw [hai]
      exact hF
    · -- chained coordinate: the constructed row
      exact ha i hiS (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i)))
  intro m
  induction m with
  | zero =>
    exact ⟨fun i => if i ∈ S then a₀ i else Classical.arbitrary V,
      fun i hi => if_pos hi, fun i _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨b, hbS, hb⟩ := ih
    -- choose deliveries for the level-m non-seed coordinates
    have hchoice : ∀ i, i ∉ S → ord i = m →
        ∃ v, v ∈ N.F i (fun j => if j ∈ N.dep i then b j else
          Classical.arbitrary V) ∧ v ∈ mark i := by
      intro i hiS him
      refine hdel i hiS _ fun j hj => ?_
      simp only [if_pos hj]
      by_cases hjS : j ∈ S
      · rw [hbS j hjS]
        exact (hseed j hjS).1
      · rcases hord i hiS j hj with h | hjlt
        · exact absurd h hjS
        · exact (hb j hjS (by omega)).1
    refine ⟨fun i => if h : i ∉ S ∧ ord i = m
        then (hchoice i h.1 h.2).choose else b i,
      fun i hi => ?_, fun i hiS him => ?_⟩
    · show (if h : i ∉ S ∧ ord i = m
          then (hchoice i h.1 h.2).choose else b i) = a₀ i
      rw [dif_neg (fun h : i ∉ S ∧ ord i = m => h.1 hi)]
      exact hbS i hi
    · by_cases him' : ord i = m
      · -- the freshly chosen level
        obtain ⟨hF, hm⟩ := (hchoice i hiS him').choose_spec
        constructor
        · show (if h : i ∉ S ∧ ord i = m
              then (hchoice i h.1 h.2).choose else b i) ∈ mark i
          rw [dif_pos ⟨hiS, him'⟩]
          exact hm
        · intro w hw
          show (if h : i ∉ S ∧ ord i = m
              then (hchoice i h.1 h.2).choose else b i) ∈ N.F i w
          rw [dif_pos ⟨hiS, him'⟩]
          have heq : N.F i w = N.F i (fun j => if j ∈ N.dep i then b j else
              Classical.arbitrary V) := by
            refine hloc i _ _ fun j hj => ?_
            rw [hw j hj]
            show (if h : j ∉ S ∧ ord j = m
                then (hchoice j h.1 h.2).choose else b j)
              = (fun j => if j ∈ N.dep i then b j else Classical.arbitrary V) j
            simp only [if_pos hj]
            by_cases hjS : j ∈ S
            · rw [dif_neg (fun h : j ∉ S ∧ ord j = m => h.1 hjS)]
            · rcases hord i hiS j hj with h | hjlt
              · exact absurd h hjS
              · refine dif_neg fun h : j ∉ S ∧ ord j = m => ?_
                have h2 := h.2
                omega
          rw [heq]
          exact hF
      · -- an earlier level: inherited, reads unchanged
        have hi' : ord i < m := by omega
        obtain ⟨hm, hrow⟩ := hb i hiS hi'
        constructor
        · show (if h : i ∉ S ∧ ord i = m
              then (hchoice i h.1 h.2).choose else b i) ∈ mark i
          rw [dif_neg (fun h : i ∉ S ∧ ord i = m => him' h.2)]
          exact hm
        · intro w hw
          show (if h : i ∉ S ∧ ord i = m
              then (hchoice i h.1 h.2).choose else b i) ∈ N.F i w
          rw [dif_neg (fun h : i ∉ S ∧ ord i = m => him' h.2)]
          refine hrow w fun j hj => ?_
          rw [hw j hj]
          show (if h : j ∉ S ∧ ord j = m
              then (hchoice j h.1 h.2).choose else b j) = b j
          by_cases hjS : j ∈ S
          · rw [dif_neg (fun h : j ∉ S ∧ ord j = m => h.1 hjS)]
          · rcases hord i hiS j hj with h | hjlt
            · exact absurd h hjS
            · refine dif_neg fun h : j ∉ S ∧ ord j = m => ?_
              have h2 := h.2
              omega

/-- **The mixed engine, end-to-end** (the rule's actual v1 wire shape,
machine-checked): pins on the seed + ∀∃ premises off it + the quotient order
+ the unpinned joint closure conclude — every mark realized at its label.
(Composition of `pins_extend_partial`, `instantClosure_of_w0Serial`, and the
assembly engine.) -/
theorem marks_of_partial_pins [Nonempty V] {N : MarkNet n V}
    {mark : Fin n → Set V} {S : Finset (Fin n)} {a₀ : Fin n → V}
    {t : Fin n → ℕ}
    (hser : Serial N) (hloc : DepLocal N) (hfeas : MarkFlowFeasible N t)
    (hseed : PartialPins N mark S a₀) (ord : Fin n → ℕ)
    (hord : ∀ i ∉ S, ∀ j ∈ N.dep i, j ∈ S ∨ ord j < ord i)
    (hdel : ∀ i ∉ S, ConditionalDelivery N mark i) (hw0 : W0Serial N) :
    ∃ ω : ℕ → Fin n → V, JointRun N ω ∧ ∀ i, ω (t i) i ∈ mark i := by
  obtain ⟨a, hpin, -⟩ := pins_extend_partial hloc hseed ord hord hdel
  exact marks_of_pinned_delivery_w0 hser hloc hfeas hpin hw0

/-! ## The battery (preregistered as M-P1/M-P2) -/

/-- The weakened seed row of M-P1: pointed delivery demanded only at
snapshots carrying the seed's OWN values everywhere (`w j = c j` on all
deps, for one fixed completion `c` of the seed) — the tolerance clause for
mark-conforming non-seed reads deleted. -/
def PartialPinsWeak (N : MarkNet n V) (mark : Fin n → Set V)
    (S : Finset (Fin n)) (c : Fin n → V) : Prop :=
  ∀ i ∈ S, c i ∈ mark i ∧ ∀ w : Fin n → V,
    (∀ j ∈ N.dep i, w j = c j) → c i ∈ N.F i w

/-- **M-P1 (the tolerance clause deleted): the mixed extension is UNSOUND
with seed rows pointed only at one fixed completion** — a seed component
admitting its pin only through one specific non-seed read, while the chained
component must (and can only) deliver a DIFFERENT mark value. Witness over
`Fin 3`: seed `{0}` reading `1 ∉ S`; `F 0 w = {2}` iff `w 1 = 0`, else `∅`;
`mark 0 = {2}`, `mark 1 = {1}`; component 1 delivers only `1`. The weak seed
row holds at the completion `c = ![2, 0]`, conditional delivery holds off the
seed, the quotient order holds — and no total pin vector exists at all. -/
theorem seedRow_weakened_refuted :
    ¬ (∀ (m : ℕ) (W : Type) (_ : Nonempty W) (N : MarkNet m W)
        (mark : Fin m → Set W) (S : Finset (Fin m)) (c : Fin m → W),
        DepLocal N → PartialPinsWeak N mark S c → (ord : Fin m → ℕ) →
        (∀ i ∉ S, ∀ j ∈ N.dep i, j ∈ S ∨ ord j < ord i) →
        (∀ i ∉ S, ConditionalDelivery N mark i) →
        ∃ a : Fin m → W, PinnedDelivery N mark a ∧ ∀ i ∈ S, a i = c i) := by
  intro hrule
  -- the witness net: 0 reads 1 (both instantaneous is irrelevant here —
  -- the extension layer never consults lags)
  set N : MarkNet 2 (Fin 3) :=
    { dep := ![{1}, ∅]
      lag := ![0, 0]
      F := ![fun w => if w 1 = 0 then {2} else ∅, fun _ => {1}]
      init := ![Set.univ, Set.univ] } with hN
  have hloc : DepLocal N := by
    intro i w w' hw
    fin_cases i
    · have h1 : w 1 = w' 1 := hw 1 (by decide)
      show (if w 1 = 0 then {2} else ∅ : Set (Fin 3))
        = (if w' 1 = 0 then {2} else ∅)
      rw [h1]
    · rfl
  have hweak : PartialPinsWeak N ![({2} : Set (Fin 3)), {1}] {0} ![2, 0] := by
    intro i hi
    have hi0 : i = 0 := by
      have := Finset.mem_singleton.1 hi
      exact this
    subst hi0
    refine ⟨rfl, fun w hw => ?_⟩
    have h1 : w 1 = 0 := hw 1 (by decide)
    show (2 : Fin 3) ∈ (if w 1 = 0 then {2} else ∅ : Set (Fin 3))
    rw [if_pos h1]
    rfl
  have hdel : ∀ i ∉ ({0} : Finset (Fin 2)),
      ConditionalDelivery N ![({2} : Set (Fin 3)), {1}] i := by
    intro i hi
    have hi1 : i = 1 := by
      fin_cases i
      · exact absurd (Finset.mem_singleton_self 0) hi
      · rfl
    subst hi1
    intro w _
    exact ⟨1, rfl, rfl⟩
  obtain ⟨a, hpin, haS⟩ := hrule 2 (Fin 3) ⟨0⟩ N
    ![({2} : Set (Fin 3)), {1}] {0} ![2, 0] hloc hweak
    (fun i => if i ∈ ({0} : Finset (Fin 2)) then 1 else 0)
    (by
      intro i hi j hj
      fin_cases i
      · exact absurd (Finset.mem_singleton_self 0) hi
      · exact absurd hj (Finset.notMem_empty j))
    hdel
  -- the total pins demand: a 1 ∈ mark 1 = {1}, and a 0 ∈ F 0 (w 1 = a 1 = 1) = ∅
  have ha1 : a 1 = 1 := (hpin 1).1
  have hrow0 := (hpin 0).2 a (fun j _ => rfl)
  have : a 0 ∈ (if a 1 = 0 then {2} else ∅ : Set (Fin 3)) := hrow0
  rw [ha1] at this
  simp at this

/-- **M-P2 (the quotient order deleted, seed empty): the mixed rule
degenerates to exactly the pinless shape Z5 kills.** With `S = ∅` the seed
rows are vacuous and the mutant's premise kit is the r3 §8.2 kit verbatim;
the swap loop with a swap-closed mark refutes it — same instance, at-label
conclusion. -/
theorem quotient_order_deleted_refuted :
    ¬ (∀ (m : ℕ) (W : Type) (_ : Nonempty W) (N : MarkNet m W)
        (mark : Fin m → Set W) (a₀ : Fin m → W) (t : Fin m → ℕ),
        Serial N → DepLocal N → MarkFlowFeasible N t →
        PartialPins N mark ∅ a₀ →
        (∀ i ∉ (∅ : Finset (Fin m)), ConditionalDelivery N mark i) →
        W0Serial N →
        ∃ ω : ℕ → Fin m → W, JointRun N ω ∧ ∀ i, ω (t i) i ∈ mark i) := by
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
  obtain ⟨ω, hrun, hmark⟩ := hrule 2 (Fin 3) ⟨0⟩ z5Net z5Mark
    (fun _ => 0) ![0, 0] hser hloc hfeas
    (fun i hi => absurd hi (Finset.notMem_empty i))
    (fun i _ => hdel i) hw0
  exact (hmark 0) (z5_run_zero hrun _ 0)

end BernsteinLogic.QtslCompose.Marks

/-! ## Axiom receipts -/

#print axioms BernsteinLogic.QtslCompose.Marks.walk_cycle_lag_zero
#print axioms BernsteinLogic.QtslCompose.Marks.walk_cycle_instant
#print axioms BernsteinLogic.QtslCompose.Marks.instantClosure_of_w0Serial
#print axioms BernsteinLogic.QtslCompose.Marks.marks_of_pinned_delivery_w0
#print axioms BernsteinLogic.QtslCompose.Marks.pins_extend_partial
#print axioms BernsteinLogic.QtslCompose.Marks.marks_of_partial_pins
#print axioms BernsteinLogic.QtslCompose.Marks.seedRow_weakened_refuted
#print axioms BernsteinLogic.QtslCompose.Marks.quotient_order_deleted_refuted
