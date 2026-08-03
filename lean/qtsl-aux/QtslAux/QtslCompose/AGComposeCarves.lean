import QtslAux.QtslCompose.AGComposeMarks

/-! # QWireComposeMarks r5 — predicate pins (carves), discrete-relational tier

**The r5 design question**: could the cyclic AG rule's value column be a
*predicate* instead of a *value*? Values are measure-zero in general, and a
predicate can follow the pattern of `STCarve`, using a hypernet (and
possibly an `HPlate` in the case of SDCPNs being the systems in cyclic
interconnection) to define it. The answer is the r5 addendum to the cyclic
AG design (statements + mutant loci preregistered — committed before these
proofs).

This module generalizes the r4 pin rows from a VALUE per mark to a CARVE
(predicate) per mark, and machine-checks the design's organizing facts. The
ten r4 declarations in `AGComposeMarks.lean` are imported, untouched.

## The soundness crux (stated in the preregistration before it was solved)

r4's point pin composes trivially across an instant cycle: the joint
assignment at the pinned instant IS the pin vector, and each pointed row
checks one component maps that point correctly. A carve pin leaves each
delivered value free within its carve, so joint existence at the instant
becomes a nonemptiness obligation over the carve product — the DIAGONAL.
Carve-invariance does not imply it (`z5_carvedDelivery_mark` below:
invariance HOLDS on the swap loop; the diagonal is what fails). The kit
therefore splits into:

- **`CarvedDelivery`** — containment (`P i ⊆ mark i`) + carved delivery
  (inputs in the neighbouring carves admit some output in the own carve).
  At `P = mark` this is literally the r3 ∀∃ premise
  (`carvedDelivery_mark_iff_conditional`); at singletons it is the r4 pin
  rows (`carvedDelivery_of_pinned`). The carve is a DIAL between the
  original design sketch's premises and the r4 repair.
- **`CarveClosure`** — the diagonal obligation, schedule-relative: at every
  stage, for every carve-conforming base, the instant subsystem closes
  jointly with labeled coordinates IN-CARVE and ADMITTED. Pinned admission
  moves INTO the closure (vs r4, where the pointed rows carried it) because
  a set-valued pin leaves the joint choice open until the diagonal closes.
  The conformance hypothesis is priced by the singleton bridge
  (`carveClosure_of_pinned`), not by a countermodel: without it, pointed
  delivery could not discharge the closure and r4 would not be subsumed.

On the wire the closure is discharged by a species-tagged certificate genus
(dgPoint / dgEnum / dgContract / dgConvex / dgMonotone — the fixpoint
arguments live per-species in the metatheorem, the Ionescu–Tulcea pattern);
here it is consumed abstractly, which is exactly the point.

Everything classical and noncomputable; nothing checker-facing.
-/

namespace BernsteinLogic.QtslCompose.Marks

open Classical

variable {n : ℕ} {V : Type*}

/-- Conformance of a base vector at stage `k`: every pipelined coordinate
labeled `k` sits inside its carve. (The closure below is only obliged on
conforming bases — the assembly only ever presents such bases, and the wire
certificates only speak about carve-conforming inputs.) -/
def CarveConf (N : MarkNet n V) (P : Fin n → Set V) (t : Fin n → ℕ)
    (k : ℕ) (base : Fin n → V) : Prop :=
  ∀ j, N.lag j ≠ 0 → t j = k → base j ∈ P j

/-- The carve rows: containment in the mark, plus carved delivery — through
every snapshot whose read coordinates sit in the neighbouring carves, some
admitted output lands in the own carve. Point pins are the singleton case;
the r3 ∀∃ premise is the `P = mark` case. -/
def CarvedDelivery (N : MarkNet n V) (mark P : Fin n → Set V) : Prop :=
  ∀ i, P i ⊆ mark i ∧
    ∀ w : Fin n → V, (∀ j ∈ N.dep i, w j ∈ P j) → (N.F i w ∩ P i).Nonempty

/-- The diagonal obligation, schedule-relative: at every stage, for every
carve-conforming base, the instantaneous subsystem closes jointly with the
labeled coordinates landing inside their carves AND admitted. -/
def CarveClosure (N : MarkNet n V) (P : Fin n → Set V) (t : Fin n → ℕ) : Prop :=
  ∀ (k : ℕ) (base : Fin n → V), CarveConf N P t k base →
    ∃ cur : Fin n → V,
      (∀ i, N.lag i = 0 → t i = k → cur i ∈ P i ∧ cur i ∈ N.F i cur) ∧
      (∀ i, N.lag i = 0 → t i ≠ k → cur i ∈ N.F i cur) ∧
      (∀ i, N.lag i ≠ 0 → cur i = base i)

/-! ## The generalized assembly engine (C1 of the preregistration) -/

section Assembly

variable [Nonempty V] {N : MarkNet n V} {mark P : Fin n → Set V} {t : Fin n → ℕ}

/-- Stage-`k` values of the pipelined coordinates: initial choice before the
pipe fills; at the mark's label, a choice from `F ∩ P` when that intersection
is nonempty (the carve-at-label invariant proves it always is), any admitted
output otherwise. -/
noncomputable def carveLaggedBody (hser : Serial N) (P : Fin n → Set V)
    (t : Fin n → ℕ) (k : ℕ) (prev : ∀ m, m < k → Fin n → V) (i : Fin n) : V :=
  if h0 : N.lag i = 0 then Classical.arbitrary V
  else if hk : k < N.lag i then (hser.1 i).some
  else if k = t i then
    (if hne : (N.F i (prev (k - N.lag i)
        (Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero h0)
          (Nat.le_of_not_lt hk)) (Nat.pos_of_ne_zero h0))) ∩ P i).Nonempty
     then hne.some
     else (hser.2 i (prev (k - N.lag i)
        (Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero h0)
          (Nat.le_of_not_lt hk)) (Nat.pos_of_ne_zero h0)))).some)
  else (hser.2 i (prev (k - N.lag i)
    (Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero h0)
      (Nat.le_of_not_lt hk)) (Nat.pos_of_ne_zero h0)))).some

/-- The constructed joint behaviour: pipelined coordinates via
`carveLaggedBody`, instantaneous coordinates closed jointly via
`CarveClosure` — defensively, under a conformance test the invariant lemma
discharges at every actual stage. -/
noncomputable def buildC (hser : Serial N) (hclose : CarveClosure N P t) :
    ℕ → Fin n → V
  | k => fun i =>
      if N.lag i = 0 then
        (if hc : CarveConf N P t k
            (carveLaggedBody hser P t k fun m hm => buildC hser hclose m) then
          (hclose k _ hc).choose i
        else Classical.arbitrary V)
      else carveLaggedBody hser P t k (fun m hm => buildC hser hclose m) i
  termination_by k => k
  decreasing_by all_goals first | exact hm | assumption | omega

/-- The stage-`k` pipelined-coordinate vector actually used by `buildC`. -/
noncomputable def carveLaggedFn (hser : Serial N) (hclose : CarveClosure N P t)
    (k : ℕ) : Fin n → V :=
  carveLaggedBody hser P t k fun m _ => buildC hser hclose m

theorem buildC_eq (hser : Serial N) (hclose : CarveClosure N P t) (k : ℕ) :
    buildC hser hclose k = fun i =>
      if N.lag i = 0 then
        (if hc : CarveConf N P t k (carveLaggedFn hser hclose k) then
          (hclose k _ hc).choose i
        else Classical.arbitrary V)
      else carveLaggedFn hser hclose k i := by
  rw [buildC]
  rfl

theorem buildC_eq_apply (hser : Serial N) (hclose : CarveClosure N P t)
    (k : ℕ) (i : Fin n) :
    buildC hser hclose k i =
      if N.lag i = 0 then
        (if hc : CarveConf N P t k (carveLaggedFn hser hclose k) then
          (hclose k _ hc).choose i
        else Classical.arbitrary V)
      else carveLaggedFn hser hclose k i :=
  congrFun (buildC_eq hser hclose k) i

variable {hser : Serial N} {hclose : CarveClosure N P t}

/-- Workhorse: for a pipelined coordinate at its own label, the stage vector's
value was drawn from `F ∩ P` — GIVEN the carve-at-label invariant below the
current stage (the walk aligns every in-neighbour at its own label one lag
earlier, where the invariant places it in its carve, so the carved-delivery
row certifies the intersection nonempty and the defensive choice takes it). -/
theorem carveLaggedFn_mem_of (hfeas : MarkFlowFeasible N t)
    (hpin : CarvedDelivery N mark P) {k : ℕ} {j : Fin n}
    (h0 : N.lag j ≠ 0) (htj : t j = k)
    (below : ∀ m, m < k → ∀ i, t i = m → buildC hser hclose m i ∈ P i) :
    carveLaggedFn hser hclose k j ∈ P j ∧
      carveLaggedFn hser hclose k j ∈ N.F j (buildC hser hclose (k - N.lag j)) := by
  have hnl : ¬ k < N.lag j := by have := hfeas.1 j; omega
  have hlt : k - N.lag j < k := by
    have h1 : 0 < N.lag j := Nat.pos_of_ne_zero h0
    have h2 : N.lag j ≤ k := Nat.le_of_not_lt hnl
    omega
  have hne : (N.F j (buildC hser hclose (k - N.lag j)) ∩ P j).Nonempty := by
    refine (hpin j).2 _ fun j' hj' => ?_
    have hrow := hfeas.2 j j' hj'
    exact below (k - N.lag j) hlt j' (by omega)
  unfold carveLaggedFn carveLaggedBody
  rw [dif_neg h0, dif_neg hnl, if_pos htj.symm, dif_pos hne]
  exact ⟨hne.some_mem.2, hne.some_mem.1⟩

/-- The carve-at-label invariant: at its label, every coordinate lands inside
its carve. (The r4 pin invariant, with membership replacing equality.) -/
theorem buildC_carve (hfeas : MarkFlowFeasible N t)
    (hpin : CarvedDelivery N mark P) :
    ∀ k i, t i = k → buildC hser hclose k i ∈ P i := by
  have H : ∀ K k, k < K → ∀ i, t i = k → buildC hser hclose k i ∈ P i := by
    intro K
    induction K with
    | zero => exact fun k hk => absurd hk (Nat.not_lt_zero k)
    | succ K ihK =>
      intro k hkK i hti
      have below : ∀ m, m < k → ∀ i', t i' = m → buildC hser hclose m i' ∈ P i' :=
        fun m hm i' hti' => ihK m (by omega) i' hti'
      rw [buildC_eq_apply]
      by_cases h0 : N.lag i = 0
      · rw [if_pos h0]
        have hc : CarveConf N P t k (carveLaggedFn hser hclose k) := fun j hj0 htj =>
          (carveLaggedFn_mem_of hfeas hpin hj0 htj below).1
        rw [dif_pos hc]
        exact ((hclose k _ hc).choose_spec.1 i h0 hti).1
      · rw [if_neg h0]
        exact (carveLaggedFn_mem_of hfeas hpin h0 hti below).1
  exact fun k i hti => H (k + 1) k (Nat.lt_succ_self k) i hti

/-- The conformance test in `buildC` always passes (standalone form of the
invariant, for the run lemma). -/
theorem buildC_conf (hfeas : MarkFlowFeasible N t)
    (hpin : CarvedDelivery N mark P) (k : ℕ) :
    CarveConf N P t k (carveLaggedFn hser hclose k) := fun j hj0 htj =>
  (carveLaggedFn_mem_of hfeas hpin hj0 htj
    fun m _ i' hti' => buildC_carve hfeas hpin m i' hti').1

/-- The stage vector IS the closure witness (pipelined coordinates agree by
the closure's base clause; the conformance dif is discharged). -/
theorem buildC_stage_eq_choose (hfeas : MarkFlowFeasible N t)
    (hpin : CarvedDelivery N mark P) (k : ℕ) :
    buildC hser hclose k =
      (hclose k (carveLaggedFn hser hclose k) (buildC_conf hfeas hpin k)).choose := by
  funext i
  rw [buildC_eq_apply]
  by_cases h0 : N.lag i = 0
  · rw [if_pos h0, dif_pos (buildC_conf hfeas hpin k)]
  · rw [if_neg h0]
    exact ((hclose k (carveLaggedFn hser hclose k)
      (buildC_conf hfeas hpin k)).choose_spec.2.2 i h0).symm

/-- The constructed behaviour is a joint run. Instant admissions (labeled or
not) discharge through the closure; a pipelined coordinate's labeled delivery
was drawn from `F ∩ P` directly. -/
theorem buildC_run (hfeas : MarkFlowFeasible N t)
    (hpin : CarvedDelivery N mark P) :
    JointRun N (buildC hser hclose) := by
  intro k i
  constructor
  · intro hlag
    by_cases h0 : N.lag i = 0
    · -- instantaneous: the constraint reads the current stage
      rw [h0, Nat.sub_zero]
      by_cases hti : t i = k
      · rw [buildC_stage_eq_choose hfeas hpin]
        exact ((hclose k _ (buildC_conf hfeas hpin k)).choose_spec.1 i h0 hti).2
      · rw [buildC_stage_eq_choose hfeas hpin]
        exact (hclose k _ (buildC_conf hfeas hpin k)).choose_spec.2.1 i h0 hti
    · -- pipelined
      by_cases hti : k = t i
      · rw [buildC_eq_apply, if_neg h0]
        exact (carveLaggedFn_mem_of hfeas hpin h0 hti.symm
          fun m _ i' hti' => buildC_carve hfeas hpin m i' hti').2
      · have hnl : ¬ k < N.lag i := not_lt.2 hlag
        rw [buildC_eq_apply, if_neg h0]
        unfold carveLaggedFn carveLaggedBody
        rw [dif_neg h0, dif_neg hnl, if_neg hti]
        exact Set.Nonempty.some_mem _
  · intro hklag
    have h0 : N.lag i ≠ 0 := by omega
    rw [buildC_eq_apply, if_neg h0]
    unfold carveLaggedFn carveLaggedBody
    rw [dif_neg h0, dif_pos hklag]
    exact Set.Nonempty.some_mem _

/-- **The generalized assembly engine** (C1): carve rows + schedule walk +
seriality + diagonal closure produce a joint run realizing every mark at its
label. No hypothesis names a value; the joint behaviour — and every delivered
point — exists only under this conclusion's binder. -/
theorem marks_of_carved_delivery (hser : Serial N) (hfeas : MarkFlowFeasible N t)
    (hpin : CarvedDelivery N mark P) (hclose : CarveClosure N P t) :
    ∃ ω : ℕ → Fin n → V, JointRun N ω ∧ ∀ i, ω (t i) i ∈ mark i :=
  ⟨buildC hser hclose, buildC_run hfeas hpin, fun i =>
    (hpin i).1 (buildC_carve hfeas hpin (t i) i rfl)⟩

end Assembly

/-! ## Singleton degeneracy (C2): a value pin IS a singleton carve -/

section Degeneracy

variable [Nonempty V] {N : MarkNet n V} {mark : Fin n → Set V}
  {a : Fin n → V} {t : Fin n → ℕ}

/-- The r4 pin rows are the singleton instance of the carve rows. -/
theorem carvedDelivery_of_pinned (hpin : PinnedDelivery N mark a) :
    CarvedDelivery N mark (fun i => {a i}) := by
  intro i
  refine ⟨fun v hv => ?_, fun w hw => ?_⟩
  · have hv' : v = a i := hv
    rw [hv']
    exact (hpin i).1
  · exact ⟨a i, (hpin i).2 w fun j hj => hw j hj, rfl⟩

/-- The r4 closure discharges the singleton diagonal. The walk is
load-bearing: every in-neighbour of a pinned instant coordinate is itself
labeled `k` (zero-lag row), so it is either an instant coordinate held at its
pin by the closure or a pipelined coordinate held at its pin by conformance —
and then the pointed row fires. -/
theorem carveClosure_of_pinned (hfeas : MarkFlowFeasible N t)
    (hpin : PinnedDelivery N mark a) (hclose : InstantClosure N a t) :
    CarveClosure N (fun i => {a i}) t := by
  intro k base hconf
  obtain ⟨cur, h1, h2, h3⟩ := hclose k base
  refine ⟨cur, fun i h0 hti => ?_, h2, h3⟩
  have hcur : cur i = a i := h1 i h0 hti
  have hdep : ∀ j ∈ N.dep i, cur j = a j := by
    intro j hj
    have hrow := hfeas.2 i j hj
    have htj : t j = k := by omega
    by_cases hj0 : N.lag j = 0
    · exact h1 j hj0 htj
    · have hb : base j ∈ ({a j} : Set V) := hconf j hj0 htj
      rw [h3 j hj0]
      exact hb
  constructor
  · show cur i ∈ ({a i} : Set V)
    rw [hcur]
    rfl
  · rw [hcur]
    exact (hpin i).2 cur hdep

/-- **Degeneracy is a theorem, not a coincidence**: the r4 engine's exact
statement, re-derived through the generalized engine at singleton carves. -/
theorem marks_of_pinned_delivery_via_carve (hser : Serial N)
    (hfeas : MarkFlowFeasible N t) (hpin : PinnedDelivery N mark a)
    (hclose : InstantClosure N a t) :
    ∃ ω : ℕ → Fin n → V, JointRun N ω ∧ ∀ i, ω (t i) i ∈ mark i :=
  marks_of_carved_delivery hser hfeas (carvedDelivery_of_pinned hpin)
    (carveClosure_of_pinned hfeas hpin hclose)

end Degeneracy

/-! ## The carve dial (C3): the r3 ∀∃ premise is the maximal-carve row -/

section Dial

variable {N : MarkNet n V} {mark : Fin n → Set V}

/-- At `P = mark`, the carve rows ARE the conditional-delivery premises: his
sketch's judgments and the r4 pin rows are the two ends of one dial. -/
theorem carvedDelivery_mark_iff_conditional :
    CarvedDelivery N mark mark ↔ ∀ i, ConditionalDelivery N mark i := by
  constructor
  · intro h i w hw
    obtain ⟨v, hvF, hvP⟩ := (h i).2 w hw
    exact ⟨v, hvF, hvP⟩
  · intro h i
    refine ⟨subset_rfl, fun w hw => ?_⟩
    obtain ⟨v, hvF, hvM⟩ := h i w hw
    exact ⟨v, hvF, hvM⟩

end Dial

/-! ## The acyclic bridge (C4): the dial's maximal end needs no diagonal on
the wire -/

section Acyclic

variable [Nonempty V] {N : MarkNet n V} {mark P : Fin n → Set V} {t : Fin n → ℕ}

/-- Acyclicity dissolves the diagonal at ANY delivery-closed carve: with a
topological order, pinned instant coordinates choose from `F ∩ P` one
`ord`-level at a time (their in-neighbours are all labeled `k` by the walk:
pipelined ones held in-carve by conformance, instant ones settled at earlier
levels), and unpinned coordinates close by seriality as in r4. -/
theorem carveClosure_of_acyclic (hser : Serial N) (hloc : DepLocal N)
    (ord : Fin n → ℕ) (hord : ∀ i, ∀ j ∈ N.dep i, ord j < ord i)
    (hfeas : MarkFlowFeasible N t) (hpin : CarvedDelivery N mark P) :
    CarveClosure N P t := by
  intro k base hconf
  suffices h : ∀ m, ∃ cur : Fin n → V,
      (∀ i, N.lag i ≠ 0 → cur i = base i) ∧
      (∀ i, ord i < m → N.lag i = 0 → t i = k → cur i ∈ P i ∧ cur i ∈ N.F i cur) ∧
      (∀ i, ord i < m → N.lag i = 0 → t i ≠ k → cur i ∈ N.F i cur) by
    obtain ⟨cur, h1, h2, h3⟩ := h (Finset.univ.sup ord + 1)
    exact ⟨cur,
      fun i h0 ht => h2 i (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))) h0 ht,
      fun i h0 ht => h3 i (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))) h0 ht,
      h1⟩
  intro m
  induction m with
  | zero =>
    refine ⟨fun i => if N.lag i ≠ 0 then base i else Classical.arbitrary V,
      fun i h0 => ?_, fun i h => absurd h (Nat.not_lt_zero _),
      fun i h => absurd h (Nat.not_lt_zero _)⟩
    show (if N.lag i ≠ 0 then base i else Classical.arbitrary V) = base i
    rw [if_pos h0]
  | succ m ih =>
    obtain ⟨cur, h1, h2, h3⟩ := ih
    -- level-m instant coordinates: labeled ones choose from F ∩ P via the
    -- carved-delivery row; unlabeled ones by seriality.
    have hchoice : ∀ i, ord i = m → N.lag i = 0 → t i = k →
        ∃ v, v ∈ N.F i cur ∧ v ∈ P i := by
      intro i him h0 hti
      have hne : (N.F i cur ∩ P i).Nonempty := by
        refine (hpin i).2 _ fun j hj => ?_
        have hrow := hfeas.2 i j hj
        have htj : t j = k := by omega
        by_cases hj0 : N.lag j = 0
        · exact (h2 j (by have := hord i j hj; omega) hj0 htj).1
        · rw [h1 j hj0]
          exact hconf j hj0 htj
      exact ⟨hne.some, hne.some_mem.1, hne.some_mem.2⟩
    refine ⟨fun i => if h : ord i = m ∧ N.lag i = 0 then
        (if hti : t i = k then (hchoice i h.1 h.2 hti).choose
         else (hser.2 i cur).some)
      else cur i, fun i h0 => ?_, fun i hi h0 hti => ?_, fun i hi h0 hti => ?_⟩
    · show (if h : ord i = m ∧ N.lag i = 0 then
          (if hti : t i = k then (hchoice i h.1 h.2 hti).choose
           else (hser.2 i cur).some)
        else cur i) = base i
      rw [dif_neg fun h => h0 h.2]
      exact h1 i h0
    · -- labeled instant coordinates below level m+1
      have hF_eq : N.F i (fun j => if h : ord j = m ∧ N.lag j = 0 then
            (if htj : t j = k then (hchoice j h.1 h.2 htj).choose
             else (hser.2 j cur).some)
          else cur j) = N.F i cur := by
        refine hloc i _ _ fun j hj => ?_
        have hji := hord i j hj
        exact dif_neg fun h => by omega
      by_cases him : ord i = m
      · show (if h : ord i = m ∧ N.lag i = 0 then
            (if htj : t i = k then (hchoice i h.1 h.2 htj).choose
             else (hser.2 i cur).some)
          else cur i) ∈ P i ∧
          (if h : ord i = m ∧ N.lag i = 0 then
            (if htj : t i = k then (hchoice i h.1 h.2 htj).choose
             else (hser.2 i cur).some)
          else cur i) ∈ N.F i fun j => if h : ord j = m ∧ N.lag j = 0 then
            (if htj : t j = k then (hchoice j h.1 h.2 htj).choose
             else (hser.2 j cur).some)
          else cur j
        rw [dif_pos ⟨him, h0⟩, dif_pos hti, hF_eq]
        exact ⟨(hchoice i him h0 hti).choose_spec.2,
          (hchoice i him h0 hti).choose_spec.1⟩
      · have hi' : ord i < m := by omega
        show (if h : ord i = m ∧ N.lag i = 0 then
            (if htj : t i = k then (hchoice i h.1 h.2 htj).choose
             else (hser.2 i cur).some)
          else cur i) ∈ P i ∧
          (if h : ord i = m ∧ N.lag i = 0 then
            (if htj : t i = k then (hchoice i h.1 h.2 htj).choose
             else (hser.2 i cur).some)
          else cur i) ∈ N.F i fun j => if h : ord j = m ∧ N.lag j = 0 then
            (if htj : t j = k then (hchoice j h.1 h.2 htj).choose
             else (hser.2 j cur).some)
          else cur j
        rw [dif_neg fun h => him h.1, hF_eq]
        exact (h2 i hi' h0 hti)
    · -- unlabeled instant coordinates below level m+1
      have hF_eq : N.F i (fun j => if h : ord j = m ∧ N.lag j = 0 then
            (if htj : t j = k then (hchoice j h.1 h.2 htj).choose
             else (hser.2 j cur).some)
          else cur j) = N.F i cur := by
        refine hloc i _ _ fun j hj => ?_
        have hji := hord i j hj
        exact dif_neg fun h => by omega
      by_cases him : ord i = m
      · show (if h : ord i = m ∧ N.lag i = 0 then
            (if htj : t i = k then (hchoice i h.1 h.2 htj).choose
             else (hser.2 i cur).some)
          else cur i) ∈ N.F i fun j => if h : ord j = m ∧ N.lag j = 0 then
            (if htj : t j = k then (hchoice j h.1 h.2 htj).choose
             else (hser.2 j cur).some)
          else cur j
        rw [dif_pos ⟨him, h0⟩, dif_neg hti, hF_eq]
        exact Set.Nonempty.some_mem _
      · show (if h : ord i = m ∧ N.lag i = 0 then
            (if htj : t i = k then (hchoice i h.1 h.2 htj).choose
             else (hser.2 i cur).some)
          else cur i) ∈ N.F i fun j => if h : ord j = m ∧ N.lag j = 0 then
            (if htj : t j = k then (hchoice j h.1 h.2 htj).choose
             else (hser.2 j cur).some)
          else cur j
        rw [dif_neg fun h => him h.1, hF_eq]
        exact h3 i (by omega) h0 hti

/-- **The dial's other end, machine-checked** (the second derivation of r4's
acyclic corollary): on acyclic networks, the original sketch's ∀∃ premises conclude
THROUGH the carve engine at the MAXIMAL carve `P = mark` — no point derived,
no diagonal presented. With `marks_of_conditional_delivery_acyclic` (r4,
via derived points) this brackets the dial from both ends. -/
theorem marks_acyclic_via_maximal_carve (hser : Serial N) (hloc : DepLocal N)
    (ord : Fin n → ℕ) (hord : ∀ i, ∀ j ∈ N.dep i, ord j < ord i)
    (hfeas : MarkFlowFeasible N t)
    (hdel : ∀ i, ConditionalDelivery N mark i) :
    ∃ ω : ℕ → Fin n → V, JointRun N ω ∧ ∀ i, ω (t i) i ∈ mark i :=
  marks_of_carved_delivery hser hfeas
    (carvedDelivery_mark_iff_conditional.mpr hdel)
    (carveClosure_of_acyclic hser hloc ord hord hfeas
      (carvedDelivery_mark_iff_conditional.mpr hdel))

end Acyclic

/-! ## The battery (C5–C7, M1′, M2′): what refuses Z5 when pins are
predicates -/

section CarveZoo

/-- **C5 — invariance is NOT the discriminant**: the swap loop's carve rows
HOLD at the maximal carve (swap maps the mark set into the mark set; the
relay copies it). What Z5 loses is the diagonal, not the delivery. -/
theorem z5_carvedDelivery_mark : CarvedDelivery z5Net z5Mark z5Mark := by
  intro i
  fin_cases i
  · refine ⟨subset_rfl, fun w hw => ?_⟩
    have h1 : w 1 ≠ 0 := hw 1 (by decide)
    exact ⟨swap3 (w 1), rfl,
      (by decide : ∀ v : Fin 3, v ≠ 0 → swap3 v ≠ 0) _ h1⟩
  · refine ⟨subset_rfl, fun w hw => ?_⟩
    exact ⟨w 0, rfl, hw 0 (by decide)⟩

/-- **C6 — the diagonal IS the discriminant**: NO carve system inside the
marks closes the swap loop's instant diagonal — containment and closure alone
contradict (the delivery rows are not even needed). The r4 refusal
`z5_no_pin` is this fact's singleton shadow. -/
theorem z5_no_carve_closure :
    ¬ ∃ P : Fin 2 → Set (Fin 3), (∀ i, P i ⊆ z5Mark i) ∧
      CarveClosure z5Net P ![0, 0] := by
  rintro ⟨P, hsub, hclose⟩
  obtain ⟨cur, h1, -, -⟩ := hclose 0 (fun _ => 0)
    (fun j hj0 _ => absurd ((by decide : ∀ j : Fin 2, z5Net.lag j = 0) j) hj0)
  have h0 := h1 0 rfl rfl
  have h1' := h1 1 rfl rfl
  have e0 : cur 0 = swap3 (cur 1) := h0.2
  have e1 : cur 1 = cur 0 := h1'.2
  rw [e1] at e0
  have hz : cur 0 = 0 :=
    (by decide : ∀ v : Fin 3, v = swap3 v → v = 0) _ e0
  exact (hsub 0 h0.1) hz

/-- **M2′ (the diagonal deleted): the carve rule without `CarveClosure` is
unsound** — carve rows at the maximal carve, dep-locality, a feasible
schedule, unpinned joint instant closure, and a nonempty composite all hold
on the swap loop, yet no joint run realizes any mark. The r4 mutant
`z5_refutes_pinless` restated in r5 vocabulary: what the stage arithmetic
cannot see, carve-invariance cannot see either. -/
theorem z5_refutes_closureless :
    ¬ (∀ (m : ℕ) (W : Type) (_ : Nonempty W) (N : MarkNet m W)
        (mark P : Fin m → Set W) (t : Fin m → ℕ),
        Serial N → DepLocal N → CarvedDelivery N mark P →
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
    hrule 2 (Fin 3) ⟨0⟩ z5Net z5Mark z5Mark ![0, 0] hser hloc
      z5_carvedDelivery_mark hfeas hw0 hprop
  obtain ⟨k, hk⟩ := hmark 0
  exact hk (z5_run_zero hrun k 0)

/-- **M1′ (the walk deleted): the carve rule without `MarkFlowFeasible` is
unsound** — the relay–delay loop carries carve rows AND a discharging
diagonal at the singleton carve `{true}` (the closure's conformance
hypothesis hands the delay's base value in-carve, and the relay copies it),
yet realizes no mark on any run. The walk is forced at carve level exactly
as at value level. -/
theorem z1_refutes_walkless_carve :
    ¬ (∀ (m : ℕ) (W : Type) (_ : Nonempty W) (N : MarkNet m W)
        (mark P : Fin m → Set W) (t : Fin m → ℕ),
        Serial N → CarvedDelivery N mark P → CarveClosure N P t →
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
  have hpin : CarvedDelivery z1Net boolMark (fun _ => {true}) := by
    intro i
    fin_cases i
    · refine ⟨fun v hv => hv, fun w hw => ?_⟩
      exact ⟨w 1, rfl, hw 1 (by decide)⟩
    · refine ⟨fun v hv => hv, fun w hw => ?_⟩
      exact ⟨w 0, rfl, hw 0 (by decide)⟩
  have hclose : CarveClosure z1Net (fun _ => {true}) ![0, 0] := by
    intro k base hconf
    by_cases hk : k = 0
    · subst hk
      have hb' : base 1 = true := hconf 1 (by decide) rfl
      refine ⟨![true, base 1], fun i h0 hti => ?_, fun i h0 hti => ?_,
        fun i h0 => ?_⟩
      · fin_cases i
        · exact ⟨rfl, hb'.symm⟩
        · exact absurd h0 (by decide)
      · fin_cases i
        · exact absurd rfl hti
        · exact absurd h0 (by decide)
      · fin_cases i
        · exact absurd rfl h0
        · rfl
    · refine ⟨![base 1, base 1], fun i h0 hti => ?_, fun i h0 hti => ?_,
        fun i h0 => ?_⟩
      · fin_cases i
        · exact absurd hti.symm hk
        · exact absurd h0 (by decide)
      · fin_cases i
        · rfl
        · exact absurd h0 (by decide)
      · fin_cases i
        · exact absurd rfl h0
        · rfl
  obtain ⟨ω, hrun, hmark⟩ :=
    hrule 2 Bool ⟨true⟩ z1Net boolMark (fun _ => {true}) ![0, 0]
      hser hpin hclose
  obtain ⟨k, hk⟩ := hmark 0
  have hk' : ω k 0 = true := hk
  rw [z1_run_false hrun k 0] at hk'
  exact Bool.false_ne_true hk'

/-! ### C7 — the positive control at a fat carve -/

/-- Two instantaneous relays over `Fin 3` — the all-ones loop's shape at an
alphabet where the mark has more than one point. -/
def relay3Net : MarkNet 2 (Fin 3) where
  dep := ![{1}, {0}]
  lag := ![0, 0]
  F := ![fun w => {w 1}, fun w => {w 0}]
  init := ![{1}, {1}]

/-- both marks: "hits a nonzero value" -/
def relay3Mark : Fin 2 → Set (Fin 3) := ![{v | v ≠ 0}, {v | v ≠ 0}]

/-- **The measure-zero objection, answered at theorem level**: the relay loop
realizes its marks through the engine with carve = mark = `{v ≠ 0}` — a
NON-singleton carve; no hypothesis names a value. (The diagonal closes at a
point the PROOF chooses; the kit never presents one. Z5's swap loop, with the
same carve and the same walk, has no such point — `z5_no_carve_closure`.) -/
theorem fatCarve_marks_realized :
    ∃ ω : ℕ → Fin 2 → Fin 3, JointRun relay3Net ω ∧
      ∀ i, ω ((![0, 0] : Fin 2 → ℕ) i) i ∈ relay3Mark i := by
  have hser : Serial relay3Net := by
    constructor
    · intro i
      fin_cases i
      · exact ⟨1, rfl⟩
      · exact ⟨1, rfl⟩
    · intro i w
      fin_cases i
      · exact ⟨w 1, rfl⟩
      · exact ⟨w 0, rfl⟩
  have hfeas : MarkFlowFeasible relay3Net ![0, 0] := by
    refine ⟨fun i => ?_, fun i j hj => ?_⟩
    · fin_cases i <;> exact Nat.le_refl 0
    · fin_cases i <;> fin_cases j
      · exact absurd hj (by decide)
      · rfl
      · rfl
      · exact absurd hj (by decide)
  have hpin : CarvedDelivery relay3Net relay3Mark relay3Mark := by
    intro i
    fin_cases i
    · refine ⟨subset_rfl, fun w hw => ?_⟩
      exact ⟨w 1, rfl, hw 1 (by decide)⟩
    · refine ⟨subset_rfl, fun w hw => ?_⟩
      exact ⟨w 0, rfl, hw 0 (by decide)⟩
  have hclose : CarveClosure relay3Net relay3Mark ![0, 0] := by
    intro k base hconf
    by_cases hk : k = 0
    · subst hk
      refine ⟨![1, 1], fun i h0 hti => ?_, fun i h0 hti => ?_, fun i h0 => ?_⟩
      · fin_cases i
        · exact ⟨(by decide : (1 : Fin 3) ≠ 0), rfl⟩
        · exact ⟨(by decide : (1 : Fin 3) ≠ 0), rfl⟩
      · fin_cases i
        · exact absurd rfl hti
        · exact absurd rfl hti
      · fin_cases i
        · exact absurd rfl h0
        · exact absurd rfl h0
    · refine ⟨![0, 0], fun i h0 hti => ?_, fun i h0 hti => ?_, fun i h0 => ?_⟩
      · fin_cases i
        · exact absurd hti.symm hk
        · exact absurd hti.symm hk
      · fin_cases i
        · rfl
        · rfl
      · fin_cases i
        · exact absurd rfl h0
        · exact absurd rfl h0
  exact marks_of_carved_delivery hser hfeas hpin hclose

end CarveZoo

end BernsteinLogic.QtslCompose.Marks

/-! ## Axiom receipts -/

#print axioms BernsteinLogic.QtslCompose.Marks.marks_of_carved_delivery
#print axioms BernsteinLogic.QtslCompose.Marks.carvedDelivery_of_pinned
#print axioms BernsteinLogic.QtslCompose.Marks.carveClosure_of_pinned
#print axioms BernsteinLogic.QtslCompose.Marks.marks_of_pinned_delivery_via_carve
#print axioms BernsteinLogic.QtslCompose.Marks.carvedDelivery_mark_iff_conditional
#print axioms BernsteinLogic.QtslCompose.Marks.carveClosure_of_acyclic
#print axioms BernsteinLogic.QtslCompose.Marks.marks_acyclic_via_maximal_carve
#print axioms BernsteinLogic.QtslCompose.Marks.z5_carvedDelivery_mark
#print axioms BernsteinLogic.QtslCompose.Marks.z5_no_carve_closure
#print axioms BernsteinLogic.QtslCompose.Marks.z5_refutes_closureless
#print axioms BernsteinLogic.QtslCompose.Marks.z1_refutes_walkless_carve
#print axioms BernsteinLogic.QtslCompose.Marks.fatCarve_marks_realized
