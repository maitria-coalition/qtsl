import SuFunctor.Universe.CertificateLayer
import SuFunctor.Plain.Battery

/-! # The funnel pattern: a certificate-layer conjunction with shared subject

Transit plus absorbing tail: an outer transit certificate (reach the
gate region within a budget, worst-case) composed with an inner
invariance certificate (the gate region is forward-invariant), citing
the inner region as the outer target.  The semantic universe *refutes*
the compositor reading of this pattern
(`Plain.funnelComp_breaks_unit_coherence`: a composite that collapses
its parts cannot be unital), so this module states what the pattern
lawfully denotes, positively: **a conjunction with shared subject in
the certificate layer** — the same-subject instance of the composite
certificate theorem (`Universe.coupledSat_comp_add_of_dips` at
`g₁ = g₂ = id`).  Its lawfulness is monotone conjunction, not
unitality; its tower-citation edge is the equality of one region
reference cited twice (the transit target and the hold invariant).

* **The honest sort** (`FunnelParts`, `FunnelData`): raw parts mirror
  the producer signature — one subject carrier *by typing* (both spec
  presentations live over the same carrier, so the one-subject
  discipline is unrepresentable to violate), two region citations, a
  budget.  Validation (`FunnelParts.assemble`) refuses unless the two
  citations are one reference and the budget clears the sign gate (a
  funnel with no transit budget asserts nothing about reaching the
  gate); the validated row carries one `gate`.
* **Positive semantics** (`funnel_coupledSat_of_parts`): two component
  certificates about one subject compose to a certificate on the
  funnel's composite atom — floors added, marks unioned — exactly when
  the composite's liveness family is re-witnessed (`hcon` is the
  certificate data of the composite).  Pure instantiation of the
  landed composite-certificate theorem at the identity transports.
* **Monotone conjunction** (`funnel_floor_ge_transit`,
  `funnel_floor_ge_hold`, `funnel_marks_superset`): the funnel's floor
  dominates each conjunct's and its mark family contains each
  conjunct's — the lawfulness the pattern *does* have, in place of the
  unitality the universe refuses.  The domination is not an equality
  (`exists_funnel_floor_ne_transit`): the funnel's floor is a genuine
  sum, strict wherever the partner's floor is nonzero.
* **The tower-citation edge as an equation** (`funnel_gate_shared`,
  `FunnelParts.assemble_isSome_iff`): assembly succeeds exactly when
  the transit target and the hold invariant are one region reference
  and the budget is positive; the assembled gate is that shared
  reference (`FunnelParts.assemble_gate_shared`).  A parts record
  whose two citations differ is refused at construction, mirroring the
  producer's refusal.
* **The negative, restated at the pattern's sort**
  (`funnelDecl_not_system_former`): no funnel row denotes a
  System-former — the would-be compositor reading is the landed
  machine-checked refusal, re-stated, not re-proved.
* **The presentations fence** (`exists_funnel_split_strengthens`):
  splitting the transit spec into finer disjuncts strengthens the
  funnel — same hold certificate, same gate, same budget, same transit
  *model class*, different composite verdicts on an explicit model.
  Composition is an operation on presentations; the row is composition
  data consumed at replay, never a semantic-class operation.  Beside
  it, the demanded dip family is not decoration
  (`exists_funnel_parts_not_coupledSat`): component certificates about
  one subject whose naive composite fails — the certificate layer's
  refusal, exhibited at this sort.

Stratum boundary, stated: at this stratum a region atom appears as its
extension (a set of carrier points); the certified family it carries
(sublevel or affine) and the row-level replay vocabulary are
certificate-row data, deliberately absent here.  Everything is
order-theoretic — no topology, no `Fintype`, no semicontinuity.
-/

namespace SuFunctor.Adequacy

noncomputable section

open scoped ENNReal
open SuFunctor.Universe

universe u

variable {K : Type u}

/-! ## The honest sort -/

/-- Raw funnel parts, as the producer delivers them: one subject
carrier by typing (both spec presentations over the same `K` — the
one-subject discipline is unrepresentable to violate), two spec
presentations, *two* region citations (the transit spec's target and
the hold spec's invariant), and a budget.  Nothing here is validated;
`assemble` is where the two citations are demanded to be one
reference and the budget meets the sign gate. -/
structure FunnelParts (K : Type u) : Type u where
  /-- The outer certificate's presentation: reach the gate within the
  budget, worst-case. -/
  transit : SpecAtom K
  /-- The inner certificate's presentation: the gate region is
  forward-invariant. -/
  hold : SpecAtom K
  /-- The region the transit spec cites as its target. -/
  transitTarget : Set K
  /-- The region the hold spec cites as its invariant. -/
  holdInvariant : Set K
  /-- The transit budget. -/
  budget : ℝ≥0∞

/-- A validated funnel row: the pattern's composition data.  One gate
region — the raw parts' two citations, already identified — and a
positive budget (the sign gate: a funnel with no transit budget
asserts nothing about reaching the gate). -/
structure FunnelData (K : Type u) : Type u where
  /-- The outer certificate's presentation. -/
  transit : SpecAtom K
  /-- The inner certificate's presentation. -/
  hold : SpecAtom K
  /-- The gate: the one region reference the row cites twice — as the
  transit target and as the hold invariant. -/
  gate : Set K
  /-- The transit budget. -/
  budget : ℝ≥0∞
  /-- The sign gate. -/
  budget_pos : 0 < budget

/-! ## Assembly: the tower-citation edge as an equation -/

namespace FunnelParts

open Classical in
/-- Assembly of a funnel row from raw parts: **refuses** — mirroring
the producer — unless the two region citations are one reference and
the budget clears the sign gate. -/
def assemble (p : FunnelParts K) : Option (FunnelData K) :=
  if h : p.transitTarget = p.holdInvariant ∧ 0 < p.budget then
    some ⟨p.transit, p.hold, p.transitTarget, p.budget, h.2⟩
  else none

/-- **The refusal is exact**: assembly succeeds iff the transit target
and the hold invariant are one region reference and the budget is
positive.  A parts record whose two citations differ is refused at
construction. -/
theorem assemble_isSome_iff {p : FunnelParts K} :
    p.assemble.isSome ↔ p.transitTarget = p.holdInvariant ∧ 0 < p.budget := by
  classical
  by_cases h : p.transitTarget = p.holdInvariant ∧ 0 < p.budget
  · simp [assemble, h]
  · simp [assemble, h]

/-- The assembled gate is the shared citation: it is the transit
target and it is the hold invariant — one reference, read off both
ways. -/
theorem assemble_gate_shared {p : FunnelParts K} {F : FunnelData K}
    (h : p.assemble = some F) :
    F.gate = p.transitTarget ∧ F.gate = p.holdInvariant := by
  classical
  by_cases hc : p.transitTarget = p.holdInvariant ∧ 0 < p.budget
  · rw [assemble, dif_pos hc, Option.some_inj] at h
    subst h
    exact ⟨rfl, hc.1⟩
  · rw [assemble, dif_neg hc] at h
    simp at h

end FunnelParts

/-- **The tower-citation edge as an equation**: for any assembled
funnel row, the transit target and the hold invariant are one region
atom.  The citation is an equality, not a pair of references that
happen to agree. -/
theorem funnel_gate_shared {p : FunnelParts K} {F : FunnelData K}
    (h : p.assemble = some F) : p.transitTarget = p.holdInvariant :=
  (FunnelParts.assemble_isSome_iff.mp (by rw [h]; rfl)).1

/-! ## The composite atom, and the positive semantics -/

/-- The funnel's composite atom: floors added, marks unioned — the
same-subject composite presentation.  A genuine spec atom: the
properness demand rides in from the transit conjunct. -/
def FunnelData.composite (F : FunnelData K) : SpecAtom K where
  floor := F.transit.floor + F.hold.floor
  marks := F.transit.marks ∪ F.hold.marks
  finite_marks := F.transit.finite_marks.union F.hold.finite_marks
  top_mem := Set.mem_union_left _ F.transit.top_mem

@[simp] theorem FunnelData.composite_floor (F : FunnelData K) :
    F.composite.floor = F.transit.floor + F.hold.floor := rfl

@[simp] theorem FunnelData.composite_marks (F : FunnelData K) :
    F.composite.marks = F.transit.marks ∪ F.hold.marks := rfl

/-- **The positive semantics: a same-subject composite certificate.**
Two component certificates about one subject — a model of the transit
presentation and a model of the hold presentation — compose to a
certificate on the funnel's composite atom exactly when the
composite's liveness family is re-witnessed: `hcon` is the certificate
data of the composite (the component dip witnesses cannot be consumed;
`exists_funnel_parts_not_coupledSat` exhibits the refusal at this
sort).  Pure instantiation of the landed composite-certificate theorem
`Universe.coupledSat_comp_add_of_dips` at `g₁ = g₂ = id`. -/
theorem funnel_coupledSat_of_parts (F : FunnelData K) {σ₁ σ₂ : K → ℝ≥0∞}
    (h₁ : σ₁ ∈ F.transit.modelClass) (h₂ : σ₂ ∈ F.hold.modelClass)
    (hcon : ∀ w ∈ F.composite.marks, Dip (σ₁ + σ₂) w) :
    σ₁ + σ₂ ∈ F.composite.modelClass := by
  rw [SpecAtom.mem_modelClass_iff] at h₁ h₂
  have himg : ∀ 𝒱 : Set (K → ℝ≥0∞), (· ∘ (id : K → K)) '' 𝒱 = 𝒱 := fun 𝒱 =>
    Set.image_id 𝒱
  have h := coupledSat_comp_add_of_dips (id : K → K) (id : K → K) h₁ h₂
    (by simp only [himg]; exact hcon)
  rw [SpecAtom.mem_modelClass_iff]
  simp only [himg] at h
  exact h

/-! ## Monotone conjunction: the lawfulness the funnel does have -/

/-- The funnel's floor dominates the transit conjunct's floor. -/
theorem funnel_floor_ge_transit (F : FunnelData K) :
    F.transit.floor ≤ F.composite.floor := fun _ => self_le_add_right _ _

/-- The funnel's floor dominates the hold conjunct's floor. -/
theorem funnel_floor_ge_hold (F : FunnelData K) :
    F.hold.floor ≤ F.composite.floor := fun _ => self_le_add_left _ _

/-- The funnel's mark family contains each conjunct's. -/
theorem funnel_marks_superset (F : FunnelData K) :
    F.transit.marks ⊆ F.composite.marks ∧
      F.hold.marks ⊆ F.composite.marks :=
  ⟨Set.subset_union_left, Set.subset_union_right⟩

/-- The floor domination is not an equality: the funnel's floor is a
genuine sum, strict wherever the partner's floor is nonzero.  (The
semantic content behind refusing to weaken `funnel_floor_ge_transit`
to an equation.) -/
theorem exists_funnel_floor_ne_transit :
    ∃ F : FunnelData Unit, F.composite.floor ≠ F.transit.floor := by
  refine ⟨⟨⟨0, {⊤}, Set.finite_singleton _, rfl⟩,
    ⟨1, {⊤}, Set.finite_singleton _, rfl⟩, Set.univ, 1, zero_lt_one⟩, ?_⟩
  intro h
  have h0 := congrFun h ()
  have h1 : (0 : ℝ≥0∞) + 1 = 0 := h0
  rw [zero_add] at h1
  exact one_ne_zero h1

/-! ## The demanded dip family is not decoration -/

/-- **The certificate-layer refusal, at the pattern's sort**: funnel
parts whose component certificates both hold, over one subject, whose
naive composite fails — one conjunct's dip is destroyed by the other's
cost.  This is why `hcon` in `funnel_coupledSat_of_parts` is demanded
certificate data and not derivable bookkeeping.  (Same geometry as the
landed `Universe.exists_coupledSat_add_fails`, re-witnessed here
because the pattern's sort demands the presentation discipline —
finite mark families — that the landed existential does not expose.) -/
theorem exists_funnel_parts_not_coupledSat :
    ∃ (F : FunnelData Unit) (σ₁ σ₂ : Unit → ℝ≥0∞),
      σ₁ ∈ F.transit.modelClass ∧ σ₂ ∈ F.hold.modelClass ∧
      σ₁ + σ₂ ∉ F.composite.modelClass := by
  refine ⟨⟨⟨0, {1, ⊤}, (Set.finite_singleton _).insert _, Or.inr rfl⟩,
    ⟨1, {⊤}, Set.finite_singleton _, rfl⟩, Set.univ, 1, zero_lt_one⟩,
    0, 1, ?_, ?_, ?_⟩
  · refine ⟨le_rfl, ?_⟩
    rintro w (rfl | hw)
    · exact ⟨(), by simp⟩
    · rw [Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨(), by simp⟩
  · refine ⟨le_rfl, ?_⟩
    rintro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨(), by simp⟩
  · intro hmem
    rw [SpecAtom.mem_modelClass_iff] at hmem
    obtain ⟨x, hx⟩ := hmem.2 1 (Set.mem_union_left _ (Or.inl rfl))
    simp at hx

/-! ## The presentations fence -/

/-- **Splitting the transit spec into finer disjuncts strengthens the
funnel.**  Three funnel rows with the same hold certificate, the same
gate, the same budget; the first's transit presentation denotes
exactly the union of the other two's model classes; yet an explicit
model satisfies the first funnel's composite and neither of the
others' — each disjunct's floor participates in its composite sum.
Composition of specs is an operation on presentations, not on their
semantic classes (`Universe.exists_boxplus_not_semantically_monotone`
is the underlying geometry): the funnel row is composition *data*
consumed at replay, and this is content, not caveat. -/
theorem exists_funnel_split_strengthens :
    ∃ (F F₁ F₂ : FunnelData Unit) (τ : Unit → ℝ≥0∞),
      F.hold = F₁.hold ∧ F₁.hold = F₂.hold ∧
      F.gate = F₁.gate ∧ F₁.gate = F₂.gate ∧
      F.budget = F₁.budget ∧ F₁.budget = F₂.budget ∧
      F.transit.modelClass = F₁.transit.modelClass ∪ F₂.transit.modelClass ∧
      τ ∈ F.composite.modelClass ∧
      τ ∉ F₁.composite.modelClass ∧ τ ∉ F₂.composite.modelClass := by
  obtain ⟨a, e, e₁, e₂, τ, hclass, hsat, hnot₁, hnot₂⟩ :=
    exists_boxplus_not_semantically_monotone
  refine ⟨⟨e, a, Set.univ, 1, zero_lt_one⟩, ⟨e₁, a, Set.univ, 1, zero_lt_one⟩,
    ⟨e₂, a, Set.univ, 1, zero_lt_one⟩, τ,
    rfl, rfl, rfl, rfl, rfl, rfl, hclass, ?_, ?_, ?_⟩
  · rw [SpecAtom.mem_modelClass_iff, FunnelData.composite_floor,
      FunnelData.composite_marks, add_comm, Set.union_comm]
    exact hsat
  · intro hmem
    rw [SpecAtom.mem_modelClass_iff, FunnelData.composite_floor,
      FunnelData.composite_marks, add_comm, Set.union_comm] at hmem
    exact hnot₁ hmem
  · intro hmem
    rw [SpecAtom.mem_modelClass_iff, FunnelData.composite_floor,
      FunnelData.composite_marks, add_comm, Set.union_comm] at hmem
    exact hnot₂ hmem

/-! ## The negative, restated at the pattern's sort -/

section Negative

open CategoryTheory CategoryTheory.WireSpan PseudoDoubleCategoryStruct
open SuFunctor.Plain

variable {El : Type u}

/-- **No funnel row denotes a System-former** — the would-be
compositor reading of the pattern is refuted: a composite that
collapses its parts into one slot cannot satisfy the unit law.  This
is the landed machine-checked refusal
(`Plain.funnelComp_breaks_unit_coherence`), re-stated at the pattern's
sort and not re-proved: what a funnel row lawfully denotes is the
certificate-layer conjunction of `funnel_coupledSat_of_parts`, and its
row is certificate-composition data, never a System former. -/
theorem funnelDecl_not_system_former {A B : WireSpan El} (M : Pat A B) :
    ¬ ∀ 𝒰 : Cpl M,
      Pen.pull (PatCell.tot
          (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M)) ''
          funnelComp ({unitPen A} : Cpl (Pat.id A)) 𝒰 = 𝒰 :=
  funnelComp_breaks_unit_coherence M

end Negative

end

end SuFunctor.Adequacy
