import SuFunctor.Universe.SpecDnf
import SuFunctor.Universe.SpecElab
import SuFunctor.Universe.CertificateLayer

/-! # Graded reach-avoid: the generators of the constructible stratum

A **graded reach-avoid atom** is the spec atom with one safety face and
one genuine liveness face — `marks = {ℓ, ⊤}`, the singleton-liveness
sub-form of the option-A presentation (the properness mark rides along
structurally; the degenerate case `ℓ = ⊤` is the pure-safety atom).
Its satisfaction is the textbook coupled demand: dominate the floor,
dip under the mark (`mem_modelClass_reachAvoid_iff`).  This module
proves that these atoms *generate* the constructible stratum, and that
the graded form is a strict generalization of standard (crisp)
reach-avoid.  Contents:

* **The decomposition is conjunctive, and exactly so**: an atom's
  liveness set enters as an *intersection* of singleton-liveness atoms
  sharing its floor (`modelClass_eq_iInter_reachAvoid`,
  `crescentClass_eq_iInter_reachAvoid`), and the disjunctive reading is
  refuted outright (`exists_modelClass_ne_iUnion_reachAvoid`: the
  union of the singleton classes strictly over-approximates — one
  unsatisfiable mark kills an atom but not the union).  Within a single
  atom, liveness *disjunction* is already expressible without leaving
  the singleton form, by mark-join (`dip_sup_iff`); the disjunction the
  DNF level spends is on unions of classes, not unions of dips.
* **The presented algebra has both connectives as data, exactly**:
  atom conjunction joins floors and accumulates marks
  (`SpecAtom.merge`, `SpecAtom.modelClass_merge` — the judgment-level
  twin of `crescentClass_inter_crescentClass`), and the DNF level
  carries disjunction as disjunct-union and conjunction as pairwise
  atom conjunction, with exact model-class semantics
  (`SpecDnf.modelClass_disj`, `SpecDnf.modelClass_conj`,
  `SpecDnf.crescentClass_disj`, `SpecDnf.crescentClass_conj`).
* **The characterization**: the classes generated from graded
  reach-avoid atoms by finite disjunction (including the empty one)
  and finite conjunction are exactly the presented spec classes — at
  the judgment stratum on an arbitrary carrier
  (`genClosure_reachAvoid_iff_exists_specDnf`) and at the hyperspace
  stratum (`genClosure_reachAvoidCres_iff_exists_specDnf`).  The
  properness mark is what closes the loop with *binary* conjunction
  alone: every liveness set is nonempty by construction, so the
  marks-intersection is anchored at the `⊤`-atom and never needs a
  nullary conjunction — and correspondingly the trivially-true class
  is *not* generated (`top_notMem_modelClass`: no presented class
  contains the inconsistent system, so no generated class is `univ`).
* **Constructibility rides the same induction**: the closure of
  lsc-data reach-avoid crescents is constructible
  (`isConstructibleUnion_of_genClosure_reachAvoidCrescentsLsc`), via
  the finite-intersection closure of constructible unions
  (`IsConstructibleUnion.inter`), new here.
* **Standard reach-avoid embeds, strictly**: with wall data — a crisp
  safe set and a crisp target — the graded judgment *is* the classical
  possibilistic reach-avoid demand: exclude the unsafe set, keep some
  target state possible (`coupledSat_crispRA_iff`).  The
  generalization is strict at the algebra level, not merely atom by
  atom: over a one-point carrier the systems `1` and `0` are
  indistinguishable by every class in the crisp-generated algebra
  (`crisp_agree`), while a graded floor separates them, so some graded
  reach-avoid class lies outside the whole crisp algebra
  (`exists_genClosure_reachAvoid_not_crispGenerated`;
  `GenClosure.mono` supplies the inclusion half of strictness).
-/

namespace SuFunctor.Universe

open scoped ENNReal
open TopologicalSpace

universe u

variable {K : Type u}

/-! ## Graded reach-avoid atoms -/

/-- The graded reach-avoid atom: one safety face, one genuine liveness
face, the properness mark riding along structurally.  `ℓ = ⊤`
degenerates to the pure-safety atom. -/
def SpecAtom.reachAvoid (u ℓ : K → ℝ≥0∞) : SpecAtom K where
  floor := u
  marks := {ℓ, ⊤}
  finite_marks := (Set.finite_singleton _).insert _
  top_mem := Or.inr rfl

@[simp] theorem SpecAtom.reachAvoid_floor (u ℓ : K → ℝ≥0∞) :
    (SpecAtom.reachAvoid u ℓ).floor = u := rfl

@[simp] theorem SpecAtom.reachAvoid_marks (u ℓ : K → ℝ≥0∞) :
    (SpecAtom.reachAvoid u ℓ).marks = {ℓ, ⊤} := rfl

/-- **The textbook shape**: satisfying a graded reach-avoid atom is
dominating the floor and dipping under the mark.  The structural
properness dip is free — any dip is a dip under `⊤`. -/
theorem mem_modelClass_reachAvoid_iff {u ℓ σ : K → ℝ≥0∞} :
    σ ∈ (SpecAtom.reachAvoid u ℓ).modelClass ↔ u ≤ σ ∧ Dip σ ℓ := by
  rw [SpecAtom.mem_modelClass_iff]
  constructor
  · rintro ⟨hsafe, hlive⟩
    exact ⟨hsafe, hlive ℓ (Or.inl rfl)⟩
  · rintro ⟨hsafe, hdip⟩
    refine ⟨hsafe, ?_⟩
    rintro v (rfl | hv)
    · exact hdip
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact hdip.mono_mark le_top

/-! ## The decomposition fork, adjudicated

Two candidate readings of how a liveness *set* relates to the
singleton-liveness atoms sharing its floor: the set could enter
disjunctively (the atom as safety ∧ (ℓ₁ ∨ … ∨ ℓₙ)) or conjunctively.
The judgment's `∀`-face decides for the conjunctive reading, exactly
(`modelClass_eq_iInter_reachAvoid`), and the disjunctive reading is
refuted by an explicit atom (`exists_modelClass_ne_iUnion_reachAvoid`). -/

/-- **The conjunctive decomposition**: every atom's model class is the
intersection of the graded reach-avoid classes at its own marks, floor
shared.  The `⊤`-mark term also anchors the safety face, which is why
the decomposition needs no side condition — the properness demand
makes the intersection nonempty-indexed by construction. -/
theorem modelClass_eq_iInter_reachAvoid (a : SpecAtom K) :
    a.modelClass
      = ⋂ ℓ ∈ a.marks, (SpecAtom.reachAvoid a.floor ℓ).modelClass := by
  ext σ
  rw [SpecAtom.mem_modelClass_iff]
  simp only [Set.mem_iInter, mem_modelClass_reachAvoid_iff]
  constructor
  · rintro ⟨hsafe, hlive⟩ ℓ hℓ
    exact ⟨hsafe, hlive ℓ hℓ⟩
  · intro h
    obtain ⟨hsafe, -⟩ := h ⊤ a.top_mem
    exact ⟨hsafe, fun v hv => (h v hv).2⟩

/-- **The disjunctive reading is refuted**: the union of the
singleton-liveness classes strictly over-approximates — an atom with
one unsatisfiable mark has an empty class, while the union survives
through its other marks.  (The witness: marks `{0, ⊤}` over the
one-point carrier; nothing dips under the zero mark, but the zero
system satisfies the `⊤`-singleton atom.) -/
theorem exists_modelClass_ne_iUnion_reachAvoid :
    ∃ a : SpecAtom Unit,
      a.modelClass
        ≠ ⋃ ℓ ∈ a.marks, (SpecAtom.reachAvoid a.floor ℓ).modelClass := by
  refine ⟨⟨0, {0, ⊤}, (Set.finite_singleton _).insert _, Or.inr rfl⟩,
    fun h => ?_⟩
  have hmem : (0 : Unit → ℝ≥0∞)
      ∈ (⟨0, {0, ⊤}, (Set.finite_singleton _).insert _, Or.inr rfl⟩
          : SpecAtom Unit).modelClass := by
    rw [h]
    refine Set.mem_biUnion (Or.inr rfl) ?_
    rw [mem_modelClass_reachAvoid_iff]
    exact ⟨le_rfl, ⟨(), by simp⟩⟩
  obtain ⟨-, hlive⟩ := hmem
  exact not_dip_zero (hlive 0 (Or.inl rfl))

/-! ## The connectives, as presentation data

The atom-level conjunction (`SpecAtom.merge`: floors join, marks
accumulate — the presented form of `crescentClass_inter_crescentClass`,
with judgment-level exactness `SpecAtom.modelClass_merge`) and the
presentation-level lattice (`SpecDnf.conj`, `SpecDnf.disj`, with their
model-class exactness) are provided by the spec-surface compile module
(`SuFunctor.Universe.SpecElab`); this module consumes them at the
hyperspace stratum below. -/

/-! ## The generated algebra -/

/-- The closure of a family of classes under finite disjunction
(including the empty one) and binary conjunction: the algebra a
generator family spans.  Deliberately no nullary conjunction — the
constructible stratum has no trivially-true class
(`top_notMem_modelClass`), and the properness mark is exactly what
makes binary conjunction suffice downstream. -/
inductive GenClosure {α : Type*} (𝔊 : Set (Set α)) : Set α → Prop
  | base {C : Set α} (h : C ∈ 𝔊) : GenClosure 𝔊 C
  | empty : GenClosure 𝔊 ∅
  | union {C D : Set α} (hC : GenClosure 𝔊 C) (hD : GenClosure 𝔊 D) :
      GenClosure 𝔊 (C ∪ D)
  | inter {C D : Set α} (hC : GenClosure 𝔊 C) (hD : GenClosure 𝔊 D) :
      GenClosure 𝔊 (C ∩ D)

/-- Closures grow with their generator families. -/
theorem GenClosure.mono {α : Type*} {𝔊 𝔊' : Set (Set α)} (h𝔊 : 𝔊 ⊆ 𝔊')
    {C : Set α} (hC : GenClosure 𝔊 C) : GenClosure 𝔊' C := by
  induction hC with
  | base h => exact GenClosure.base (h𝔊 h)
  | empty => exact GenClosure.empty
  | union _ _ ih₁ ih₂ => exact ih₁.union ih₂
  | inter _ _ ih₁ ih₂ => exact ih₁.inter ih₂

/-- An anchored finite intersection stays in the closure: `G` meets
the intersection of a finite family of closure members.  The anchor is
what dissolves the empty case (`G ∩ ⋂ over ∅ = G`), so no nullary
conjunction is ever consumed. -/
theorem GenClosure.inter_biInter {α β : Type*} {𝔊 : Set (Set α)}
    {G : Set α} (hG : GenClosure 𝔊 G) (t : Finset β) (f : β → Set α)
    (hf : ∀ b ∈ t, GenClosure 𝔊 (f b)) :
    GenClosure 𝔊 (G ∩ ⋂ b ∈ t, f b) := by
  classical
  revert hf
  refine Finset.induction_on t (fun _ => by simpa using hG) ?_
  intro a s _ ih hf
  rw [Finset.set_biInter_insert]
  have hrw : G ∩ (f a ∩ ⋂ b ∈ s, f b) = f a ∩ (G ∩ ⋂ b ∈ s, f b) := by
    rw [← Set.inter_assoc, Set.inter_comm G (f a), Set.inter_assoc]
  rw [hrw]
  exact (hf a (Finset.mem_insert_self a s)).inter
    (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

/-- The graded reach-avoid generator family at the judgment stratum. -/
def reachAvoidClasses (K : Type u) : Set (Set (K → ℝ≥0∞)) :=
  {C | ∃ u ℓ : K → ℝ≥0∞, C = (SpecAtom.reachAvoid u ℓ).modelClass}

theorem mem_reachAvoidClasses (u ℓ : K → ℝ≥0∞) :
    (SpecAtom.reachAvoid u ℓ).modelClass ∈ reachAvoidClasses K :=
  ⟨u, ℓ, rfl⟩

/-- Every atom's class is generated: the conjunctive decomposition,
anchored at its own properness mark. -/
theorem genClosure_reachAvoid_modelClass (a : SpecAtom K) :
    GenClosure (reachAvoidClasses K) a.modelClass := by
  classical
  rw [modelClass_eq_iInter_reachAvoid a]
  have habs : (⋂ ℓ ∈ a.marks, (SpecAtom.reachAvoid a.floor ℓ).modelClass)
      = (SpecAtom.reachAvoid a.floor ⊤).modelClass
        ∩ ⋂ ℓ ∈ a.marks, (SpecAtom.reachAvoid a.floor ℓ).modelClass :=
    (Set.inter_eq_self_of_subset_right
      (Set.biInter_subset_of_mem a.top_mem)).symm
  rw [habs]
  have hset : (⋂ ℓ ∈ a.marks, (SpecAtom.reachAvoid a.floor ℓ).modelClass)
      = ⋂ ℓ ∈ a.finite_marks.toFinset,
          (SpecAtom.reachAvoid a.floor ℓ).modelClass := by
    ext σ
    simp [Set.Finite.mem_toFinset]
  rw [hset]
  exact GenClosure.inter_biInter
    (GenClosure.base (mem_reachAvoidClasses a.floor ⊤)) _ _
    fun ℓ _ => GenClosure.base (mem_reachAvoidClasses a.floor ℓ)

/-- Every presented class is generated: disjunct by disjunct. -/
theorem genClosure_reachAvoid_specDnf (D : SpecDnf K) :
    GenClosure (reachAvoidClasses K) D.modelClass := by
  classical
  have h : D.modelClass
      = ⋃ a ∈ D.finite_atoms.toFinset, a.modelClass := by
    ext σ
    simp [SpecDnf.modelClass, Set.Finite.mem_toFinset]
  rw [h]
  refine Finset.induction_on D.finite_atoms.toFinset
    (by simpa using GenClosure.empty (𝔊 := reachAvoidClasses K)) ?_
  intro a s _ ih
  rw [Finset.set_biUnion_insert]
  exact (genClosure_reachAvoid_modelClass a).union ih

/-- **The characterization, judgment stratum**: the algebra generated
by graded reach-avoid atoms under finite disjunction and finite
conjunction is exactly the presented spec classes. -/
theorem genClosure_reachAvoid_iff_exists_specDnf {C : Set (K → ℝ≥0∞)} :
    GenClosure (reachAvoidClasses K) C
      ↔ ∃ D : SpecDnf K, C = D.modelClass := by
  constructor
  · intro h
    induction h with
    | base h =>
        obtain ⟨u, ℓ, rfl⟩ := h
        refine ⟨⟨{SpecAtom.reachAvoid u ℓ}, Set.finite_singleton _⟩, ?_⟩
        ext σ
        simp [SpecDnf.modelClass]
    | empty =>
        refine ⟨⟨∅, Set.finite_empty⟩, ?_⟩
        ext σ
        simp [SpecDnf.modelClass]
    | union _ _ ih₁ ih₂ =>
        obtain ⟨D₁, rfl⟩ := ih₁
        obtain ⟨D₂, rfl⟩ := ih₂
        exact ⟨D₁.disj D₂, (SpecDnf.modelClass_disj D₁ D₂).symm⟩
    | inter _ _ ih₁ ih₂ =>
        obtain ⟨D₁, rfl⟩ := ih₁
        obtain ⟨D₂, rfl⟩ := ih₂
        exact ⟨D₁.conj D₂, (SpecDnf.modelClass_conj D₁ D₂).symm⟩
  · rintro ⟨D, rfl⟩
    exact genClosure_reachAvoid_specDnf D

/-! ## The hyperspace mirror -/

section Hyperspace

variable {V : Type*} [Fintype V]

/-- The conjunctive decomposition at the hyperspace stratum: an atom's
crescent is the intersection of the singleton-liveness crescents at
its own marks.  Pure set algebra — the `⊤`-escape of each singleton
comes from the atom's own properness mark, no dip monotonicity
consumed. -/
theorem crescentClass_eq_iInter_reachAvoid (a : SpecAtom (ProbState V)) :
    crescentClass a.floor a.marks
      = ⋂ ℓ ∈ a.marks, crescentClass a.floor {ℓ, ⊤} := by
  ext L
  simp only [mem_crescentClass_iff, Set.mem_iInter]
  constructor
  · rintro ⟨hsafe, hesc⟩ ℓ hℓ
    refine ⟨hsafe, ?_⟩
    rintro v (rfl | hv)
    · exact hesc _ hℓ
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact hesc ⊤ a.top_mem
  · intro h
    obtain ⟨hsafe, -⟩ := h ⊤ a.top_mem
    exact ⟨hsafe, fun v hv => (h v hv).2 v (Or.inl rfl)⟩

/-- Disjunction is exact at the hyperspace stratum. -/
theorem SpecDnf.crescentClass_disj (D E : SpecDnf (ProbState V)) :
    (D.disj E).crescentClass = D.crescentClass ∪ E.crescentClass := by
  simp only [SpecDnf.crescentClass, SpecDnf.disj_atoms, Set.biUnion_union]

/-- Conjunction is exact at the hyperspace stratum: pairwise atom
conjunction distributes through both unions, each pair landing by
`crescentClass_inter_crescentClass`. -/
theorem SpecDnf.crescentClass_conj (D E : SpecDnf (ProbState V)) :
    (D.conj E).crescentClass = D.crescentClass ∩ E.crescentClass := by
  ext L
  simp only [SpecDnf.crescentClass, SpecDnf.conj_atoms, Set.mem_inter_iff,
    Set.mem_iUnion, exists_prop, Set.mem_image2]
  constructor
  · rintro ⟨c, ⟨a, ha, b, hb, rfl⟩, hc⟩
    rw [SpecAtom.merge_floor, SpecAtom.merge_marks,
      ← crescentClass_inter_crescentClass] at hc
    exact ⟨⟨a, ha, hc.1⟩, ⟨b, hb, hc.2⟩⟩
  · rintro ⟨⟨a, ha, hma⟩, ⟨b, hb, hmb⟩⟩
    refine ⟨a.merge b, ⟨a, ha, b, hb, rfl⟩, ?_⟩
    rw [SpecAtom.merge_floor, SpecAtom.merge_marks,
      ← crescentClass_inter_crescentClass]
    exact ⟨hma, hmb⟩

/-- The graded reach-avoid generator family at the hyperspace
stratum. -/
def reachAvoidCrescents (V : Type*) [Fintype V] :
    Set (Set (NonemptyCompacts (BelState V))) :=
  {C | ∃ u ℓ : ProbPenalty V, C = crescentClass u {ℓ, ⊤}}

theorem mem_reachAvoidCrescents (u ℓ : ProbPenalty V) :
    crescentClass u {ℓ, ⊤} ∈ reachAvoidCrescents V :=
  ⟨u, ℓ, rfl⟩

/-- Every atom's crescent is generated. -/
theorem genClosure_reachAvoid_crescentClass (a : SpecAtom (ProbState V)) :
    GenClosure (reachAvoidCrescents V) (crescentClass a.floor a.marks) := by
  classical
  rw [crescentClass_eq_iInter_reachAvoid a]
  have habs : (⋂ ℓ ∈ a.marks, crescentClass a.floor {ℓ, ⊤})
      = crescentClass a.floor {⊤, ⊤}
        ∩ ⋂ ℓ ∈ a.marks, crescentClass a.floor {ℓ, ⊤} :=
    (Set.inter_eq_self_of_subset_right
      (Set.biInter_subset_of_mem a.top_mem)).symm
  rw [habs]
  have hset : (⋂ ℓ ∈ a.marks, crescentClass a.floor {ℓ, ⊤})
      = ⋂ ℓ ∈ a.finite_marks.toFinset, crescentClass a.floor {ℓ, ⊤} := by
    ext L
    simp [Set.Finite.mem_toFinset]
  rw [hset]
  exact GenClosure.inter_biInter
    (GenClosure.base (mem_reachAvoidCrescents a.floor ⊤)) _ _
    fun ℓ _ => GenClosure.base (mem_reachAvoidCrescents a.floor ℓ)

/-- **The characterization, hyperspace stratum**: the algebra generated
by graded reach-avoid crescents under finite disjunction and finite
conjunction is exactly the presented spec classes of the hyperspace. -/
theorem genClosure_reachAvoidCres_iff_exists_specDnf
    {C : Set (NonemptyCompacts (BelState V))} :
    GenClosure (reachAvoidCrescents V) C
      ↔ ∃ D : SpecDnf (ProbState V), C = D.crescentClass := by
  classical
  constructor
  · intro h
    induction h with
    | base h =>
        obtain ⟨u, ℓ, rfl⟩ := h
        refine ⟨⟨{SpecAtom.reachAvoid u ℓ}, Set.finite_singleton _⟩, ?_⟩
        ext L
        simp [SpecDnf.crescentClass]
    | empty =>
        refine ⟨⟨∅, Set.finite_empty⟩, ?_⟩
        ext L
        simp [SpecDnf.crescentClass]
    | union _ _ ih₁ ih₂ =>
        obtain ⟨D₁, rfl⟩ := ih₁
        obtain ⟨D₂, rfl⟩ := ih₂
        exact ⟨D₁.disj D₂, (SpecDnf.crescentClass_disj D₁ D₂).symm⟩
    | inter _ _ ih₁ ih₂ =>
        obtain ⟨D₁, rfl⟩ := ih₁
        obtain ⟨D₂, rfl⟩ := ih₂
        exact ⟨D₁.conj D₂, (SpecDnf.crescentClass_conj D₁ D₂).symm⟩
  · rintro ⟨D, rfl⟩
    have h : D.crescentClass
        = ⋃ a ∈ D.finite_atoms.toFinset, crescentClass a.floor a.marks := by
      ext L
      simp [SpecDnf.crescentClass, Set.Finite.mem_toFinset]
    rw [h]
    refine Finset.induction_on D.finite_atoms.toFinset
      (by simpa using GenClosure.empty (𝔊 := reachAvoidCrescents V)) ?_
    intro a s _ ih
    rw [Finset.set_biUnion_insert]
    exact (genClosure_reachAvoid_crescentClass a).union ih

end Hyperspace

/-! ## Constructibility rides the same induction -/

/-- Locally closed sets intersect to locally closed sets: opens
intersect with opens, closeds with closeds. -/
theorem isLocallyClosed_inter {X : Type*} [TopologicalSpace X]
    {s t : Set X} (hs : IsLocallyClosed s) (ht : IsLocallyClosed t) :
    IsLocallyClosed (s ∩ t) := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hs
  obtain ⟨U', Z', hU', hZ', rfl⟩ := ht
  exact ⟨U ∩ U', Z ∩ Z', hU.inter hU', hZ.inter hZ',
    Set.inter_inter_inter_comm U Z U' Z'⟩

/-- Constructible unions are closed under finite intersection: locally
closed sets intersect to locally closed sets, and intersection
distributes over the finite unions.  The index bookkeeping is the
product, re-flattened along `finProdFinEquiv`. -/
theorem IsConstructibleUnion.inter {X : Type*} [TopologicalSpace X]
    {s t : Set X} (hs : IsConstructibleUnion s)
    (ht : IsConstructibleUnion t) : IsConstructibleUnion (s ∩ t) := by
  obtain ⟨n, C, hC, rfl⟩ := hs
  obtain ⟨m, C', hC', rfl⟩ := ht
  refine ⟨n * m,
    fun k => C (finProdFinEquiv.symm k).1 ∩ C' (finProdFinEquiv.symm k).2,
    fun k => isLocallyClosed_inter (hC _) (hC' _), ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    refine ⟨finProdFinEquiv (i, j), ?_⟩
    simpa [Equiv.symm_apply_apply] using Set.mem_inter hi hj
  · rintro ⟨k, hk⟩
    exact ⟨⟨_, hk.1⟩, ⟨_, hk.2⟩⟩

section Constructible

variable {V : Type*} [Fintype V]

/-- The lsc-data graded reach-avoid crescents: the generator family
with the semicontinuity the constructible stratum consumes. -/
def reachAvoidCrescentsLsc (V : Type*) [Fintype V] :
    Set (Set (NonemptyCompacts (BelState V))) :=
  {C | ∃ u ℓ : ProbPenalty V, LowerSemicontinuous u
    ∧ LowerSemicontinuous ℓ ∧ C = crescentClass u {ℓ, ⊤}}

/-- **The generated algebra is constructible**, hypotheses riding the
generators: each lsc-data reach-avoid crescent is locally closed, and
constructibility survives the closure's unions and intersections. -/
theorem isConstructibleUnion_of_genClosure_reachAvoidCrescentsLsc
    {C : Set (NonemptyCompacts (BelState V))}
    (h : GenClosure (reachAvoidCrescentsLsc V) C) :
    IsConstructibleUnion C := by
  induction h with
  | base h =>
      obtain ⟨u, ℓ, hu, hℓ, rfl⟩ := h
      refine IsLocallyClosed.isConstructibleUnion
        (isLocallyClosed_crescentClass hu
          ((Set.finite_singleton _).insert _) ?_)
      rintro v (rfl | hv)
      · exact hℓ
      · rw [Set.mem_singleton_iff] at hv
        subst hv
        exact lowerSemicontinuous_const
  | empty => exact isConstructibleUnion_empty
  | union _ _ ih₁ ih₂ => exact ih₁.union ih₂
  | inter _ _ ih₁ ih₂ => exact ih₁.inter ih₂

end Constructible

/-! ## Standard reach-avoid: the crisp fragment, and strictness -/

/-- Crisp penalties: walls, the `{0, ⊤}`-valued members.  The data of
standard (non-graded) reach-avoid. -/
def IsCrisp (v : K → ℝ≥0∞) : Prop := ∀ x, v x = 0 ∨ v x = ⊤

-- `wallOn` (the wall of a set: free inside, forbidden outside — the
-- carrier-generic form of `Carrier.wall`) is provided by
-- `SuFunctor.Universe.SpecElab`.

theorem isCrisp_wallOn (S : Set K) : IsCrisp (wallOn S) := fun x => by
  by_cases h : x ∈ S <;> simp [wallOn, h]

/-- **Standard reach-avoid, verbatim**: against wall data — safe set
`S`, target set `T` — the graded judgment is the classical
possibilistic reach-avoid demand: every unsafe state is excluded
outright, and some target state remains possible. -/
theorem coupledSat_crispRA_iff {σ : K → ℝ≥0∞} {S T : Set K} :
    σ ∈ (SpecAtom.reachAvoid (wallOn S) (wallOn Tᶜ)).modelClass
      ↔ (∀ x, x ∉ S → σ x = ⊤) ∧ ∃ x ∈ T, σ x < ⊤ := by
  rw [mem_modelClass_reachAvoid_iff]
  constructor
  · rintro ⟨hsafe, x, hx⟩
    refine ⟨fun y hy => ?_, x, ?_, lt_of_lt_of_le hx le_top⟩
    · have h := hsafe y
      simp only [wallOn, if_neg hy] at h
      exact top_le_iff.mp h
    · by_contra hxT
      simp only [wallOn, if_pos (Set.mem_compl hxT)] at hx
      exact absurd hx (not_lt.mpr zero_le)
  · rintro ⟨havoid, x, hxT, hx⟩
    constructor
    · intro y
      simp only [wallOn]
      split_ifs with h
      · exact zero_le
      · exact le_of_eq (havoid y h).symm
    · refine ⟨x, ?_⟩
      simp only [wallOn, if_neg (fun hc : x ∈ Tᶜ => hc hxT)]
      exact hx

/-- The crisp reach-avoid generator family: wall data on both faces. -/
def crispReachAvoidClasses (K : Type u) : Set (Set (K → ℝ≥0∞)) :=
  {C | ∃ u ℓ : K → ℝ≥0∞, IsCrisp u ∧ IsCrisp ℓ
    ∧ C = (SpecAtom.reachAvoid u ℓ).modelClass}

/-- The crisp generators are graded generators: the inclusion half of
strictness. -/
theorem crispReachAvoidClasses_subset :
    crispReachAvoidClasses K ⊆ reachAvoidClasses K := by
  rintro C ⟨u, ℓ, -, -, rfl⟩
  exact ⟨u, ℓ, rfl⟩

/-- Over the one-point carrier, `≤` reads at the point. -/
private theorem pi_le_unit_iff {f g : Unit → ℝ≥0∞} : f ≤ g ↔ f () ≤ g () :=
  ⟨fun h => h (), fun h x => by cases x; exact h⟩

/-- **Crisp indistinguishability**: over the one-point carrier, no
class in the crisp-generated algebra separates the graded systems `1`
and `0` — every wall either admits both (it reads `0`) or excludes
both (it reads `⊤`, and neither system is infinite), and every crisp
mark either refuses both dips (zero mark) or grants both (top mark). -/
theorem crisp_agree {C : Set (Unit → ℝ≥0∞)}
    (h : GenClosure (crispReachAvoidClasses Unit) C) :
    ((fun _ => (1 : ℝ≥0∞)) ∈ C ↔ (fun _ => (0 : ℝ≥0∞)) ∈ C) := by
  induction h with
  | base h =>
      obtain ⟨u, ℓ, hu, hℓ, rfl⟩ := h
      rw [mem_modelClass_reachAvoid_iff, mem_modelClass_reachAvoid_iff,
        pi_le_unit_iff, pi_le_unit_iff, dip_unit_iff, dip_unit_iff]
      rcases hu () with hu' | hu' <;> rcases hℓ () with hℓ' | hℓ' <;>
        rw [hu', hℓ'] <;> simp
  | empty => exact Iff.rfl
  | union _ _ ih₁ ih₂ =>
      simp only [Set.mem_union]
      exact or_congr ih₁ ih₂
  | inter _ _ ih₁ ih₂ =>
      simp only [Set.mem_inter_iff]
      exact and_congr ih₁ ih₂

/-- **The generalization is strict, at the algebra level**: a graded
floor over the one-point carrier separates systems the entire
crisp-generated algebra cannot — so its class, itself a graded
reach-avoid generator, lies outside the crisp algebra.  With
`crispReachAvoidClasses_subset` and `GenClosure.mono`, the crisp
algebra sits strictly inside the graded one. -/
theorem exists_genClosure_reachAvoid_not_crispGenerated :
    ∃ C : Set (Unit → ℝ≥0∞),
      GenClosure (reachAvoidClasses Unit) C
        ∧ ¬ GenClosure (crispReachAvoidClasses Unit) C := by
  refine ⟨(SpecAtom.reachAvoid (fun _ => (1 : ℝ≥0∞)) ⊤).modelClass,
    GenClosure.base (mem_reachAvoidClasses _ _), fun h => ?_⟩
  have hag := crisp_agree h
  rw [mem_modelClass_reachAvoid_iff, mem_modelClass_reachAvoid_iff,
    pi_le_unit_iff, pi_le_unit_iff, dip_unit_iff, dip_unit_iff] at hag
  have h0 := hag.mp ⟨le_rfl, ENNReal.one_lt_top⟩
  simpa using h0.1

end SuFunctor.Universe
