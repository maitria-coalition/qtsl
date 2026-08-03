import SuFunctor.Universe.NablaDictionary

/-! # Disjunction elimination over the inclusion-ordered class fibres

The spec stratum of the semantic universe assigns to each interface a
fibre of *classes* in the hyperspace, ordered by inclusion, with the
locally-closed crescents as its atoms and the constructible classes
(`dnfClass`) as its disjunctions.  This module settles how disjunction
elimination — including the context-carrying form, where the eliminated
disjunction sits under a conjunctive context — fares over such fibres.

* **The forcing theorems** (`ctxOrE_valid_iff`, `orI_ctxOrE_valid_iff`):
  over any inclusion-ordered class fibre, contextual disjunction
  elimination is valid for all contexts and conclusions **iff** the
  interpretation of the disjunction is contained in the union of the
  disjuncts' classes; adding soundness of the two introduction rules
  forces it to *be* the union.  Union-exactness is not a design taste —
  it is the unique interpretation of `∨` under which the rule pair is
  sound.
* **The countermodel schema**
  (`exists_ctxOrE_countermodel_of_ssubset`): any interpretation that
  strictly inflates the union — a convex envelope, a locally-closed
  envelope, any closure operator whatsoever — admits an explicit
  context and conclusion refuting the contextual elimination.  The
  historical failure of the elimination rule over hull-valued
  semantics is the convex instance of this schema.
* **The constructible stratum validates the rule, with equality**
  (`dnfClass_append`, `inter_dnfClass_append`, `ctxOrE_dnfClass`): the
  class of the DNF join is literally the union of the classes,
  conjunctive contexts distribute through it by the powerset frame
  law, and the conclusion remains a citizen
  (`isConstructibleUnion_dnfClass_append`).  Nothing beyond finite set
  algebra is consumed: no chain distributivity, no chart condition.
* **The body reading of disjunction fails the class-level rule**
  (`boxClass_union_ssubset`,
  `exists_ctxOrE_countermodel_body_reading`): interpreting the
  disjunction of two safety atoms through a single body — the box
  class of the union of the bodies — strictly inflates the union of
  the classes.  The inflating witness is the *hedger*: the two-point
  citizen committed to the union and to neither disjunct.  Against
  single-body conclusions the inflation is invisible (which is why the
  functional-level reading was sound for the single-conclusion
  grammar); against class-level (DNF) conclusions, which the
  pair-sequent grammar expresses, it refutes the contextual
  elimination outright.
* **The availability crux, in-universe**
  (`exists_union_crescentClass_not_isLocallyClosed`): two spec-atom
  classes of the landed form — one closed atom, one escape atom — whose
  union is *not locally closed* in the hyperspace.  A fibre of
  locally-closed classes only cannot hold its own disjunctions; the
  constructible enlargement (`IsConstructibleUnion`, `dnfClass`) is
  the minimal repair, and by the forcing theorem it is also the only
  sound one.
-/

namespace SuFunctor.Universe

open scoped ENNReal
open TopologicalSpace

/-! ## The forcing theorems

Over an inclusion-ordered class fibre, write `A`, `B` for the classes
of the two disjuncts and `J` for the class assigned to their
disjunction.  Contextual disjunction elimination — from `γ ∩ A ⊆ ψ` and
`γ ∩ B ⊆ ψ` conclude `γ ∩ J ⊆ ψ` — is valid for all `γ`, `ψ` exactly
when `J` adds nothing beyond the union. -/

section Forcing

variable {α : Type*} {A B J : Set α}

/-- Contextual disjunction elimination is sound whenever the
disjunction's class is contained in the union of the disjuncts'
classes. -/
theorem ctxOrE_of_subset_union (hJ : J ⊆ A ∪ B) {γ ψ : Set α}
    (h₁ : γ ∩ A ⊆ ψ) (h₂ : γ ∩ B ⊆ ψ) : γ ∩ J ⊆ ψ := by
  rintro x ⟨hxγ, hxJ⟩
  rcases hJ hxJ with hA | hB
  · exact h₁ ⟨hxγ, hA⟩
  · exact h₂ ⟨hxγ, hB⟩

/-- Conversely, validity of contextual disjunction elimination for all
contexts and conclusions forces the disjunction's class into the union:
instantiate the context with the whole fibre and the conclusion with
the union itself. -/
theorem subset_union_of_ctxOrE
    (h : ∀ γ ψ : Set α, γ ∩ A ⊆ ψ → γ ∩ B ⊆ ψ → γ ∩ J ⊆ ψ) :
    J ⊆ A ∪ B := by
  have h' := h Set.univ (A ∪ B) (fun x hx => Or.inl hx.2)
    (fun x hx => Or.inr hx.2)
  intro x hx
  exact h' ⟨Set.mem_univ x, hx⟩

/-- **The forcing iff**: over inclusion-ordered class fibres,
contextual disjunction elimination is valid for all contexts and
conclusions iff the disjunction's class is contained in the union of
the disjuncts' classes. -/
theorem ctxOrE_valid_iff :
    (∀ γ ψ : Set α, γ ∩ A ⊆ ψ → γ ∩ B ⊆ ψ → γ ∩ J ⊆ ψ) ↔ J ⊆ A ∪ B :=
  ⟨subset_union_of_ctxOrE, fun hJ _ _ h₁ h₂ => ctxOrE_of_subset_union hJ h₁ h₂⟩

/-- **Union-exactness is forced**: soundness of the two introduction
rules together with contextual elimination holds iff the disjunction's
class *is* the union of the disjuncts' classes.  The fibre order leaves
no freedom in the interpretation of `∨`. -/
theorem orI_ctxOrE_valid_iff :
    (A ⊆ J ∧ B ⊆ J ∧
        ∀ γ ψ : Set α, γ ∩ A ⊆ ψ → γ ∩ B ⊆ ψ → γ ∩ J ⊆ ψ)
      ↔ J = A ∪ B := by
  constructor
  · rintro ⟨hA, hB, hctx⟩
    exact (subset_union_of_ctxOrE hctx).antisymm (Set.union_subset hA hB)
  · rintro rfl
    exact ⟨Set.subset_union_left, Set.subset_union_right,
      fun _ _ h₁ h₂ => ctxOrE_of_subset_union subset_rfl h₁ h₂⟩

/-- **The countermodel schema**: any interpretation of the disjunction
that strictly inflates the union of the disjuncts' classes — by a
convex envelope, a locally-closed envelope, or any other closure —
admits an explicit context and conclusion refuting contextual
disjunction elimination. -/
theorem exists_ctxOrE_countermodel_of_ssubset (h : A ∪ B ⊂ J) :
    ∃ γ ψ : Set α, γ ∩ A ⊆ ψ ∧ γ ∩ B ⊆ ψ ∧ ¬ γ ∩ J ⊆ ψ := by
  refine ⟨Set.univ, A ∪ B, fun x hx => Or.inl hx.2,
    fun x hx => Or.inr hx.2, fun hcon => ?_⟩
  obtain ⟨x, hxJ, hxAB⟩ := Set.exists_of_ssubset h
  exact hxAB (hcon ⟨Set.mem_univ x, hxJ⟩)

end Forcing

/-! ## The constructible stratum validates the rule, with equality

The landed spec algebra interprets the disjunction of two coupled DNFs
by concatenating their disjunct families; the class of the result is
literally the union of the classes, so the forcing criterion is met on
the nose and the elimination rule holds by the powerset frame law. -/

section Dnf

variable {V : Type*} [Fintype V]

/-- **The class of the DNF join is the union of the classes**: the
disjunction of the constructible stratum is plain union, with no
envelope and no closure. -/
theorem dnfClass_append {n m : ℕ} (u : Fin n → ProbPenalty V)
    (𝒱 : Fin n → Set (ProbPenalty V)) (u' : Fin m → ProbPenalty V)
    (𝒱' : Fin m → Set (ProbPenalty V)) :
    dnfClass (Fin.append u u') (Fin.append 𝒱 𝒱')
      = dnfClass u 𝒱 ∪ dnfClass u' 𝒱' := by
  ext K
  simp only [dnfClass, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    revert hi
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · intro hj
      rw [Fin.append_left, Fin.append_left] at hj
      exact Or.inl ⟨j, hj⟩
    · intro hj
      rw [Fin.append_right, Fin.append_right] at hj
      exact Or.inr ⟨j, hj⟩
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · exact ⟨Fin.castAdd m j,
        by rw [Fin.append_left, Fin.append_left]; exact hj⟩
    · exact ⟨Fin.natAdd n j,
        by rw [Fin.append_right, Fin.append_right]; exact hj⟩

/-- **The disjunction property at the system boundary**: membership in
the joined class is membership in one disjunct's class — the
certificate's choice byte is its witness.  (Contrast the functional
level, where the disjunction property provably fails: a system may
satisfy the pointwise-min disjunction of two specs while satisfying
neither.) -/
theorem mem_dnfClass_append_iff {n m : ℕ} {u : Fin n → ProbPenalty V}
    {𝒱 : Fin n → Set (ProbPenalty V)} {u' : Fin m → ProbPenalty V}
    {𝒱' : Fin m → Set (ProbPenalty V)} {K : NonemptyCompacts (BelState V)} :
    K ∈ dnfClass (Fin.append u u') (Fin.append 𝒱 𝒱')
      ↔ K ∈ dnfClass u 𝒱 ∨ K ∈ dnfClass u' 𝒱' := by
  rw [dnfClass_append]
  rfl

/-- Disjunction introduction, left: a citizen of a disjunct's class is
a citizen of the join's class. -/
theorem dnfClass_subset_append_left {n m : ℕ} (u : Fin n → ProbPenalty V)
    (𝒱 : Fin n → Set (ProbPenalty V)) (u' : Fin m → ProbPenalty V)
    (𝒱' : Fin m → Set (ProbPenalty V)) :
    dnfClass u 𝒱 ⊆ dnfClass (Fin.append u u') (Fin.append 𝒱 𝒱') := by
  rw [dnfClass_append]
  exact Set.subset_union_left

/-- Disjunction introduction, right. -/
theorem dnfClass_subset_append_right {n m : ℕ} (u : Fin n → ProbPenalty V)
    (𝒱 : Fin n → Set (ProbPenalty V)) (u' : Fin m → ProbPenalty V)
    (𝒱' : Fin m → Set (ProbPenalty V)) :
    dnfClass u' 𝒱' ⊆ dnfClass (Fin.append u u') (Fin.append 𝒱 𝒱') := by
  rw [dnfClass_append]
  exact Set.subset_union_right

/-- **Contextual distribution with equality**: a conjunctive context
distributes through the constructible disjunction on the nose — the
powerset frame law, no chain distributivity of the value lattice
consumed. -/
theorem inter_dnfClass_append {n m : ℕ}
    (γ : Set (NonemptyCompacts (BelState V)))
    (u : Fin n → ProbPenalty V) (𝒱 : Fin n → Set (ProbPenalty V))
    (u' : Fin m → ProbPenalty V) (𝒱' : Fin m → Set (ProbPenalty V)) :
    γ ∩ dnfClass (Fin.append u u') (Fin.append 𝒱 𝒱')
      = (γ ∩ dnfClass u 𝒱) ∪ (γ ∩ dnfClass u' 𝒱') := by
  rw [dnfClass_append, Set.inter_union_distrib_left]

/-- **Contextual disjunction elimination over the constructible
stratum**, arbitrary class context and arbitrary class conclusion:
sound outright, as an instance of the forcing criterion met with
equality. -/
theorem ctxOrE_dnfClass {n m : ℕ} {u : Fin n → ProbPenalty V}
    {𝒱 : Fin n → Set (ProbPenalty V)} {u' : Fin m → ProbPenalty V}
    {𝒱' : Fin m → Set (ProbPenalty V)}
    {γ ψ : Set (NonemptyCompacts (BelState V))}
    (h₁ : γ ∩ dnfClass u 𝒱 ⊆ ψ) (h₂ : γ ∩ dnfClass u' 𝒱' ⊆ ψ) :
    γ ∩ dnfClass (Fin.append u u') (Fin.append 𝒱 𝒱') ⊆ ψ :=
  ctxOrE_of_subset_union (dnfClass_append u 𝒱 u' 𝒱').subset h₁ h₂

/-- **The conclusion stays a citizen**: the constructible classes are
closed under the disjunction the elimination rule eliminates. -/
theorem isConstructibleUnion_dnfClass_append {n m : ℕ}
    {u : Fin n → ProbPenalty V} {𝒱 : Fin n → Set (ProbPenalty V)}
    {u' : Fin m → ProbPenalty V} {𝒱' : Fin m → Set (ProbPenalty V)}
    (hu : ∀ i, LowerSemicontinuous (u i)) (h𝒱 : ∀ i, (𝒱 i).Finite)
    (hlsc : ∀ i, ∀ v ∈ 𝒱 i, LowerSemicontinuous v)
    (hu' : ∀ i, LowerSemicontinuous (u' i)) (h𝒱' : ∀ i, (𝒱' i).Finite)
    (hlsc' : ∀ i, ∀ v ∈ 𝒱' i, LowerSemicontinuous v) :
    IsConstructibleUnion
      (dnfClass (Fin.append u u') (Fin.append 𝒱 𝒱')) := by
  rw [dnfClass_append]
  exact (isConstructibleUnion_dnfClass hu h𝒱 hlsc).union
    (isConstructibleUnion_dnfClass hu' h𝒱' hlsc')

end Dnf

/-! ## The body reading fails the class-level rule

Interpreting the disjunction of two safety atoms through a single body
— the box class of the union of the bodies — strictly inflates the
union of the classes: the hedger, a citizen committed to the union and
to neither disjunct, lies in the gap.  By the countermodel schema this
refutes contextual elimination against class-level conclusions, which
the pair-sequent grammar can express. -/

section BodyReading

variable {α : Type*} [TopologicalSpace α]

/-- **The hedger**: the two-point citizen `{x, y}` is committed to the
union body `{x, y}` and to neither singleton body. -/
theorem exists_mem_boxClass_pair_not_mem_union {x y : α} (hxy : x ≠ y) :
    ∃ K : NonemptyCompacts α,
      K ∈ boxClass ({x, y} : Set α)
        ∧ K ∉ boxClass {x} ∪ boxClass {y} := by
  refine ⟨⟨⟨{x, y}, ((Set.finite_singleton y).insert x).isCompact⟩,
    ⟨x, Set.mem_insert x {y}⟩⟩, fun z hz => hz, ?_⟩
  rintro (h | h)
  · exact hxy (Set.mem_singleton_iff.mp
      (h (Set.mem_insert_of_mem x rfl))).symm
  · exact hxy (Set.mem_singleton_iff.mp (h (Set.mem_insert x {y})))

/-- Box classes are monotone in the body. -/
theorem boxClass_mono {S T : Set α} (h : S ⊆ T) :
    boxClass S ⊆ boxClass T :=
  fun _ hK => hK.trans h

/-- **The body reading strictly inflates**: the box class of a
two-point union body strictly contains the union of the two singleton
box classes. -/
theorem boxClass_union_ssubset {x y : α} (hxy : x ≠ y) :
    boxClass ({x} : Set α) ∪ boxClass {y} ⊂ boxClass ({x, y} : Set α) := by
  rw [Set.ssubset_def]
  obtain ⟨K, hKmem, hKnot⟩ := exists_mem_boxClass_pair_not_mem_union hxy
  refine ⟨Set.union_subset (boxClass_mono ?_) (boxClass_mono ?_),
    fun hcon => hKnot (hcon hKmem)⟩
  · exact Set.singleton_subset_iff.mpr (Set.mem_insert x {y})
  · exact Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem x rfl)

/-- **The body reading refutes contextual elimination at the class
level**: composing the strict inflation with the countermodel schema
yields an explicit class context and class conclusion against which
the body-compiled disjunction fails the rule.  Against single-body
conclusions the two readings agree; the pair-sequent grammar's DNF
conclusions are exactly where they separate. -/
theorem exists_ctxOrE_countermodel_body_reading {x y : α} (hxy : x ≠ y) :
    ∃ γ ψ : Set (NonemptyCompacts α),
      γ ∩ boxClass {x} ⊆ ψ ∧ γ ∩ boxClass {y} ⊆ ψ
        ∧ ¬ γ ∩ boxClass ({x, y} : Set α) ⊆ ψ :=
  exists_ctxOrE_countermodel_of_ssubset (boxClass_union_ssubset hxy)

/-- The carrier has the two distinct points the separation needs. -/
theorem dirac_true_ne_dirac_false :
    (BelState.dirac true : BelState Bool) ≠ BelState.dirac false := by
  intro h
  have h1 : ((BelState.dirac true : BelState Bool) : Bool → ℝ) true
      = ((BelState.dirac false : BelState Bool) : Bool → ℝ) true := by
    rw [h]
  rw [BelState.dirac_apply_same,
    BelState.dirac_apply_of_ne (by decide : true ≠ false)] at h1
  norm_num at h1

/-- The body-reading countermodel, instantiated on the carrier: the
same two point-mass bodies that witness the failure of the disjunction
property at the functional level witness the failure of the
body-compiled contextual elimination at the class level. -/
theorem exists_ctxOrE_countermodel_body_reading_carrier :
    ∃ γ ψ : Set (NonemptyCompacts (BelState Bool)),
      γ ∩ boxClass {BelState.dirac true} ⊆ ψ
        ∧ γ ∩ boxClass {BelState.dirac false} ⊆ ψ
        ∧ ¬ γ ∩ boxClass
            ({BelState.dirac true, BelState.dirac false}
              : Set (BelState Bool)) ⊆ ψ :=
  exists_ctxOrE_countermodel_body_reading dirac_true_ne_dirac_false

end BodyReading

/-! ## The availability crux: crescent unions exit local closedness

The disjunction the elimination rule needs is plain union, and the
union of two spec-atom classes of the landed form is in general *not
locally closed* in the hyperspace: a fibre of locally-closed classes
only cannot hold its own disjunctions.  The witness pairs a closed atom
(a box class on a body reaching the frontier of an escape region) with
an escape atom (a hit class of that region): the closed atom owns a
point of the escape atom's frontier, and frontier citizens outside
both accumulate on it. -/

section Availability

/-- The body of the zero penalty is the whole carrier: at grade one,
every distribution is admitted along its polar ray. -/
theorem compile_zero {V : Type*} [Fintype V] [Nonempty V] :
    compile (0 : ProbPenalty V) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  rcases BelState.exists_polar x with hx0 | ⟨μ, m, hm0, hm1, he⟩
  · obtain ⟨μ⟩ := (inferInstance : Nonempty (ProbState V))
    exact ⟨μ, 0, le_rfl, by rw [Pi.zero_apply, grade_zero]; norm_num,
      by rw [hx0, zero_smul]⟩
  · exact ⟨μ, m, hm0.le, by rw [Pi.zero_apply, grade_zero]; exact hm1, he⟩

/-- The singleton embedding into the hyperspace is continuous for the
Vietoris topology. -/
theorem continuous_singletonNC {α : Type*} [TopologicalSpace α] :
    Continuous ({·} : α → NonemptyCompacts α) :=
  continuous_induced_rng.mpr TopologicalSpace.vietoris.continuous_singleton

/-- A two-outcome distribution from its two weights. -/
def mkBel (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    BelState Bool :=
  ⟨fun t => if t then a else b,
    fun t => by cases t <;> simp [ha, hb],
    by rw [Fintype.sum_bool]; simpa using hab⟩

@[simp] theorem mkBel_apply_true {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) :
    ((mkBel a b ha hb hab : BelState Bool) : Bool → ℝ) true = a := by
  simp [mkBel]

@[simp] theorem mkBel_apply_false {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) :
    ((mkBel a b ha hb hab : BelState Bool) : Bool → ℝ) false = b := by
  simp [mkBel]

/-- Convergence of two-outcome states follows from convergence of the
weights. -/
theorem tendsto_mkBel_of_tendsto {af bf : ℕ → ℝ} {a b : ℝ}
    (haf : ∀ n, 0 ≤ af n) (hbf : ∀ n, 0 ≤ bf n)
    (habf : ∀ n, af n + bf n ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)
    (hta : Filter.Tendsto af Filter.atTop (nhds a))
    (htb : Filter.Tendsto bf Filter.atTop (nhds b)) :
    Filter.Tendsto
      (fun n => mkBel (af n) (bf n) (haf n) (hbf n) (habf n))
      Filter.atTop (nhds (mkBel a b ha hb hab)) := by
  rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff, tendsto_pi_nhds]
  intro t
  cases t
  · simpa [mkBel, Function.comp] using htb
  · simpa [mkBel, Function.comp] using hta

/-- **Locally closed classes are not closed under union, in the
hyperspace, at spec atoms of the landed form**: there are citizens `u`
(a closed atom, demand-free) and `v` (the escape mark of an open
region) whose atom classes union to a non-locally-closed class.  The
constructible stratum is therefore an enlargement the spec algebra
*requires*, not a convenience.

The geometry: `compile v` is the half-carrier of weight at most
one-half on `true`, so the escape atom's class is the hit class of the
open region beyond it; `compile u` is the sub-segment of that
half-carrier with nothing on `false`, so the closed atom's class owns
the singleton of the tip `p = (1/2, 0)`.  The singletons of
`(1/2, εₙ)` lie in the closure of the escape atom (bump the
`true`-coordinate into the region), outside both atoms, and converge
to the tip: were the union `U ∩ Z` with `U` open and `Z` closed, they
would eventually lie in `U`, and always in `Z` (being limits of the
escape atom), hence in the union — which they are not. -/
theorem exists_union_crescentClass_not_isLocallyClosed :
    ∃ u v : ProbPenalty Bool,
      LowerSemicontinuous u ∧ LowerSemicontinuous v ∧
        ¬ IsLocallyClosed
          (crescentClass u ∅
            ∪ crescentClass (0 : ProbPenalty Bool) {v}) := by
  classical
  -- the two bodies
  set Rv : Set (BelState Bool) := {x | (x : Bool → ℝ) true ≤ 1 / 2}
    with hRv_def
  set Ru : Set (BelState Bool) :=
    {x | (x : Bool → ℝ) false = 0 ∧ (x : Bool → ℝ) true ≤ 1 / 2}
    with hRu_def
  have hcont_true :
      Continuous fun x : BelState Bool => (x : Bool → ℝ) true :=
    (continuous_apply true).comp continuous_subtype_val
  have hcont_false :
      Continuous fun x : BelState Bool => (x : Bool → ℝ) false :=
    (continuous_apply false).comp continuous_subtype_val
  have hRv_cl : IsClosed Rv := isClosed_le hcont_true continuous_const
  have hRu_cl : IsClosed Ru := by
    have hsplit : Ru
        = {x : BelState Bool | (x : Bool → ℝ) false = 0} ∩ Rv := by
      rw [hRu_def, hRv_def]
      rfl
    rw [hsplit]
    exact (isClosed_eq hcont_false continuous_const).inter hRv_cl
  have hscale_apply : ∀ (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
      (x : BelState Bool) (b : Bool),
      ((BelState.scale t h0 h1 x : BelState Bool) : Bool → ℝ) b
        = t * (x : Bool → ℝ) b := by
    intro t h0 h1 x b
    rw [BelState.coe_scale]
    simp
  have hRv_rad : IsRadial Rv := by
    intro x hx t h0 h1
    have hx' : (x : Bool → ℝ) true ≤ 1 / 2 := hx
    show ((BelState.scale t h0 h1 x : BelState Bool) : Bool → ℝ) true ≤ 1 / 2
    rw [hscale_apply]
    exact (mul_le_of_le_one_left (x.nonneg true) h1).trans hx'
  have hRu_rad : IsRadial Ru := by
    rintro x ⟨hx0, hx2⟩ t h0 h1
    refine ⟨?_, ?_⟩
    · rw [hscale_apply, hx0, mul_zero]
    · rw [hscale_apply]
      exact (mul_le_of_le_one_left (x.nonneg true) h1).trans hx2
  have hz_Ru : BelState.zero Bool ∈ Ru := by
    refine ⟨?_, ?_⟩
    · rw [BelState.zero_apply]
    · rw [BelState.zero_apply]; norm_num
  have hz_Rv : BelState.zero Bool ∈ Rv := by
    show ((BelState.zero Bool : BelState Bool) : Bool → ℝ) true ≤ 1 / 2
    rw [BelState.zero_apply]; norm_num
  obtain ⟨u, hu_lsc, hcu⟩ :=
    exists_lsc_compile_eq_iff.mpr ⟨⟨_, hz_Ru⟩, hRu_cl, hRu_rad⟩
  obtain ⟨v, hv_lsc, hcv⟩ :=
    exists_lsc_compile_eq_iff.mpr ⟨⟨_, hz_Rv⟩, hRv_cl, hRv_rad⟩
  refine ⟨u, v, hu_lsc, hv_lsc, ?_⟩
  rintro ⟨U, Z, hU, hZ, hUZ⟩
  -- the tip and its singleton citizen
  have h12 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h0le : (0 : ℝ) ≤ 0 := le_rfl
  have hmass_p : (1 : ℝ) / 2 + 0 ≤ 1 := by norm_num
  set p := mkBel (1 / 2) 0 h12 h0le hmass_p with hp
  have hpRu : p ∈ Ru := by
    refine ⟨?_, ?_⟩
    · rw [hp]; simp
    · rw [hp]; simp
  have hK₀_cres :
      ({p} : NonemptyCompacts (BelState Bool)) ∈ crescentClass u ∅ := by
    rw [mem_crescentClass_iff]
    refine ⟨?_, fun w hw => absurd hw (Set.notMem_empty w)⟩
    rw [hcu]
    rintro z rfl
    exact hpRu
  have hK₀UZ : ({p} : NonemptyCompacts (BelState Bool)) ∈ U ∩ Z := by
    rw [← hUZ]
    exact Or.inl hK₀_cres
  -- the vanishing weight sequence
  have he_pos : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + 8)⁻¹ := fun n => by positivity
  have he_le : ∀ n : ℕ, ((n : ℝ) + 8)⁻¹ ≤ 1 / 8 := by
    intro n
    have h8 : (8 : ℝ) ≤ (n : ℝ) + 8 := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    calc ((n : ℝ) + 8)⁻¹ ≤ (8 : ℝ)⁻¹ := by gcongr
      _ = 1 / 8 := by norm_num
  have hmass_q : ∀ n : ℕ, (1 : ℝ) / 2 + ((n : ℝ) + 8)⁻¹ ≤ 1 := fun n => by
    have := he_le n
    linarith
  have he_tendsto :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 8)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_right _ 8 tendsto_natCast_atTop_atTop)
  -- the frontier singletons converge to the tip, so one of them is in U
  have htp : Filter.Tendsto
      (fun n : ℕ =>
        ({mkBel (1 / 2) (((n : ℝ) + 8)⁻¹) h12 (he_pos n).le (hmass_q n)}
          : NonemptyCompacts (BelState Bool)))
      Filter.atTop (nhds ({p} : NonemptyCompacts (BelState Bool))) := by
    refine (continuous_singletonNC.tendsto p).comp ?_
    rw [hp]
    exact tendsto_mkBel_of_tendsto _ _ _ h12 h0le hmass_p
      tendsto_const_nhds he_tendsto
  obtain ⟨n₀, hn₀U⟩ : ∃ n : ℕ,
      ({mkBel (1 / 2) (((n : ℝ) + 8)⁻¹) h12 (he_pos n).le (hmass_q n)}
        : NonemptyCompacts (BelState Bool)) ∈ U := by
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        ({mkBel (1 / 2) (((n : ℝ) + 8)⁻¹) h12 (he_pos n).le (hmass_q n)}
          : NonemptyCompacts (BelState Bool)) ∈ U :=
      htp (hU.mem_nhds hK₀UZ.1)
    exact hev.exists
  set ε := ((n₀ : ℝ) + 8)⁻¹ with hε_def
  set qε := mkBel (1 / 2) ε h12 (he_pos n₀).le (hmass_q n₀) with hq
  -- the chosen frontier singleton is also in Z, through the closure of
  -- the escape atom
  have hqεZ : ({qε} : NonemptyCompacts (BelState Bool)) ∈ Z := by
    have ha' : ∀ m : ℕ, (0 : ℝ) ≤ 1 / 2 + ((m : ℝ) + 8)⁻¹ := fun m => by
      have := (he_pos m).le
      linarith
    have hmass' : ∀ m : ℕ, 1 / 2 + ((m : ℝ) + 8)⁻¹ + ε ≤ 1 := fun m => by
      have h1 := he_le m
      have h2 : ε ≤ 1 / 8 := by rw [hε_def]; exact he_le n₀
      linarith
    have htend : Filter.Tendsto
        (fun m : ℕ =>
          ({mkBel (1 / 2 + ((m : ℝ) + 8)⁻¹) ε (ha' m) (he_pos n₀).le
              (hmass' m)} : NonemptyCompacts (BelState Bool)))
        Filter.atTop (nhds ({qε} : NonemptyCompacts (BelState Bool))) := by
      refine (continuous_singletonNC.tendsto qε).comp ?_
      rw [hq]
      refine tendsto_mkBel_of_tendsto _ _ _ h12 (he_pos n₀).le (hmass_q n₀)
        ?_ tendsto_const_nhds
      simpa using tendsto_const_nhds.add he_tendsto
    have hmem : ∀ m : ℕ,
        ({mkBel (1 / 2 + ((m : ℝ) + 8)⁻¹) ε (ha' m) (he_pos n₀).le
            (hmass' m)} : NonemptyCompacts (BelState Bool))
          ∈ crescentClass (0 : ProbPenalty Bool) {v} := by
      intro m
      rw [mem_crescentClass_iff]
      refine ⟨?_, ?_⟩
      · rw [compile_zero]
        exact fun z _ => Set.mem_univ z
      · rintro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        refine ⟨mkBel (1 / 2 + ((m : ℝ) + 8)⁻¹) ε (ha' m) (he_pos n₀).le
          (hmass' m), rfl, ?_⟩
        rw [hcv]
        intro hcon
        have hcon' : ((mkBel (1 / 2 + ((m : ℝ) + 8)⁻¹) ε (ha' m)
            (he_pos n₀).le (hmass' m) : BelState Bool) : Bool → ℝ) true
              ≤ 1 / 2 := hcon
        rw [mkBel_apply_true] at hcon'
        have := he_pos m
        linarith
    have hclos : ({qε} : NonemptyCompacts (BelState Bool))
        ∈ closure (crescentClass (0 : ProbPenalty Bool) {v}) :=
      mem_closure_of_tendsto htend (Filter.Eventually.of_forall hmem)
    have hsubZ : crescentClass (0 : ProbPenalty Bool) {v} ⊆ Z := by
      intro K hK
      have hKS : K ∈ U ∩ Z := by
        rw [← hUZ]
        exact Or.inr hK
      exact hKS.2
    exact closure_minimal hsubZ hZ hclos
  -- the frontier singleton is therefore in the union — but it is in
  -- neither atom class
  have hqεS : ({qε} : NonemptyCompacts (BelState Bool))
      ∈ crescentClass u ∅
        ∪ crescentClass (0 : ProbPenalty Bool) {v} := by
    rw [hUZ]
    exact ⟨hn₀U, hqεZ⟩
  rcases hqεS with h | h
  · have hsub' := (mem_crescentClass_iff.mp h).1
    rw [hcu] at hsub'
    have hqRu : qε ∈ Ru := hsub' rfl
    have hq0 : ((qε : BelState Bool) : Bool → ℝ) false = 0 := hqRu.1
    rw [hq, mkBel_apply_false] at hq0
    rw [hε_def] at hq0
    exact (he_pos n₀).ne' hq0
  · obtain ⟨x, hxK, hxc⟩ := (mem_crescentClass_iff.mp h).2 v rfl
    have hx' : x = qε := hxK
    rw [hcv] at hxc
    apply hxc
    rw [hx']
    show ((qε : BelState Bool) : Bool → ℝ) true ≤ 1 / 2
    simp [hq]

end Availability

end SuFunctor.Universe
