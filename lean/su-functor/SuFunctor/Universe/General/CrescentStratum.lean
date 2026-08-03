import SuFunctor.Universe.General.Closedness
import SuFunctor.Universe.FellTopology
import SuFunctor.Universe.LocallyClosedLayer
import SuFunctor.Universe.DisjunctionElim

/-! # The class stratum at the general carrier

The hyperspace storey of the semantic universe — crescents,
constructible classes, and the judgment transport — stated over the
**general** subprobability carrier: `SubProbabilityMeasure X` for an
arbitrary topological measurable space `X`, with the class fibre living
in the Fell hyperspace `FellCloseds (SubProbabilityMeasure X)`.  This
retires the finite-outcome fence on the class machinery: the finite
stratum's presentation over `NonemptyCompacts (BelState V)`
(`SuFunctor.Universe.VietorisStratum`, `LocallyClosedLayer`) becomes the
compact-Hausdorff case of this one, through the `fell_eq_vietoris`
collapse.

Ambient adjudication (registered in the prereg before this file): the
general bodies are closed but not compact, so mathlib's Vietoris
hyperspaces (`Compacts`, `NonemptyCompacts` — the library deliberately
equips no type of closeds) cannot hold them; the house `FellCloseds` is
the hyperspace the chapter's storey paragraph already names, and both
crescent faces ride only the **lower (hit-open) subbasis that Fell and
Vietoris share**:

* the containment face `{F | ↑F ⊆ S(u)}` is closed because its
  complement is the hit class of the *open* complement of the (closed)
  body — `FellCloseds.isClosed_subsets_of_isClosed`;
* the escape face is the hit class of an open region itself —
  `FellCloseds.isOpen_inter_nonempty_of_isOpen`.

So the new substance at this stratum is entirely on the compile side —
closedness of bodies is lower semicontinuity of penalties
(`General.isClosed_compile`), landed in `General.Closedness` — and this
module is the assembly: the (∪, ∩, grade-product-free) body algebra,
the crescent geometry, the constructible closure, and the judgment
transport, each with its hypotheses named.

Consumed, not re-minted (already carrier-general upstream):
`IsConstructibleUnion` and its union closure
(`SuFunctor.Universe.LocallyClosedLayer`), the forcing theorems of
disjunction elimination (`SuFunctor.Universe.DisjunctionElim`, section
`Forcing`), and the coupled judgment itself
(`SuFunctor.Universe.CoupledJudgment`, arbitrary carrier).

Hypothesis discipline, stated once: `[Nonempty X]` enters exactly where
the bottom state must be a body point (`zero_mem_compile`) or where
closedness of bodies is consumed (`isClosed_compile`); lower
semicontinuity is per-penalty supply, named in each statement;
`𝒱.Finite` enters only for local closedness of a crescent (finitely
many open escape demands).  Nothing here assumes the carrier finite,
compact, or metrizable.
-/

namespace SuFunctor.Universe.General

open MeasureTheory
open scoped ENNReal NNReal Topology

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

/-! ## The grade algebra of the lattice operations -/

/-- The grade of a join is the meet of the grades: pure antitonicity on
a linear order — no coercion consumed. -/
theorem gradeN_sup (a b : ℝ≥0∞) : gradeN (a ⊔ b) = gradeN a ⊓ gradeN b := by
  rcases le_total a b with h | h
  · rw [sup_eq_right.mpr h, inf_eq_right.mpr (gradeN_anti h)]
  · rw [sup_eq_left.mpr h, inf_eq_left.mpr (gradeN_anti h)]

/-- The grade of a meet is the join of the grades. -/
theorem gradeN_inf (a b : ℝ≥0∞) : gradeN (a ⊓ b) = gradeN a ⊔ gradeN b := by
  rcases le_total a b with h | h
  · rw [inf_eq_left.mpr h, sup_eq_left.mpr (gradeN_anti h)]
  · rw [inf_eq_right.mpr h, sup_eq_right.mpr (gradeN_anti h)]

/-- The grade of a sum is the product of the grades: the ℝ≥0 face of
`grade_add` — the compositor's scaling law. -/
theorem gradeN_add (a b : ℝ≥0∞) : gradeN (a + b) = gradeN a * gradeN b := by
  ext
  rw [coe_gradeN, grade_add, NNReal.coe_mul, coe_gradeN, coe_gradeN]

/-! ## The body algebra: (⊔, ⊓, 0) compiles to (∩, ∪, univ) -/

/-- **Intersection of bodies is conjunction**: the pointwise max
compiles to the body intersection, over the general carrier, with no
topological hypothesis and no `Nonempty`. -/
theorem compile_sup (f g : Penalty X) :
    compile (f ⊔ g) = compile f ∩ compile g := by
  ext ν
  constructor
  · rintro ⟨μ, γ, hle, he⟩
    rw [Pi.sup_apply, gradeN_sup] at hle
    exact ⟨⟨μ, γ, hle.trans inf_le_left, he⟩,
      ⟨μ, γ, hle.trans inf_le_right, he⟩⟩
  · rintro ⟨hf, hg⟩
    obtain ⟨μ, γ, hlef, he⟩ := hf
    rcases eq_or_ne γ 0 with rfl | hγ
    · exact ⟨μ, 0, zero_le, he⟩
    · have hleg : γ ≤ gradeN (g μ) := compile_scale_le hg hγ he
      exact ⟨μ, γ, by rw [Pi.sup_apply, gradeN_sup]; exact le_inf hlef hleg,
        he⟩

/-- **Disjunction of systems is union of bodies** — exactly, with no
hull, over the general carrier. -/
theorem compile_inf (f g : Penalty X) :
    compile (f ⊓ g) = compile f ∪ compile g := by
  ext ν
  constructor
  · rintro ⟨μ, γ, hle, he⟩
    rw [Pi.inf_apply, gradeN_inf] at hle
    rcases le_sup_iff.mp hle with h | h
    · exact Or.inl ⟨μ, γ, h, he⟩
    · exact Or.inr ⟨μ, γ, h, he⟩
  · rintro (⟨μ, γ, hle, he⟩ | ⟨μ, γ, hle, he⟩)
    · exact ⟨μ, γ, by
        rw [Pi.inf_apply, gradeN_inf]
        exact hle.trans le_sup_left, he⟩
    · exact ⟨μ, γ, by
        rw [Pi.inf_apply, gradeN_inf]
        exact hle.trans le_sup_right, he⟩

/-- The body of the zero penalty is the whole carrier: at grade one,
every state is admitted along its polar ray.  `[Nonempty X]` pays for
the bottom state's ray. -/
theorem compile_zero [Nonempty X] :
    compile (0 : Penalty X) = Set.univ := by
  refine Set.eq_univ_of_forall fun ν => ?_
  rcases SubProbabilityMeasure.exists_polar ν with h0 | ⟨μ, m, _, hm1, he⟩
  · rw [h0]
    exact zero_mem_compile _
  · exact ⟨μ, m, by rw [Pi.zero_apply, gradeN_zero]; exact hm1, he⟩

/-! ## The judgment, compiled -/

/-- **Dips are escapes**: the system dips under a mark iff its body
protrudes past the mark's body.  `[Nonempty X]` pays for the bottom
state in the backward direction's zero-scale case. -/
theorem dip_iff_compile_escape [Nonempty X] {σ v : Penalty X} :
    Dip σ v ↔ ∃ ν ∈ compile σ, ν ∉ compile v := by
  constructor
  · rintro ⟨μ, hμ⟩
    have hσtop : σ μ ≠ ⊤ := fun h => absurd hμ (by rw [h]; exact not_top_lt)
    refine ⟨SubProbabilityMeasure.scalePoint (gradeN (σ μ)) (gradeN_le_one _) μ,
      scalePoint_mem_compile le_rfl, fun hmem => ?_⟩
    have hb := compile_scale_le hmem (gradeN_pos hσtop).ne'
      (SubProbabilityMeasure.coe_scalePoint _ _ _)
    exact absurd hμ (not_lt.mpr (gradeN_le_gradeN_iff.mp hb))
  · rintro ⟨x, ⟨μ, γ, hle, he⟩, hxv⟩
    have hγ : γ ≠ 0 := by
      rintro rfl
      apply hxv
      have hx0 : x = 0 := SubProbabilityMeasure.ext (by
        rw [he, zero_smul, SubProbabilityMeasure.coe_zero])
      rw [hx0]
      exact zero_mem_compile v
    have hnot : ¬ γ ≤ gradeN (v μ) := fun hc => hxv ⟨μ, γ, hc, he⟩
    exact ⟨μ, gradeN_lt_gradeN_iff.mp (lt_of_lt_of_le (not_le.mp hnot) hle)⟩

/-- **The judgment, compiled, at the general carrier**: coupled
satisfaction is containment in the safety body together with escape
past every liveness body.  (Membership-iff-domination is
`compile_subset_compile_iff`, consumed; this composes it with the dip
dictionary.) -/
theorem coupledSat_iff_compile [Nonempty X] {σ u : Penalty X}
    {𝒱 : Set (Penalty X)} :
    CoupledSat σ u 𝒱
      ↔ compile σ ⊆ compile u
        ∧ ∀ v ∈ 𝒱, ∃ x ∈ compile σ, x ∉ compile v := by
  rw [CoupledSat, ← compile_subset_compile_iff]
  exact and_congr Iff.rfl (forall₂_congr fun v _ => dip_iff_compile_escape)

/-! ## The compile as a Fell-hyperspace point -/

/-- The body of a citizen, packaged as a point of the Fell hyperspace
of the general carrier.  Closedness is the general dictionary's
topological leg (`isClosed_compile`); no compactness exists to package,
and none is needed — the Fell hyperspace holds every closed set. -/
noncomputable def compileF [Nonempty X] (f : Penalty X)
    (hf : LowerSemicontinuous f) : FellCloseds (SubProbabilityMeasure X) :=
  ⟨compile f, isClosed_compile hf⟩

@[simp] theorem coe_compileF [Nonempty X] (f : Penalty X)
    (hf : LowerSemicontinuous f) :
    (compileF f hf : Set (SubProbabilityMeasure X)) = compile f := rfl

/-! ## Spec classes are crescents in the Fell hyperspace -/

/-- The hyperspace class of a spec atom `(u, 𝒱)` at the general
carrier: closed sets contained in the safety body that escape every
liveness body. -/
def crescentClass (u : Penalty X) (𝒱 : Set (Penalty X)) :
    Set (FellCloseds (SubProbabilityMeasure X)) :=
  {F | (F : Set (SubProbabilityMeasure X)) ⊆ compile u}
    ∩ ⋂ v ∈ 𝒱,
        {F | ((F : Set (SubProbabilityMeasure X)) ∩ (compile v)ᶜ).Nonempty}

theorem mem_crescentClass_iff {u : Penalty X} {𝒱 : Set (Penalty X)}
    {F : FellCloseds (SubProbabilityMeasure X)} :
    F ∈ crescentClass u 𝒱
      ↔ (F : Set (SubProbabilityMeasure X)) ⊆ compile u
        ∧ ∀ v ∈ 𝒱,
            ((F : Set (SubProbabilityMeasure X)) ∩ (compile v)ᶜ).Nonempty := by
  simp [crescentClass]

/-- **The judgment transports to crescent membership** at the general
carrier: a citizen satisfies a spec atom iff its body lies in the
atom's crescent class. -/
theorem compileF_mem_crescentClass_iff [Nonempty X] {σ u : Penalty X}
    {𝒱 : Set (Penalty X)} (hσ : LowerSemicontinuous σ) :
    compileF σ hσ ∈ crescentClass u 𝒱 ↔ CoupledSat σ u 𝒱 := by
  rw [mem_crescentClass_iff, coe_compileF, coupledSat_iff_compile]
  refine and_congr Iff.rfl (forall₂_congr fun v _ => ?_)
  constructor
  · rintro ⟨x, hx1, hx2⟩
    exact ⟨x, hx1, hx2⟩
  · rintro ⟨x, hx1, hx2⟩
    exact ⟨x, hx1, hx2⟩

/-- The safety face is closed in the Fell hyperspace: containment in a
citizen's body is a closed demand.  The closedness supply is the
general dictionary's `isClosed_compile` — lower semicontinuity of `u`
is exactly what pays for it (mutant m1 drops this hypothesis and the
proof must go red here). -/
theorem isClosed_safety_face [Nonempty X] {u : Penalty X}
    (hu : LowerSemicontinuous u) :
    IsClosed {F : FellCloseds (SubProbabilityMeasure X) |
      (F : Set (SubProbabilityMeasure X)) ⊆ compile u} :=
  FellCloseds.isClosed_subsets_of_isClosed (isClosed_compile hu)

/-- The escape face is open in the Fell hyperspace: protruding past a
citizen's body is a hit of the open escape region. -/
theorem isOpen_escape_face [Nonempty X] {v : Penalty X}
    (hv : LowerSemicontinuous v) :
    IsOpen {F : FellCloseds (SubProbabilityMeasure X) |
      ((F : Set (SubProbabilityMeasure X)) ∩ (compile v)ᶜ).Nonempty} :=
  FellCloseds.isOpen_inter_nonempty_of_isOpen (isClosed_compile hv).isOpen_compl

/-- **Spec-atom classes are locally closed in the general Fell
hyperspace**: one closed containment demand, finitely many open escape
demands.  Consumes: lower semicontinuity of the floor and of every
mark (body closedness), and finiteness of the liveness family (a
finite intersection of opens). -/
theorem isLocallyClosed_crescentClass [Nonempty X] {u : Penalty X}
    {𝒱 : Set (Penalty X)} (hu : LowerSemicontinuous u)
    (h𝒱 : 𝒱.Finite) (hlsc : ∀ v ∈ 𝒱, LowerSemicontinuous v) :
    IsLocallyClosed (crescentClass u 𝒱) :=
  ⟨⋂ v ∈ 𝒱,
      {F | ((F : Set (SubProbabilityMeasure X)) ∩ (compile v)ᶜ).Nonempty},
    {F | (F : Set (SubProbabilityMeasure X)) ⊆ compile u},
    h𝒱.isOpen_biInter fun v hv => isOpen_escape_face (hlsc v hv),
    isClosed_safety_face hu,
    Set.inter_comm _ _⟩

/-- Crescents are constructible: the locally-closed layer sits inside
the constructible one (`IsConstructibleUnion` is carrier-general —
consumed from `LocallyClosedLayer`, not re-minted). -/
theorem isConstructibleUnion_crescentClass [Nonempty X] {u : Penalty X}
    {𝒱 : Set (Penalty X)} (hu : LowerSemicontinuous u)
    (h𝒱 : 𝒱.Finite) (hlsc : ∀ v ∈ 𝒱, LowerSemicontinuous v) :
    IsConstructibleUnion (crescentClass u 𝒱) :=
  IsLocallyClosed.isConstructibleUnion
    (isLocallyClosed_crescentClass hu h𝒱 hlsc)

/-- **The hit-union law** at the general carrier: escape past a
max-merged liveness body is escape past one of the merged bodies — the
lower face turns the liveness disjunction into an exact identity of
open classes. -/
theorem escape_face_sup (v₁ v₂ : Penalty X) :
    {F : FellCloseds (SubProbabilityMeasure X) |
        ((F : Set (SubProbabilityMeasure X)) ∩ (compile (v₁ ⊔ v₂))ᶜ).Nonempty}
      = {F : FellCloseds (SubProbabilityMeasure X) |
          ((F : Set (SubProbabilityMeasure X)) ∩ (compile v₁)ᶜ).Nonempty}
        ∪ {F : FellCloseds (SubProbabilityMeasure X) |
            ((F : Set (SubProbabilityMeasure X)) ∩ (compile v₂)ᶜ).Nonempty} := by
  ext F
  rw [Set.mem_setOf_eq, compile_sup, Set.compl_inter,
    Set.inter_union_distrib_left]
  exact Set.union_nonempty

/-- Atom conjunction is exact at the class level, over the general
carrier: crescents intersect to crescents, safety floors joining and
liveness demands accumulating. -/
theorem crescentClass_inter_crescentClass {u₁ u₂ : Penalty X}
    {𝒱₁ 𝒱₂ : Set (Penalty X)} :
    crescentClass u₁ 𝒱₁ ∩ crescentClass u₂ 𝒱₂
      = crescentClass (u₁ ⊔ u₂) (𝒱₁ ∪ 𝒱₂) := by
  ext F
  simp only [Set.mem_inter_iff, mem_crescentClass_iff, compile_sup,
    Set.subset_inter_iff]
  constructor
  · rintro ⟨⟨h1, e1⟩, h2, e2⟩
    refine ⟨⟨h1, h2⟩, fun v hv => ?_⟩
    rcases hv with hv | hv
    · exact e1 v hv
    · exact e2 v hv
  · rintro ⟨⟨h1, h2⟩, e⟩
    exact ⟨⟨h1, fun v hv => e v (Set.mem_union_left _ hv)⟩,
      ⟨h2, fun v hv => e v (Set.mem_union_right _ hv)⟩⟩

/-! ## The constructible stratum: DNF classes at the general carrier -/

/-- The hyperspace class of a coupled DNF at the general carrier: the
union of its disjuncts' crescents. -/
def dnfClass {n : ℕ} (u : Fin n → Penalty X)
    (𝒱 : Fin n → Set (Penalty X)) :
    Set (FellCloseds (SubProbabilityMeasure X)) :=
  ⋃ i, crescentClass (u i) (𝒱 i)

/-- The judgment against a DNF transports to membership of the body in
the DNF's class. -/
theorem compileF_mem_dnfClass_iff [Nonempty X] {σ : Penalty X}
    (hσ : LowerSemicontinuous σ) {n : ℕ} {u : Fin n → Penalty X}
    {𝒱 : Fin n → Set (Penalty X)} :
    compileF σ hσ ∈ dnfClass u 𝒱 ↔ ∃ i, CoupledSat σ (u i) (𝒱 i) := by
  simp only [dnfClass, Set.mem_iUnion]
  exact exists_congr fun i => compileF_mem_crescentClass_iff hσ

/-- **DNF classes are constructible at the general carrier**: finite
unions of locally closed crescents. -/
theorem isConstructibleUnion_dnfClass [Nonempty X] {n : ℕ}
    {u : Fin n → Penalty X} {𝒱 : Fin n → Set (Penalty X)}
    (hu : ∀ i, LowerSemicontinuous (u i)) (h𝒱 : ∀ i, (𝒱 i).Finite)
    (hlsc : ∀ i, ∀ v ∈ 𝒱 i, LowerSemicontinuous v) :
    IsConstructibleUnion (dnfClass u 𝒱) :=
  ⟨n, fun i => crescentClass (u i) (𝒱 i),
    fun i => isLocallyClosed_crescentClass (hu i) (h𝒱 i) (hlsc i), rfl⟩

/-- **The class of the DNF join is the union of the classes**: the
disjunction of the constructible stratum is plain union, at the general
carrier as at the finite one — no envelope, no closure. -/
theorem dnfClass_append {n m : ℕ} (u : Fin n → Penalty X)
    (𝒱 : Fin n → Set (Penalty X)) (u' : Fin m → Penalty X)
    (𝒱' : Fin m → Set (Penalty X)) :
    dnfClass (Fin.append u u') (Fin.append 𝒱 𝒱')
      = dnfClass u 𝒱 ∪ dnfClass u' 𝒱' := by
  ext F
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

/-- Contextual distribution with equality, general carrier: a
conjunctive context distributes through the constructible disjunction
by the powerset frame law. -/
theorem inter_dnfClass_append {n m : ℕ}
    (γ : Set (FellCloseds (SubProbabilityMeasure X)))
    (u : Fin n → Penalty X) (𝒱 : Fin n → Set (Penalty X))
    (u' : Fin m → Penalty X) (𝒱' : Fin m → Set (Penalty X)) :
    γ ∩ dnfClass (Fin.append u u') (Fin.append 𝒱 𝒱')
      = (γ ∩ dnfClass u 𝒱) ∪ (γ ∩ dnfClass u' 𝒱') := by
  rw [dnfClass_append, Set.inter_union_distrib_left]

/-- **Contextual disjunction elimination over the general constructible
stratum**: sound outright, as an instance of the (carrier-general,
consumed) forcing criterion met with equality. -/
theorem ctxOrE_dnfClass {n m : ℕ} {u : Fin n → Penalty X}
    {𝒱 : Fin n → Set (Penalty X)} {u' : Fin m → Penalty X}
    {𝒱' : Fin m → Set (Penalty X)}
    {γ ψ : Set (FellCloseds (SubProbabilityMeasure X))}
    (h₁ : γ ∩ dnfClass u 𝒱 ⊆ ψ) (h₂ : γ ∩ dnfClass u' 𝒱' ⊆ ψ) :
    γ ∩ dnfClass (Fin.append u u') (Fin.append 𝒱 𝒱') ⊆ ψ :=
  ctxOrE_of_subset_union (dnfClass_append u 𝒱 u' 𝒱').subset h₁ h₂

end SuFunctor.Universe.General
