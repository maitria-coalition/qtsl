import SuFunctor.Universe.TransportCitizenship

/-! # Coupled DNF presentations: atoms, transport, and the model-class
structure theorem

The constructible normal form of the spec algebra, as *data*: a *spec
atom* is a safety floor together with a finite liveness family that
always contains the top penalty (the properness demand — the empty
liveness slot is unrepresentable, and every atom demands at least
existence); a *coupled DNF* is a finite family of atoms.  Presentations,
not classes: the class semantics is the model class of an atom (the
systems satisfying its coupled judgment) and the union of those over a
DNF's atoms — so citizenship of the semantics is a property the
presentation *carries* rather than one to be re-proved per fibre
operation.

This module is carrier-generic (`K` an arbitrary type; penalties are
`K → ℝ≥0∞`, the order-theoretic stratum of the coupled judgment).  Its
contents:

* **Atom transport is precomposition, atom-wise** (`SpecAtom.comap`):
  pull the floor and each mark along a carrier map.  The properness
  mark is a fixed point of every transport, so the option-A shape is
  preserved by construction; so is finiteness.  Functoriality is
  definitional (`comap_id`, `comap_comp`).
* **The judgment reads bottom the properness way**
  (`SpecAtom.not_coupledSat_top`, `SpecDnf.top_notMem_modelClass`): the
  inconsistent system satisfies no atom and belongs to no DNF's model
  class — ex falso inverts structurally, because every liveness slot is
  nonempty by construction.
* **Judgment invariance along surjections** (`coupledSat_comap_iff`):
  precomposition with a surjective carrier map changes no verdict of
  the coupled judgment.  (The pushforward instance of this statement on
  the probability carrier is `coupledSat_pullPen_iff`; this is the same
  fact with the carrier map abstract.)
* **The model-class structure theorem** (`image_comap_modelClass`):
  along a surjective carrier map, the precomposition image of an atom's
  model class is exactly the model class of the transported atom
  intersected with the *range* of precomposition — the functions
  factoring through the map, i.e. the fibre-constant ones.  This is the
  model-space face of the hyperspace structure theorem
  (`transportClass_crescentClass`), with range membership playing the
  saturation role.  Surjectivity is consumed at exactly one step (the
  forward inclusion's dip-witness production); the reverse inclusion is
  unconditional, by the repair `σ ⊔ u` (join the candidate with the
  floor: safety is restored off the range, and every dip survives
  because the floor sits strictly below the mark at the dip point).
* **Both factors of the structure theorem are exact**: along a
  non-surjective map the image escapes the transported atom's model
  class outright (`exists_image_modelClass_not_subset` — the pulled
  mark degenerates to the zero penalty, which nothing dips under), and
  along a surjective map the transported class contains
  non-fibre-constant models outside the image
  (`exists_modelClass_comap_not_subset_image`).
* **The compositor's faces, separated**: pointwise sums of pulled
  floors compose safety unconditionally (`add_comp_safety_le`), the
  body-level face of the composite floor is the radial grade product
  (`compile_pullPen_add_pullPen`, on the finite probability carrier) —
  and the liveness face is a genuine design seam, recorded as a
  theorem (`exists_coupledSat_add_fails`): models of two atoms need
  not compose to a model of the pairwise atom, even along identity
  transports, because one component's dip is destroyed by the other's
  cost.
* **Citizenship, by construction** (finite probability carrier):
  the hyperspace class of a presented DNF — the union of its atoms'
  crescents — is constructible
  (`SpecDnf.isConstructibleUnion_crescentClass`), with *only*
  semicontinuity hypotheses: the finiteness that constructibility
  needs is carried by the presentation.  The judgment transports to
  hyperspace membership atom-for-atom
  (`SpecDnf.compileNC_mem_crescentClass_iff`).
-/

namespace SuFunctor.Universe

open scoped ENNReal
open TopologicalSpace

universe u

/-! ## Spec atoms and coupled DNFs, as presentations -/

/-- A spec atom over a carrier `K`: a safety floor and a finite
liveness family containing the top penalty.  The two structural fields
are the presentation discipline: finiteness is what constructibility of
the semantics consumes, and membership of the properness demand (the
liveness slot is never empty; every spec demands at least existence)
is the option-A shape of the judgment. -/
structure SpecAtom (K : Type u) : Type u where
  /-- The safety floor: the ∀-face of the coupled judgment. -/
  floor : K → ℝ≥0∞
  /-- The liveness family: the ∃-face, one dip demanded per mark. -/
  marks : Set (K → ℝ≥0∞)
  /-- The liveness family is finite. -/
  finite_marks : marks.Finite
  /-- The liveness family contains the properness demand. -/
  top_mem : ⊤ ∈ marks

namespace SpecAtom

variable {K K₁ K₂ K₃ : Type u}

theorem ext {a b : SpecAtom K} (hf : a.floor = b.floor)
    (hm : a.marks = b.marks) : a = b := by
  cases a; cases b
  cases hf; cases hm
  rfl

/-- The liveness family of an atom is nonempty: the properness demand
is always in it. -/
theorem marks_nonempty (a : SpecAtom K) : a.marks.Nonempty :=
  ⟨⊤, a.top_mem⟩

/-- Atom transport along a carrier map, contravariantly: precompose
the floor and each mark.  The properness mark is a fixed point of
every transport, and finiteness is preserved, so transported atoms are
atoms — by construction. -/
def comap (g : K₁ → K₂) (a : SpecAtom K₂) : SpecAtom K₁ where
  floor := a.floor ∘ g
  marks := (· ∘ g) '' a.marks
  finite_marks := a.finite_marks.image _
  top_mem := ⟨⊤, a.top_mem, rfl⟩

@[simp] theorem comap_floor (g : K₁ → K₂) (a : SpecAtom K₂) :
    (a.comap g).floor = a.floor ∘ g := rfl

@[simp] theorem comap_marks (g : K₁ → K₂) (a : SpecAtom K₂) :
    (a.comap g).marks = (· ∘ g) '' a.marks := rfl

@[simp] theorem comap_id (a : SpecAtom K) : a.comap id = a := by
  apply ext
  · rfl
  · rw [comap_marks]
    exact Set.image_id _

theorem comap_comp (g₁ : K₁ → K₂) (g₂ : K₂ → K₃) (a : SpecAtom K₃) :
    (a.comap g₂).comap g₁ = a.comap (g₂ ∘ g₁) := by
  apply ext
  · rfl
  · rw [comap_marks, comap_marks, comap_marks, Set.image_image]
    rfl

/-- The model class of an atom: the systems satisfying its coupled
judgment.  The semantics of the presentation. -/
def modelClass (a : SpecAtom K) : Set (K → ℝ≥0∞) :=
  {σ | CoupledSat σ a.floor a.marks}

@[simp] theorem mem_modelClass_iff {a : SpecAtom K} {σ : K → ℝ≥0∞} :
    σ ∈ a.modelClass ↔ CoupledSat σ a.floor a.marks :=
  Iff.rfl

/-- **Ex falso inverts, structurally**: the inconsistent system
satisfies no atom — under the option-A shape every liveness slot is
nonempty, so this holds with no side condition. -/
theorem not_coupledSat_top (a : SpecAtom K) :
    ¬ CoupledSat (⊤ : K → ℝ≥0∞) a.floor a.marks :=
  not_coupledSat_top_system a.marks_nonempty

end SpecAtom

/-- A coupled DNF over a carrier: a finite family of spec atoms.  The
constructible normal form of the spec algebra, as data. -/
structure SpecDnf (K : Type u) : Type u where
  /-- The disjuncts. -/
  atoms : Set (SpecAtom K)
  /-- The disjunct family is finite. -/
  finite_atoms : atoms.Finite

namespace SpecDnf

variable {K K₁ K₂ K₃ : Type u}

theorem ext {D E : SpecDnf K} (h : D.atoms = E.atoms) : D = E := by
  cases D; cases E
  cases h
  rfl

/-- DNF transport: atom transport, disjunct-wise. -/
def comap (g : K₁ → K₂) (D : SpecDnf K₂) : SpecDnf K₁ where
  atoms := SpecAtom.comap g '' D.atoms
  finite_atoms := D.finite_atoms.image _

@[simp] theorem comap_atoms (g : K₁ → K₂) (D : SpecDnf K₂) :
    (D.comap g).atoms = SpecAtom.comap g '' D.atoms := rfl

@[simp] theorem comap_id (D : SpecDnf K) : D.comap id = D := by
  apply ext
  rw [comap_atoms]
  have h : SpecAtom.comap (id : K → K) = id := funext fun a => a.comap_id
  rw [h, Set.image_id]

theorem comap_comp (g₁ : K₁ → K₂) (g₂ : K₂ → K₃) (D : SpecDnf K₃) :
    (D.comap g₂).comap g₁ = D.comap (g₂ ∘ g₁) := by
  apply ext
  rw [comap_atoms, comap_atoms, comap_atoms, Set.image_image]
  exact Set.image_congr fun a _ => a.comap_comp g₁ g₂

/-- The model class of a DNF: the union of its disjuncts' model
classes — the disjunction is plain union, per the forcing theorems of
the elimination-rule stratum. -/
def modelClass (D : SpecDnf K) : Set (K → ℝ≥0∞) :=
  ⋃ a ∈ D.atoms, a.modelClass

theorem mem_modelClass_iff {D : SpecDnf K} {σ : K → ℝ≥0∞} :
    σ ∈ D.modelClass ↔ ∃ a ∈ D.atoms, CoupledSat σ a.floor a.marks := by
  simp [modelClass]

/-- The presentation order is sound for the semantic order: more
disjuncts, more models. -/
theorem modelClass_mono {D E : SpecDnf K} (h : D.atoms ⊆ E.atoms) :
    D.modelClass ⊆ E.modelClass :=
  Set.biUnion_subset_biUnion_left h

/-- The inconsistent system belongs to no DNF's model class: the
bottom of the judgment reads the properness way, structurally. -/
theorem top_notMem_modelClass (D : SpecDnf K) :
    (⊤ : K → ℝ≥0∞) ∉ D.modelClass := by
  rw [mem_modelClass_iff]
  rintro ⟨a, -, hsat⟩
  exact a.not_coupledSat_top hsat

end SpecDnf

/-! ## Transport of the judgment, and the model-class structure theorem -/

section Transport

variable {K₁ K₂ : Type u}

/-- Dips transport along surjective carrier maps, in both directions:
the forward direction is unconditional (the image point witnesses),
the reverse consumes surjectivity (the dip witness needs a preimage).
The generic escape-face fact. -/
theorem dip_comap_iff {g : K₁ → K₂} (hg : Function.Surjective g)
    {σ v : K₂ → ℝ≥0∞} : Dip (σ ∘ g) (v ∘ g) ↔ Dip σ v := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨g x, hx⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨x, hy⟩

/-- **Judgment invariance along surjections**: precomposition with a
surjective carrier map changes no verdict of the coupled judgment.
(The pushforward instance on the probability carrier is
`coupledSat_pullPen_iff`; here the carrier map is abstract.) -/
theorem coupledSat_comap_iff {g : K₁ → K₂} (hg : Function.Surjective g)
    {σ u : K₂ → ℝ≥0∞} {𝒱 : Set (K₂ → ℝ≥0∞)} :
    CoupledSat (σ ∘ g) (u ∘ g) ((· ∘ g) '' 𝒱) ↔ CoupledSat σ u 𝒱 := by
  constructor
  · rintro ⟨hsafe, hlive⟩
    refine ⟨fun y => ?_, fun v hv => ?_⟩
    · obtain ⟨x, rfl⟩ := hg y
      exact hsafe x
    · exact (dip_comap_iff hg).mp (hlive (v ∘ g) ⟨v, hv, rfl⟩)
  · rintro ⟨hsafe, hlive⟩
    refine ⟨fun x => hsafe (g x), ?_⟩
    rintro v' ⟨v, hv, rfl⟩
    exact (dip_comap_iff hg).mpr (hlive v hv)

/-- **The model-class structure theorem**: along a surjective carrier
map, the precomposition image of an atom's model class is exactly the
model class of the transported atom, intersected with the range of
precomposition (the fibre-constant functions — the model-space face of
the saturation factor).  Surjectivity is consumed at exactly one step,
the forward inclusion's dip-witness production; the reverse inclusion
is unconditional, by the repair `σ ⊔ u`. -/
theorem image_comap_modelClass {g : K₁ → K₂} (hg : Function.Surjective g)
    (u : K₂ → ℝ≥0∞) (𝒱 : Set (K₂ → ℝ≥0∞)) :
    (· ∘ g) '' {σ | CoupledSat σ u 𝒱}
      = {τ | CoupledSat τ (u ∘ g) ((· ∘ g) '' 𝒱)}
        ∩ Set.range (· ∘ g) := by
  ext τ
  constructor
  · rintro ⟨σ, ⟨hsafe, hlive⟩, rfl⟩
    refine ⟨⟨fun x => hsafe (g x), ?_⟩, σ, rfl⟩
    rintro v' ⟨v, hv, rfl⟩
    obtain ⟨y, hy⟩ := hlive v hv
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨x, hy⟩
  · rintro ⟨⟨hsafe, hlive⟩, σ', rfl⟩
    refine ⟨σ' ⊔ u, ⟨le_sup_right, fun v hv => ?_⟩, funext fun x => ?_⟩
    · obtain ⟨x, hx⟩ := hlive (v ∘ g) ⟨v, hv, rfl⟩
      refine ⟨g x, ?_⟩
      have h₁ : σ' (g x) < v (g x) := hx
      have h₂ : u (g x) < v (g x) := lt_of_le_of_lt (hsafe x) hx
      simpa [Pi.sup_apply] using sup_lt_iff.mpr ⟨h₁, h₂⟩
    · show (σ' ⊔ u) (g x) = σ' (g x)
      rw [Pi.sup_apply]
      exact sup_eq_left.mpr (hsafe x)

/-- The atom form of the structure theorem. -/
theorem SpecAtom.image_comap_modelClass {g : K₁ → K₂}
    (hg : Function.Surjective g) (a : SpecAtom K₂) :
    (· ∘ g) '' a.modelClass
      = (a.comap g).modelClass ∩ Set.range (· ∘ g) :=
  _root_.SuFunctor.Universe.image_comap_modelClass hg a.floor a.marks

/-- The DNF form of the structure theorem: unions distribute through
both the image and the range intersection, so the disjunct-wise
operation presents no inflated join at the transport seam. -/
theorem SpecDnf.image_comap_modelClass {g : K₁ → K₂}
    (hg : Function.Surjective g) (D : SpecDnf K₂) :
    (· ∘ g) '' D.modelClass
      = (D.comap g).modelClass ∩ Set.range (· ∘ g) := by
  rw [SpecDnf.modelClass, Set.image_iUnion₂, SpecDnf.modelClass,
    SpecDnf.comap_atoms, Set.biUnion_image, Set.iUnion₂_inter]
  exact Set.iUnion₂_congr fun a ha => a.image_comap_modelClass hg

/-- The lax comparison direction, atom form: image-transported models
model the transported atom (surjective stratum). -/
theorem SpecAtom.image_modelClass_subset {g : K₁ → K₂}
    (hg : Function.Surjective g) (a : SpecAtom K₂) :
    (· ∘ g) '' a.modelClass ⊆ (a.comap g).modelClass := by
  rw [a.image_comap_modelClass hg]
  exact Set.inter_subset_left

/-- The lax comparison direction, DNF form. -/
theorem SpecDnf.image_modelClass_subset {g : K₁ → K₂}
    (hg : Function.Surjective g) (D : SpecDnf K₂) :
    (· ∘ g) '' D.modelClass ⊆ (D.comap g).modelClass := by
  rw [D.image_comap_modelClass hg]
  exact Set.inter_subset_left

end Transport

/-! ## Both factors of the structure theorem are exact -/

section Seam

/-- **Escape witnesses die outside the range**: along a non-surjective
carrier map the image-transported model class escapes the transported
atom's model class outright.  The mechanism is the exact-stratum
mirror of the hyperspace seam witness: the pulled liveness mark
degenerates to the zero penalty, which nothing dips under — the
transported atom is unsatisfiable while the transported image is
inhabited. -/
theorem exists_image_modelClass_not_subset :
    ∃ (g : Unit → Bool) (u : Bool → ℝ≥0∞) (𝒱 : Set (Bool → ℝ≥0∞)),
      ⊤ ∈ 𝒱 ∧ 𝒱.Finite ∧
      ¬ ((· ∘ g) '' {σ | CoupledSat σ u 𝒱}
          ⊆ {τ | CoupledSat τ (u ∘ g) ((· ∘ g) '' 𝒱)}) := by
  classical
  set v : Bool → ℝ≥0∞ := fun b => if b then 0 else ⊤ with hv
  refine ⟨fun _ => true, 0, {v, ⊤}, Or.inr rfl,
    ((Set.finite_singleton _).insert _), fun hsub => ?_⟩
  have hzero : (fun _ => (0 : ℝ≥0∞)) ∈ (· ∘ (fun _ : Unit => true)) ''
      {σ | CoupledSat σ 0 {v, ⊤}} := by
    refine ⟨0, ⟨le_rfl, ?_⟩, rfl⟩
    rintro w (rfl | hw)
    · exact ⟨false, by simp [hv]⟩
    · rw [Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨true, by simp⟩
  have hpull : v ∘ (fun _ : Unit => true) = 0 := by
    funext x
    simp [hv]
  refine SuFunctor.Universe.not_coupledSat_of_zero_mem
    (σ := fun _ => (0 : ℝ≥0∞))
    (u := (0 : Bool → ℝ≥0∞) ∘ (fun _ : Unit => true))
    (𝒱 := (· ∘ (fun _ : Unit => true)) '' {v, ⊤}) ?_ (hsub hzero)
  exact ⟨v, Or.inl rfl, hpull⟩

/-- **The range factor is exact**: along a surjective (non-injective)
carrier map, the transported atom's model class contains models that
are not fibre-constant, hence outside the image — the structure
theorem's intersection cannot be dropped. -/
theorem exists_modelClass_comap_not_subset_image :
    ∃ (g : Bool → Unit) (u : Unit → ℝ≥0∞) (𝒱 : Set (Unit → ℝ≥0∞)),
      Function.Surjective g ∧ ⊤ ∈ 𝒱 ∧
      ¬ ({τ | CoupledSat τ (u ∘ g) ((· ∘ g) '' 𝒱)}
          ⊆ (· ∘ g) '' {σ | CoupledSat σ u 𝒱}) := by
  classical
  refine ⟨fun _ => Unit.unit, 0, {⊤}, fun y => ⟨true, rfl⟩, rfl,
    fun hsub => ?_⟩
  set τ : Bool → ℝ≥0∞ := fun b => if b then 0 else ⊤ with hτ
  have hmem : τ ∈ {τ' | CoupledSat τ'
      ((0 : Unit → ℝ≥0∞) ∘ (fun _ => Unit.unit))
      ((· ∘ (fun _ : Bool => Unit.unit)) '' {⊤})} := by
    refine ⟨pi_zero_le τ, ?_⟩
    rintro w ⟨w', hw', rfl⟩
    rw [Set.mem_singleton_iff] at hw'
    subst hw'
    exact ⟨true, by simp [hτ]⟩
  obtain ⟨σ, -, heq⟩ := hsub hmem
  have h₁ : σ Unit.unit = 0 := by
    have := congrFun heq true
    simpa [hτ] using this
  have h₂ : σ Unit.unit = ⊤ := by
    have := congrFun heq false
    simpa [hτ] using this
  rw [h₁] at h₂
  exact ENNReal.zero_ne_top h₂

end Seam

/-! ## The compositor's faces, separated -/

section Compositor

variable {K K₁ K₂ : Type u}

/-- The safety face composes unconditionally: pointwise sums of pulled
floors dominate pointwise sums of pulled models. -/
theorem add_comp_safety_le (g₁ : K → K₁) (g₂ : K → K₂)
    {u₁ σ₁ : K₁ → ℝ≥0∞} {u₂ σ₂ : K₂ → ℝ≥0∞}
    (h₁ : u₁ ≤ σ₁) (h₂ : u₂ ≤ σ₂) :
    (u₁ ∘ g₁) + (u₂ ∘ g₂) ≤ (σ₁ ∘ g₁) + (σ₂ ∘ g₂) :=
  fun x => add_le_add (h₁ (g₁ x)) (h₂ (g₂ x))

/-- **The liveness face is a design seam, not a theorem**: models of
two atoms need not compose to a model of the pairwise atom — one
component's dip is destroyed by the other component's cost, already
along identity transports.  (The witnesses: the zero system dips under
the unit mark, but the composite system pays the partner's unit floor
everywhere, and the dip is gone.)  The pairwise compositor is sound on
the safety face (`add_comp_safety_le`) and at the body level
(`compile_pullPen_add_pullPen`); which liveness family it should carry
is a semantics-design question, deliberately left open. -/
theorem exists_coupledSat_add_fails :
    ∃ (σ₁ σ₂ u₁ u₂ : Unit → ℝ≥0∞) (𝒱₁ 𝒱₂ : Set (Unit → ℝ≥0∞)),
      ⊤ ∈ 𝒱₁ ∧ ⊤ ∈ 𝒱₂ ∧
      CoupledSat σ₁ u₁ 𝒱₁ ∧ CoupledSat σ₂ u₂ 𝒱₂ ∧
      ¬ CoupledSat (σ₁ + σ₂) (u₁ + u₂) (𝒱₁ ∪ 𝒱₂) := by
  refine ⟨0, 1, 0, 1, {1, ⊤}, {⊤}, Or.inr rfl, rfl, ?_, ?_, ?_⟩
  · refine ⟨le_rfl, ?_⟩
    rintro w (rfl | hw)
    · exact ⟨Unit.unit, by simp⟩
    · rw [Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨Unit.unit, by simp⟩
  · refine ⟨le_rfl, ?_⟩
    rintro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨Unit.unit, by simp⟩
  · rintro ⟨-, hlive⟩
    obtain ⟨x, hx⟩ := hlive 1 (Or.inl (Or.inl rfl))
    simp at hx

/-- **The body-level face of the composite floor is the radial grade
product** (finite probability carrier): the body of a sum of pulled
penalties is the radial product of the pulled bodies — the two landed
dictionaries composed. -/
theorem compile_pullPen_add_pullPen {V W₁ W₂ : Type*} [Fintype V]
    [Nonempty V] [Fintype W₁] [Fintype W₂] (j₁ : V → W₁) (j₂ : V → W₂)
    (u₁ : ProbPenalty W₁) (u₂ : ProbPenalty W₂) :
    compile (pullPen j₁ u₁ + pullPen j₂ u₂)
      = radProd (BelState.push j₁ ⁻¹' compile u₁)
          (BelState.push j₂ ⁻¹' compile u₂) := by
  rw [compile_add_radProd, compile_pullPen, compile_pullPen]

end Compositor

/-! ## Citizenship, by construction -/

/-- The empty class is constructible: the empty union. -/
theorem isConstructibleUnion_empty {X : Type*} [TopologicalSpace X] :
    IsConstructibleUnion (∅ : Set X) :=
  ⟨0, Fin.elim0, fun i => i.elim0, by simp⟩

/-- Finite unions of locally closed classes are constructible —
the finite-family form of `IsConstructibleUnion.union`. -/
theorem isConstructibleUnion_biUnion_finset {X β : Type*}
    [TopologicalSpace X] (t : Finset β) (f : β → Set X)
    (hf : ∀ b ∈ t, IsLocallyClosed (f b)) :
    IsConstructibleUnion (⋃ b ∈ t, f b) := by
  classical
  revert hf
  refine Finset.induction_on t
    (fun _ => by simpa using isConstructibleUnion_empty) ?_
  intro a s ha ih hf
  rw [Finset.set_biUnion_insert]
  exact (IsLocallyClosed.isConstructibleUnion
      (hf a (Finset.mem_insert_self a s))).union
    (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

section Citizenship

variable {V : Type*} [Fintype V]

/-- The hyperspace class of a presented DNF over the probability
carrier: the union of its atoms' crescents. -/
def SpecDnf.crescentClass (D : SpecDnf (ProbState V)) :
    Set (NonemptyCompacts (BelState V)) :=
  ⋃ a ∈ D.atoms, _root_.SuFunctor.Universe.crescentClass a.floor a.marks

/-- **Citizenship, by construction**: the hyperspace class of a
presented DNF is constructible, under semicontinuity hypotheses only —
the finiteness that constructibility consumes (of the disjunct family,
and of each liveness family) is carried by the presentation. -/
theorem SpecDnf.isConstructibleUnion_crescentClass
    (D : SpecDnf (ProbState V))
    (hfloor : ∀ a ∈ D.atoms, LowerSemicontinuous a.floor)
    (hmarks : ∀ a ∈ D.atoms, ∀ v ∈ a.marks, LowerSemicontinuous v) :
    IsConstructibleUnion D.crescentClass := by
  classical
  have h : D.crescentClass
      = ⋃ a ∈ D.finite_atoms.toFinset,
          SuFunctor.Universe.crescentClass a.floor a.marks := by
    ext L
    simp [SpecDnf.crescentClass, Set.Finite.mem_toFinset]
  rw [h]
  refine isConstructibleUnion_biUnion_finset _ _ fun a ha => ?_
  have ha' : a ∈ D.atoms := D.finite_atoms.mem_toFinset.mp ha
  exact isLocallyClosed_crescentClass (hfloor a ha') a.finite_marks
    (hmarks a ha')

/-- **The judgment transports to hyperspace membership, atom for
atom**: a citizen's body lies in a presented DNF's class iff the
citizen models the DNF. -/
theorem SpecDnf.compileNC_mem_crescentClass_iff [Nonempty V]
    {σ : ProbPenalty V} (hσ : LowerSemicontinuous σ)
    (D : SpecDnf (ProbState V)) :
    compileNC σ hσ ∈ D.crescentClass ↔ σ ∈ D.modelClass := by
  rw [SpecDnf.mem_modelClass_iff]
  simp only [SpecDnf.crescentClass, Set.mem_iUnion, exists_prop]
  exact exists_congr fun a => and_congr_right fun _ =>
    _root_.SuFunctor.Universe.compileNC_mem_crescentClass_iff hσ

end Citizenship

end SuFunctor.Universe
