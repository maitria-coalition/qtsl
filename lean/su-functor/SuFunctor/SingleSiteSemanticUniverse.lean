import SuFunctor.Plain.SpecFunctor
import SuFunctor.Plain.Seam
import SuFunctor.Universe.SpecDnf
import DoubleCat.Opfibration

/-! # The single-site semantic universe

The single-site total of the spec tier — the site-blind construction
generalized by the full `SemanticUniverse`
(`SuFunctor.Spacetime.Universe`), which iterates this total over the
profiled wiring base and recovers it per site through the
constant-profile embedding (`constProfile`, per-site conservativity).
Over the wiring base in
state-family presentation (`DoubleCat.WireSpan`), assign to each
interface the **coupled DNF presentations** over its state space —
finite families of spec atoms (safety floor + finite liveness family
containing the properness demand), the constructible normal form of
the spec algebra as *data*; to each wiring pattern the DNF
presentations over its apex.  Transport is **atom-level**, disjunct-
wise (pull the floor and each mark — the canonical fibre operation,
judgment-invariant along surjections); the compositor is **atom-level
pairing** (floors compose by pushforward-then-add, liveness families
by pulled union), and the unit is the vacuous atom `(0, {⊤})` — the
austere unit and the properness demand are the *same atom*, which is
exactly why the unit laws close on the nose: every transport fixes the
properness mark, and every atom's own marks absorb it.

`SingleSiteSemanticUniverse` is the plain double Grothendieck total of this
functor: objects are interfaces with a designated spec presentation;
loose arrows are wiring patterns with an apex presentation; systems
enter as ideal points (singleton presentations of singleton-class
atoms), and the fibres present constructible hyperspace classes at
the finite stratum (`SuFunctor.Universe.SpecDnf`, citizenship by
construction; the finite-carrier reading crosses the seam of
`SuFunctor.Plain.Seam`).  The strict projection to the wiring base is
a **discrete double opfibration**, by one-line consumption of the
generic theorem — the lifting calculus never inspects fibre internals.

Relation to the image-level functor (`SuFunctor.Plain.specFunctor`,
the arbitrary-class tier, which remains as the generality reservoir):
this functor **refines** it.  Componentwise, on the surjective
sub-base, the image-level transport of the semantics is exactly the
semantics of the atom-level transport cut to the transport's range
(`specMap_modelClass_eq` — the model-class structure theorem
instantiated at the wiring base), and the inclusion half is the
comparison 2-cell in the inclusion-ordered fibres.  Away from the
surjective stratum the two genuinely part company, and the atom-level
operation is the one under which the fibres keep their constructible
presentations.

Convexity plays no role at this tier: citizenship of a fibre is
*constructibility* of its presented class (finite unions of locally
closed crescents), not convexity — atoms, presentations, and transport
are all indifferent to convex structure.
-/

namespace SuFunctor

noncomputable section

open CategoryTheory CategoryTheory.WireSpan PseudoDoubleCategoryStruct
open SuFunctor.Plain SuFunctor.Universe
open scoped NNReal ENNReal

universe u

/-! ## Pushforward surjectivity at the exact stratum -/

/-- Pushforward of joints along a surjective carrier map is
surjective: push the section forward — no weight surgery needed, since
joints exist over every carrier. -/
theorem Plain.Joint.push_surjective {X Y : Type u} {h : X → Y}
    (hh : Function.Surjective h) :
    Function.Surjective (Joint.push h) := by
  obtain ⟨s, hs⟩ := hh.hasRightInverse
  intro ν
  refine ⟨ν.push s, ?_⟩
  rw [Joint.push_push]
  have hid : h ∘ s = id := funext fun y => hs y
  rw [hid, Joint.push_id]

/-! ## Atom and DNF transport at the exact stratum -/

variable {El : Type u}

/-- Atom transport along a state map, contravariantly: pull the floor
and each mark along pushforward of joints.  (Along a backward wire-map
state map this is tight transport; along a backward apex-state map it
is cell transport.) -/
def atomPull {X Y : Type u} (h : X → Y) (a : SpecAtom (Joint Y)) :
    SpecAtom (Joint X) :=
  a.comap (Joint.push h)

@[simp] theorem atomPull_floor {X Y : Type u} (h : X → Y)
    (a : SpecAtom (Joint Y)) :
    (atomPull h a).floor = Pen.pull h a.floor := rfl

@[simp] theorem atomPull_marks {X Y : Type u} (h : X → Y)
    (a : SpecAtom (Joint Y)) :
    (atomPull h a).marks = Pen.pull h '' a.marks := rfl

theorem atomPull_id {X : Type u} (a : SpecAtom (Joint X)) :
    atomPull id a = a := by
  show a.comap (Joint.push id) = a
  have h : Joint.push (id : X → X) = id := funext fun μ => Joint.push_id μ
  rw [h, SpecAtom.comap_id]

theorem atomPull_atomPull {X Y Z : Type u} (h₁ : X → Y) (h₂ : Y → Z)
    (a : SpecAtom (Joint Z)) :
    atomPull h₁ (atomPull h₂ a) = atomPull (h₂ ∘ h₁) a := by
  show (a.comap (Joint.push h₂)).comap (Joint.push h₁)
    = a.comap (Joint.push (h₂ ∘ h₁))
  rw [SpecAtom.comap_comp]
  have h : Joint.push h₂ ∘ Joint.push h₁ = Joint.push (h₂ ∘ h₁) :=
    funext fun μ => Joint.push_push h₁ h₂ μ
  rw [h]

/-- The DNF fibre at an interface: coupled DNF presentations over its
state space. -/
abbrev DnfSpec (A : WireSpan El) : Type u := SpecDnf (Joint (states A))

/-- The DNF decorations over a wiring pattern: coupled DNF
presentations over its apex state space. -/
abbrev DnfCpl {A B : WireSpan El} (M : Pat A B) : Type u :=
  SpecDnf (Joint (Pat.Tot M))

/-- DNF transport along a state map: atom transport, disjunct-wise. -/
def dnfPull {X Y : Type u} (h : X → Y) (D : SpecDnf (Joint Y)) :
    SpecDnf (Joint X) :=
  D.comap (Joint.push h)

@[simp] theorem dnfPull_atoms {X Y : Type u} (h : X → Y)
    (D : SpecDnf (Joint Y)) :
    (dnfPull h D).atoms = atomPull h '' D.atoms := rfl

theorem dnfPull_id {X : Type u} (D : SpecDnf (Joint X)) :
    dnfPull id D = D := by
  show D.comap (Joint.push id) = D
  have h : Joint.push (id : X → X) = id := funext fun μ => Joint.push_id μ
  rw [h, SpecDnf.comap_id]

theorem dnfPull_dnfPull {X Y Z : Type u} (h₁ : X → Y) (h₂ : Y → Z)
    (D : SpecDnf (Joint Z)) :
    dnfPull h₁ (dnfPull h₂ D) = dnfPull (h₂ ∘ h₁) D := by
  show (D.comap (Joint.push h₂)).comap (Joint.push h₁)
    = D.comap (Joint.push (h₂ ∘ h₁))
  rw [SpecDnf.comap_comp]
  have h : Joint.push h₂ ∘ Joint.push h₁ = Joint.push (h₂ ∘ h₁) :=
    funext fun μ => Joint.push_push h₁ h₂ μ
  rw [h]

/-! ## The atom-level compositor and unit -/

/-- The atom-level compositor: floors compose by pushforward-then-add
(`boxplus`), liveness families by pulled union.  The properness mark
of the left component transports to the properness mark of the
composite, so option-A shape is preserved by construction. -/
def atomBoxplus {A B C : WireSpan El} {M : Pat A B} {N : Pat B C}
    (a₁ : SpecAtom (Joint (Pat.Tot M))) (a₂ : SpecAtom (Joint (Pat.Tot N))) :
    SpecAtom (Joint (Pat.Tot (Pat.comp M N))) where
  floor := boxplus a₁.floor a₂.floor
  marks := Pen.pull (Pat.compFst M N) '' a₁.marks
    ∪ Pen.pull (Pat.compSnd M N) '' a₂.marks
  finite_marks := (a₁.finite_marks.image _).union (a₂.finite_marks.image _)
  top_mem := Or.inl ⟨⊤, a₁.top_mem, rfl⟩

@[simp] theorem atomBoxplus_floor {A B C : WireSpan El} {M : Pat A B}
    {N : Pat B C} (a₁ : SpecAtom (Joint (Pat.Tot M)))
    (a₂ : SpecAtom (Joint (Pat.Tot N))) :
    (atomBoxplus a₁ a₂).floor = boxplus a₁.floor a₂.floor := rfl

@[simp] theorem atomBoxplus_marks {A B C : WireSpan El} {M : Pat A B}
    {N : Pat B C} (a₁ : SpecAtom (Joint (Pat.Tot M)))
    (a₂ : SpecAtom (Joint (Pat.Tot N))) :
    (atomBoxplus a₁ a₂).marks
      = Pen.pull (Pat.compFst M N) '' a₁.marks
        ∪ Pen.pull (Pat.compSnd M N) '' a₂.marks := rfl

/-- The unit atom: the austere unit floor with the properness demand —
the vacuous atom `(0, {⊤})`.  Under the option-A shape this is forced:
the unit must be absorbed by every atom's marks after the unitor
transport, and the properness mark is the one mark every atom carries. -/
def unitAtom (A : WireSpan El) : SpecAtom (Joint (Pat.Tot (Pat.id A))) where
  floor := unitPen A
  marks := {⊤}
  finite_marks := Set.finite_singleton _
  top_mem := rfl

/-! ## The atom-level coherence cores

Floors are the landed element cores verbatim; marks are the
definitional `Tot`-calculus read through `Pen.pull_pull`, with the
unit laws consuming the option-A absorption (`⊤ ∈ marks`). -/

section Cores

variable {A B C D A' B' C' : WireSpan El}

/-- Naturality core, atom level. -/
theorem atomPull_tot_hComp_boxplus {M₁ : Pat A B} {M₂ : Pat B C}
    {N₁ : Pat A' B'} {N₂ : Pat B' C'} {φ : A ⟶ A'} {γ : B ⟶ B'}
    {ψ : C ⟶ C'} (α : PatCell M₁ N₁ φ γ) (β : PatCell M₂ N₂ γ ψ)
    (a₁ : SpecAtom (Joint (Pat.Tot M₁))) (a₂ : SpecAtom (Joint (Pat.Tot M₂))) :
    atomPull (PatCell.tot
        (PseudoDoubleCategoryStruct.hComp (C := WireSpan El) α β))
        (atomBoxplus a₁ a₂) =
      atomBoxplus (atomPull (PatCell.tot α) a₁)
        (atomPull (PatCell.tot β) a₂) := by
  apply SpecAtom.ext
  · exact pull_tot_hComp_boxplus α β a₁.floor a₂.floor
  · show Pen.pull (PatCell.tot
        (PseudoDoubleCategoryStruct.hComp (C := WireSpan El) α β)) ''
        (Pen.pull (Pat.compFst M₁ M₂) '' a₁.marks
          ∪ Pen.pull (Pat.compSnd M₁ M₂) '' a₂.marks)
      = Pen.pull (Pat.compFst N₁ N₂) '' (Pen.pull (PatCell.tot α) '' a₁.marks)
        ∪ Pen.pull (Pat.compSnd N₁ N₂) '' (Pen.pull (PatCell.tot β) '' a₂.marks)
    simp only [Set.image_union, Set.image_image]
    refine congrArg₂ (· ∪ ·) ?_ ?_
    · exact Set.image_congr fun v _ => by
        rw [Pen.pull_pull, Pen.pull_pull]
        rfl
    · exact Set.image_congr fun v _ => by
        rw [Pen.pull_pull, Pen.pull_pull]
        rfl

/-- Associativity core, atom level. -/
theorem atomPull_tot_lAssoc_boxplus (M : Pat A B) (N : Pat B C) (P : Pat C D)
    (a₁ : SpecAtom (Joint (Pat.Tot M))) (a₂ : SpecAtom (Joint (Pat.Tot N)))
    (a₃ : SpecAtom (Joint (Pat.Tot P))) :
    atomPull (PatCell.tot
        (PseudoDoubleCategoryStruct.lAssoc (C := WireSpan El) M N P))
        (atomBoxplus (atomBoxplus a₁ a₂) a₃) =
      atomBoxplus a₁ (atomBoxplus a₂ a₃) := by
  apply SpecAtom.ext
  · exact pull_tot_lAssoc_boxplus M N P a₁.floor a₂.floor a₃.floor
  · show Pen.pull (PatCell.tot
        (PseudoDoubleCategoryStruct.lAssoc (C := WireSpan El) M N P)) ''
        (Pen.pull (Pat.compFst (Pat.comp M N) P) ''
            (Pen.pull (Pat.compFst M N) '' a₁.marks
              ∪ Pen.pull (Pat.compSnd M N) '' a₂.marks)
          ∪ Pen.pull (Pat.compSnd (Pat.comp M N) P) '' a₃.marks)
      = Pen.pull (Pat.compFst M (Pat.comp N P)) '' a₁.marks
        ∪ Pen.pull (Pat.compSnd M (Pat.comp N P)) ''
            (Pen.pull (Pat.compFst N P) '' a₂.marks
              ∪ Pen.pull (Pat.compSnd N P) '' a₃.marks)
    simp only [Set.image_union, Set.image_image, Set.union_assoc]
    refine congrArg₂ (· ∪ ·) ?_ (congrArg₂ (· ∪ ·) ?_ ?_)
    · exact Set.image_congr fun v _ => by
        rw [Pen.pull_pull, Pen.pull_pull]
        rfl
    · exact Set.image_congr fun v _ => by
        rw [Pen.pull_pull, Pen.pull_pull, Pen.pull_pull]
        rfl
    · exact Set.image_congr fun v _ => by
        rw [Pen.pull_pull, Pen.pull_pull]
        rfl

/-- Left unit core, atom level: the unit atom's transported mark is
absorbed by the atom's own properness mark — the option-A absorption,
consumed here and in the right core and nowhere else. -/
theorem atomPull_tot_lLeftUnitor_boxplus (M : Pat A B)
    (a : SpecAtom (Joint (Pat.Tot M))) :
    atomPull (PatCell.tot
        (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M))
        (atomBoxplus (unitAtom A) a) = a := by
  apply SpecAtom.ext
  · exact pull_tot_lLeftUnitor_boxplus M a.floor
  · show Pen.pull (PatCell.tot
        (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M)) ''
        (Pen.pull (Pat.compFst (Pat.id A) M) '' ({⊤} : Set (Pen (Pat.Tot (Pat.id A))))
          ∪ Pen.pull (Pat.compSnd (Pat.id A) M) '' a.marks)
      = a.marks
    simp only [Set.image_union, Set.image_image, Set.image_singleton]
    have hmarks : (fun v => Pen.pull (PatCell.tot
        (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M))
          (Pen.pull (Pat.compSnd (Pat.id A) M) v)) '' a.marks = a.marks := by
      rw [show (fun v => Pen.pull (PatCell.tot
          (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M))
            (Pen.pull (Pat.compSnd (Pat.id A) M) v))
          = (id : Pen (Pat.Tot M) → Pen (Pat.Tot M)) from funext fun v => by
        rw [Pen.pull_pull]
        exact Pen.pull_id v]
      exact Set.image_id _
    rw [hmarks]
    exact Set.union_eq_self_of_subset_left
      (Set.singleton_subset_iff.mpr a.top_mem)

/-- Right unit core, atom level, dually. -/
theorem atomPull_tot_lRightUnitor_boxplus (M : Pat A B)
    (a : SpecAtom (Joint (Pat.Tot M))) :
    atomPull (PatCell.tot
        (PseudoDoubleCategoryStruct.lRightUnitor (C := WireSpan El) M))
        (atomBoxplus a (unitAtom B)) = a := by
  apply SpecAtom.ext
  · exact pull_tot_lRightUnitor_boxplus M a.floor
  · show Pen.pull (PatCell.tot
        (PseudoDoubleCategoryStruct.lRightUnitor (C := WireSpan El) M)) ''
        (Pen.pull (Pat.compFst M (Pat.id B)) '' a.marks
          ∪ Pen.pull (Pat.compSnd M (Pat.id B)) '' ({⊤} : Set (Pen (Pat.Tot (Pat.id B)))))
      = a.marks
    simp only [Set.image_union, Set.image_image, Set.image_singleton]
    have hmarks : (fun v => Pen.pull (PatCell.tot
        (PseudoDoubleCategoryStruct.lRightUnitor (C := WireSpan El) M))
          (Pen.pull (Pat.compFst M (Pat.id B)) v)) '' a.marks = a.marks := by
      rw [show (fun v => Pen.pull (PatCell.tot
          (PseudoDoubleCategoryStruct.lRightUnitor (C := WireSpan El) M))
            (Pen.pull (Pat.compFst M (Pat.id B)) v))
          = (id : Pen (Pat.Tot M) → Pen (Pat.Tot M)) from funext fun v => by
        rw [Pen.pull_pull]
        exact Pen.pull_id v]
      exact Set.image_id _
    rw [hmarks]
    exact Set.union_eq_self_of_subset_right
      (Set.singleton_subset_iff.mpr a.top_mem)

/-- The unit atom transports to the unit atom along loose-identity
cells. -/
theorem atomPull_tot_hId_unitAtom {A A' : WireSpan El} (f : A ⟶ A') :
    atomPull (PatCell.tot
        (PseudoDoubleCategoryStruct.hId (C := WireSpan El) f))
        (unitAtom A) = unitAtom A' := by
  apply SpecAtom.ext
  · rfl
  · show Pen.pull (PatCell.tot
        (PseudoDoubleCategoryStruct.hId (C := WireSpan El) f)) ''
        ({⊤} : Set (Pen (Pat.Tot (Pat.id A)))) = {⊤}
    rw [Set.image_singleton]
    rfl

end Cores

/-! ## The functor -/

/-- The object-and-tight-arrow tier: DNF presentations, transported
atom-wise along the wire map. -/
def dnfObj (El : Type u) : WireSpan El ⥤ Type u where
  obj A := SpecDnf (Joint (states A))
  map φ := TypeCat.ofHom (dnfPull (res φ))
  map_id A :=
    congrArg TypeCat.ofHom (funext fun D => by
      show dnfPull (res (𝟙 A)) D = D
      exact dnfPull_id D)
  map_comp f g :=
    congrArg TypeCat.ofHom (funext fun D => by
      show dnfPull (res (f ≫ g)) D = dnfPull (res g) (dnfPull (res f) D)
      exact (dnfPull_dnfPull (res g) (res f) D).symm)

/-- The DNF compositor: atom-level pairing, disjunct-wise. -/
def dnfBoxplus {A B C : WireSpan El} {M : Pat A B} {N : Pat B C}
    (D₁ : DnfCpl M) (D₂ : DnfCpl N) : DnfCpl (Pat.comp M N) where
  atoms := Set.image2 atomBoxplus D₁.atoms D₂.atoms
  finite_atoms := D₁.finite_atoms.image2 _ D₂.finite_atoms

/-- The DNF unit: the singleton of the unit atom. -/
def dnfUnit (A : WireSpan El) : DnfCpl (Pat.id A) where
  atoms := {unitAtom A}
  finite_atoms := Set.finite_singleton _

/-- **The DNF spec decoration functor**: a span-valued lax double
functor on the wiring base, with coupled-DNF-presentation fibres.
Every comparison datum is constructed and every coherence law is
proved, each obligation lifting disjunct-wise from the atom-level
cores — the plain double Grothendieck construction consumes this
instance as-is. -/
def dnfSpecFunctor (El : Type u) :
    SpanValued.{u + 1, u, u, u + 1, u} (WireSpan El) where
  toFunctor := dnfObj El
  mapLoose M := fun _ _ => DnfCpl M
  mapCell γ := fun _ _ 𝒰 => dnfPull (PatCell.tot γ) 𝒰
  mapCell_vId M := by
    have key : ∀ 𝒰 : DnfCpl M,
        dnfPull (PatCell.tot
          (PseudoDoubleCategoryStruct.vId (C := WireSpan El) M)) 𝒰 = 𝒰 :=
      fun 𝒰 => dnfPull_id 𝒰
    funext 𝒮 𝒯 𝒰
    exact (key 𝒰).trans (eq_of_heq (DepSpan.FamCell.heq_apply
      ((dnfObj El).map_id _) ((dnfObj El).map_id _)
      (Cell.cast_heq ((dnfObj El).map_id _).symm ((dnfObj El).map_id _).symm
        (PseudoDoubleCategoryStruct.vId (C := Type u) (fun _ _ => DnfCpl M)))
      𝒮 𝒯 𝒰)).symm
  mapCell_vComp α β := by
    have key : ∀ 𝒰,
        dnfPull (PatCell.tot
          (PseudoDoubleCategoryStruct.vComp (C := WireSpan El) α β)) 𝒰 =
          dnfPull (PatCell.tot β) (dnfPull (PatCell.tot α) 𝒰) :=
      fun 𝒰 => (dnfPull_dnfPull (PatCell.tot β) (PatCell.tot α) 𝒰).symm
    funext 𝒮 𝒯 𝒰
    rw [cast_apply_const]
    exact key 𝒰
  laxComp M N := fun _ _ s => dnfBoxplus s.2.1 s.2.2
  laxId A := fun _ _ _ => dnfUnit A
  laxComp_natural α β := by
    have key : ∀ (𝒰₁ : DnfCpl _) (𝒰₂ : DnfCpl _),
        dnfPull (PatCell.tot
            (PseudoDoubleCategoryStruct.hComp (C := WireSpan El) α β))
            (dnfBoxplus 𝒰₁ 𝒰₂) =
          dnfBoxplus (dnfPull (PatCell.tot α) 𝒰₁)
            (dnfPull (PatCell.tot β) 𝒰₂) := by
      intro 𝒰₁ 𝒰₂
      apply SpecDnf.ext
      show atomPull _ '' Set.image2 atomBoxplus 𝒰₁.atoms 𝒰₂.atoms
        = Set.image2 atomBoxplus (atomPull _ '' 𝒰₁.atoms)
            (atomPull _ '' 𝒰₂.atoms)
      rw [Set.image_image2, Set.image2_image_left, Set.image2_image_right]
      exact Set.image2_congr fun a₁ _ a₂ _ =>
        atomPull_tot_hComp_boxplus α β a₁ a₂
    exact (Cell.eq_cast_iff_heq (C := Type u)).mpr
      (DepSpan.FamCell.heq_of_apply (by simp) (by simp)
        fun 𝒮 𝒱 s => heq_of_eq (key s.2.1 s.2.2))
  laxId_natural f := by
    have key : dnfPull (PatCell.tot
        (PseudoDoubleCategoryStruct.hId (C := WireSpan El) f))
        (dnfUnit _) = dnfUnit _ := by
      apply SpecDnf.ext
      show atomPull _ '' {unitAtom _} = {unitAtom _}
      rw [Set.image_singleton, atomPull_tot_hId_unitAtom]
    exact (Cell.eq_cast_iff_heq (C := Type u)).mpr
      (DepSpan.FamCell.heq_of_apply (by simp) (by simp)
        fun 𝒮 𝒮' e => heq_of_eq key)
  laxComp_assoc M N P := by
    have key : ∀ (𝒰₁ : DnfCpl M) (𝒰₂ : DnfCpl N) (𝒰₃ : DnfCpl P),
        dnfPull (PatCell.tot
            (PseudoDoubleCategoryStruct.lAssoc (C := WireSpan El) M N P))
            (dnfBoxplus (dnfBoxplus 𝒰₁ 𝒰₂) 𝒰₃) =
          dnfBoxplus 𝒰₁ (dnfBoxplus 𝒰₂ 𝒰₃) := by
      intro 𝒰₁ 𝒰₂ 𝒰₃
      apply SpecDnf.ext
      show atomPull _ '' Set.image2 atomBoxplus
          (Set.image2 atomBoxplus 𝒰₁.atoms 𝒰₂.atoms) 𝒰₃.atoms
        = Set.image2 atomBoxplus 𝒰₁.atoms
            (Set.image2 atomBoxplus 𝒰₂.atoms 𝒰₃.atoms)
      rw [Set.image_image2]
      exact Set.image2_assoc fun a₁ a₂ a₃ =>
        atomPull_tot_lAssoc_boxplus M N P a₁ a₂ a₃
    exact (Cell.eq_cast_iff_heq (C := Type u)).mpr
      (DepSpan.FamCell.heq_of_apply (by simp) (by simp)
        fun 𝒮 𝒱 s => heq_of_eq (key s.2.1.2.1 s.2.1.2.2 s.2.2))
  laxComp_leftUnitor M := by
    have key : ∀ 𝒰 : DnfCpl M,
        dnfPull (PatCell.tot
            (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M))
            (dnfBoxplus (dnfUnit _) 𝒰) = 𝒰 := by
      intro 𝒰
      apply SpecDnf.ext
      show atomPull _ '' Set.image2 atomBoxplus {unitAtom _} 𝒰.atoms
        = 𝒰.atoms
      rw [Set.image2_singleton_left, ← Set.image_comp]
      have h : atomPull (PatCell.tot
            (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M)) ∘
            atomBoxplus (unitAtom _) = id :=
        funext fun a => atomPull_tot_lLeftUnitor_boxplus M a
      rw [h, Set.image_id]
    exact (Cell.eq_cast_iff_heq (C := Type u)).mpr
      (DepSpan.FamCell.heq_of_apply (by simp) (by simp)
        fun 𝒮 𝒯 s => heq_of_eq (by
          obtain ⟨𝒮', e, 𝒰⟩ := s
          obtain ⟨⟨rfl⟩⟩ := e
          exact key 𝒰))
  laxComp_rightUnitor M := by
    have key : ∀ 𝒰 : DnfCpl M,
        dnfPull (PatCell.tot
            (PseudoDoubleCategoryStruct.lRightUnitor (C := WireSpan El) M))
            (dnfBoxplus 𝒰 (dnfUnit _)) = 𝒰 := by
      intro 𝒰
      apply SpecDnf.ext
      show atomPull _ '' Set.image2 atomBoxplus 𝒰.atoms {unitAtom _}
        = 𝒰.atoms
      rw [Set.image2_singleton_right, ← Set.image_comp]
      have h : atomPull (PatCell.tot
            (PseudoDoubleCategoryStruct.lRightUnitor (C := WireSpan El) M)) ∘
            (fun a => atomBoxplus a (unitAtom _)) = id :=
        funext fun a => atomPull_tot_lRightUnitor_boxplus M a
      rw [h, Set.image_id]
    exact (Cell.eq_cast_iff_heq (C := Type u)).mpr
      (DepSpan.FamCell.heq_of_apply (by simp) (by simp)
        fun 𝒮 𝒯 s => heq_of_eq (by
          obtain ⟨𝒯', 𝒰, e⟩ := s
          obtain ⟨⟨rfl⟩⟩ := e
          exact key 𝒰))

/-! ## The single-site semantic universe -/

/-- **The single-site semantic universe**: the plain double
Grothendieck total of the DNF spec decoration functor.  Objects are interfaces with a
designated coupled-DNF presentation; loose arrows are wiring patterns
with an apex presentation; the fibre order (inclusion of atom
families, sound for inclusion of model classes) is the judgment layer,
carried on top of this total rather than as a second fibration. -/
abbrev SingleSiteSemanticUniverse (El : Type u) :=
  SpanValued.Grothendieck (dnfSpecFunctor El)

/-- The semantic universe is a pseudo double category, by instance
search — the plain construction consumes the functor as-is. -/
theorem singleSiteSemanticUniverse_pseudoDoubleCategory (El : Type u) :
    ∃ _ : PseudoDoubleCategory (SingleSiteSemanticUniverse El), True :=
  ⟨inferInstance, trivial⟩

/-- The strict projection of the semantic universe to the wiring
base. -/
def singleSiteUniverseProj (El : Type u) :
    LaxDoubleFunctor (SingleSiteSemanticUniverse El) (WireSpan El) :=
  SpanValued.proj (dnfSpecFunctor El)

/-- The projection is pseudo: its laxators are invertible. -/
theorem singleSiteUniverseProj_isPseudo (El : Type u) :
    (singleSiteUniverseProj El).IsPseudo :=
  SpanValued.proj_isPseudo (dnfSpecFunctor El)

/-- **The projection is a discrete double opfibration** — by one-line
consumption of the generic theorem, which never inspects fibre
internals: tight arrows and cells lift uniquely along the indexing's
own atom-level actions, and the split opcleavage is the canonical-lift
data of the covariant construction. -/
theorem singleSiteUniverseProj_discreteOpfibration (El : Type u) :
    IsDiscreteDoubleOpfibration (singleSiteUniverseProj El) :=
  SpanValued.proj_isDiscreteOpfibration (dnfSpecFunctor El)

/-! ## The comparison to the image-level functor

Componentwise content of the comparison 2-cell: on the surjective
sub-base, the image-level transport (`specMap`, the fibre operation of
`specFunctor`) of a presentation's model class is exactly the model
class of the atom-level transport cut to the transport's range — the
model-class structure theorem instantiated at the wiring base.  The
inclusion half is the 2-cell in the inclusion-ordered fibres; the new
functor refines the image-level one, never replaces it. -/

section Comparison

variable {A B : WireSpan El}

/-- Tight components, structure form. -/
theorem specMap_modelClass_eq (φ : A ⟶ B)
    (hφ : Function.Surjective (res φ)) (D : DnfSpec A) :
    specMap φ D.modelClass
      = (dnfPull (res φ) D).modelClass ∩ Set.range (Pen.pull (res φ)) :=
  SpecDnf.image_comap_modelClass (Plain.Joint.push_surjective hφ) D

/-- Tight components, inclusion form: the comparison 2-cell. -/
theorem specMap_modelClass_subset (φ : A ⟶ B)
    (hφ : Function.Surjective (res φ)) (D : DnfSpec A) :
    specMap φ D.modelClass ⊆ (dnfPull (res φ) D).modelClass :=
  SpecDnf.image_modelClass_subset (Plain.Joint.push_surjective hφ) D

/-- Cell components, structure form. -/
theorem cellMap_modelClass_eq {A' B' : WireSpan El} {M : Pat A B}
    {N : Pat A' B'} {φ : A ⟶ A'} {ψ : B ⟶ B'} (γ : PatCell M N φ ψ)
    (hγ : Function.Surjective (PatCell.tot γ)) (D : DnfCpl M) :
    Pen.pull (PatCell.tot γ) '' D.modelClass
      = (dnfPull (PatCell.tot γ) D).modelClass
        ∩ Set.range (Pen.pull (PatCell.tot γ)) :=
  SpecDnf.image_comap_modelClass (Plain.Joint.push_surjective hγ) D

/-- Cell components, inclusion form. -/
theorem cellMap_modelClass_subset {A' B' : WireSpan El} {M : Pat A B}
    {N : Pat A' B'} {φ : A ⟶ A'} {ψ : B ⟶ B'} (γ : PatCell M N φ ψ)
    (hγ : Function.Surjective (PatCell.tot γ)) (D : DnfCpl M) :
    Pen.pull (PatCell.tot γ) '' D.modelClass
      ⊆ (dnfPull (PatCell.tot γ) D).modelClass :=
  SpecDnf.image_modelClass_subset (Plain.Joint.push_surjective hγ) D

end Comparison

/-! ## The finite-stratum reading, across the seam

Over a finite carrier the exact-stratum presentations read into the
probability-carrier presentations through the landed seam equivalence
(`SuFunctor.Plain.Seam`) and the flat-stratum restriction; there the
citizenship theorem applies, and the fibres of the semantic universe
present constructible hyperspace classes. -/

section Reading

variable {V : Type u} [Fintype V]

/-- The semantic reading of an exact-stratum atom over a finite
carrier: through the seam equivalence and the flat-stratum
restriction, onto the probability carrier where the hyperspace
machinery lives. -/
def Universe.SpecAtom.probRead (a : SpecAtom (Joint V)) :
    SpecAtom (Universe.ProbState V) :=
  a.comap fun μ => jointEquivBel.symm μ.toBel

/-- The semantic reading of an exact-stratum DNF presentation. -/
def Universe.SpecDnf.probRead (D : SpecDnf (Joint V)) :
    SpecDnf (Universe.ProbState V) :=
  D.comap fun μ => jointEquivBel.symm μ.toBel

/-- **The fibres present constructible classes at the finite
stratum**: the hyperspace class of the semantic reading of any
exact-stratum presentation is constructible, under semicontinuity
hypotheses only — the finiteness constructibility consumes is carried
by the presentation, through the reading, by construction. -/
theorem Universe.SpecDnf.isConstructibleUnion_probRead
    (D : SpecDnf (Joint V))
    (hfloor : ∀ a ∈ D.probRead.atoms, LowerSemicontinuous a.floor)
    (hmarks : ∀ a ∈ D.probRead.atoms, ∀ v ∈ a.marks, LowerSemicontinuous v) :
    IsConstructibleUnion D.probRead.crescentClass :=
  D.probRead.isConstructibleUnion_crescentClass hfloor hmarks

end Reading

end

end SuFunctor
