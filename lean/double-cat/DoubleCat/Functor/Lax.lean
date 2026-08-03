import DoubleCat.Basic

/-!
# Lax double functors

A lax double functor between pseudo double categories consists of a functor
on the tight categories, an action on loose arrows and on cells preserving
tight boundaries strictly, and comparison cells (a compositor and a unit
comparison, jointly the "laxators") mediating loose composition and loose
identities, which are globular, natural, and coherent (associativity and
two unit triangles).

This is the notion of Grandis–Paré ("Adjoint for double categories", 2004)
and Cruttwell–Lambert–Pronk–Szyld ("Double fibrations", 2022, Definition
2.9); for span-valued functors it unpacks to the data used in Patterson
("Structured and decorated cospans from the viewpoint of double category
theory", 2023, §3), whose Grothendieck construction is developed in
`DoubleCat.Grothendieck`.

## Main definitions

* `CategoryTheory.LaxDoubleFunctor C D`: the structure described above.
* `CategoryTheory.LaxDoubleFunctor.id`: the identity lax double functor.

The compositor is directed `F m ⊙ F n ⟶ F (m ⊙ n)` (lax direction); a lax
double functor whose compositor and unit comparison are invertible is a
pseudo double functor (`CategoryTheory.LaxDoubleFunctor.IsPseudo`, defined
in `DoubleCat.Functor.Pseudo`).
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

universe w₁ t₁ v₁ u₁ w₂ t₂ v₂ u₂

variable (C : Type u₁) [Category.{v₁} C] [PseudoDoubleCategoryStruct C]
  [PseudoDoubleCategory C]
variable (D : Type u₂) [Category.{v₂} D] [PseudoDoubleCategoryStruct D]
  [PseudoDoubleCategory D]

/-- A lax double functor between pseudo double categories: a functor on tight
categories, an action on loose arrows and cells, and globular comparison cells
(compositor `laxComp` and unit comparison `laxId`), natural and coherent.

The direction of the comparisons is lax: `F m ⊙ F n ⟶ F (m ⊙ n)` and
`𝟙ˡ (F a) ⟶ F (𝟙ˡ a)`. -/
structure LaxDoubleFunctor extends C ⥤ D where

  /-- The action on loose arrows. -/
  mapLoose : ∀ {a b : C}, Loose a b → Loose (obj a) (obj b)

  /-- The action on cells.  Tight boundaries are preserved strictly. -/
  mapCell : ∀ {a b c d : C} {m : Loose a b} {n : Loose c d} {f : a ⟶ c}
    {g : b ⟶ d}, Cell m n f g → Cell (mapLoose m) (mapLoose n) (map f) (map g)

  /-- The action on cells preserves tight-wise identity cells. -/
  mapCell_vId : ∀ {a b : C} (m : Loose a b),
    mapCell (vId m) = Cell.cast (map_id a).symm (map_id b).symm
      (vId (mapLoose m))

  /-- The action on cells preserves tight-wise composition. -/
  mapCell_vComp : ∀ {a₁ b₁ a₂ b₂ a₃ b₃ : C}
    {m₁ : Loose a₁ b₁} {m₂ : Loose a₂ b₂} {m₃ : Loose a₃ b₃}
    {f₁ : a₁ ⟶ a₂} {g₁ : b₁ ⟶ b₂} {f₂ : a₂ ⟶ a₃} {g₂ : b₂ ⟶ b₃}
    (α : Cell m₁ m₂ f₁ g₁) (β : Cell m₂ m₃ f₂ g₂),
    mapCell (α ≫ᵥ β) = Cell.cast (map_comp f₁ f₂).symm (map_comp g₁ g₂).symm
      (mapCell α ≫ᵥ mapCell β)

  /-- The compositor: a globular comparison cell `F m ⊙ F n ⟶ F (m ⊙ n)`. -/
  laxComp : ∀ {a b c : C} (m : Loose a b) (n : Loose b c),
    Cell (mapLoose m ⊙ mapLoose n) (mapLoose (m ⊙ n)) (𝟙 (obj a)) (𝟙 (obj c))

  /-- The unit comparison: a globular cell `𝟙ˡ (F a) ⟶ F (𝟙ˡ a)`. -/
  laxId : ∀ (a : C),
    Cell (lId (obj a)) (mapLoose (lId a)) (𝟙 (obj a)) (𝟙 (obj a))

  /-- Naturality of the compositor in cells. -/
  laxComp_natural : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ : C}
    {m₁ : Loose a₁ a₂} {m₂ : Loose a₂ a₃} {n₁ : Loose b₁ b₂} {n₂ : Loose b₂ b₃}
    {f : a₁ ⟶ b₁} {g : a₂ ⟶ b₂} {h : a₃ ⟶ b₃}
    (α : Cell m₁ n₁ f g) (β : Cell m₂ n₂ g h),
    laxComp m₁ m₂ ≫ᵥ mapCell (α ⊚ β) =
      Cell.cast (by simp) (by simp)
        ((mapCell α ⊚ mapCell β) ≫ᵥ laxComp n₁ n₂)

  /-- Naturality of the unit comparison in tight arrows. -/
  laxId_natural : ∀ {a b : C} (f : a ⟶ b),
    laxId a ≫ᵥ mapCell (hId f) =
      Cell.cast (by simp) (by simp) (hId (map f) ≫ᵥ laxId b)

  /-- Associativity coherence of the compositor. -/
  laxComp_assoc : ∀ {a b c d : C} (m : Loose a b) (n : Loose b c)
    (p : Loose c d),
    (laxComp m n ⊚ vId (mapLoose p)) ≫ᵥ laxComp (m ⊙ n) p ≫ᵥ
        mapCell (lAssoc m n p) =
      Cell.cast (by simp [map_id]) (by simp [map_id])
        (lAssoc (mapLoose m) (mapLoose n) (mapLoose p) ≫ᵥ
          (vId (mapLoose m) ⊚ laxComp n p) ≫ᵥ laxComp m (n ⊙ p))

  /-- Left unit coherence of the laxators. -/
  laxComp_leftUnitor : ∀ {a b : C} (m : Loose a b),
    (laxId a ⊚ vId (mapLoose m)) ≫ᵥ laxComp (lId a) m ≫ᵥ
        mapCell (lLeftUnitor m) =
      Cell.cast (by simp [map_id]) (by simp [map_id]) (lLeftUnitor (mapLoose m))

  /-- Right unit coherence of the laxators. -/
  laxComp_rightUnitor : ∀ {a b : C} (m : Loose a b),
    (vId (mapLoose m) ⊚ laxId b) ≫ᵥ laxComp m (lId b) ≫ᵥ
        mapCell (lRightUnitor m) =
      Cell.cast (by simp [map_id]) (by simp [map_id]) (lRightUnitor (mapLoose m))

namespace LaxDoubleFunctor

variable {C D}

attribute [simp] mapCell_vId mapCell_vComp

/-- The action on cells commutes with `Cell.cast`: transport along boundary
equalities maps to transport along their images. -/
@[simp]
theorem mapCell_cast (F : LaxDoubleFunctor C D) {a b c d : C} {m : Loose a b}
    {n : Loose c d} {f f' : a ⟶ c} {g g' : b ⟶ d} (hf : f = f') (hg : g = g')
    (α : Cell m n f g) :
    F.mapCell (α.cast hf hg) =
      (F.mapCell α).cast (by rw [hf]) (by rw [hg]) := by
  subst hf; subst hg; rfl

section Heq

variable (F : LaxDoubleFunctor C D)

/-!
### The functor axioms, in heterogeneous form
-/

/-- Congruence of the cell action along heterogeneous equality (with equal
loose boundaries and propositionally equal tight boundaries). -/
theorem mapCell_congr_heq {a b c d : C} {m : Loose a b} {n : Loose c d}
    {f f' : a ⟶ c} {g g' : b ⟶ d} {α : Cell m n f g} {α' : Cell m n f' g'}
    (hf : f = f') (hg : g = g') (hα : α ≍ α') : F.mapCell α ≍ F.mapCell α' := by
  subst hf; subst hg; rw [eq_of_heq hα]

theorem mapCell_vId_heq {a b : C} (m : Loose a b) :
    F.mapCell (vId m) ≍ vId (F.mapLoose m) := by
  rw [F.mapCell_vId]; exact Cell.cast_heq _ _ _

theorem mapCell_vComp_heq {a₁ b₁ a₂ b₂ a₃ b₃ : C}
    {m₁ : Loose a₁ b₁} {m₂ : Loose a₂ b₂} {m₃ : Loose a₃ b₃}
    {f₁ : a₁ ⟶ a₂} {g₁ : b₁ ⟶ b₂} {f₂ : a₂ ⟶ a₃} {g₂ : b₂ ⟶ b₃}
    (α : Cell m₁ m₂ f₁ g₁) (β : Cell m₂ m₃ f₂ g₂) :
    F.mapCell (α ≫ᵥ β) ≍ F.mapCell α ≫ᵥ F.mapCell β := by
  rw [F.mapCell_vComp]; exact Cell.cast_heq _ _ _

theorem laxComp_natural_heq {a₁ a₂ a₃ b₁ b₂ b₃ : C}
    {m₁ : Loose a₁ a₂} {m₂ : Loose a₂ a₃} {n₁ : Loose b₁ b₂} {n₂ : Loose b₂ b₃}
    {f : a₁ ⟶ b₁} {g : a₂ ⟶ b₂} {h : a₃ ⟶ b₃}
    (α : Cell m₁ n₁ f g) (β : Cell m₂ n₂ g h) :
    F.laxComp m₁ m₂ ≫ᵥ F.mapCell (α ⊚ β) ≍
      (F.mapCell α ⊚ F.mapCell β) ≫ᵥ F.laxComp n₁ n₂ := by
  rw [F.laxComp_natural]; exact Cell.cast_heq _ _ _

theorem laxId_natural_heq {a b : C} (f : a ⟶ b) :
    F.laxId a ≫ᵥ F.mapCell (hId f) ≍ hId (F.map f) ≫ᵥ F.laxId b := by
  rw [F.laxId_natural]; exact Cell.cast_heq _ _ _

theorem laxComp_assoc_heq {a b c d : C} (m : Loose a b) (n : Loose b c)
    (p : Loose c d) :
    (F.laxComp m n ⊚ vId (F.mapLoose p)) ≫ᵥ F.laxComp (m ⊙ n) p ≫ᵥ
        F.mapCell (lAssoc m n p) ≍
      lAssoc (F.mapLoose m) (F.mapLoose n) (F.mapLoose p) ≫ᵥ
        (vId (F.mapLoose m) ⊚ F.laxComp n p) ≫ᵥ F.laxComp m (n ⊙ p) := by
  rw [F.laxComp_assoc]; exact Cell.cast_heq _ _ _

theorem laxComp_leftUnitor_heq {a b : C} (m : Loose a b) :
    (F.laxId a ⊚ vId (F.mapLoose m)) ≫ᵥ F.laxComp (lId a) m ≫ᵥ
        F.mapCell (lLeftUnitor m) ≍ lLeftUnitor (F.mapLoose m) := by
  rw [F.laxComp_leftUnitor]; exact Cell.cast_heq _ _ _

theorem laxComp_rightUnitor_heq {a b : C} (m : Loose a b) :
    (vId (F.mapLoose m) ⊚ F.laxId b) ≫ᵥ F.laxComp m (lId b) ≫ᵥ
        F.mapCell (lRightUnitor m) ≍ lRightUnitor (F.mapLoose m) := by
  rw [F.laxComp_rightUnitor]; exact Cell.cast_heq _ _ _

end Heq

/-- The identity lax double functor.  Its laxators are identity cells. -/
def id : LaxDoubleFunctor C C where
  toFunctor := Functor.id C
  mapLoose m := m
  mapCell α := α
  mapCell_vId m := rfl
  mapCell_vComp α β := rfl
  laxComp m n := vId (m ⊙ n)
  laxId a := vId (lId a)
  laxComp_natural α β := by
    simp [PseudoDoubleCategory.vId_vComp, PseudoDoubleCategory.vComp_vId]
  laxId_natural f := by
    simp [PseudoDoubleCategory.vId_vComp, PseudoDoubleCategory.vComp_vId]
  laxComp_assoc m n p := by
    simp [PseudoDoubleCategory.hComp_vId, PseudoDoubleCategory.vId_vComp,
      PseudoDoubleCategory.vComp_vId]
  laxComp_leftUnitor m := by
    simp [PseudoDoubleCategory.hComp_vId, PseudoDoubleCategory.vId_vComp,
      PseudoDoubleCategory.vComp_vId]
  laxComp_rightUnitor m := by
    simp [PseudoDoubleCategory.hComp_vId, PseudoDoubleCategory.vId_vComp,
      PseudoDoubleCategory.vComp_vId]

end LaxDoubleFunctor

end CategoryTheory
