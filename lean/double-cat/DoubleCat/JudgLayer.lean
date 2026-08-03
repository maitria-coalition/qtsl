import DoubleCat.Basic
import DoubleCat.Vert

/-!
# The judgment layer over a pseudo double category

The thin carrier for judgment-level semantics: given a pseudo double
category `B` and an **ordered decoration datum** on it — a decoration
type for each loose arrow, a fibre preorder (the judgment order), a
covariant transport along cells, a lax composition and unit, with the
transport monotone and coherent with `B`'s structure cells — the
**judgment layer** `JudgLayer B Θ` has `B`'s objects and tight arrows,
decorated loose arrows, and *judgment-inclusions* as cells: a cell from
`(m, u)` to `(n, v)` over `(f, g)` is the (mere) existence of a base
cell along which `u` transports into `v`'s downset,

  `Cell (m,u) (n,v) f g  :=  PLift (∃ γ : Cell m n f g, pull γ u ≤ v)`.

Cells are propositions by construction, so the judgment layer is thin —
the hypothesis of the free-promotion transpose
(`VirtualDoubleFunctor.promoteThin`), which the semantic-universe
totals themselves cannot satisfy: their Grothendieck cells carry base
cells as *data* (the wiring base's cells are state maps).  The judgment
layer is exactly what the fibre order of those totals — "the judgment
layer, carried on top of the total" in their own docstrings — looks
like as a pseudo double category in its own right.

Decorations here are deliberately **endpoint-blind** (indexed by the
loose arrow alone, not by chosen points of object fibres): this is the
shape both semantic-universe decoration functors have at the loose
level (their two-sided families are constant), and it removes the
dependent-endpoint heterogeneous-equality calculus wholesale — the
datum's coherence fields are plain equalities.

The propositional datum (`JudgmentOrder.propDatum`) decorates every
loose arrow of any base with a proposition, ordered by implication;
over the vertically-trivial base (`DoubleCat.Vert`) its judgment layer
is the implication double category (`DoubleCat.ImplDouble`) up to
wrapper — the single-object Prop-shadow of the judgment layer, made
precise.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

universe w' w t v u

set_option linter.checkUnivs false in
/-- An ordered decoration datum on a pseudo double category `B`:
decorations of loose arrows, a fibre preorder (the judgment order),
transport along cells, lax composition and unit, monotonicity, and
coherence of the transport with `B`'s structure cells.  The coherence
fields are stated as equalities — both semantic-universe instances
have them on the nose — and the four inverse structure cells of the
judgment layer are *derived* from the forward ones through the
roundtrip laws (`pull_inv` below), so no inverse coherence is ever
assumed. -/
structure JudgmentOrder (B : Type u) [Category.{v} B]
    [PseudoDoubleCategoryStruct.{w, t, v, u} B] :
    Type (max u v w t (w' + 1)) where
  /-- The decorations of a loose arrow (endpoint-blind). -/
  Dec : ∀ {a b : B}, Loose a b → Type w'
  /-- The judgment order on decorations. -/
  le : ∀ {a b : B} {m : Loose a b}, Dec m → Dec m → Prop
  /-- Reflexivity of the judgment order. -/
  le_refl : ∀ {a b : B} {m : Loose a b} (u : Dec m), le u u
  /-- Transitivity of the judgment order. -/
  le_trans : ∀ {a b : B} {m : Loose a b} {u v w'' : Dec m},
    le u v → le v w'' → le u w''
  /-- Covariant transport of decorations along a base cell. -/
  pull : ∀ {a b c d : B} {m : Loose a b} {n : Loose c d} {f : a ⟶ c}
    {g : b ⟶ d}, Cell m n f g → Dec m → Dec n
  /-- Lax composition of decorations over loose composition. -/
  dcomp : ∀ {a b c : B} {m : Loose a b} {n : Loose b c},
    Dec m → Dec n → Dec (m ⊙ n)
  /-- The unit decoration over the loose identity. -/
  dunit : ∀ (a : B), Dec (𝟙ˡ a)
  /-- Transport along the tight-wise identity is the identity. -/
  pull_vId : ∀ {a b : B} {m : Loose a b} (u : Dec m),
    pull (vId m) u = u
  /-- Transport along a tight-wise composite is the composite of the
  transports. -/
  pull_vComp : ∀ {a₁ b₁ a₂ b₂ a₃ b₃ : B}
    {m₁ : Loose a₁ b₁} {m₂ : Loose a₂ b₂} {m₃ : Loose a₃ b₃}
    {f₁ : a₁ ⟶ a₂} {g₁ : b₁ ⟶ b₂} {f₂ : a₂ ⟶ a₃} {g₂ : b₂ ⟶ b₃}
    (α : Cell m₁ m₂ f₁ g₁) (β : Cell m₂ m₃ f₂ g₂) (u : Dec m₁),
    pull (α ≫ᵥ β) u = pull β (pull α u)
  /-- Transport is monotone in the judgment order. -/
  pull_mono : ∀ {a b c d : B} {m : Loose a b} {n : Loose c d}
    {f : a ⟶ c} {g : b ⟶ d} (γ : Cell m n f g) {u v : Dec m},
    le u v → le (pull γ u) (pull γ v)
  /-- Lax composition is monotone in both arguments. -/
  dcomp_mono : ∀ {a b c : B} {m : Loose a b} {n : Loose b c}
    {u u' : Dec m} {v v' : Dec n},
    le u u' → le v v' → le (dcomp u v) (dcomp u' v')
  /-- The unit decoration transports to the unit decoration along the
  loose-identity cell. -/
  pull_hId : ∀ {a b : B} (f : a ⟶ b),
    pull (hId f) (dunit a) = dunit b
  /-- Naturality: transporting a lax composite along a loose-wise
  composite cell is the lax composite of the transports. -/
  pull_hComp : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ : B}
    {m₁ : Loose a₁ a₂} {m₂ : Loose a₂ a₃}
    {n₁ : Loose b₁ b₂} {n₂ : Loose b₂ b₃}
    {f : a₁ ⟶ b₁} {g : a₂ ⟶ b₂} {h : a₃ ⟶ b₃}
    (α : Cell m₁ n₁ f g) (β : Cell m₂ n₂ g h)
    (u : Dec m₁) (v : Dec m₂),
    pull (α ⊚ β) (dcomp u v) = dcomp (pull α u) (pull β v)
  /-- Transport along the associator reassociates the lax composite. -/
  pull_lAssoc : ∀ {a b c d : B} (m : Loose a b) (n : Loose b c)
    (p : Loose c d) (u : Dec m) (v : Dec n) (w'' : Dec p),
    pull (lAssoc m n p) (dcomp (dcomp u v) w'') = dcomp u (dcomp v w'')
  /-- Transport along the left unitor strips the unit decoration. -/
  pull_lLeftUnitor : ∀ {a b : B} (m : Loose a b) (u : Dec m),
    pull (lLeftUnitor m) (dcomp (dunit a) u) = u
  /-- Transport along the right unitor strips the unit decoration. -/
  pull_lRightUnitor : ∀ {a b : B} (m : Loose a b) (u : Dec m),
    pull (lRightUnitor m) (dcomp u (dunit b)) = u

namespace JudgmentOrder

variable {B : Type u} [Category.{v} B]
  [PseudoDoubleCategoryStruct.{w, t, v, u} B]

/-- Transport is blind to boundary casts: `Cell.cast` only reindexes
the tight sides, and decorations are endpoint-blind.  Free, generically
— never a datum field. -/
theorem pull_cast (Θ : JudgmentOrder.{w'} B) {a b c d : B}
    {m : Loose a b} {n : Loose c d} {f f' : a ⟶ c} {g g' : b ⟶ d}
    (hf : f = f') (hg : g = g') (γ : Cell m n f g) (u : Θ.Dec m) :
    Θ.pull (Cell.cast hf hg γ) u = Θ.pull γ u := by
  subst hf; subst hg; rfl

/-- Inverse transport, derived: if a globular cell transports `u` to
`v` on the nose and composes with `σ'` to (a cast of) the tight-wise
identity, then `σ'` transports `v` back to `u`.  Powers the four
inverse structure cells of the judgment layer, so the datum never
assumes inverse coherences. -/
theorem pull_inv [PseudoDoubleCategory B] (Θ : JudgmentOrder.{w'} B)
    {a b : B} {m n : Loose a b}
    {σ : Cell m n (𝟙 a) (𝟙 b)} {σ' : Cell n m (𝟙 a) (𝟙 b)}
    (hround : σ ≫ᵥ σ' =
      Cell.cast (Category.id_comp (𝟙 a)).symm
        (Category.id_comp (𝟙 b)).symm (vId m))
    {u : Θ.Dec m} {v : Θ.Dec n} (hfwd : Θ.pull σ u = v) :
    Θ.pull σ' v = u := by
  rw [← hfwd, ← Θ.pull_vComp, hround, Θ.pull_cast, Θ.pull_vId]

/-- The propositional decoration datum, over any base: every loose
arrow is decorated by a proposition, ordered by implication, with
trivial transport, conjunction as lax composition, and `True` as the
unit.  Its judgment layer over the vertically-trivial base is the
implication double category up to wrapper — the Prop-shadow of the
judgment layer. -/
def propDatum : JudgmentOrder.{0} B where
  Dec _ := Prop
  le u v := u → v
  le_refl _ := fun h => h
  le_trans h₁ h₂ := fun h => h₂ (h₁ h)
  pull _ := id
  dcomp u v := u ∧ v
  dunit _ := True
  pull_vId _ := rfl
  pull_vComp _ _ _ := rfl
  pull_mono := @fun _ _ _ _ _ _ _ _ _ _ _ h => h
  dcomp_mono h₁ h₂ := fun h => ⟨h₁ h.1, h₂ h.2⟩
  pull_hId _ := rfl
  pull_hComp _ _ _ _ := rfl
  pull_lAssoc _ _ _ _ _ _ := propext and_assoc
  pull_lLeftUnitor _ u := true_and u
  pull_lRightUnitor _ u := and_true u

end JudgmentOrder

/-- The carrier of the judgment layer: `B`'s objects, wrapped so the
instance collides with nothing `B` itself carries. -/
structure JudgLayer (B : Type u) [Category.{v} B]
    [PseudoDoubleCategoryStruct.{w, t, v, u} B]
    (Θ : JudgmentOrder.{w'} B) : Type u where
  /-- Wrap an object. -/
  of ::
  /-- Unwrap an object. -/
  un : B

namespace JudgLayer

variable {B : Type u} [Category.{v} B]
  [PseudoDoubleCategoryStruct.{w, t, v, u} B] {Θ : JudgmentOrder.{w'} B}

instance : Category.{v} (JudgLayer B Θ) where
  Hom a b := a.un ⟶ b.un
  id a := 𝟙 a.un
  comp f g := f ≫ g

/-- A loose arrow of the judgment layer: a loose arrow of the base with
a decoration. -/
structure JLoose (Θ : JudgmentOrder.{w'} B) (a b : JudgLayer B Θ) :
    Type (max w w') where
  /-- The underlying loose arrow. -/
  base : Loose a.un b.un
  /-- The decoration. -/
  dec : Θ.Dec base

/-- Cells are judgment-inclusions: the mere existence of a base cell
along which the source decoration transports into the target
decoration's downset.  (`PseudoDoubleCategory B` powers the inverse
structure cells, through the roundtrip laws and `pull_inv`.) -/
instance [PseudoDoubleCategory B] :
    PseudoDoubleCategoryStruct.{max w w', 0} (JudgLayer B Θ) where
  Loose a b := JLoose Θ a b
  Cell M N f g := PLift (∃ γ : Cell M.base N.base f g,
    Θ.le (Θ.pull γ M.dec) N.dec)
  vId M := ⟨⟨vId M.base, by rw [Θ.pull_vId]; exact Θ.le_refl _⟩⟩
  vComp α β :=
    ⟨α.down.elim fun γ₁ h₁ => β.down.elim fun γ₂ h₂ =>
      ⟨γ₁ ≫ᵥ γ₂, by
        rw [Θ.pull_vComp]
        exact Θ.le_trans (Θ.pull_mono γ₂ h₁) h₂⟩⟩
  lId a := ⟨𝟙ˡ a.un, Θ.dunit a.un⟩
  lComp M N := ⟨M.base ⊙ N.base, Θ.dcomp M.dec N.dec⟩
  hId f :=
    ⟨⟨PseudoDoubleCategoryStruct.hId (C := B) f, by
      rw [Θ.pull_hId]; exact Θ.le_refl _⟩⟩
  hComp α β :=
    ⟨α.down.elim fun γ₁ h₁ => β.down.elim fun γ₂ h₂ =>
      ⟨γ₁ ⊚ γ₂, by
        rw [Θ.pull_hComp]
        exact Θ.dcomp_mono h₁ h₂⟩⟩
  lAssoc M N P :=
    ⟨⟨lAssoc M.base N.base P.base, by
      rw [Θ.pull_lAssoc]; exact Θ.le_refl _⟩⟩
  lAssocInv M N P :=
    ⟨⟨lAssocInv M.base N.base P.base, by
      rw [Θ.pull_inv (PseudoDoubleCategory.lAssoc_lAssocInv
        M.base N.base P.base) (Θ.pull_lAssoc M.base N.base P.base
          M.dec N.dec P.dec)]
      exact Θ.le_refl _⟩⟩
  lLeftUnitor M :=
    ⟨⟨lLeftUnitor M.base, by
      rw [Θ.pull_lLeftUnitor]; exact Θ.le_refl _⟩⟩
  lLeftUnitorInv M :=
    ⟨⟨lLeftUnitorInv M.base, by
      rw [Θ.pull_inv (PseudoDoubleCategory.lLeftUnitor_lLeftUnitorInv
        M.base) (Θ.pull_lLeftUnitor M.base M.dec)]
      exact Θ.le_refl _⟩⟩
  lRightUnitor M :=
    ⟨⟨lRightUnitor M.base, by
      rw [Θ.pull_lRightUnitor]; exact Θ.le_refl _⟩⟩
  lRightUnitorInv M :=
    ⟨⟨lRightUnitorInv M.base, by
      rw [Θ.pull_inv (PseudoDoubleCategory.lRightUnitor_lRightUnitorInv
        M.base) (Θ.pull_lRightUnitor M.base M.dec)]
      exact Θ.le_refl _⟩⟩

instance [PseudoDoubleCategory B] {a b c d : JudgLayer B Θ}
    (M : Loose a b) (N : Loose c d) (f : a ⟶ c) (g : b ⟶ d) :
    Subsingleton (Cell M N f g) :=
  inferInstanceAs (Subsingleton (PLift _))

/-- **Thinness**, in the explicit form the free-promotion transpose
consumes: every cell type of the judgment layer is a subsingleton. -/
theorem cell_subsingleton [PseudoDoubleCategory B]
    {a b c d : JudgLayer B Θ} (M : Loose a b)
    (N : Loose c d) (f : a ⟶ c) (g : b ⟶ d) :
    Subsingleton (Cell M N f g) :=
  inferInstanceAs (Subsingleton (PLift _))

/-- The judgment layer is a pseudo double category: its cells are
proof-irrelevant. -/
instance [PseudoDoubleCategory B] : PseudoDoubleCategory (JudgLayer B Θ) where
  vId_vComp _ := Subsingleton.elim _ _
  vComp_vId _ := Subsingleton.elim _ _
  vComp_assoc _ _ _ := Subsingleton.elim _ _
  hId_id _ := Subsingleton.elim _ _
  hId_comp _ _ := Subsingleton.elim _ _
  hComp_vId _ _ := Subsingleton.elim _ _
  interchange _ _ _ _ := Subsingleton.elim _ _
  lAssoc_natural _ _ _ := Subsingleton.elim _ _
  lLeftUnitor_natural _ := Subsingleton.elim _ _
  lRightUnitor_natural _ := Subsingleton.elim _ _
  lAssoc_lAssocInv _ _ _ := Subsingleton.elim _ _
  lAssocInv_lAssoc _ _ _ := Subsingleton.elim _ _
  lLeftUnitor_lLeftUnitorInv _ := Subsingleton.elim _ _
  lLeftUnitorInv_lLeftUnitor _ := Subsingleton.elim _ _
  lRightUnitor_lRightUnitorInv _ := Subsingleton.elim _ _
  lRightUnitorInv_lRightUnitor _ := Subsingleton.elim _ _
  pentagon _ _ _ _ := Subsingleton.elim _ _
  triangle _ _ := Subsingleton.elim _ _

/-- A judgment-inclusion within a fibre: a decoration below another in
the judgment order is a cell over identity boundaries, with the
tight-wise identity as base witness.  (The directed-square shape —
region inclusion to judgment-class inclusion — enters the carrier
through this constructor.) -/
def cellOfLe [PseudoDoubleCategory B] {a b : JudgLayer B Θ}
    {m : Loose a.un b.un} {u v : Θ.Dec m} (h : Θ.le u v) :
    Cell (C := JudgLayer B Θ) (⟨m, u⟩ : JLoose Θ a b) ⟨m, v⟩
      (𝟙 a) (𝟙 b) :=
  ⟨⟨vId m, by rw [Θ.pull_vId]; exact h⟩⟩

end JudgLayer

end CategoryTheory
