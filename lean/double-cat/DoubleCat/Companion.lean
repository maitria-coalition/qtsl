import DoubleCat.Basic
import DoubleCat.Sq
import DoubleCat.LooseBicategory
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Companions and conjoints

A companion of a tight arrow `f : a ⟶ b` is a loose arrow `m : Loose a b`
together with binding cells `η : Cell (lId a) m (𝟙 a) f` and
`ε : Cell m (lId b) f (𝟙 b)` whose tight-wise composite is the
loose-identity cell on `f` and whose loose-wise composite is (up to the
unitors) the tight-identity cell on `m`.  A conjoint is the loose dual: a
loose arrow `Loose b a` bound to `f` by the mirror-image cells.

This is the notion of Grandis–Paré ("Adjoint for double categories", 2004,
where companion pairs are called "orthogonal companions" and conjoints
"orthogonal adjoints") and Shulman ("Framed bicategories and monoidal
fibrations", 2008); a pseudo double category in which every tight arrow
has both a companion and a conjoint is a proarrow equipment (framed
bicategory), the setting in which the structured/decorated-cospan
constructions live.

In the double category of commutative squares every tight arrow is its own
companion, and a tight arrow has a conjoint precisely when it is invertible
(a conjoint of `f` in `Sq` is exactly a two-sided inverse: its binding
cells are the commutation squares `𝟙 = f ≫ m` and `m ≫ f = 𝟙`) — so `Sq`
witnesses satisfiability of the companion structure but is not an
equipment; the genuinely equipment-shaped examples are `Span` and
`DepSpan`.
-/

namespace CategoryTheory

open PseudoDoubleCategoryStruct

/-- Discharges tight-boundary side goals: `rfl`, or `simp` up to `rfl`. -/
local macro "boundary" : tactic => `(tactic| first | rfl | (simp; rfl) | simp)

universe w t v u

variable {C : Type u} [Category.{v} C] [PseudoDoubleCategoryStruct C]
  [PseudoDoubleCategory C]

/-- A companion of a tight arrow: a loose arrow bound to it by a unit and a
counit cell satisfying the two companion identities. -/
structure Companion {a b : C} (f : a ⟶ b) where

  /-- The underlying loose arrow. -/
  loose : Loose a b

  /-- The unit binding cell. -/
  eta : Cell (lId a) loose (𝟙 a) f

  /-- The counit binding cell. -/
  eps : Cell loose (lId b) f (𝟙 b)

  /-- The tight-wise composite of the binding cells is the loose-identity
  cell on `f`. -/
  eta_vComp_eps : eta ≫ᵥ eps = (hId f).cast (by boundary) (by boundary)

  /-- The loose-wise composite of the binding cells is, up to the unitors,
  the tight-wise identity cell on the loose arrow. -/
  eta_hComp_eps :
    lLeftUnitorInv loose ≫ᵥ (eta ⊚ eps) ≫ᵥ lRightUnitor loose =
      (vId loose).cast (by boundary) (by boundary)

/-- A conjoint of a tight arrow: a loose arrow in the opposite direction
bound to it by the mirror-image unit and counit. -/
structure Conjoint {a b : C} (f : a ⟶ b) where

  /-- The underlying loose arrow (running against `f`). -/
  loose : Loose b a

  /-- The unit binding cell. -/
  eta : Cell (lId a) loose f (𝟙 a)

  /-- The counit binding cell. -/
  eps : Cell loose (lId b) (𝟙 b) f

  /-- The tight-wise composite of the binding cells is the loose-identity
  cell on `f`. -/
  eta_vComp_eps : eta ≫ᵥ eps = (hId f).cast (by boundary) (by boundary)

  /-- The loose-wise composite of the binding cells is, up to the unitors,
  the tight-wise identity cell on the loose arrow. -/
  eps_hComp_eta :
    lRightUnitorInv loose ≫ᵥ (eps ⊚ eta) ≫ᵥ lLeftUnitor loose =
      (vId loose).cast (by boundary) (by boundary)

/-- A pseudo double category in which every tight arrow has a companion and a
conjoint: a proarrow equipment (framed bicategory).  Stated as data — a
choice of companions and conjoints — since chosen structure is more useful
than mere existence. -/
class Equipment (C : Type u) [Category.{v} C] [PseudoDoubleCategoryStruct C]
    [PseudoDoubleCategory C] where

  /-- A chosen companion for every tight arrow. -/
  companion : ∀ {a b : C} (f : a ⟶ b), Companion f

  /-- A chosen conjoint for every tight arrow. -/
  conjoint : ∀ {a b : C} (f : a ⟶ b), Conjoint f

namespace Companion

open PseudoDoubleCategory

/-- The loose identity is a companion of the tight identity.  The loose-wise
binding law is the derived coherence `λ_{𝟙ˡ} = ρ_{𝟙ˡ}`
(`lLeftUnitor_lId_eq_lRightUnitor_lId`, imported from mathlib's bicategory
theory through the loose bicategory). -/
def id (a : C) : Companion (𝟙 a) where
  loose := 𝟙ˡ a
  eta := vId (𝟙ˡ a)
  eps := vId (𝟙ˡ a)
  eta_vComp_eps := by
    rw [PseudoDoubleCategory.vComp_vId, PseudoDoubleCategory.hId_id]
  eta_hComp_eps := by
    rw [PseudoDoubleCategory.hComp_vId,
      ← lLeftUnitor_lId_eq_lRightUnitor_lId, Cell.eq_cast_iff_heq]
    exact (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vId_vComp_heq _)).trans (lLeftUnitorInv_lLeftUnitor_heq _)

variable {a b : C} {f : a ⟶ b}

/-- The comparison 2-cell between two companions of the same tight arrow:
paste the counit of one against the unit of the other. -/
def theta (M N : Companion f) : (M.loose : Loose a b) ⟶ N.loose :=
  (lLeftUnitorInv M.loose ≫ᵥ ((N.eta ⊚ M.eps) ≫ᵥ lRightUnitor N.loose)).cast
    (by simp) (by simp)

theorem theta_aux (M N : Companion f) :
    ((N.eta ⊚ M.eps) ≫ᵥ lRightUnitor N.loose) ≫ᵥ N.eps ≍
      lLeftUnitor M.loose ≫ᵥ M.eps :=
  (vComp_assoc_heq _ _ _).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (lRightUnitor_natural_heq N.eps).symm).trans <|
    (vComp_assoc_heq _ _ _).symm.trans <|
    (vComp_congr_heq (by simp) (by simp) rfl rfl
      (heq_of_eq (interchange N.eta M.eps N.eps (hId (𝟙 b))).symm)
      HEq.rfl).trans <|
    (vComp_congr_heq (by simp) (by simp) rfl rfl
      (hComp_congr_heq (by simp) (by simp) (by simp)
        (Cell.eq_cast_iff_heq.mp N.eta_vComp_eps)
        ((vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
          (heq_of_eq (PseudoDoubleCategory.hId_id b))).trans
          (vComp_vId_heq M.eps)))
      HEq.rfl).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (heq_of_eq (lLeftUnitor_lId_eq_lRightUnitor_lId b).symm)).trans
    (lLeftUnitor_natural_heq M.eps)

theorem theta_vComp_theta (M N : Companion f) :
    M.theta N ≫ N.theta M = 𝟙 M.loose := by
  rw [globularComp_def, globularId_def, Cell.cast_eq_iff_heq]
  have slide : ((N.eta ⊚ M.eps) ≫ᵥ lRightUnitor N.loose) ≫ᵥ
      lLeftUnitorInv N.loose ≍
        lLeftUnitorInv (𝟙ˡ a ⊙ M.loose) ≫ᵥ
          (vId (𝟙ˡ a) ⊚ ((N.eta ⊚ M.eps) ≫ᵥ
            lRightUnitor N.loose).cast (f' := 𝟙 a) (g' := 𝟙 b)
              (by simp) (by simp)) :=
    (lLeftUnitorInv_natural_heq _).trans
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (hComp_congr_heq (by simp) (by simp) (by simp)
          ((hId_congr_heq (by simp)).trans
            (heq_of_eq (PseudoDoubleCategory.hId_id a)))
          (Cell.cast_heq _ _ _).symm))
  have col : ((N.eta ⊚ M.eps) ≫ᵥ lRightUnitor N.loose).cast
        (f' := 𝟙 a) (g' := 𝟙 b) (by simp) (by simp) ≫ᵥ N.eps ≍
          (lLeftUnitor M.loose ≫ᵥ M.eps).cast (f' := f) (g' := 𝟙 b)
            (by simp) (by simp) :=
    (vComp_congr_heq (by simp) (by simp) rfl rfl
      (Cell.cast_heq _ _ _) HEq.rfl).trans <|
      (theta_aux M N).trans (Cell.cast_heq _ _ _).symm
  have fold : M.eta ⊚ ((lLeftUnitor M.loose ≫ᵥ M.eps).cast (f' := f)
      (g' := 𝟙 b) (by simp) (by simp)) ≍
        lLeftUnitor (𝟙ˡ a ⊙ M.loose) ≫ᵥ (M.eta ⊚ M.eps) :=
    (hComp_congr_heq (by simp) (by simp) (by simp)
      (vId_vComp_heq M.eta).symm (Cell.cast_heq _ _ _)).trans <|
    (heq_of_eq (interchange (vId (𝟙ˡ a)) (lLeftUnitor M.loose)
      M.eta M.eps)).trans
    (vComp_congr_heq rfl rfl (by simp) (by simp)
      (heq_of_eq (vId_lId_hComp_lLeftUnitor M.loose)) HEq.rfl)
  exact (vComp_congr_heq (by simp) (by simp) (by simp) (by simp)
      (Cell.cast_heq _ _ _) (Cell.cast_heq _ _ _)).trans <|
    (vComp_assoc_heq _ _ _).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_assoc_heq _ _ _).symm).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_congr_heq (by simp) (by simp) rfl rfl slide HEq.rfl)).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_assoc_heq _ _ _)).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_assoc_heq _ _ _).symm)).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_congr_heq (by simp) (by simp) rfl rfl
          (heq_of_eq (interchange (vId (𝟙ˡ a))
            (((N.eta ⊚ M.eps) ≫ᵥ lRightUnitor N.loose).cast
              (f' := 𝟙 a) (g' := 𝟙 b) (by simp) (by simp))
            M.eta N.eps)).symm HEq.rfl))).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_congr_heq (by simp) (by simp) rfl rfl
          (hComp_congr_heq (by simp) (by simp) (by simp)
            (vId_vComp_heq M.eta) col) HEq.rfl))).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_congr_heq (by simp) (by simp) rfl rfl fold HEq.rfl))).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_assoc_heq _ _ _))).trans <|
    (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      ((vComp_assoc_heq _ _ _).symm.trans <|
        (vComp_congr_heq (by simp) (by simp) rfl rfl
          (lLeftUnitorInv_lLeftUnitor_heq _) HEq.rfl).trans
        (vId_vComp_heq _))).trans
    (Cell.eq_cast_iff_heq.mp M.eta_hComp_eps)

/-- Any two companions of the same tight arrow are isomorphic as loose arrows
(globularly): the comparison cells in the two directions are mutually
inverse. -/
def isoLoose (M N : Companion f) : (M.loose : Loose a b) ≅ N.loose where
  hom := M.theta N
  inv := N.theta M
  hom_inv_id := theta_vComp_theta M N
  inv_hom_id := theta_vComp_theta N M

open Bicategory in

theorem tube {B : Type u} [Bicategory.{t, w} B] {a b c : B}
    {m : a ⟶ b} {n : b ⟶ c}
    {Em : 𝟙 a ≫ m ⟶ m ≫ 𝟙 b} {En : 𝟙 b ≫ n ⟶ n ≫ 𝟙 c}
    (hm : (λ_ m).inv ≫ (Em ≫ (ρ_ m).hom) = 𝟙 m)
    (hn : (λ_ n).inv ≫ (En ≫ (ρ_ n).hom) = 𝟙 n) :
    (λ_ (m ≫ n)).inv ≫
        ((((α_ (𝟙 a) m n).inv ≫ ((Em ▷ n) ≫ (α_ m (𝟙 b) n).hom)) ≫
          ((((ρ_ m).inv ▷ (𝟙 b ≫ n)) ≫ ((m ≫ 𝟙 b) ◁ (λ_ n).hom)) ≫
            (((α_ m (𝟙 b) n).hom ≫ (m ◁ En)) ≫ (α_ m n (𝟙 c)).inv))) ≫
          (ρ_ (m ≫ n)).hom) = 𝟙 (m ≫ n) := by
  have hm' : Em = (λ_ m).hom ≫ (ρ_ m).inv := by
    rw [Iso.inv_comp_eq, Category.comp_id] at hm
    rw [← hm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hn' : En = (λ_ n).hom ≫ (ρ_ n).inv := by
    rw [Iso.inv_comp_eq, Category.comp_id] at hn
    rw [← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  subst hm' hn'
  bicategory

open Bicategory in

theorem comp_tube {a b c : C} (m : Loose a b) (n : Loose b c)
    (Em : Cell (lId a ⊙ m) (m ⊙ lId b) (𝟙 a) (𝟙 b))
    (En : Cell (lId b ⊙ n) (n ⊙ lId c) (𝟙 b) (𝟙 c))
    (hm : lLeftUnitorInv m ≫ᵥ (Em ≫ᵥ lRightUnitor m) =
      (vId m).cast (by simp) (by simp))
    (hn : lLeftUnitorInv n ≫ᵥ (En ≫ᵥ lRightUnitor n) =
      (vId n).cast (by simp) (by simp)) :
    lLeftUnitorInv (m ⊙ n) ≫ᵥ
        (((lAssocInv (lId a) m n ≫ᵥ ((Em ⊚ vId n) ≫ᵥ lAssoc m (lId b) n)) ≫ᵥ
          (((lRightUnitorInv m ⊚ vId (lId b ⊙ n)) ≫ᵥ
              (vId (m ⊙ lId b) ⊚ lLeftUnitor n)) ≫ᵥ
            ((lAssoc m (lId b) n ≫ᵥ (vId m ⊚ En)) ≫ᵥ lAssocInv m n (lId c)))) ≫ᵥ
          lRightUnitor (m ⊙ n)) ≍ vId (m ⊙ n) := by
  have hm' : (λ_ (show (LooseBicat.mk a : LooseBicat C) ⟶ LooseBicat.mk b
      from m)).inv ≫ (Em ≫ (ρ_ (show (LooseBicat.mk a : LooseBicat C) ⟶
        LooseBicat.mk b from m)).hom) = 𝟙 _ := by
    rw [globularComp_def, globularComp_def, globularId_def,
      Cell.cast_eq_iff_heq]
    exact (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (Cell.cast_heq _ _ _)).trans (Cell.eq_cast_iff_heq.mp hm)
  have hn' : (λ_ (show (LooseBicat.mk b : LooseBicat C) ⟶ LooseBicat.mk c
      from n)).inv ≫ (En ≫ (ρ_ (show (LooseBicat.mk b : LooseBicat C) ⟶
        LooseBicat.mk c from n)).hom) = 𝟙 _ := by
    rw [globularComp_def, globularComp_def, globularId_def,
      Cell.cast_eq_iff_heq]
    exact (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
      (Cell.cast_heq _ _ _)).trans (Cell.eq_cast_iff_heq.mp hn)
  have h := tube hm' hn'

  rw [globularComp_def, globularComp_def, globularComp_def,
    globularComp_def, globularComp_def, globularComp_def,
    globularComp_def, globularComp_def, globularComp_def] at h
  simp only [cast_vComp, vComp_cast, Cell.cast_cast] at h
  exact Cell.cast_eq_iff_heq.mp h

variable {c : C} {g : b ⟶ c}

/-- Companions compose: a companion of `f` and a companion of `g` yield a
companion of `f ≫ g` with loose arrow the loose composite. -/
def comp (M : Companion f) (N : Companion g) : Companion (f ≫ g) where
  loose := M.loose ⊙ N.loose
  eta := (M.eta ≫ᵥ (lRightUnitorInv M.loose ≫ᵥ (vId M.loose ⊚ N.eta))).cast
    (by simp) (by simp)
  eps := ((M.eps ⊚ vId N.loose) ≫ᵥ (lLeftUnitor N.loose ≫ᵥ N.eps)).cast
    (by simp) (by simp)
  eta_vComp_eps := by
    rw [Cell.eq_cast_iff_heq]
    exact (vComp_congr_heq (by simp) (by simp) (by simp) (by simp)
        (Cell.cast_heq _ _ _) (Cell.cast_heq _ _ _)).trans <|

      (vComp_assoc_heq _ _ _).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_assoc_heq _ _ _)).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
          (vComp_assoc_heq _ _ _).symm)).trans <|

      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
          (vComp_congr_heq (by simp) (by simp) rfl rfl
            ((heq_of_eq (interchange (vId M.loose) N.eta M.eps
                (vId N.loose))).symm.trans <|
              (hComp_congr_heq (by simp) (by simp) (by simp)
                (vId_vComp_heq M.eps) (vComp_vId_heq N.eta)).trans <|
              (hComp_congr_heq (by simp) (by simp) (by simp)
                (vComp_vId_heq M.eps).symm (vId_vComp_heq N.eta).symm).trans
              (heq_of_eq (interchange M.eps (vId (lId b)) (vId (lId b))
                N.eta)))
            HEq.rfl))).trans <|

      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
          (vComp_assoc_heq _ _ _))).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_assoc_heq _ _ _).symm).trans <|

      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_congr_heq (by simp) (by simp) rfl rfl
          ((vComp_congr_heq rfl rfl rfl rfl HEq.rfl
            (hComp_congr_heq rfl rfl rfl HEq.rfl
              (heq_of_eq (PseudoDoubleCategory.hId_id b).symm))).trans
            (lRightUnitorInv_natural_heq M.eps).symm)
          HEq.rfl)).trans <|

      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
          (vComp_assoc_heq _ _ _).symm)).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
          (vComp_congr_heq (by simp) (by simp) rfl rfl
            ((vComp_congr_heq rfl rfl rfl rfl
              (hComp_congr_heq rfl rfl rfl
                (heq_of_eq (PseudoDoubleCategory.hId_id b).symm) HEq.rfl)
              HEq.rfl).trans
              (lLeftUnitor_natural_heq N.eta))
            HEq.rfl))).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
          (vComp_assoc_heq _ _ _))).trans <|

      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_assoc_heq _ _ _)).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
          (vComp_assoc_heq _ _ _).symm)).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
          (vComp_congr_heq (by simp) (by simp) rfl rfl
            ((vComp_congr_heq (by simp) (by simp) rfl rfl
              (heq_of_eq
                (lLeftUnitorInv_lId_eq_lRightUnitorInv_lId b).symm)
              HEq.rfl).trans
              (lLeftUnitorInv_lLeftUnitor_heq (lId b)))
            HEq.rfl))).trans <|
      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
          (vId_vComp_heq _))).trans <|

      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
          (Cell.eq_cast_iff_heq.mp N.eta_vComp_eps))).trans <|
      (vComp_assoc_heq _ _ _).symm.trans <|
      (vComp_congr_heq (by simp) (by simp) rfl rfl
        (Cell.eq_cast_iff_heq.mp M.eta_vComp_eps) HEq.rfl).trans
      (heq_of_eq (PseudoDoubleCategory.hId_comp f g).symm)
  eta_hComp_eps := by
    rw [Cell.eq_cast_iff_heq]

    have inner :=
      (hComp_congr_heq (by simp) (by simp) (by simp)
        (Cell.cast_heq (f' := 𝟙 a) (g' := f ≫ g) (by simp) (by simp) _)
        (Cell.cast_heq (f' := f ≫ g) (g' := 𝟙 c) (by simp) (by simp) _)).trans <|
      (heq_of_eq (interchange M.eta (M.eps ⊚ vId N.loose)
        (lRightUnitorInv M.loose ≫ᵥ (vId M.loose ⊚ N.eta))
        (lLeftUnitor N.loose ≫ᵥ N.eps))).trans <|
      (vComp_congr_heq rfl rfl rfl rfl HEq.rfl
        (heq_of_eq (interchange (lRightUnitorInv M.loose)
          (lLeftUnitor N.loose) (vId M.loose ⊚ N.eta) N.eps))).trans <|

      (vComp_congr_heq (by simp) (by simp) rfl rfl
        ((vId_vComp_heq _).symm.trans <|
          (vComp_congr_heq (by simp) (by simp) rfl rfl
            (lAssocInv_lAssoc_heq (lId a) M.loose N.loose).symm
            HEq.rfl).trans <|
          (vComp_assoc_heq _ _ _).trans <|
          (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
            (lAssoc_natural_heq M.eta M.eps (vId N.loose)).symm))
        HEq.rfl).trans <|

      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_congr_heq (by simp) (by simp) rfl rfl
          ((hComp_congr_heq (by simp) (by simp) (by simp)
            (vComp_vId_heq (lRightUnitorInv M.loose)).symm
            (vId_vComp_heq (lLeftUnitor N.loose)).symm).trans
            (heq_of_eq (interchange (lRightUnitorInv M.loose)
              (vId (lId b ⊙ N.loose)) (vId (M.loose ⊙ lId b))
              (lLeftUnitor N.loose))))
          HEq.rfl)).trans <|

      (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
          ((vComp_vId_heq _).symm.trans <|
            (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
              (lAssoc_lAssocInv_heq M.loose N.loose (lId c)).symm).trans <|
            (vComp_assoc_heq _ _ _).symm.trans <|
            (vComp_congr_heq (by simp) (by simp) rfl rfl
              (lAssoc_natural_heq (vId M.loose) N.eta N.eps)
              HEq.rfl))))
    exact (vComp_congr_heq rfl rfl (by simp) (by simp) HEq.rfl
        (vComp_congr_heq (by simp) (by simp) rfl rfl inner HEq.rfl)).trans
      (comp_tube M.loose N.loose _ _ M.eta_hComp_eps N.eta_hComp_eps)

end Companion

namespace Sq

variable (B : Type u) [Category.{v} B]

/-- In `Sq` every tight arrow is its own companion. -/
def companion {a b : Sq B} (f : a ⟶ b) : Companion f where
  loose := f
  eta := ⟨by simp⟩
  eps := ⟨by simp⟩
  eta_vComp_eps := Subsingleton.elim _ _
  eta_hComp_eps := Subsingleton.elim _ _

variable {B}

/-- In `Sq` every isomorphism has a conjoint, namely its inverse.  (This is
sharp: a conjoint of `f` in `Sq` is exactly a two-sided inverse of `f`.) -/
def conjointOfIso {a b : Sq B} (f : a ≅ b) : Conjoint f.hom where
  loose := f.inv
  eta := ⟨by simp⟩
  eps := ⟨by simp⟩
  eta_vComp_eps := Subsingleton.elim _ _
  eps_hComp_eta := Subsingleton.elim _ _

end Sq

end CategoryTheory
