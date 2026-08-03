import DoubleCat.Monoidal.Strong
import Mathlib.Tactic.Abel

/-!
# The parametric graded model, and the linearization of the coherence axioms

Given abelian groups `G` (grades) and `A` (weights) and a record `W` of
weight functions — `chi` for the interchanger, `mu` for the unit
interchanger, `assoc`, `lunit`, `runit` for the loose associator and
unitors, `braid` for the loose braiding — `WPt W` is the one-object
pseudo double category whose loose arrows are elements of `G` (composing
by addition, tensoring by addition) and whose cells `m ⟶ n` exist only
for `m = n` and carry a weight in `A` (adding under both compositions and
under the tensor), equipped with the braided monoidal double category
data in which each structure cell carries the weight `W` prescribes and
each inverse structure cell carries the negated weight.

Every pasting equation in this family linearizes: the weight of a
composite is the sum of the weights of its parts, and transport along
tight boundaries is the identity.  Two groups of consequences:

* **The data-level laws are free.**  `MonoidalDoubleCategory (WPt W)`
  and `BraidedDoubleCategory (WPt W)` hold for *every* `W`: naturality
  and invertibility of the structure cells impose no condition on the
  component weights.  Likewise every graded model is strong
  (`instStrong`): a globular cell of weight `w` has the inverse of
  weight `-w`.

* **Each coherence mixin is equivalent to its linearization** — an
  explicit additive functional equation in the weight functions
  (`m1Pentagon_iff` … `m11bBraidingUnit_iff`).

The characterizations turn both satisfaction and refutation of coherence
axioms into elementary arithmetic: over finite groups (`ZMod n`) both
are decidable (`decide`), and over `ℤ` polynomial witnesses are checked
by `ring`/`norm_num`.  `DoubleCat.Monoidal.Falsifiability` builds the
refutation table on this machinery;
`DoubleCat.Monoidal.GradedCounterexample` is the standalone
integer-graded instance of the same construction.
-/

namespace CategoryTheory

namespace MonoidalDoubleCategory

namespace Graded

open PseudoDoubleCategoryStruct MonoidalDoubleCategoryStruct MonoidalCategory

/-- A record of weight functions for the graded model: `chi` for the
interchanger, `mu` for the unit interchanger, `assoc`, `lunit`, `runit` for
the loose associator and unitors, `braid` for the loose braiding. -/
structure Weights (G A : Type) [AddCommGroup G] [AddCommGroup A] where

  chi : G → G → G → G → A

  mu : A

  assoc : G → G → G → A

  lunit : G → A

  runit : G → A

  braid : G → G → A

variable {G A : Type} [AddCommGroup G] [AddCommGroup A]

/-- The one-object base category of the graded model over a weight record
`W` (the parameter keeps distinct records' instances apart). -/
def WPt (_ : Weights G A) : Type := Discrete PUnit

variable (W : Weights G A)

/-- The point. -/
def wpt : WPt W := ⟨PUnit.unit⟩

instance : Category (WPt W) := inferInstanceAs (Category (Discrete PUnit))

instance : MonoidalCategory (WPt W) :=
  inferInstanceAs (MonoidalCategory (Discrete PUnit))

instance : Subsingleton (WPt W) :=
  ⟨fun a b => by cases a; cases b; rfl⟩

instance (X Y : WPt W) : Subsingleton (X ⟶ Y) :=
  inferInstanceAs (Subsingleton (ULift (PLift _)))

instance : BraidedCategory (WPt W) where
  braiding _ _ := eqToIso (Subsingleton.elim _ _)
  braiding_naturality_right := by intros; exact Subsingleton.elim _ _
  braiding_naturality_left := by intros; exact Subsingleton.elim _ _
  hexagon_forward := by intros; exact Subsingleton.elim _ _
  hexagon_reverse := by intros; exact Subsingleton.elim _ _

instance : SymmetricCategory (WPt W) where
  symmetry := by intros; exact Subsingleton.elim _ _

/-- A cell between grades in `G`: it exists only for equal grades and carries
a weight in `A`. -/
structure WCell (A : Type) {G : Type} (m n : G) : Type where

  eq : m = n

  wt : A

theorem WCell.ext {m n : G} {α β : WCell A m n} (h : α.wt = β.wt) :
    α = β := by
  obtain ⟨e₁, w₁⟩ := α
  obtain ⟨e₂, w₂⟩ := β
  cases h
  rfl

/-- The one-object double category with grades in `G` as loose arrows
(composing by addition) and `A`-weighted cells. -/
instance ptStruct : PseudoDoubleCategoryStruct (WPt W) where
  Loose _ _ := G
  Cell m n _ _ := WCell A m n
  vId _ := ⟨rfl, 0⟩
  vComp α β := ⟨α.eq.trans β.eq, α.wt + β.wt⟩
  lId _ := 0
  lComp m n := m + n
  hId _ := ⟨rfl, 0⟩
  hComp α β := ⟨by rw [α.eq, β.eq], α.wt + β.wt⟩
  lAssoc m n p := ⟨add_assoc m n p, 0⟩
  lAssocInv m n p := ⟨(add_assoc m n p).symm, 0⟩
  lLeftUnitor m := ⟨zero_add m, 0⟩
  lLeftUnitorInv m := ⟨(zero_add m).symm, 0⟩
  lRightUnitor m := ⟨add_zero m, 0⟩
  lRightUnitorInv m := ⟨(add_zero m).symm, 0⟩

@[simp]
theorem gcast {a b c d : WPt W} {m : Loose a b} {n : Loose c d}
    {f f' : a ⟶ c} {g g' : b ⟶ d} (hf : f = f') (hg : g = g')
    (α : Cell m n f g) : Cell.cast hf hg α = α := by
  subst hf; subst hg; rfl

@[simp] theorem vComp_wt {a b c d e f : WPt W} {m : Loose a b}
    {n : Loose c d} {p : Loose e f} {f₁ : a ⟶ c} {g₁ : b ⟶ d} {f₂ : c ⟶ e}
    {g₂ : d ⟶ f} (α : Cell m n f₁ g₁) (β : Cell n p f₂ g₂) :
    (α ≫ᵥ β).wt = α.wt + β.wt := rfl

@[simp] theorem hComp_wt {a₁ a₂ a₃ b₁ b₂ b₃ : WPt W}
    {m₁ : Loose a₁ a₂} {m₂ : Loose a₂ a₃} {n₁ : Loose b₁ b₂}
    {n₂ : Loose b₂ b₃} {f : a₁ ⟶ b₁} {g : a₂ ⟶ b₂} {h : a₃ ⟶ b₃}
    (α : Cell m₁ n₁ f g) (β : Cell m₂ n₂ g h) :
    (α ⊚ β).wt = α.wt + β.wt := rfl

@[simp] theorem vId_wt {a b : WPt W} (m : Loose a b) : (vId m).wt = 0 := rfl

@[simp] theorem hId_wt {a b : WPt W} (f : a ⟶ b) : (hId f).wt = 0 := rfl

@[simp] theorem lAssoc_wt {a b c d : WPt W} (m : Loose a b) (n : Loose b c)
    (p : Loose c d) : (lAssoc m n p).wt = 0 := rfl

@[simp] theorem lAssocInv_wt {a b c d : WPt W} (m : Loose a b)
    (n : Loose b c) (p : Loose c d) : (lAssocInv m n p).wt = 0 := rfl

@[simp] theorem lLeftUnitor_wt {a b : WPt W} (m : Loose a b) :
    (lLeftUnitor m).wt = 0 := rfl

@[simp] theorem lLeftUnitorInv_wt {a b : WPt W} (m : Loose a b) :
    (lLeftUnitorInv m).wt = 0 := rfl

@[simp] theorem lRightUnitor_wt {a b : WPt W} (m : Loose a b) :
    (lRightUnitor m).wt = 0 := rfl

@[simp] theorem lRightUnitorInv_wt {a b : WPt W} (m : Loose a b) :
    (lRightUnitorInv m).wt = 0 := rfl

@[reducible] def gadd (x y : G) : G := x + y

@[simp] theorem gadd_eq (x y : G) : gadd (G := G) x y = x + y := rfl

@[simp] theorem lComp_eq {a b c : WPt W} (m : Loose a b) (n : Loose b c) :
    m ⊙ n = gadd (G := G) m n := rfl

@[simp] theorem lId_eq (a : WPt W) : (lId a : Loose a a) = (0 : G) := rfl

instance : PseudoDoubleCategory (WPt W) where
  vId_vComp _ := WCell.ext (by simp)
  vComp_vId _ := WCell.ext (by simp)
  vComp_assoc _ _ _ := WCell.ext (by simp <;> abel)
  hId_id _ := WCell.ext (by simp)
  hId_comp _ _ := WCell.ext (by simp)
  hComp_vId _ _ := WCell.ext (by simp)
  interchange _ _ _ _ := WCell.ext (by simp <;> abel)
  lAssoc_natural _ _ _ := WCell.ext (by simp <;> abel)
  lLeftUnitor_natural _ := WCell.ext (by simp <;> abel)
  lRightUnitor_natural _ := WCell.ext (by simp <;> abel)
  lAssoc_lAssocInv _ _ _ := WCell.ext (by simp)
  lAssocInv_lAssoc _ _ _ := WCell.ext (by simp)
  lLeftUnitor_lLeftUnitorInv _ := WCell.ext (by simp)
  lLeftUnitorInv_lLeftUnitor _ := WCell.ext (by simp)
  lRightUnitor_lRightUnitorInv _ := WCell.ext (by simp)
  lRightUnitorInv_lRightUnitor _ := WCell.ext (by simp)
  pentagon _ _ _ _ := WCell.ext (by simp)
  triangle _ _ := WCell.ext (by simp)

/-- The monoidal data: each structure cell carries the weight `W` prescribes;
each inverse carries the negated weight. -/
instance monStruct : MonoidalDoubleCategoryStruct (WPt W) where
  tLoose m n := gadd m n
  tCell α β := ⟨by rw [α.eq, β.eq], α.wt + β.wt⟩
  chi m n m' n' :=
    ⟨by simp only [lComp_eq, gadd_eq]; abel, W.chi m n m' n'⟩
  mu a b := ⟨by simp only [lId_eq, gadd_eq]; abel, W.mu⟩
  tAssoc m n p := ⟨by simp only [gadd_eq]; abel, W.assoc m n p⟩
  tAssocInv m n p := ⟨by simp only [gadd_eq]; abel, -W.assoc m n p⟩
  tLeftUnitor m := ⟨by simp only [lId_eq, gadd_eq]; abel, W.lunit m⟩
  tLeftUnitorInv m := ⟨by simp only [lId_eq, gadd_eq]; abel, -W.lunit m⟩
  tRightUnitor m := ⟨by simp only [lId_eq, gadd_eq]; abel, W.runit m⟩
  tRightUnitorInv m := ⟨by simp only [lId_eq, gadd_eq]; abel, -W.runit m⟩

@[simp] theorem tLoose_eq {a b c d : WPt W} (m : Loose a b)
    (n : Loose c d) : m ⊠ n = gadd (G := G) m n := rfl

/-- The braided data: braiding weight from `W`. -/
instance braidedStruct : BraidedDoubleCategoryStruct (WPt W) where
  toMonoidalDoubleCategoryStruct := monStruct W
  tBraiding m n := ⟨by simp only [tLoose_eq, gadd_eq]; abel, W.braid m n⟩
  tBraidingInv m n := ⟨by simp only [tLoose_eq, gadd_eq]; abel, -W.braid m n⟩

@[simp] theorem tCell_wt {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : WPt W}
    {m₁ : Loose a₁ b₁} {n₁ : Loose c₁ d₁} {m₂ : Loose a₂ b₂}
    {n₂ : Loose c₂ d₂} {f₁ : a₁ ⟶ c₁} {g₁ : b₁ ⟶ d₁} {f₂ : a₂ ⟶ c₂}
    {g₂ : b₂ ⟶ d₂} (α : Cell m₁ n₁ f₁ g₁) (β : Cell m₂ n₂ f₂ g₂) :
    (α ⊠ᶜ β).wt = α.wt + β.wt := rfl

@[simp] theorem chi_wt {a b c a' b' c' : WPt W} (m : Loose a b)
    (n : Loose b c) (m' : Loose a' b') (n' : Loose b' c') :
    (chi m n m' n').wt = W.chi m n m' n' := rfl

@[simp] theorem mu_wt (a b : WPt W) : (mu a b).wt = W.mu := rfl

@[simp] theorem tAssoc_wt {a b c d e f : WPt W} (m : Loose a b)
    (n : Loose c d) (p : Loose e f) :
    (tAssoc m n p).wt = W.assoc m n p := rfl

@[simp] theorem tAssocInv_wt {a b c d e f : WPt W} (m : Loose a b)
    (n : Loose c d) (p : Loose e f) :
    (tAssocInv m n p).wt = -W.assoc m n p := rfl

@[simp] theorem tLeftUnitor_wt {a b : WPt W} (m : Loose a b) :
    (tLeftUnitor m).wt = W.lunit m := rfl

@[simp] theorem tLeftUnitorInv_wt {a b : WPt W} (m : Loose a b) :
    (tLeftUnitorInv m).wt = -W.lunit m := rfl

@[simp] theorem tRightUnitor_wt {a b : WPt W} (m : Loose a b) :
    (tRightUnitor m).wt = W.runit m := rfl

@[simp] theorem tRightUnitorInv_wt {a b : WPt W} (m : Loose a b) :
    (tRightUnitorInv m).wt = -W.runit m := rfl

@[simp] theorem tBraiding_wt {a b c d : WPt W} (m : Loose a b)
    (n : Loose c d) : (tBraiding m n).wt = W.braid m n := rfl

@[simp] theorem tBraidingInv_wt {a b c d : WPt W} (m : Loose a b)
    (n : Loose c d) : (tBraidingInv m n).wt = -W.braid m n := rfl

instance instLaws : MonoidalDoubleCategory (WPt W) where
  tCell_vId _ _ := WCell.ext (by simp)
  tCell_vComp _ _ _ _ := WCell.ext (by simp <;> abel)
  chi_natural α β α' β' :=
    WCell.ext (by simp [α.eq, β.eq, α'.eq, β'.eq] <;> abel)
  mu_natural _ _ := WCell.ext (by simp)
  tAssoc_natural α β γ := WCell.ext (by simp [α.eq, β.eq, γ.eq] <;> abel)
  tLeftUnitor_natural α := WCell.ext (by simp [α.eq] <;> abel)
  tRightUnitor_natural α := WCell.ext (by simp [α.eq] <;> abel)
  tAssoc_tAssocInv _ _ _ := WCell.ext (by simp)
  tAssocInv_tAssoc _ _ _ := WCell.ext (by simp)
  tLeftUnitor_tLeftUnitorInv _ := WCell.ext (by simp)
  tLeftUnitorInv_tLeftUnitor _ := WCell.ext (by simp)
  tRightUnitor_tRightUnitorInv _ := WCell.ext (by simp)
  tRightUnitorInv_tRightUnitor _ := WCell.ext (by simp)

instance instBraidedLaws : BraidedDoubleCategory (WPt W) where
  tBraiding_natural α β := WCell.ext (by simp [α.eq, β.eq] <;> abel)
  tBraiding_tBraidingInv _ _ := WCell.ext (by simp)
  tBraidingInv_tBraiding _ _ := WCell.ext (by simp)

theorem isInvertible_globular {a b : WPt W} {m n : Loose a b}
    (α : Cell m n (𝟙 a) (𝟙 b)) : α.IsInvertible :=
  ⟨⟨α.eq.symm, -α.wt⟩, WCell.ext (by simp), WCell.ext (by simp)⟩

/-- Every graded model is strong: a globular cell of weight `w` has the
inverse of weight `-w`. -/
instance instStrong : StrongMonoidalDoubleCategory (WPt W) where
  chi_isInvertible _ _ _ _ := isInvertible_globular W _
  mu_isInvertible _ _ := isInvertible_globular W _

/-!
### Linearization of the coherence mixins

Each mixin is equivalent to an explicit additive functional equation in the
weight functions.  Over finite groups both satisfaction and refutation are
decidable; over `ℤ`, polynomial witnesses are checked by `ring`/`norm_num`.
-/

/-- M1 linearized: the pentagon holds iff the associator weights satisfy the
additive pentagon equation. -/
theorem m1Pentagon_iff :
    M1Pentagon (WPt W) ↔
      ∀ m n p q : G,
        W.assoc m n p + (W.assoc m (n + p) q + W.assoc n p q) =
          W.assoc (m + n) p q + W.assoc m n (p + q) := by
  constructor
  · intro h m n p q
    have e := h.pentagon (a₁ := wpt W) (b₁ := wpt W) (a₂ := wpt W)
      (b₂ := wpt W) (a₃ := wpt W) (b₃ := wpt W) (a₄ := wpt W) (b₄ := wpt W)
      m n p q
    have ew := congrArg WCell.wt e
    simpa using ew
  · intro h
    refine ⟨fun m n p q => WCell.ext ?_⟩
    simpa using h m n p q

theorem m2Triangle_iff :
    M2Triangle (WPt W) ↔
      ∀ m n : G, W.assoc m 0 n + W.lunit n = W.runit m := by
  constructor
  · intro h m n
    have e := h.triangle (a := wpt W) (b := wpt W) (c := wpt W) (d := wpt W)
      m n
    have ew := congrArg WCell.wt e
    simpa using ew
  · intro h
    refine ⟨fun m n => WCell.ext ?_⟩
    simpa using h m n

theorem m3Hexagons_iff :
    M3Hexagons (WPt W) ↔
      (∀ m n p : G,
        W.assoc m n p + (W.braid m (n + p) + W.assoc n p m) =
          W.braid m n + (W.assoc n m p + W.braid m p)) ∧
      (∀ m n p : G,
        -W.assoc m n p + (W.braid (m + n) p + -W.assoc p m n) =
          W.braid n p + (-W.assoc m p n + W.braid m p)) ∧
      (∀ m n : G, W.braid m n + W.braid n m = 0) := by
  constructor
  · intro h
    refine ⟨fun m n p => ?_, fun m n p => ?_, fun m n => ?_⟩
    · have e := h.hexagon_forward (a₁ := wpt W) (b₁ := wpt W) (a₂ := wpt W)
        (b₂ := wpt W) (a₃ := wpt W) (b₃ := wpt W) m n p
      have ew := congrArg WCell.wt e
      simpa using ew
    · have e := h.hexagon_reverse (a₁ := wpt W) (b₁ := wpt W) (a₂ := wpt W)
        (b₂ := wpt W) (a₃ := wpt W) (b₃ := wpt W) m n p
      have ew := congrArg WCell.wt e
      simpa using ew
    · have e := h.involutive (a := wpt W) (b := wpt W) (c := wpt W)
        (d := wpt W) m n
      have ew := congrArg WCell.wt e
      simpa using ew
  · intro ⟨h₁, h₂, h₃⟩
    refine ⟨fun m n p => WCell.ext ?_, fun m n p => WCell.ext ?_,
      fun m n => WCell.ext ?_⟩
    · simpa using h₁ m n p
    · simpa using h₂ m n p
    · simpa using h₃ m n

theorem m4InterchangerAssoc_iff :
    M4InterchangerAssoc (WPt W) ↔
      ∀ m n p m' n' p' : G,
        W.chi m n m' n' + W.chi (m + n) p (m' + n') p' =
          W.chi n p n' p' + W.chi m (n + p) m' (n' + p') := by
  constructor
  · intro h m n p m' n' p'
    have e := h.assoc (a := wpt W) (b := wpt W) (c := wpt W) (d := wpt W)
      (a' := wpt W) (b' := wpt W) (c' := wpt W) (d' := wpt W)
      m n p m' n' p'
    have ew := congrArg WCell.wt e
    simpa using ew
  · intro h
    refine ⟨fun m n p m' n' p' => WCell.ext ?_⟩
    simpa using h m n p m' n' p'

theorem m5InterchangerUnit_iff :
    M5InterchangerUnit (WPt W) ↔
      (∀ m m' : G, W.mu + W.chi 0 m 0 m' = 0) ∧
      (∀ m m' : G, W.mu + W.chi m 0 m' 0 = 0) := by
  constructor
  · intro h
    refine ⟨fun m m' => ?_, fun m m' => ?_⟩
    · have e := h.left (a := wpt W) (b := wpt W) (a' := wpt W) (b' := wpt W)
        m m'
      have ew := congrArg WCell.wt e
      simpa using ew
    · have e := h.right (a := wpt W) (b := wpt W) (a' := wpt W) (b' := wpt W)
        m m'
      have ew := congrArg WCell.wt e
      simpa using ew
  · intro ⟨hl, hr⟩
    refine ⟨fun m m' => WCell.ext ?_, fun m m' => WCell.ext ?_⟩
    · simpa using hl m m'
    · simpa using hr m m'

theorem m6BraidingInterchanger_iff :
    M6BraidingInterchanger (WPt W) ↔
      ∀ m n m' n' : G,
        W.chi m n m' n' + W.braid (m + n) (m' + n') =
          W.braid m m' + W.braid n n' + W.chi m' n' m n := by
  constructor
  · intro h m n m' n'
    have e := h.braiding_chi (a := wpt W) (b := wpt W) (c := wpt W)
      (a' := wpt W) (b' := wpt W) (c' := wpt W) m n m' n'
    have ew := congrArg WCell.wt e
    simpa using ew
  · intro h
    refine ⟨fun m n m' n' => WCell.ext ?_⟩
    simpa using h m n m' n'

theorem m7UnitorUnit_iff :
    M7UnitorUnit (WPt W) ↔
      (W.mu + W.lunit 0 = 0) ∧ (W.mu + W.runit 0 = 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have e := h.left (wpt W)
      have ew := congrArg WCell.wt e
      simpa using ew
    · have e := h.right (wpt W)
      have ew := congrArg WCell.wt e
      simpa using ew
  · intro ⟨hl, hr⟩
    refine ⟨fun a => WCell.ext ?_, fun a => WCell.ext ?_⟩
    · simpa using hl
    · simpa using hr

theorem m9AssociatorInterchanger_iff :
    M9AssociatorInterchanger (WPt W) ↔
      ∀ m₁ n₁ m₂ n₂ m₃ n₃ : G,
        W.chi (m₁ + m₂) (n₁ + n₂) m₃ n₃ + W.chi m₁ n₁ m₂ n₂ +
            W.assoc (m₁ + n₁) (m₂ + n₂) (m₃ + n₃) =
          W.assoc m₁ m₂ m₃ + W.assoc n₁ n₂ n₃ +
            (W.chi m₁ n₁ (m₂ + m₃) (n₂ + n₃) + W.chi m₂ n₂ m₃ n₃) := by
  constructor
  · intro h m₁ n₁ m₂ n₂ m₃ n₃
    have e := h.assoc_chi (a₁ := wpt W) (b₁ := wpt W) (c₁ := wpt W)
      (a₂ := wpt W) (b₂ := wpt W) (c₂ := wpt W) (a₃ := wpt W) (b₃ := wpt W)
      (c₃ := wpt W) m₁ n₁ m₂ n₂ m₃ n₃
    have ew := congrArg WCell.wt e
    simpa using ew
  · intro h
    refine ⟨fun m₁ n₁ m₂ n₂ m₃ n₃ => WCell.ext ?_⟩
    simpa using h m₁ n₁ m₂ n₂ m₃ n₃

theorem m10UnitorInterchanger_iff :
    M10UnitorInterchanger (WPt W) ↔
      (∀ m n : G,
        W.chi 0 0 m n + W.lunit (m + n) = W.lunit m + W.lunit n) ∧
      (∀ m n : G,
        W.chi m n 0 0 + W.runit (m + n) = W.runit m + W.runit n) := by
  constructor
  · intro h
    refine ⟨fun m n => ?_, fun m n => ?_⟩
    · have e := h.left (a := wpt W) (b := wpt W) (c := wpt W) m n
      have ew := congrArg WCell.wt e
      simpa using ew
    · have e := h.right (a := wpt W) (b := wpt W) (c := wpt W) m n
      have ew := congrArg WCell.wt e
      simpa using ew
  · intro ⟨hl, hr⟩
    refine ⟨fun m n => WCell.ext ?_, fun m n => WCell.ext ?_⟩
    · simpa using hl m n
    · simpa using hr m n

theorem m11aAssociatorUnit_iff :
    M11aAssociatorUnit (WPt W) ↔ W.assoc 0 0 0 = 0 := by
  constructor
  · intro h
    have e := h.assoc_mu (wpt W) (wpt W) (wpt W)
    have ew := congrArg WCell.wt e
    simpa using ew
  · intro h
    refine ⟨fun a b c => WCell.ext ?_⟩
    simp [h]

theorem m11bBraidingUnit_iff :
    M11bBraidingUnit (WPt W) ↔ W.braid 0 0 = 0 := by
  constructor
  · intro h
    have e := h.braiding_mu (wpt W) (wpt W)
    have ew := congrArg WCell.wt e
    simpa using ew
  · intro h
    refine ⟨fun a b => WCell.ext ?_⟩
    simp [h]

end Graded

end MonoidalDoubleCategory

end CategoryTheory
