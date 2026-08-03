import SuFunctor.Site.WindowPenalty
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Whiskering

/-! # The interval base site of temporal type theory, and the anchor quotient

The site-level leg of the inclusion of Schultz–Spivak temporal type
theory (*Temporal Type Theory: a topos-theoretic approach to systems
and behavior*, arXiv:1710.10258) into the site-indexed spec tier.

Temporal type theory takes behavior types to be sheaves on the
**translation-invariant interval base site** `𝕀`: objects are
durations `ℓ ≥ 0`, morphisms `ℓ′ ⟶ ℓ` are *shave-off* pairs `[r|s]`
with `r + ℓ′ + s = ℓ` (place an interval of duration `ℓ′` inside one
of duration `ℓ`, leaving gap `r` on the left and `s` on the right),
and the covers of `ℓ` are the families of *wavy* arrows (`r, s > 0` —
the strictly interior placements).  This module builds:

* `IntervalBase` — the base site as a category, with the shave-off
  calculus proved (their `def:IRinv`);
* `Window` — anchored closed windows `[d, u] ⊆ ℝ` under inclusion:
  the classical window family of the spec tier's site direction
  (the inclusion-ordered opposite of their interval domain `𝕀ℝ`,
  `def:interval_domain`);
* `anchorQuot : Window ⥤ IntervalBase` — the **translation quotient**
  (length of a window; gaps of an inclusion), with the discrete
  (bi)fibration property of their `lem:discrete_fibration` proved as
  unique-lift theorems in both directions, surjectivity on objects,
  and the cover correspondence: an inclusion's gaps are both positive
  iff the subwindow is strictly interior — the base site's wavy
  covers are exactly the interior covers the spec tier's window
  presheaves restrict along;
* `ssTraj X` — the motivating behavior type of temporal type theory,
  anchored form: `ℓ ↦ (trajectories [0, ℓ] → X)`, restriction along
  `[r|s]` = translate by `r` and clip;
* `windowTraj X` — the spec tier's own trajectory presheaf
  `W ↦ Traj W.set X` with `trajRes` restriction;
* `anchorTrajIso` — the natural isomorphism between the pullback of
  `ssTraj X` along the anchor quotient and `windowTraj X`: the
  behavior type of trajectories *is* the window-trajectory presheaf,
  up to the translation that the quotient exists to forget.  (Strict
  equality is impossible — translation-invariance is the point — so
  the natural isomorphism is the correct strength of the claim.)
* `behaviorPullback` — precomposition with the anchor quotient: the
  functorial inclusion of *all* behavior types into window
  presheaves, of which the trajectory identification is the
  motivating component.

No coverage machinery (`GrothendieckTopology`, sheafification) is
consumed or built here: the spec tier's fibre objects are the *lax*
sections of the window presheaf (persistent families — see
`SuFunctor.Site.MatchingFork` for why strict sections were never the
fibre objects), so the inclusion owes no descent.  The sheaf
condition of temporal type theory is deliberately left on the shelf,
priced as a successor.
-/

namespace SuFunctor

namespace Site

namespace TTT

noncomputable section

open CategoryTheory
open scoped NNReal

/-! ## The interval base site -/

/-- An object of the translation-invariant interval base site of
temporal type theory: a duration. -/
@[ext]
structure IntervalBase : Type where
  /-- The duration of the interval. -/
  len : ℝ≥0

/-- A shave-off morphism `[r|s] : ℓ′ ⟶ ℓ` of the interval base site:
place a subinterval of duration `ℓ′` inside an interval of duration
`ℓ`, leaving gap `r` on the left and `s` on the right. -/
@[ext]
structure Shave (a b : IntervalBase) : Type where
  /-- The left gap. -/
  r : ℝ≥0
  /-- The right gap. -/
  s : ℝ≥0
  /-- The placement equation. -/
  eq : r + a.len + s = b.len

instance : Category IntervalBase where
  Hom := Shave
  id a := ⟨0, 0, by simp⟩
  comp {a b c} e₁ e₂ :=
    ⟨e₂.r + e₁.r, e₁.s + e₂.s, by
      have h₁ := e₁.eq
      have h₂ := e₂.eq
      calc e₂.r + e₁.r + a.len + (e₁.s + e₂.s)
          = e₂.r + (e₁.r + a.len + e₁.s) + e₂.s := by ring
        _ = c.len := by rw [h₁, h₂]⟩
  id_comp e := by ext <;> simp
  comp_id e := by ext <;> simp
  assoc e₁ e₂ e₃ := by ext <;> simp [add_assoc]

@[simp] theorem id_r (a : IntervalBase) : Shave.r (𝟙 a) = 0 := rfl
@[simp] theorem id_s (a : IntervalBase) : Shave.s (𝟙 a) = 0 := rfl
@[simp] theorem comp_r {a b c : IntervalBase} (e₁ : a ⟶ b) (e₂ : b ⟶ c) :
    (e₁ ≫ e₂).r = e₂.r + e₁.r := rfl
@[simp] theorem comp_s {a b c : IntervalBase} (e₁ : a ⟶ b) (e₂ : b ⟶ c) :
    (e₁ ≫ e₂).s = e₁.s + e₂.s := rfl

/-! ## Anchored windows: the classical window family -/

/-- An anchored closed window `[d, u] ⊆ ℝ`: an object of the classical
window family of the spec tier's site direction. -/
@[ext]
structure Window : Type where
  /-- Left endpoint. -/
  d : ℝ
  /-- Right endpoint. -/
  u : ℝ
  /-- Nondegeneracy. -/
  dle : d ≤ u

namespace Window

/-- Windows are preordered by inclusion (the categorical direction:
a morphism `W′ ⟶ W` is an inclusion of `W′` into `W`). -/
instance : Preorder Window where
  le W' W := W.d ≤ W'.d ∧ W'.u ≤ W.u
  le_refl W := ⟨le_refl _, le_refl _⟩
  le_trans W₁ W₂ W₃ h₁ h₂ := ⟨h₂.1.trans h₁.1, h₁.2.trans h₂.2⟩

/-- The window's carrier set. -/
def set (W : Window) : Set ℝ := Set.Icc W.d W.u

theorem set_mono {W' W : Window} (h : W' ≤ W) : W'.set ⊆ W.set :=
  Set.Icc_subset_Icc h.1 h.2

theorem set_subset_iff {W' W : Window} : W'.set ⊆ W.set ↔ W' ≤ W :=
  Set.Icc_subset_Icc_iff W'.dle

/-- The window's duration. -/
def len (W : Window) : ℝ≥0 := ⟨W.u - W.d, sub_nonneg.mpr W.dle⟩

@[simp] theorem coe_len (W : Window) : (W.len : ℝ) = W.u - W.d := rfl

end Window

/-! ## The anchor quotient -/

/-- **The translation quotient**: a window forgets its anchor and
remembers its duration; an inclusion forgets its position and
remembers its gaps.  This is the quotient by translation through
which temporal type theory's base site arises from the interval
domain. -/
def anchorQuot : Window ⥤ IntervalBase where
  obj W := ⟨W.len⟩
  map {W' W} h :=
    { r := ⟨W'.d - W.d, sub_nonneg.mpr (leOfHom h).1⟩
      s := ⟨W.u - W'.u, sub_nonneg.mpr (leOfHom h).2⟩
      eq := by
        apply NNReal.coe_injective
        rw [NNReal.coe_add, NNReal.coe_add]
        show (W'.d - W.d) + (W'.u - W'.d) + (W.u - W'.u) = W.u - W.d
        ring }
  map_id W := by
    refine Shave.ext ?_ ?_
    · exact NNReal.coe_injective (by show W.d - W.d = (0 : ℝ); ring)
    · exact NNReal.coe_injective (by show W.u - W.u = (0 : ℝ); ring)
  map_comp {W₁ W₂ W₃} h₁ h₂ := by
    refine Shave.ext ?_ ?_
    · exact NNReal.coe_injective (by
        show W₁.d - W₃.d = (W₂.d - W₃.d) + (W₁.d - W₂.d)
        ring)
    · exact NNReal.coe_injective (by
        show W₃.u - W₁.u = (W₂.u - W₁.u) + (W₃.u - W₂.u)
        ring)

@[simp] theorem anchorQuot_obj (W : Window) : anchorQuot.obj W = ⟨W.len⟩ := rfl

@[simp] theorem anchorQuot_map_r {W' W : Window} (h : W' ⟶ W) :
    ((anchorQuot.map h).r : ℝ) = W'.d - W.d := rfl

@[simp] theorem anchorQuot_map_s {W' W : Window} (h : W' ⟶ W) :
    ((anchorQuot.map h).s : ℝ) = W.u - W'.u := rfl

/-- Every duration is the length of its `0`-anchored representative:
the quotient is surjective on objects on the nose. -/
theorem anchorQuot_obj_surjective : Function.Surjective anchorQuot.obj := by
  intro ℓ
  refine ⟨⟨0, ℓ.len, ℓ.len.coe_nonneg⟩, ?_⟩
  ext
  show (ℓ.len : ℝ) - 0 = (ℓ.len : ℝ)
  ring

/-- **The unique upward lift** (the opfibration half of temporal type
theory's discrete-fibration lemma for the translation quotient): given
a window and a prescribed gap pair, there is exactly one superwindow
realizing those gaps. -/
theorem existsUnique_lift_up (W' : Window) (r s : ℝ≥0) :
    ∃! W : Window, ∃ h : W' ≤ W,
      (anchorQuot.map (homOfLE h)).r = r ∧ (anchorQuot.map (homOfLE h)).s = s := by
  have hd : (W'.d - r : ℝ) ≤ W'.u + s := by
    have := W'.dle
    have hr := r.coe_nonneg
    have hs := s.coe_nonneg
    linarith
  refine ⟨⟨W'.d - r, W'.u + s, hd⟩,
    ⟨⟨by linarith [r.coe_nonneg], by linarith [s.coe_nonneg]⟩, ?_, ?_⟩, ?_⟩
  · apply NNReal.coe_injective
    simp
  · apply NNReal.coe_injective
    simp
  · rintro W ⟨h, hr, hs⟩
    have hr' : W'.d - W.d = (r : ℝ) := congrArg NNReal.toReal hr
    have hs' : W.u - W'.u = (s : ℝ) := congrArg NNReal.toReal hs
    ext
    · linarith
    · linarith

/-- **The unique downward lift** (the fibration half): given a window
and a gap pair that fits inside it, there is exactly one subwindow
realizing those gaps. -/
theorem existsUnique_lift_down (W : Window) (r s : ℝ≥0) (hrs : r + s ≤ W.len) :
    ∃! W' : Window, ∃ h : W' ≤ W,
      (anchorQuot.map (homOfLE h)).r = r ∧ (anchorQuot.map (homOfLE h)).s = s := by
  have hrs' : (r : ℝ) + s ≤ W.u - W.d := by
    have := NNReal.coe_le_coe.mpr hrs
    push_cast at this
    simpa using this
  have hd : (W.d + r : ℝ) ≤ W.u - s := by linarith
  refine ⟨⟨W.d + r, W.u - s, hd⟩,
    ⟨⟨by linarith [r.coe_nonneg], by linarith [s.coe_nonneg]⟩, ?_, ?_⟩, ?_⟩
  · apply NNReal.coe_injective
    simp
  · apply NNReal.coe_injective
    simp
  · rintro W' ⟨h, hr, hs⟩
    have hr' : W'.d - W.d = (r : ℝ) := congrArg NNReal.toReal hr
    have hs' : W.u - W'.u = (s : ℝ) := congrArg NNReal.toReal hs
    ext
    · linarith
    · linarith

/-- **The cover correspondence**: an inclusion's gaps are both positive
iff the subwindow is strictly interior.  The base site's wavy covers
are exactly the interior covers. -/
theorem wavy_iff_strictlyInterior {W' W : Window} (h : W' ≤ W) :
    (0 < (anchorQuot.map (homOfLE h)).r ∧ 0 < (anchorQuot.map (homOfLE h)).s) ↔
      (W.d < W'.d ∧ W'.u < W.u) := by
  rw [← NNReal.coe_pos, ← NNReal.coe_pos, anchorQuot_map_r, anchorQuot_map_s,
    sub_pos, sub_pos]

/-! ## The trajectory behavior type, and the identification -/

variable (X : Type)

/-- The motivating behavior type of temporal type theory, anchored
form: length-`ℓ` behaviors of a state space `X` are trajectories
`[0, ℓ] → X`; restriction along a shave-off `[r|s]` translates by `r`
and clips. -/
def ssTraj : IntervalBaseᵒᵖ ⥤ Type where
  obj ℓ := Traj (Set.Icc (0 : ℝ) (ℓ.unop.len : ℝ)) X
  map {ℓ ℓ'} e := TypeCat.ofHom fun x => fun t =>
    x ⟨(t : ℝ) + (e.unop.r : ℝ),
      ⟨add_nonneg t.2.1 e.unop.r.coe_nonneg, by
        have heq : ((e.unop.r : ℝ) + ℓ'.unop.len + e.unop.s) = ℓ.unop.len := by
          have := congrArg NNReal.toReal e.unop.eq
          push_cast at this
          simpa using this
        have ht := t.2.2
        have hs := e.unop.s.coe_nonneg
        linarith⟩⟩
  map_id ℓ :=
    congrArg TypeCat.ofHom (funext fun x => funext fun t =>
      congrArg x (Subtype.ext (by simp)))
  map_comp {ℓ₁ ℓ₂ ℓ₃} f g :=
    congrArg TypeCat.ofHom (funext fun x => funext fun t =>
      congrArg x (Subtype.ext (by
        show (t : ℝ) + (((f ≫ g).unop.r : ℝ≥0) : ℝ)
            = ((t : ℝ) + (g.unop.r : ℝ)) + (f.unop.r : ℝ)
        rw [show (f ≫ g).unop.r = f.unop.r + g.unop.r from rfl, NNReal.coe_add]
        ring)))

/-- The spec tier's own trajectory presheaf on the classical windows:
`W ↦ Traj W.set X`, restriction by clipping. -/
def windowTraj : Windowᵒᵖ ⥤ Type where
  obj W := Traj W.unop.set X
  map h := TypeCat.ofHom (trajRes (Window.set_mono (leOfHom h.unop)))
  map_id W := rfl
  map_comp h₁ h₂ := rfl

/-- The translation equivalence between anchored trajectories over
`[0, len W]` and trajectories over the window itself. -/
def anchorTrajEquiv (W : Window) :
    Traj (Set.Icc (0 : ℝ) (W.len : ℝ)) X ≃ Traj W.set X where
  toFun x := fun t =>
    x ⟨(t : ℝ) - W.d,
      ⟨sub_nonneg.mpr t.2.1, by
        have ht := t.2.2
        simp only [Window.coe_len]
        linarith⟩⟩
  invFun y := fun t =>
    y ⟨(t : ℝ) + W.d,
      ⟨by
        have := t.2.1
        linarith, by
        have ht := t.2.2
        simp only [Window.coe_len] at ht
        linarith⟩⟩
  left_inv x := funext fun t => congrArg x (Subtype.ext (by
    show ((t : ℝ) + W.d) - W.d = (t : ℝ)
    ring))
  right_inv y := funext fun t => congrArg y (Subtype.ext (by
    show ((t : ℝ) - W.d) + W.d = (t : ℝ)
    ring))

/-- **The identification**: the pullback of the trajectory behavior
type along the anchor quotient is naturally isomorphic to the window
trajectory presheaf — trajectories, as a behavior type of temporal
type theory, *are* the spec tier's window trajectories, up to the
translation the quotient exists to forget. -/
def anchorTrajIso : anchorQuot.op ⋙ ssTraj X ≅ windowTraj X :=
  NatIso.ofComponents
    (fun W => (anchorTrajEquiv X W.unop).toIso)
    (fun {W W'} h =>
      congrArg TypeCat.ofHom (funext fun x => funext fun t =>
        congrArg x (Subtype.ext (by
          show ((t : ℝ) - W'.unop.d) + ((anchorQuot.map h.unop).r : ℝ)
              = (t : ℝ) - W.unop.d
          rw [anchorQuot_map_r]
          ring))))

/-- Precomposition with the anchor quotient: the functorial inclusion
of all behavior types into window presheaves. -/
def behaviorPullback : (IntervalBaseᵒᵖ ⥤ Type) ⥤ (Windowᵒᵖ ⥤ Type) :=
  (Functor.whiskeringLeft _ _ _).obj anchorQuot.op

@[simp] theorem behaviorPullback_obj (B : IntervalBaseᵒᵖ ⥤ Type) :
    behaviorPullback.obj B = anchorQuot.op ⋙ B := rfl

end

end TTT

end Site

end SuFunctor
