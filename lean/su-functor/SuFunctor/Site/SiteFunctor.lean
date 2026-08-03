import SuFunctor.Site.WindowPenalty
import DoubleCat.Opfibration

/-! # The site-indexed spec-class decoration functor, and its plain total

The sheaf upgrade of the spec-class decoration tier: over the *unchanged*
wiring base (`DoubleCat.WireSpan` — interfaces and wirings, exactly as in
the plain tier), assign to each interface not one class of penalty
functionals but a **window-indexed persistent family** of them — the
fibre-sheaf presentation of the spec tier, with the site direction
entering through the decoration and never through the base.  Every
operation of the plain functor lifts componentwise:

* tight and cell transports are the componentwise images of penalty
  pullback along `trajMap`-transported wire/apex maps;
* the compositor is the componentwise `Set.image2` of the window
  compositor `boxplusW`; the unit is the componentwise singleton of the
  austere window unit;
* persistence of every result is exactly the site-direction naturality
  package of `SuFunctor.Site.WindowPenalty` (`penExt_pull_trajMap`,
  `penExt_boxplusW`, `penExt_unitPenW`).

Each lax-double-functor obligation reduces componentwise, by
`Subtype.ext` and one `funext`, to the corresponding plain coherence
core at trajectory carriers — the proofs below are the plain tier's
scripts with the componentwise wrapper added and nothing else changed.
The plain double Grothendieck construction (`DoubleCat.Grothendieck`)
then consumes the functor as-is: the total is a pseudo double category
with a strict pseudo projection, and the projection is a discrete
double opfibration **by the generic theorem** (`DoubleCat.Opfibration`),
which never inspects fibre internals — the site dimension rides inside
the fibre objects, invisible to the lifting calculus.

Fibres are the *persistent* families (the lax sections of the window
presheaf of classes).  The strict sections (matching families) are not
closed under the compositor — `SuFunctor.Site.MatchingFork` — so the
site dimension selects the fibre objects; it never perturbs the seven
obligations, whose laxators here are exactly as strict or as lax as the
plain tier's.
-/

namespace SuFunctor

namespace Site

noncomputable section

open CategoryTheory CategoryTheory.WireSpan PseudoDoubleCategoryStruct
open SuFunctor.Plain
open scoped NNReal ENNReal

universe u

variable {T ι : Type u}

/-- The site-indexed spec fibre at an interface: persistent
window-indexed families of penalty classes on trajectories over the
interface's states.  (Componentwise inclusion is the fibre order; the
judgment against a family is componentwise membership of ideal
points.) -/
def WSpec (U : ι → Set T) {El : Type u} (A : WireSpan El) : Type u :=
  {Φ : ∀ i, Set (Pen (Traj (U i) (states A))) // IsPersistent U Φ}

/-- The site-indexed decorations over a wiring pattern: persistent
window-indexed families of apex penalty classes.  Boundary families are
pure designations, exactly as in the plain tier. -/
def WCpl (U : ι → Set T) {El : Type u} {A B : WireSpan El} (M : Pat A B) :
    Type u :=
  {Φ : ∀ i, Set (Pen (Traj (U i) (Pat.Tot M))) // IsPersistent U Φ}

variable (U : ι → Set T) {El : Type u}

/-- Tight transport of site-indexed spec families: the componentwise
image of penalty pullback along the (trajectory-transported) wire
map. -/
def wSpecMap {A B : WireSpan El} (φ : A ⟶ B) (𝒮 : WSpec U A) :
    WSpec U B :=
  ⟨fun i => Pen.pull (trajMap (res φ)) '' 𝒮.1 i,
    𝒮.2.image_pull_trajMap (res φ)⟩

/-- Cell transport of site-indexed decorations: the componentwise image
of penalty pullback along the (trajectory-transported) backward apex
map. -/
def wCellMap {A B A' B' : WireSpan El} {M : Pat A B} {N : Pat A' B'}
    {φ : A ⟶ A'} {ψ : B ⟶ B'} (γ : PatCell M N φ ψ) (𝒰 : WCpl U M) :
    WCpl U N :=
  ⟨fun i => Pen.pull (trajMap (PatCell.tot γ)) '' 𝒰.1 i,
    𝒰.2.image_pull_trajMap (PatCell.tot γ)⟩

/-- The site-indexed compositor: componentwise `image2` of the window
compositor.  Persistence rides the window–compositor exchange. -/
def wComp {A B C : WireSpan El} {M : Pat A B} {N : Pat B C}
    (𝒰 : WCpl U M) (𝒱 : WCpl U N) : WCpl U (Pat.comp M N) :=
  ⟨fun i => Set.image2 boxplusW (𝒰.1 i) (𝒱.1 i),
    𝒰.2.image2_boxplusW 𝒱.2⟩

/-- The site-indexed unit: the componentwise singleton of the austere
window unit. -/
def wUnit (A : WireSpan El) : WCpl U (Pat.id A) :=
  ⟨fun i => {unitPenW A (U i)}, isPersistent_unitPenW U A⟩

/-- The object-and-tight-arrow tier of the site-indexed functor.
(Promotion with `TypeCat.ofHom` exactly as in the plain tier; the
functor laws are componentwise the plain arguments.) -/
def wSpecObj (U : ι → Set T) (El : Type u) : WireSpan El ⥤ Type u where
  obj A := WSpec U A
  map φ := TypeCat.ofHom (wSpecMap U φ)
  map_id A :=
    congrArg TypeCat.ofHom (funext fun 𝒮 => Subtype.ext (funext fun i => by
      show Pen.pull (trajMap (res (𝟙 A))) '' 𝒮.1 i = 𝒮.1 i
      have h : Pen.pull (trajMap (W := U i) (X := states A) (res (𝟙 A)))
          = id :=
        funext fun f => Pen.pull_id f
      rw [h, Set.image_id]))
  map_comp f g :=
    congrArg TypeCat.ofHom (funext fun 𝒮 => Subtype.ext (funext fun i => by
      show Pen.pull (trajMap (res (f ≫ g))) '' 𝒮.1 i =
        Pen.pull (trajMap (res g)) '' (Pen.pull (trajMap (res f)) '' 𝒮.1 i)
      rw [← Set.image_comp]
      congr 1
      funext u
      exact (Pen.pull_pull (trajMap (res f)) (trajMap (res g)) u).symm))

/-- **The site-indexed spec-class decoration functor**: a span-valued
lax double functor on the *unchanged* wiring base whose fibres are
persistent window-indexed class families.  Every obligation is the
plain tier's, componentwise. -/
def siteSpecFunctor (U : ι → Set T) (El : Type u) :
    SpanValued.{u + 1, u, u, u + 1, u} (WireSpan El) where
  toFunctor := wSpecObj U El
  mapLoose M := fun _ _ => WCpl U M
  mapCell γ := fun _ _ 𝒰 => wCellMap U γ 𝒰
  mapCell_vId M := by
    have key : ∀ 𝒰 : WCpl U M,
        wCellMap U (PseudoDoubleCategoryStruct.vId (C := WireSpan El) M) 𝒰
          = 𝒰 := by
      intro 𝒰
      refine Subtype.ext (funext fun i => ?_)
      show Pen.pull (trajMap (PatCell.tot
          (PseudoDoubleCategoryStruct.vId (C := WireSpan El) M))) '' 𝒰.1 i
        = 𝒰.1 i
      have h : Pen.pull (trajMap (W := U i) (X := Pat.Tot M) (PatCell.tot
          (PseudoDoubleCategoryStruct.vId (C := WireSpan El) M))) = id :=
        funext fun u => Pen.pull_id u
      rw [h, Set.image_id]
    funext 𝒮 𝒯 𝒰
    exact (key 𝒰).trans (eq_of_heq (DepSpan.FamCell.heq_apply
      ((wSpecObj U El).map_id _) ((wSpecObj U El).map_id _)
      (Cell.cast_heq ((wSpecObj U El).map_id _).symm
        ((wSpecObj U El).map_id _).symm
        (PseudoDoubleCategoryStruct.vId (C := Type u) (fun _ _ => WCpl U M)))
      𝒮 𝒯 𝒰)).symm
  mapCell_vComp α β := by
    have key : ∀ 𝒰,
        wCellMap U (PseudoDoubleCategoryStruct.vComp (C := WireSpan El) α β)
            𝒰 =
          wCellMap U β (wCellMap U α 𝒰) := by
      intro 𝒰
      refine Subtype.ext (funext fun i => ?_)
      show Pen.pull (trajMap (PatCell.tot
          (PseudoDoubleCategoryStruct.vComp (C := WireSpan El) α β))) ''
            𝒰.1 i =
        Pen.pull (trajMap (PatCell.tot β)) ''
          (Pen.pull (trajMap (PatCell.tot α)) '' 𝒰.1 i)
      rw [← Set.image_comp]
      congr 1
      funext u
      exact (Pen.pull_pull (trajMap (PatCell.tot α))
        (trajMap (PatCell.tot β)) u).symm
    funext 𝒮 𝒯 𝒰
    rw [cast_apply_const]
    exact key 𝒰
  laxComp M N := fun _ _ s => wComp U s.2.1 s.2.2
  laxId A := fun _ _ _ => wUnit U A
  laxComp_natural α β := by
    have key : ∀ (𝒰₁ : WCpl U _) (𝒰₂ : WCpl U _),
        wCellMap U (PseudoDoubleCategoryStruct.hComp (C := WireSpan El) α β)
            (wComp U 𝒰₁ 𝒰₂) =
          wComp U (wCellMap U α 𝒰₁) (wCellMap U β 𝒰₂) := by
      intro 𝒰₁ 𝒰₂
      refine Subtype.ext (funext fun i => ?_)
      show Pen.pull (trajMap (PatCell.tot
          (PseudoDoubleCategoryStruct.hComp (C := WireSpan El) α β))) ''
            Set.image2 boxplusW (𝒰₁.1 i) (𝒰₂.1 i) =
        Set.image2 boxplusW
          (Pen.pull (trajMap (PatCell.tot α)) '' 𝒰₁.1 i)
          (Pen.pull (trajMap (PatCell.tot β)) '' 𝒰₂.1 i)
      rw [Set.image_image2, Set.image2_image_left, Set.image2_image_right]
      exact Set.image2_congr fun u₁ _ u₂ _ =>
        pullW_tot_hComp_boxplusW α β u₁ u₂
    exact (Cell.eq_cast_iff_heq (C := Type u)).mpr
      (DepSpan.FamCell.heq_of_apply (by simp) (by simp)
        fun 𝒮 𝒱 s => heq_of_eq (key s.2.1 s.2.2))
  laxId_natural f := by
    have key : wCellMap U (PseudoDoubleCategoryStruct.hId (C := WireSpan El) f)
        (wUnit U _) = wUnit U _ := by
      refine Subtype.ext (funext fun i => ?_)
      show Pen.pull (trajMap (PatCell.tot
          (PseudoDoubleCategoryStruct.hId (C := WireSpan El) f))) ''
            {unitPenW _ (U i)} = {unitPenW _ (U i)}
      rw [Set.image_singleton]
      exact rfl
    exact (Cell.eq_cast_iff_heq (C := Type u)).mpr
      (DepSpan.FamCell.heq_of_apply (by simp) (by simp)
        fun 𝒮 𝒮' e => heq_of_eq key)
  laxComp_assoc M N P := by
    have key : ∀ (𝒰₁ : WCpl U M) (𝒰₂ : WCpl U N) (𝒰₃ : WCpl U P),
        wCellMap U (PseudoDoubleCategoryStruct.lAssoc (C := WireSpan El) M N P)
            (wComp U (wComp U 𝒰₁ 𝒰₂) 𝒰₃) =
          wComp U 𝒰₁ (wComp U 𝒰₂ 𝒰₃) := by
      intro 𝒰₁ 𝒰₂ 𝒰₃
      refine Subtype.ext (funext fun i => ?_)
      show Pen.pull (trajMap (PatCell.tot
          (PseudoDoubleCategoryStruct.lAssoc (C := WireSpan El) M N P))) ''
            Set.image2 boxplusW
              (Set.image2 boxplusW (𝒰₁.1 i) (𝒰₂.1 i)) (𝒰₃.1 i) =
        Set.image2 boxplusW (𝒰₁.1 i)
          (Set.image2 boxplusW (𝒰₂.1 i) (𝒰₃.1 i))
      rw [Set.image_image2]
      exact Set.image2_assoc fun u₁ u₂ u₃ =>
        pullW_tot_lAssoc_boxplusW M N P u₁ u₂ u₃
    exact (Cell.eq_cast_iff_heq (C := Type u)).mpr
      (DepSpan.FamCell.heq_of_apply (by simp) (by simp)
        fun 𝒮 𝒱 s => heq_of_eq (key s.2.1.2.1 s.2.1.2.2 s.2.2))
  laxComp_leftUnitor M := by
    have key : ∀ 𝒰 : WCpl U M,
        wCellMap U
            (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M)
            (wComp U (wUnit U _) 𝒰) = 𝒰 := by
      intro 𝒰
      refine Subtype.ext (funext fun i => ?_)
      show Pen.pull (trajMap (PatCell.tot
          (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M))) ''
            Set.image2 boxplusW {unitPenW _ (U i)} (𝒰.1 i) = 𝒰.1 i
      rw [Set.image2_singleton_left, ← Set.image_comp]
      have h : Pen.pull (trajMap (PatCell.tot
            (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M))) ∘
            boxplusW (unitPenW _ (U i)) = id :=
        funext fun u => pullW_tot_lLeftUnitor_boxplusW M u
      rw [h, Set.image_id]
    exact (Cell.eq_cast_iff_heq (C := Type u)).mpr
      (DepSpan.FamCell.heq_of_apply (by simp) (by simp)
        fun 𝒮 𝒯 s => heq_of_eq (by
          obtain ⟨𝒮', e, 𝒰⟩ := s
          obtain ⟨⟨rfl⟩⟩ := e
          exact key 𝒰))
  laxComp_rightUnitor M := by
    have key : ∀ 𝒰 : WCpl U M,
        wCellMap U
            (PseudoDoubleCategoryStruct.lRightUnitor (C := WireSpan El) M)
            (wComp U 𝒰 (wUnit U _)) = 𝒰 := by
      intro 𝒰
      refine Subtype.ext (funext fun i => ?_)
      show Pen.pull (trajMap (PatCell.tot
          (PseudoDoubleCategoryStruct.lRightUnitor (C := WireSpan El) M))) ''
            Set.image2 boxplusW (𝒰.1 i) {unitPenW _ (U i)} = 𝒰.1 i
      rw [Set.image2_singleton_right, ← Set.image_comp]
      have h : Pen.pull (trajMap (PatCell.tot
            (PseudoDoubleCategoryStruct.lRightUnitor (C := WireSpan El) M))) ∘
            (fun u => boxplusW u (unitPenW _ (U i))) = id :=
        funext fun u => pullW_tot_lRightUnitor_boxplusW M u
      rw [h, Set.image_id]
    exact (Cell.eq_cast_iff_heq (C := Type u)).mpr
      (DepSpan.FamCell.heq_of_apply (by simp) (by simp)
        fun 𝒮 𝒯 s => heq_of_eq (by
          obtain ⟨𝒯', 𝒰, e⟩ := s
          obtain ⟨⟨rfl⟩⟩ := e
          exact key 𝒰))

/-! ## The total: the plain construction consumes the site-indexed
functor as-is -/

/-- **The double category of site-indexed spec classes**: the plain
double Grothendieck construction applied to the site-indexed decoration
functor.  Objects are interfaces with a designated persistent family of
window classes; loose arrows are wiring patterns with a persistent
family of window apex classes; the site dimension lives entirely in the
fibre stratum. -/
abbrev SiteSpecTotal (U : ι → Set T) (El : Type u) :=
  SpanValued.Grothendieck (siteSpecFunctor U El)

/-- The verdict, machine form: the total of the site-indexed functor
under the plain construction is a pseudo double category — the sheaf
upgrade costs the double-categorical tier nothing. -/
theorem siteSpecTotal_pseudoDoubleCategory (U : ι → Set T) (El : Type u) :
    ∃ _ : PseudoDoubleCategory (SiteSpecTotal U El), True :=
  ⟨inferInstance, trivial⟩

/-- The strict projection to the (unchanged) wiring base. -/
def siteSpecProj (U : ι → Set T) (El : Type u) :
    LaxDoubleFunctor (SiteSpecTotal U El) (WireSpan El) :=
  SpanValued.proj (siteSpecFunctor U El)

/-- The projection is pseudo, exactly as in the plain tier. -/
theorem siteSpecProj_isPseudo (U : ι → Set T) (El : Type u) :
    (siteSpecProj U El).IsPseudo :=
  SpanValued.proj_isPseudo (siteSpecFunctor U El)

/-- **The discrete-opfibration property survives the site dimension,
verbatim**: the projection of the site-indexed total is a discrete
double opfibration by the generic theorem for span-valued functors,
whose lifting calculus never inspects fibre internals — the window
index is invisible to it. -/
theorem siteSpecProj_discreteOpfibration (U : ι → Set T) (El : Type u) :
    IsDiscreteDoubleOpfibration (SpanValued.proj (siteSpecFunctor U El)) :=
  SpanValued.proj_isDiscreteOpfibration (siteSpecFunctor U El)

end

end Site

end SuFunctor
