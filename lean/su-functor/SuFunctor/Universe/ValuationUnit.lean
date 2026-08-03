import SuFunctor.Universe.FellRestrict
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # The valuation layer's unit square over clipping

The mechanized (point-set) shadow of the valuation-locale naturality
square of the temporal-sheaf-carrier design (rung F): the **unit** of
the
valuation/measure layer — the Dirac at a hyperspace point — is natural
along the site's restriction maps in their clipping leg,

`map (restrictOpen U) ∘ dirac = dirac ∘ restrictOpen U`.

At points the square is one line; its entire mathematical load is that
clipping is a *morphism* of the relevant structure — measurability
here, riding exactly the landed Fell continuity of
`fell.continuous_restrictOpen` (the localic statement rides the same
fact as frame-map-hood of the clip's inverse image).  The
proper-pushforward leg of the restriction is the same square again
once its continuity lands; no other ingredient changes.

The Borel structure on the Fell hyperspaces stands in for the
valuation locale's frame of opens — the design-normative semantics is
localic, this file is its point-set shadow (the two-track discipline
of the memo's §11 honest-prices note).
-/

namespace SuFunctor.Universe

open MeasureTheory

namespace fell

variable {α : Type*} [TopologicalSpace α] {U : Set α}

attribute [local instance] SuFunctor.Universe.fell

/-- Borel structure on a Fell hyperspace: the point-set stand-in for
the valuation locale's frame. -/
local instance (Y : Type*) [TopologicalSpace Y] :
    MeasurableSpace (Set Y) := borel _

local instance (Y : Type*) [TopologicalSpace Y] :
    BorelSpace (Set Y) := ⟨rfl⟩

/-- **Unit naturality over clipping**: pushforward of a Dirac along
the clip map is the Dirac of the clip.  The one square of the
valuation layer's presheaf structure whose validity is nontrivial —
and its load is exactly `fell.continuous_restrictOpen`. -/
theorem map_dirac_restrictOpen (hU : IsOpen U) (F : Set α) :
    (Measure.dirac F).map (restrictOpen U)
      = Measure.dirac (restrictOpen U F) :=
  Measure.map_dirac' ((continuous_restrictOpen hU).measurable) F

end fell

end SuFunctor.Universe

#print axioms SuFunctor.Universe.fell.map_dirac_restrictOpen
