import SuFunctor.Site.SiteFunctor

/-! # The acceptance battery at the site stratum

The plain tier's acceptance battery, re-run against the site-indexed
functor: the retired-obligation twins componentwise, the citizen layer
per window, and the preregistered mutants — each mutation reinstating a
retirement mechanism and refuted by an explicit witness at trajectory
carriers.

* **No funnel** (`mem_wComp_iff`, `wComp_nonempty`): the composite
  family is componentwise exactly the image of the pairs; families
  nonempty at every window compose to families nonempty at every
  window.
* **No tax** (`wUnit_transparent`): the unit family composes
  transparently on the nose, at every window simultaneously.
* **Ideal points compose and transport** (`singleton_boxplusW`,
  `transport_singletonW`): per window, the citizen collapse is the
  plain tier's, at trajectory carriers.
* **The judgment is the fibre order** (`wIdealPoint_le_iff`):
  membership of a window ideal point is inclusion of its singleton in
  the window class — componentwise, one order carrying entailment and
  satisfaction.
* **Monotonicity** (`wComp_mono`, `wCellMap_mono`): every operation is
  componentwise monotone in the inclusion order.

Mutants (preregistered; each mirrors a retirement mechanism):

* **M1, the tax** (`taxedBoxplusW_breaks_unit_transparency`): any
  nonzero constant charge on the window compositor breaks unit
  transparency — witness: the zero penalty at the zero joint over
  trajectories.
* **M2, the funnel** (`funnelCompW_breaks_unit_coherence`): the
  constant-`univ` compositor cannot be unital — witness: the empty
  class.
* **M3, middle-forgetting** (`#check_failure` pin): composing loose
  arrows of the site total along different middle objects does not
  typecheck; the shared middle is enforced by the indexing, window
  structure notwithstanding.
* **M4, the matching fork**, lives in its own module
  (`SuFunctor.Site.MatchingFork`): the strict-section fibres are not
  closed under the compositor — the site dimension's genuine boundary.
* **M5, descent hypotheses**: the delimiting fixtures are already
  landed with the descent theorem
  (`FellCloseds.not_surjective_toProjLim_nondirectedPair`,
  `FellCloseds.not_iInf_induced_le_vietoris`) and are cited by
  `SuFunctor.Site.ClassDescent`, not duplicated.
-/

namespace SuFunctor

namespace Site

noncomputable section

open CategoryTheory CategoryTheory.WireSpan PseudoDoubleCategoryStruct
open SuFunctor.Plain
open scoped NNReal ENNReal

universe u

variable {T ι : Type u} {U : ι → Set T} {El : Type u}
variable {A B C : WireSpan El}

/-! ## Positive twins -/

/-- **No funnel, membership form**: the composite family is
componentwise exactly the image of the pairs. -/
theorem mem_wComp_iff {M : Pat A B} {N : Pat B C} {𝒰 : WCpl U M}
    {𝒱 : WCpl U N} {i : ι}
    {w : Pen (Traj (U i) (Pat.Tot (Pat.comp M N)))} :
    w ∈ (wComp U 𝒰 𝒱).1 i ↔
      ∃ u₁ ∈ 𝒰.1 i, ∃ u₂ ∈ 𝒱.1 i, boxplusW u₁ u₂ = w :=
  Set.mem_image2

/-- **No funnel, nonemptiness form**: componentwise nonempty inputs
give componentwise nonempty composites — no window collapses. -/
theorem wComp_nonempty {M : Pat A B} {N : Pat B C} {𝒰 : WCpl U M}
    {𝒱 : WCpl U N} (h₁ : ∀ i, (𝒰.1 i).Nonempty)
    (h₂ : ∀ i, (𝒱.1 i).Nonempty) :
    ∀ i, ((wComp U 𝒰 𝒱).1 i).Nonempty :=
  fun i => (h₁ i).image2 (h₂ i)

/-- **No tax**: the unit family composes transparently on the nose, at
every window simultaneously (the functor's unit coherence, battery
form). -/
theorem wUnit_transparent {M : Pat A B} (𝒰 : WCpl U M) :
    wCellMap U (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M)
      (wComp U (wUnit U A) 𝒰) = 𝒰 := by
  refine Subtype.ext (funext fun i => ?_)
  show Pen.pull (trajMap (PatCell.tot
      (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M))) ''
        Set.image2 boxplusW {unitPenW A (U i)} (𝒰.1 i) = 𝒰.1 i
  rw [Set.image2_singleton_left, ← Set.image_comp]
  have h : Pen.pull (trajMap (PatCell.tot
        (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M))) ∘
        boxplusW (unitPenW A (U i)) = id :=
    funext fun u => pullW_tot_lLeftUnitor_boxplusW M u
  rw [h, Set.image_id]

/-- **Ideal points compose**, per window: singleton classes compose to
the singleton of the composite. -/
theorem singleton_boxplusW {W : Set T} {M : Pat A B} {N : Pat B C}
    (u₁ : Pen (Traj W (Pat.Tot M))) (u₂ : Pen (Traj W (Pat.Tot N))) :
    Set.image2 boxplusW ({u₁} : Set (Pen (Traj W (Pat.Tot M))))
        ({u₂} : Set (Pen (Traj W (Pat.Tot N)))) =
      {boxplusW u₁ u₂} :=
  Set.image2_singleton

/-- **Ideal points transport**, per window: the componentwise tight
transport of a singleton is the singleton of the transported
penalty. -/
theorem transport_singletonW {W : Set T} (φ : A ⟶ B)
    (σ : Pen (Traj W (states A))) :
    Pen.pull (trajMap (res φ)) '' ({σ} : Set (Pen (Traj W (states A)))) =
      {Pen.pull (trajMap (res φ)) σ} :=
  Set.image_singleton

/-- **The judgment is the fibre order**, per window: a window ideal
point satisfies a window class iff its singleton is included in it. -/
theorem wIdealPoint_le_iff {W : Set T} (σ : Pen (Traj W (states A)))
    (S : Set (Pen (Traj W (states A)))) :
    ({σ} : Set (Pen (Traj W (states A)))) ⊆ S ↔ σ ∈ S :=
  Set.singleton_subset_iff

/-- **Compositor monotonicity**, componentwise. -/
theorem wComp_mono {M : Pat A B} {N : Pat B C} {𝒰 𝒰' : WCpl U M}
    {𝒱 𝒱' : WCpl U N} (h₁ : ∀ i, 𝒰.1 i ⊆ 𝒰'.1 i)
    (h₂ : ∀ i, 𝒱.1 i ⊆ 𝒱'.1 i) :
    ∀ i, (wComp U 𝒰 𝒱).1 i ⊆ (wComp U 𝒰' 𝒱').1 i :=
  fun i => Set.image2_subset (h₁ i) (h₂ i)

/-- **Cell-transport monotonicity**, componentwise. -/
theorem wCellMap_mono {A' B' : WireSpan El} {M : Pat A B} {N : Pat A' B'}
    {φ : A ⟶ A'} {ψ : B ⟶ B'} (γ : PatCell M N φ ψ) {𝒰 𝒰' : WCpl U M}
    (h : ∀ i, 𝒰.1 i ⊆ 𝒰'.1 i) :
    ∀ i, (wCellMap U γ 𝒰).1 i ⊆ (wCellMap U γ 𝒰').1 i :=
  fun i => Set.image_mono (h i)

/-! ## Preregistered mutants -/

/-- Mutant M1: the taxed window compositor — a constant charge on every
composite. -/
def taxedBoxplusW {W : Set T} {M : Pat A B} {N : Pat B C} (c : ℝ≥0∞)
    (u₁ : Pen (Traj W (Pat.Tot M))) (u₂ : Pen (Traj W (Pat.Tot N))) :
    Pen (Traj W (Pat.Tot (Pat.comp M N))) :=
  fun ν => boxplusW u₁ u₂ ν + c

/-- **M1 fails as predicted**: any nonzero tax breaks unit transparency
at the window, witnessed by the zero penalty at the zero joint over
trajectories. -/
theorem taxedBoxplusW_breaks_unit_transparency {W : Set T} (M : Pat A B)
    {c : ℝ≥0∞} (hc : c ≠ 0) :
    ¬ ∀ u : Pen (Traj W (Pat.Tot M)),
      Pen.pull (trajMap (PatCell.tot
          (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M)))
          (taxedBoxplusW c (unitPenW A W) u) = u := by
  intro h
  have h0 := congrFun (h fun _ => 0)
    (Joint.zero (Traj W (Pat.Tot M)))
  simp only [Pen.pull_apply, taxedBoxplusW, boxplusW_apply, unitPenW_apply,
    zero_add] at h0
  exact hc h0

/-- Mutant M2: the funnel — a window compositor that ignores its
inputs. -/
def funnelCompW {W : Set T} {M : Pat A B} {N : Pat B C}
    (_ : Set (Pen (Traj W (Pat.Tot M))))
    (_ : Set (Pen (Traj W (Pat.Tot N)))) :
    Set (Pen (Traj W (Pat.Tot (Pat.comp M N)))) :=
  Set.univ

/-- **M2 fails as predicted**: a funnel cannot be unital at any window —
against the empty class, stripping the unit from the funnelled
composite yields a nonempty class. -/
theorem funnelCompW_breaks_unit_coherence {W : Set T} (M : Pat A B) :
    ¬ ∀ 𝒰 : Set (Pen (Traj W (Pat.Tot M))),
      Pen.pull (trajMap (PatCell.tot
          (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M))) ''
          funnelCompW ({unitPenW A W} :
            Set (Pen (Traj W (Pat.Tot (Pat.id A))))) 𝒰 = 𝒰 := by
  intro h
  have h0 := h ∅
  simp only [funnelCompW] at h0
  have hne : (Pen.pull (trajMap (PatCell.tot
      (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M))) ''
      (Set.univ : Set (Pen (Traj W
        (Pat.Tot (Pat.comp (Pat.id A) M)))))).Nonempty :=
    Set.univ_nonempty.image _
  rw [h0] at hne
  exact Set.not_nonempty_empty hne

/-! Mutant M3: middle-forgetting is unrepresentable at the site total.
Composing decorated loose arrows along *different* middle objects is a
type error — the pullback sharing of the middle is by typing, exactly
as in the plain total; the window structure changes nothing about it.
Kept as an elaboration-failure pin. -/
section MutantM3

variable {p q q' r : SpanValued.Grothendieck (siteSpecFunctor U El)}

open SpanValued in
#check_failure fun (L₁ : GLoose p q) (L₂ : GLoose q' r) => L₁.comp L₂

end MutantM3

end

end Site

end SuFunctor
