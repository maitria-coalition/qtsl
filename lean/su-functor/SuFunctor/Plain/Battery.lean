import SuFunctor.Plain.SpecFunctor

/-! # The acceptance battery: the retired obligations, transposed to classes

`SuFunctorLegacy.Refute` keeps the record of why no sound, unital, syntactic
one-slot composition of *single* judgments can support the structure
squares of a pseudo presentation: the mixed-row funnel (a composite that
collapses content), the threshold tax (a composite that charges a
tautology), and the failed coherence bundle.  This module runs the same
battery against the class-level composition of the spec-class decoration
functor — positive twins first, then the preregistered mutants, each of
which reinstates one retirement mechanism and is refuted by an explicit
witness.

Battery summary:

* **No funnel** (`mem_boxplusClass_iff`, `boxplusClass_nonempty`): the
  composite class is exactly the image of the pairs — content is
  retained, and nonempty inputs never collapse.
* **No tax** (`unitClass_transparent`): the unit class composes
  transparently on the nose, where every sound one-slot table provably
  taxed some tautology.
* **Ideal points compose** (`singleton_boxplus`,
  `transport_singleton`): the singleton embedding of systems into the
  class fibres is closed under composition and transport — the citizen
  collapse happens fibrewise, and composing two systems' ideal points is
  the ideal point of their composite.
* **The judgment is the fibre order** (`idealPoint_le_iff`): membership
  of an ideal point is inclusion of its singleton — one order carries
  both the entailment between classes and the satisfaction judgment, so
  no second fibration is needed.
* **Monotonicity** (`boxplusClass_mono`, `mapCellClass_mono`): every
  operation of the functor is monotone in the inclusion order — the
  ordered-fibre structure rides the plain construction as a property.

Mutants (preregistered before the construction was attempted; each
mirrors a retirement mechanism of the one-slot table):

* **M1, the tax** (`taxedBoxplus_breaks_unit_transparency`): adding any
  nonzero constant to the composite breaks unit transparency, witnessed
  by the zero penalty at the zero joint — the class-level composition is
  tax-free *exactly because* it must be, not by accident.
* **M2, the funnel** (`funnelComp_breaks_unit_coherence`): collapsing
  the composite to a constant class breaks the unit law against the
  empty class — a funnel cannot be unital.
* **M3, middle-forgetting** (`#check_failure` pin): composing decorated
  loose arrows of the total along *different* middle objects does not
  typecheck — the pullback sharing of the middle is by typing, so the
  configuration that forced the retired funnel is unrepresentable here.
-/

namespace SuFunctor

namespace Plain

open CategoryTheory CategoryTheory.WireSpan PseudoDoubleCategoryStruct
open scoped NNReal ENNReal

universe u

noncomputable section

variable {El : Type u} {A B C : WireSpan El}

/-! ## Positive twins -/

/-- **No funnel, membership form**: the composite class is exactly the
image of the pairs. -/
theorem mem_boxplusClass_iff {M : Pat A B} {N : Pat B C} {𝒰₁ : Cpl M}
    {𝒰₂ : Cpl N} {w : Pen (Pat.Tot (Pat.comp M N))} :
    w ∈ Set.image2 boxplus 𝒰₁ 𝒰₂ ↔
      ∃ u₁ ∈ 𝒰₁, ∃ u₂ ∈ 𝒰₂, boxplus u₁ u₂ = w :=
  Set.mem_image2

/-- **No funnel, nonemptiness form**: nonempty inputs never collapse. -/
theorem boxplusClass_nonempty {M : Pat A B} {N : Pat B C} {𝒰₁ : Cpl M}
    {𝒰₂ : Cpl N} (h₁ : 𝒰₁.Nonempty) (h₂ : 𝒰₂.Nonempty) :
    (Set.image2 boxplus 𝒰₁ 𝒰₂).Nonempty :=
  h₁.image2 h₂

/-- **No tax, class form**: the unit class composes transparently on the
nose (modulo the base unitor's definitional apex transport).  The
element-level form is `pull_tot_lLeftUnitor_boxplus`; this is its image
under the class-level compositor — the statement whose one-slot analogue
was refuted. -/
theorem unitClass_transparent (M : Pat A B) (𝒰 : Cpl M) :
    Pen.pull (PatCell.tot
        (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M)) ''
        Set.image2 boxplus ({unitPen A} : Cpl (Pat.id A)) 𝒰 = 𝒰 := by
  rw [Set.image2_singleton_left, ← Set.image_comp]
  have h : Pen.pull (PatCell.tot
      (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M)) ∘
      boxplus (unitPen A) = id :=
    funext fun u => pull_tot_lLeftUnitor_boxplus M u
  rw [h, Set.image_id]

/-- **Ideal points compose**: the composite of two singleton classes is
the singleton of the composite — systems enter the spec fibres as ideal
points and stay ideal under wiring. -/
theorem singleton_boxplus {M : Pat A B} {N : Pat B C}
    (u₁ : Pen (Pat.Tot M)) (u₂ : Pen (Pat.Tot N)) :
    Set.image2 boxplus ({u₁} : Cpl M) ({u₂} : Cpl N) =
      {boxplus u₁ u₂} :=
  Set.image2_singleton

/-- **Ideal points transport**: tight transport of a singleton class is
the singleton of the transported penalty (cylinder extension of the
system's body).  (Stated on `specMap`, the underlying function of the
functor's promoted morphism.) -/
theorem transport_singleton (φ : A ⟶ B) (σ : Pen (states A)) :
    specMap (El := El) φ {σ} = {Pen.pull (res φ) σ} :=
  Set.image_singleton

/-- **The judgment is the fibre order**: an ideal point satisfies a spec
class iff its singleton is included in it.  One order carries entailment
and satisfaction; no second fibration. -/
theorem idealPoint_le_iff (σ : Pen (states A)) (𝒮 : SpecClass A) :
    ({σ} : SpecClass A) ⊆ 𝒮 ↔ σ ∈ 𝒮 :=
  Set.singleton_subset_iff

/-- **Compositor monotonicity** in the inclusion order (the fibre
2-cells are inclusions, and composition respects them). -/
theorem boxplusClass_mono {M : Pat A B} {N : Pat B C} {𝒰₁ 𝒰₁' : Cpl M}
    {𝒰₂ 𝒰₂' : Cpl N} (h₁ : 𝒰₁ ⊆ 𝒰₁') (h₂ : 𝒰₂ ⊆ 𝒰₂') :
    Set.image2 boxplus 𝒰₁ 𝒰₂ ⊆ Set.image2 boxplus 𝒰₁' 𝒰₂' :=
  Set.image2_subset h₁ h₂

/-- **Cell-transport monotonicity**: the decoration action of every base
cell is monotone — the "monotone cell action" half of the ordered-fibre
structure, as a property of the plain functor. -/
theorem mapCellClass_mono {A' B' : WireSpan El} {M : Pat A B}
    {N : Pat A' B'} {φ : A ⟶ A'} {ψ : B ⟶ B'} (γ : PatCell M N φ ψ)
    {𝒰 𝒰' : Cpl M} (h : 𝒰 ⊆ 𝒰') :
    Pen.pull (PatCell.tot γ) '' 𝒰 ⊆ Pen.pull (PatCell.tot γ) '' 𝒰' :=
  Set.image_mono h

/-! ## Preregistered mutants -/

/-- Mutant M1: the taxed composite — pushforward-then-add, plus a
constant charge on every composite.  (The class-level shadow of the
retired Fréchet row, whose sound thresholds provably taxed a
tautology.) -/
def taxedBoxplus {M : Pat A B} {N : Pat B C} (c : ℝ≥0∞)
    (u₁ : Pen (Pat.Tot M)) (u₂ : Pen (Pat.Tot N)) :
    Pen (Pat.Tot (Pat.comp M N)) :=
  fun ν => boxplus u₁ u₂ ν + c

/-- **M1 fails as predicted**: any nonzero tax breaks unit transparency,
witnessed by the zero penalty at the zero joint.  The untaxed law
(`pull_tot_lLeftUnitor_boxplus`) is therefore load-bearing, not
decorative: perturbing the compositor in the retired design's direction
refutes exactly the obligation the retired design failed. -/
theorem taxedBoxplus_breaks_unit_transparency (M : Pat A B) {c : ℝ≥0∞}
    (hc : c ≠ 0) :
    ¬ ∀ u : Pen (Pat.Tot M),
      Pen.pull (PatCell.tot
          (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M))
          (taxedBoxplus c (unitPen A) u) = u := by
  intro h
  have h0 := congrFun (h fun _ => 0) (Joint.zero (Pat.Tot M))
  simp only [Pen.pull_apply, taxedBoxplus, boxplus_apply, unitPen_apply,
    zero_add] at h0
  exact hc h0

/-- Mutant M2: the funnel — a composite that ignores its inputs.  (The
class-level shadow of the retired mixed-row collapse to the vacuous
judgment.) -/
def funnelComp {M : Pat A B} {N : Pat B C} (_ : Cpl M) (_ : Cpl N) :
    Cpl (Pat.comp M N) :=
  Set.univ

/-- **M2 fails as predicted**: a funnel cannot be unital — against the
empty class, stripping the unit from the funnelled composite yields a
nonempty class.  Content retention is forced by the unit law, which is
the structural reason the retired collapse could not survive in any
repaired design. -/
theorem funnelComp_breaks_unit_coherence (M : Pat A B) :
    ¬ ∀ 𝒰 : Cpl M,
      Pen.pull (PatCell.tot
          (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M)) ''
          funnelComp ({unitPen A} : Cpl (Pat.id A)) 𝒰 = 𝒰 := by
  intro h
  have h0 := h ∅
  simp only [funnelComp] at h0
  have hne : (Pen.pull (PatCell.tot
      (PseudoDoubleCategoryStruct.lLeftUnitor (C := WireSpan El) M)) ''
      (Set.univ : Set (Pen (Pat.Tot (Pat.comp (Pat.id A) M))))).Nonempty :=
    Set.univ_nonempty.image _
  rw [h0] at hne
  exact Set.not_nonempty_empty hne

/-! Mutant M3: middle-forgetting is unrepresentable.  In the retired
design a one-slot table had to accept every premise pair, which is what
made the funnel expressible; in the total of the plain construction,
composing loose arrows along *different* middle objects is a type
error — the shared middle is enforced by the indexing.  Kept as an
elaboration-failure pin. -/
section MutantM3

variable {p q q' r : SpanValued.Grothendieck (specFunctor El)}

open SpanValued in
#check_failure fun (L₁ : GLoose p q) (L₂ : GLoose q' r) => L₁.comp L₂

end MutantM3

end

end Plain

end SuFunctor
