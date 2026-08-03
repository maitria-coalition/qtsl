import SuFunctor.Target
import DoubleCat.Functor.Pseudo

/-! # Inclusions of classical semantic objects into the credal stratum

An *adequacy square* compares a modeling framework's own semantics with
the denotation its compiled presentation receives in the semantic
universe: compiling and then denoting must agree with interpreting
classically and then including the classical object into the credal
stratum.  This module is the shared library of those inclusions,
together with the constructors that package a proved equivalence of
constraints as an invertible globular cell of `Crd V` — the
double-categorical form in which the squares are stated.

* `singletonC μ` — the **singleton-credal inclusion**: a subprobability
  mass function, included as the constraint satisfied by exactly `μ`.
  This is the precise face of the imprecise stratum: a credal set with
  one element, presented per-element (the constraint's extension *is*
  the singleton set).
* `diracC v` — the **deterministic inclusion**: a single outcome,
  included as the point-mass constraint — the composite of the Dirac
  embedding with `singletonC`.
* `looseConj L` — a finite family of constraints as a loose-arrow
  diagram: the fold is definitionally an iterated `⊙`
  (`looseConj_cons`), with the empty family the loose identity
  (`looseConj_nil`).
* `Crd.cellOfEntails` / `Crd.looseIso_ofIff` — an entailment of
  constraints is a globular cell; an equivalence is an invertible one.
  Every adequacy square factors through these: the framework-specific
  content is a pointwise equivalence, and the packaging into the double
  category is uniform.
-/

namespace SuFunctor

open CategoryTheory PseudoDoubleCategoryStruct

universe u

variable {V : Type u}

/-- The singleton-credal inclusion: the constraint satisfied by exactly
the given subprobability mass function.  As a credal set (a set of
admissible models), this is `{μ}` — the precise face of the imprecise
stratum, presented per-element. -/
def singletonC (μ : SubPMF V) : SubPMF V → Prop := fun ν => ν = μ

@[simp] theorem singletonC_iff (μ ν : SubPMF V) :
    singletonC μ ν ↔ ν = μ := Iff.rfl

theorem singletonC_self (μ : SubPMF V) : singletonC μ μ := rfl

/-- The inclusion is injective: distinct precise models include as
distinct constraints — no information is lost at the bottom edge. -/
theorem singletonC_injective :
    Function.Injective (singletonC (V := V)) := by
  intro μ ν h
  have h' := congrFun h μ
  rw [eq_iff_iff] at h'
  exact h'.mp rfl

/-- The deterministic inclusion: a single outcome, as the point-mass
constraint.  Deterministic semantics include into the credal stratum
through the probabilistic face: outcome ↦ Dirac mass ↦ singleton. -/
noncomputable def diracC (v : V) : SubPMF V → Prop :=
  singletonC (SubPMF.dirac v)

/-! ## Finite-carrier probability toolkit

Small stratum-generic lemmas the squares share: extensionality, the
probability of an event as a sum over the whole (finite) carrier, and
the probability of a singleton. -/

namespace SubPMF

theorem ext' {μ ν : SubPMF V} (h : μ.wt = ν.wt) : μ = ν := by
  cases μ; cases ν; simpa using h

theorem prob_eq_sum_univ [Fintype V] (μ : SubPMF V) (A : Set V) :
    μ.prob A = ∑ v, A.indicator μ.wt v := by
  classical
  unfold SubPMF.prob
  rw [Finset.sum_subset (Finset.subset_univ μ.wt.support)]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [Set.indicator_apply]
  · intro v _ hv
    have h0 : μ.wt v = 0 := by
      by_contra h
      exact hv (Finsupp.mem_support_iff.mpr h)
    rw [h0, ite_self]

theorem prob_singleton [Fintype V] (μ : SubPMF V) (v : V) :
    μ.prob {v} = μ.wt v := by
  classical
  rw [prob_eq_sum_univ]
  simp [Set.indicator_apply, Set.mem_singleton_iff]

end SubPMF

/-! ## Formal conjunctions of constraints -/

/-- The formal conjunction of a list of constraints. -/
def looseConj : List (SubPMF V → Prop) → (SubPMF V → Prop)
  | [] => fun _ => True
  | c :: L => fun μ => c μ ∧ looseConj L μ

theorem looseConj_iff (L : List (SubPMF V → Prop)) (μ : SubPMF V) :
    looseConj L μ ↔ ∀ c ∈ L, c μ := by
  induction L with
  | nil => simp [looseConj]
  | cons c L ih => simp [looseConj, ih]

/-- The empty conjunction is the loose identity of `Crd V`. -/
theorem looseConj_nil {a : Crd V} :
    (looseConj [] : Loose a a) = 𝟙ˡ a := rfl

/-- A cons is a loose composition: the conjunction of a list of
constraints is definitionally the iterated `⊙` of its elements — a
genuine loose-arrow diagram of `Crd V`. -/
theorem looseConj_cons {a : Crd V} (m : SubPMF V → Prop)
    (L : List (SubPMF V → Prop)) :
    looseConj (m :: L) =
      PseudoDoubleCategoryStruct.lComp (a := a) (b := a) (c := a)
        m (looseConj L) := rfl

namespace Crd

/-- An entailment of constraints, packaged as a globular cell of
`Crd V`. -/
def cellOfEntails {a b : Crd V} {m n : Loose a b}
    (h : ∀ μ, m μ → n μ) : Cell m n (𝟙 a) (𝟙 b) :=
  ⟨h⟩

/-- An equivalence of constraints yields an *invertible* globular
cell: the two directions are the two cells, and the inverse laws are
automatic because `Crd V` is thin. -/
theorem isInvertible_cellOfEntails {a b : Crd V} {m n : Loose a b}
    (h : ∀ μ, m μ ↔ n μ) :
    Cell.IsInvertible (cellOfEntails (fun μ => (h μ).mp)) :=
  ⟨cellOfEntails (fun μ => (h μ).mpr),
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- The packaging every adequacy square uses: a pointwise equivalence
of constraints is an isomorphism of loose arrows in `Crd V` (an
invertible globular cell). -/
theorem looseIso_ofIff {a b : Crd V} {m n : Loose a b}
    (h : ∀ μ, m μ ↔ n μ) :
    ∃ α : Cell m n (𝟙 a) (𝟙 b), Cell.IsInvertible α :=
  ⟨cellOfEntails (fun μ => (h μ).mp), isInvertible_cellOfEntails h⟩

end Crd

end SuFunctor
