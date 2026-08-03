import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import DoubleCat.Functor.Lax

/-! # The target: subprobability mass functions and per-element constraints

The denotation stratum of the semantic universe presents a model as a
credal set of *subprobability* measures — partiality (mass loss) is
native, and the verdict operators are the lower/upper envelopes over the
set.  This module carries the stratum of that stack which is exact and
measure-free: **finitely supported subprobability mass functions with
rational values** on an arbitrary carrier.  On the countable discrete
valuation spaces of the certificate calculus this stratum is dense
enough for every judgment of the graded layer (events are cylinders;
expectations of their indicators are finite sums), and it is the
stratum on which the per-rule semantic squares are stated — the
envelope layer quantifies over it pointwise, per the quantifier
discipline of the semantic-universe chapter (per-element first,
envelope last).

The double category `Crd V` defined here is thin and single-object:

* loose arrows are per-element semantic constraints
  (`SubPMF V → Prop`);
* loose composition is conjunction — the least-committal combination
  of two constraints on a common carrier (the natural-extension glue
  degenerates to intersection when no marginalization is involved);
* cells are pointwise entailments of constraints, so every cell
  equation of the pseudo-double-category axioms holds by proof
  irrelevance.

The upgrades that leave this stratum are deliberate successors: credal
sets and envelope verdicts (lifting each judgment kind through its
component — lower reads the radially maximal slice, upper reads the
whole set), marginal interfaces with glue-and-hide composition (where
the coupling and marginal-compatibility stock takes over as compositor
content), and σ-additive measures on Polish record spaces.
-/

namespace SuFunctor

universe u

variable {V : Type u}

/-- A finitely supported subprobability mass function with rational
values: nonnegative weights summing to at most `1`.  Mass strictly below
`1` is meaningful (a model licensed to lose mass), which is why neither
component of the verdict pair determines the other here. -/
structure SubPMF (V : Type u) : Type u where
  /-- The weight function, finitely supported. -/
  wt : V →₀ ℚ
  /-- Weights are nonnegative. -/
  nonneg : ∀ v, 0 ≤ wt v
  /-- Total mass is at most one. -/
  mass_le_one : ∑ v ∈ wt.support, wt v ≤ 1

namespace SubPMF

/-- The probability of a set of outcomes: the weight it captures. -/
noncomputable def prob (μ : SubPMF V) (S : Set V) : ℚ :=
  letI := Classical.decPred fun v => v ∈ S
  ∑ v ∈ μ.wt.support, if v ∈ S then μ.wt v else 0

theorem prob_nonneg (μ : SubPMF V) (S : Set V) : 0 ≤ μ.prob S := by
  classical
  unfold prob
  refine Finset.sum_nonneg fun v _ => ?_
  by_cases h : v ∈ S <;> simp [h, μ.nonneg v]

@[simp] theorem prob_empty (μ : SubPMF V) : μ.prob (∅ : Set V) = 0 := by
  classical
  unfold prob
  refine Finset.sum_eq_zero fun v _ => ?_
  simp

theorem prob_mono (μ : SubPMF V) {S T : Set V} (h : S ⊆ T) :
    μ.prob S ≤ μ.prob T := by
  classical
  unfold prob
  refine Finset.sum_le_sum fun v _ => ?_
  by_cases hv : v ∈ S
  · simp [hv, h hv]
  · by_cases hv' : v ∈ T <;> simp [hv, hv', μ.nonneg v]

/-- Modularity: the inclusion–exclusion identity, exact at this
stratum. -/
theorem prob_union_add_inter (μ : SubPMF V) (S T : Set V) :
    μ.prob (S ∪ T) + μ.prob (S ∩ T) = μ.prob S + μ.prob T := by
  classical
  unfold prob
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hS : v ∈ S <;> by_cases hT : v ∈ T <;>
    simp [hS, hT, Set.mem_union, Set.mem_inter_iff]

/-- The total mass of the model. -/
noncomputable def mass (μ : SubPMF V) : ℚ := μ.prob Set.univ

theorem prob_le_mass (μ : SubPMF V) (S : Set V) : μ.prob S ≤ μ.mass :=
  μ.prob_mono (Set.subset_univ S)

theorem mass_le_one' (μ : SubPMF V) : μ.mass ≤ 1 := by
  classical
  have h : μ.mass = ∑ v ∈ μ.wt.support, μ.wt v := by
    unfold mass prob
    exact Finset.sum_congr rfl fun v _ => by simp
  rw [h]; exact μ.mass_le_one

theorem prob_le_one (μ : SubPMF V) (S : Set V) : μ.prob S ≤ 1 :=
  le_trans (μ.prob_le_mass S) μ.mass_le_one'

/-- Boole's inequality (the union bound), the engine of the upper-kind
composition row. -/
theorem prob_union_le (μ : SubPMF V) (S T : Set V) :
    μ.prob (S ∪ T) ≤ μ.prob S + μ.prob T := by
  have h := μ.prob_union_add_inter S T
  have h' := μ.prob_nonneg (S ∩ T)
  linarith

/-- The Fréchet inequality, the engine of the lower-kind combination
cell.  Sound for subprobability mass: only `μ(univ) ≤ 1` is consumed, so
partiality strengthens rather than threatens it. -/
theorem frechet_inter (μ : SubPMF V) (S T : Set V) :
    μ.prob S + μ.prob T - 1 ≤ μ.prob (S ∩ T) := by
  have h := μ.prob_union_add_inter S T
  have h' := μ.prob_le_one (S ∪ T)
  linarith

/-- The zero mass function: the model that has lost all of its mass.
It satisfies every sequent-kind judgment and every upper bound, and
refutes every lower bound with positive threshold — the universal
witness of the countermodel analysis that retired the kind-table
composition (see `SuFunctorLegacy.Refute`), kept here as the canonical
inhabitant: it exists over every carrier, including the empty one. -/
def zero (V : Type u) : SubPMF V where
  wt := 0
  nonneg _ := by simp
  mass_le_one := by simp

@[simp] theorem zero_prob (S : Set V) : (SubPMF.zero V).prob S = 0 := by
  classical
  unfold SubPMF.prob
  rw [show (SubPMF.zero V).wt = 0 from rfl]
  simp

instance : Inhabited (SubPMF V) := ⟨zero V⟩

/-- The point mass at an outcome: the degenerate (possibilistic) face's
generator inside the subprobability stratum. -/
noncomputable def dirac (v : V) : SubPMF V where
  wt := Finsupp.single v 1
  nonneg w := by
    classical
    rcases eq_or_ne v w with rfl | h
    · simp
    · simp [Finsupp.single_apply, h]
  mass_le_one := by
    classical
    rw [Finsupp.support_single_ne_zero v one_ne_zero]
    simp

theorem dirac_prob_of_mem {v : V} {S : Set V}
    (h : v ∈ S) : (SubPMF.dirac v).prob S = 1 := by
  classical
  unfold SubPMF.prob SubPMF.dirac
  rw [Finsupp.support_single_ne_zero v one_ne_zero]
  simp [h]

end SubPMF

/-- The thin, single-object double category of per-element semantic
constraints over a carrier `V`: loose arrows are constraints on
subprobability mass functions, cells are pointwise entailments. -/
structure Crd (V : Type u) : Type where
  mk' ::

namespace Crd

open CategoryTheory PseudoDoubleCategoryStruct

instance : CategoryTheory.Category.{0} (Crd V) where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

instance : PseudoDoubleCategoryStruct (Crd V) where
  Loose _ _ := SubPMF V → Prop
  Cell m n _ _ := PLift (∀ μ, m μ → n μ)
  vId _ := ⟨fun _ h => h⟩
  vComp α β := ⟨fun μ h => β.down μ (α.down μ h)⟩
  lId _ := fun _ => True
  lComp m n := fun μ => m μ ∧ n μ
  hId _ := ⟨fun _ h => h⟩
  hComp α β := ⟨fun μ h => ⟨α.down μ h.1, β.down μ h.2⟩⟩
  lAssoc _ _ _ := ⟨fun _ h => ⟨h.1.1, h.1.2, h.2⟩⟩
  lAssocInv _ _ _ := ⟨fun _ h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
  lLeftUnitor _ := ⟨fun _ h => h.2⟩
  lLeftUnitorInv _ := ⟨fun _ h => ⟨trivial, h⟩⟩
  lRightUnitor _ := ⟨fun _ h => h.1⟩
  lRightUnitorInv _ := ⟨fun _ h => ⟨h, trivial⟩⟩

instance {a b c d : Crd V} (m : Loose a b) (n : Loose c d) (f : a ⟶ c)
    (g : b ⟶ d) : Subsingleton (Cell m n f g) :=
  inferInstanceAs (Subsingleton (PLift _))

/-- Cells are proof-irrelevant, so every axiom holds by
`Subsingleton.elim` (the pattern of the double category of commutative
squares). -/
instance : PseudoDoubleCategory (Crd V) where
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

end Crd

end SuFunctor
