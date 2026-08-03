import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-! # Aggregation reduction

This module reduces guards on aggregate quantities to pointwise obligations,
and proves the elementary inequality rows used to bound multiset aggregates
in QTSL certificates.

* `aggReduce`: if a guard `G` is nonpositive on a set `K` of aggregate
  values, and the aggregation map sends every state in scope into `K`, then
  `G ∘ agg` is nonpositive on the scope — an aggregate obligation reduces to
  a constraint on the aggregate's range.
* `query m f`: the aggregate `∑ f` over a multiset `m` of contributors, with
  simp lemmas for the empty multiset and cons.
* `query_const_one`, `query_count`: counting rows — querying the constant
  `1` returns the cardinality, and any query is the count-weighted sum over
  the underlying finite set of distinct contributors.
* `coupling_row`: pointwise bounds `l ≤ f ≤ u` on contributors couple the
  aggregate to the count: `l * card ≤ query m f ≤ u * card`.
* `count_row_nonneg`, `count_row_le`: the count is nonnegative and respects
  a cardinality cap.
* `moment_row`: the Cauchy-Schwarz row `(query m f)^2 ≤ card * query m f²`,
  bounding the first moment by the second.
-/

namespace Qtsl.QtslCompose

/-- Reduction of an aggregate guard: if `G ≤ 0` holds on a set `K` of
aggregate values and `agg` maps every state in `scope` into `K`, then
`G (agg x) ≤ 0` for every `x ∈ scope`. -/
theorem aggReduce {X A : Type*} (agg : X → A) (scope : Set X) (K : Set A)
    (G : A → ℝ) (hG : ∀ a ∈ K, G a ≤ 0) (hin : ∀ x ∈ scope, agg x ∈ K) :
    ∀ x ∈ scope, G (agg x) ≤ 0 :=
  fun x hx => hG (agg x) (hin x hx)

variable {C : Type*}

/-- The aggregate query: the sum of `f` over the contributors of the
multiset `m`, with multiplicity. -/
def query (m : Multiset C) (f : C → ℝ) : ℝ := (m.map f).sum

@[simp] theorem query_zero (f : C → ℝ) : query 0 f = 0 := rfl

@[simp] theorem query_cons (a : C) (m : Multiset C) (f : C → ℝ) :
    query (a ::ₘ m) f = f a + query m f := by
  unfold query
  rw [Multiset.map_cons, Multiset.sum_cons]

theorem query_const_one (m : Multiset C) :
    query m (fun _ => (1 : ℝ)) = m.card := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [query_cons, ih, Multiset.card_cons]
    push_cast
    linarith

/-- A query is the count-weighted sum over the distinct contributors:
`query m f = ∑ c ∈ m.toFinset, m.count c * f c`. -/
theorem query_count [DecidableEq C] (m : Multiset C) (f : C → ℝ) :
    query m f = ∑ c ∈ m.toFinset, (m.count c : ℝ) * f c := by
  unfold query
  rw [Finset.sum_multiset_map_count]
  exact Finset.sum_congr rfl fun c _ => by rw [nsmul_eq_mul]

theorem query_nonneg {m : Multiset C} {f : C → ℝ} (hf : ∀ c ∈ m, 0 ≤ f c) :
    0 ≤ query m f := by
  refine Multiset.sum_nonneg fun x hx => ?_
  obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hx
  exact hf c hc

/-- Coupling row: pointwise bounds `l ≤ f c ≤ u` on all contributors couple
the aggregate to the count, `l * m.card ≤ query m f ≤ u * m.card`. -/
theorem coupling_row {m : Multiset C} {f : C → ℝ} {l u : ℝ}
    (hl : ∀ c ∈ m, l ≤ f c) (hu : ∀ c ∈ m, f c ≤ u) :
    l * m.card ≤ query m f ∧ query m f ≤ u * m.card := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    have hla : l ≤ f a := hl a (Multiset.mem_cons_self a m)
    have hua : f a ≤ u := hu a (Multiset.mem_cons_self a m)
    have ihm := ih (fun c hc => hl c (Multiset.mem_cons_of_mem hc))
      (fun c hc => hu c (Multiset.mem_cons_of_mem hc))
    rw [query_cons, Multiset.card_cons]
    push_cast
    constructor
    · linarith [ihm.1]
    · linarith [ihm.2]

theorem count_row_nonneg (m : Multiset C) : (0 : ℝ) ≤ m.card := by
  exact_mod_cast Nat.zero_le m.card

theorem count_row_le {m : Multiset C} {M : ℕ} (h : m.card ≤ M) :
    (m.card : ℝ) ≤ M := by exact_mod_cast h

/-- Moment row (Cauchy-Schwarz for multiset sums): the squared first moment
is bounded by the count times the second moment,
`(query m f)^2 ≤ m.card * query m (f ^ 2)`. -/
theorem moment_row (m : Multiset C) (f : C → ℝ) :
    (query m f) ^ 2 ≤ m.card * query m (fun c => f c ^ 2) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [query_cons, query_cons, Multiset.card_cons]
    rcases Nat.eq_zero_or_pos m.card with h0 | hpos
    · have hm : m = 0 := Multiset.card_eq_zero.mp h0
      subst hm
      simp only [query_zero, Multiset.card_zero]
      push_cast
      nlinarith [sq_nonneg (f a)]
    · have hQ : 0 ≤ query m (fun c => f c ^ 2) :=
        query_nonneg fun c _ => sq_nonneg (f c)
      have hkpos : (0 : ℝ) < m.card := by exact_mod_cast hpos
      push_cast
      nlinarith [sq_nonneg ((m.card : ℝ) * f a - query m f), ih, hQ, hkpos,
        sq_nonneg (f a - query m f), sq_nonneg (f a + query m f)]

end Qtsl.QtslCompose

#print axioms Qtsl.QtslCompose.aggReduce
#print axioms Qtsl.QtslCompose.query_count
#print axioms Qtsl.QtslCompose.coupling_row
#print axioms Qtsl.QtslCompose.moment_row
