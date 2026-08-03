import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Rat.Encodable
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.LocallyClosed

/-! # ω-semialgebraic sets: rational polynomial pieces and countable carving

The polynomial stratum of the piecewise-analytic space hierarchy of
Huot–Lew–Mansinghka–Staton, *ωPAP spaces* (arXiv:2302.10636), following
Lee et al.'s first-order notion: where their pieces are carved by finitely
many *analytic* inequalities, ours are carved by finitely many polynomial
inequalities **with rational coefficients** (`BasicSet`, a basic
semialgebraic set over ℚ), and an **ω-semialgebraic set** (`IsOmegaSA`)
is a countable union of such pieces.

Two axes are load-bearing, independently:

* **Countability**: `ℕ ⊆ ℝ` is ω-semialgebraic on sight (one degree-1
  piece per point) but is definable in no o-minimal structure, having
  infinitely many connected components.
* **Coefficient pinning**: the carving data of a piece is a finite list
  over a *countable* alphabet (`Countable (PolyCond n)`), which is what
  makes a piece finite, exactly-transmissible data.  Without the pin,
  degree-1 pieces like `{x : x ≥ π}` satisfy the letter of "polynomial of
  finite degree" while breaking exactness; with it, the carving-data type
  is countable and each piece is finite rational data.  (Real-algebraic
  coefficients would give the same *sets* — real-closure quantifier
  elimination — at the cost of a heavier data story; ℚ is the wire-native
  choice.)

Design choices, each load-bearing for the composition theorems downstream:

* **Two sign conditions** (`p ≤ 0`, `p < 0`) and no equation condition:
  `p = 0` is the pair `p ≤ 0, -p ≤ 0`, while the two-sign system is
  complement-perfect (`PolyCond.holds_neg_iff`), making complements of
  basic sets *finite unions* of basic sets (`compl_basicSet_eq`) with no
  quantifier elimination anywhere.
* **ℕ-indexed piece families** with a canonical empty piece (`false'`),
  so finite and countable families embed uniformly and countable unions
  of countable unions re-index along `Nat.pairEquiv`.
* **Substitution, not projection**: the preimage of a basic set under a
  (rational-coefficient) polynomial map is again basic, by substituting
  (`MvPolynomial.bind₁`) into the carving data (`basicSet_subst`).
  Images are never taken; Tarski–Seidenberg is deliberately not consumed.

Every piece is closed-in-open (`isLocallyClosed_basicSet`); the pathology
budget of an ω-semialgebraic set sits entirely in the countable union
(`ℚ ⊆ ℝ` is ω-semialgebraic and nowhere locally compact).
-/

namespace SuFunctor.StateSpace

open MvPolynomial Set

noncomputable section

/-- A sign condition on a polynomial: `≤ 0` or `< 0`.  The two-sign system
is complement-perfect: the negation of `p ≤ 0` is `-p < 0` and vice versa. -/
inductive SignCond : Type
  | le : SignCond
  | lt : SignCond
  deriving DecidableEq

instance : Countable SignCond :=
  ⟨⟨fun s => match s with | .le => 0 | .lt => 1,
    fun a b h => by cases a <;> cases b <;> simp_all⟩⟩

/-- One rational-coefficient polynomial sign condition on `ℝⁿ` (ambient
`Fin n → ℝ`).  The coefficient pin to `ℚ` is part of the class definition:
it is what makes a piece finite exact data. -/
structure PolyCond (n : ℕ) : Type where
  /-- The carving polynomial, coefficients pinned to ℚ. -/
  poly : MvPolynomial (Fin n) ℚ
  /-- The sign condition imposed on `poly`. -/
  sign : SignCond

/-- The carving alphabet is countable — the exact-fragment fact: a basic
piece is a finite word over a countable alphabet, hence finite
exactly-transmissible data.  This is the theorem that dies if the
coefficient pin is widened to ℝ (`c ↦ ⟨C c, le⟩` then injects ℝ). -/
instance {n : ℕ} : Countable (MvPolynomial (Fin n) ℚ) :=
  Countable.of_equiv ((Fin n →₀ ℕ) →₀ ℚ) AddMonoidAlgebra.coeffEquiv.symm

instance {n : ℕ} : Countable (PolyCond n) :=
  Countable.of_equiv (MvPolynomial (Fin n) ℚ × SignCond)
    ⟨fun p => ⟨p.1, p.2⟩, fun c => (c.poly, c.sign), fun _ => rfl, fun _ => rfl⟩

/-- The piece-data type is countable: the exact-fragment receipt at the
level of whole pieces. -/
theorem countable_pieceData (n : ℕ) : Countable (List (PolyCond n)) :=
  inferInstance

/-- Continuity of rational-polynomial evaluation on the real ambient. -/
lemma continuous_aeval {n : ℕ} (p : MvPolynomial (Fin n) ℚ) :
    Continuous fun x : Fin n → ℝ => aeval x p := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq =>
      have h : (fun x : Fin n → ℝ => aeval x (p + q)) =
          fun x => aeval x p + aeval x q := by
        funext x; simp [map_add]
      rw [h]; exact hp.add hq
  | mul_X p i hp =>
      have h : (fun x : Fin n → ℝ => aeval x (p * X i)) =
          fun x => aeval x p * x i := by
        funext x; simp [map_mul, aeval_X]
      rw [h]; exact hp.mul (continuous_apply i)

namespace PolyCond

variable {n : ℕ}

/-- The predicate the condition imposes at a point of the real ambient. -/
def holds (c : PolyCond n) (x : Fin n → ℝ) : Prop :=
  match c.sign with
  | .le => aeval x c.poly ≤ 0
  | .lt => aeval x c.poly < 0

@[simp] lemma holds_le {p : MvPolynomial (Fin n) ℚ} {x : Fin n → ℝ} :
    holds ⟨p, .le⟩ x ↔ aeval x p ≤ 0 := Iff.rfl

@[simp] lemma holds_lt {p : MvPolynomial (Fin n) ℚ} {x : Fin n → ℝ} :
    holds ⟨p, .lt⟩ x ↔ aeval x p < 0 := Iff.rfl

/-- The complementary condition. -/
def neg (c : PolyCond n) : PolyCond n :=
  ⟨-c.poly, match c.sign with | .le => .lt | .lt => .le⟩

lemma holds_neg_iff (c : PolyCond n) (x : Fin n → ℝ) :
    c.neg.holds x ↔ ¬ c.holds x := by
  obtain ⟨p, s⟩ := c
  cases s <;> simp [neg, holds, map_neg, neg_lt_zero, neg_nonpos, not_le, not_lt]

/-- The canonically false condition `1 < 0`, used as the empty piece. -/
def false' (n : ℕ) : PolyCond n := ⟨1, .lt⟩

@[simp] lemma not_holds_false' (x : Fin n → ℝ) : ¬ (false' n).holds x := by
  simp [false', holds]

/-- Pull a condition back along a polynomial substitution. -/
def subst {m : ℕ} (c : PolyCond m) (P : Fin m → MvPolynomial (Fin n) ℚ) :
    PolyCond n :=
  ⟨bind₁ P c.poly, c.sign⟩

lemma holds_subst {m : ℕ} (c : PolyCond m)
    (P : Fin m → MvPolynomial (Fin n) ℚ) (x : Fin n → ℝ) :
    (c.subst P).holds x ↔ c.holds (fun j => aeval x (P j)) := by
  obtain ⟨p, s⟩ := c
  cases s <;> simp [subst, holds, aeval_bind₁]

end PolyCond

/-- The basic (semialgebraic-over-ℚ) set carved by a finite list of
polynomial sign conditions: the conjunction of the conditions. -/
def BasicSet {n : ℕ} (L : List (PolyCond n)) : Set (Fin n → ℝ) :=
  {x | ∀ c ∈ L, c.holds x}

section BasicSet

variable {n m : ℕ}

@[simp] lemma mem_basicSet {L : List (PolyCond n)} {x : Fin n → ℝ} :
    x ∈ BasicSet L ↔ ∀ c ∈ L, c.holds x := Iff.rfl

@[simp] lemma basicSet_nil : BasicSet ([] : List (PolyCond n)) = univ := by
  ext x; simp

lemma basicSet_cons (c : PolyCond n) (L : List (PolyCond n)) :
    BasicSet (c :: L) = {x | c.holds x} ∩ BasicSet L := by
  ext x; simp [and_comm]

lemma basicSet_append (L₁ L₂ : List (PolyCond n)) :
    BasicSet (L₁ ++ L₂) = BasicSet L₁ ∩ BasicSet L₂ := by
  ext x; simp [or_imp, forall_and]

@[simp] lemma basicSet_false' :
    BasicSet [PolyCond.false' n] = (∅ : Set (Fin n → ℝ)) := by
  ext x; simp

/-- Substitution computes preimages: the preimage of a basic set under the
evaluation of a rational polynomial family is the basic set of the
substituted conditions.  This is the whole composition engine; no
projection, no quantifier elimination. -/
lemma basicSet_subst (L : List (PolyCond m)) (P : Fin m → MvPolynomial (Fin n) ℚ)
    (x : Fin n → ℝ) :
    x ∈ BasicSet (L.map (PolyCond.subst · P)) ↔
      (fun j => aeval x (P j)) ∈ BasicSet L := by
  simp only [mem_basicSet, List.mem_map]
  constructor
  · rintro h c hc
    exact (PolyCond.holds_subst c P x).mp (h _ ⟨c, hc, rfl⟩)
  · rintro h - ⟨c, hc, rfl⟩
    exact (PolyCond.holds_subst c P x).mpr (h c hc)

/-- Each single condition carves a locally closed set. -/
lemma isLocallyClosed_setOf_holds (c : PolyCond n) :
    IsLocallyClosed {x | c.holds x} := by
  obtain ⟨p, s⟩ := c
  cases s
  · have h : {x | PolyCond.holds ⟨p, .le⟩ x} = (fun x => aeval x p) ⁻¹' Iic 0 := by
      ext x; simp [PolyCond.holds]
    rw [h]
    exact (isClosed_Iic.preimage (continuous_aeval p)).isLocallyClosed
  · have h : {x | PolyCond.holds ⟨p, .lt⟩ x} = (fun x => aeval x p) ⁻¹' Iio 0 := by
      ext x; simp [PolyCond.holds]
    rw [h]
    exact (isOpen_Iio.preimage (continuous_aeval p)).isLocallyClosed

/-- Basic sets are locally closed (closed-in-open): each polynomial piece
is a topologically tame citizen; all pathology budget of the
ω-semialgebraic class sits in the countable union. -/
lemma isLocallyClosed_basicSet (L : List (PolyCond n)) :
    IsLocallyClosed (BasicSet L) := by
  induction L with
  | nil => simpa using isOpen_univ.isLocallyClosed
  | cons c L ih =>
      rw [basicSet_cons]
      exact (isLocallyClosed_setOf_holds c).inter ih

/-- The complement of a basic set is a *finite* union of basic sets — the
two-sign system is complement-perfect. -/
lemma compl_basicSet_eq (L : List (PolyCond n)) :
    (BasicSet L)ᶜ = ⋃ c ∈ L, BasicSet [c.neg] := by
  ext x
  simp only [mem_compl_iff, mem_basicSet, mem_iUnion]
  constructor
  · intro h
    push_neg at h
    obtain ⟨c, hc, hnot⟩ := h
    exact ⟨c, hc, by simpa [PolyCond.holds_neg_iff] using hnot⟩
  · rintro ⟨c, hc, h⟩ hall
    have hn := h c.neg (by simp)
    rw [PolyCond.holds_neg_iff] at hn
    exact hn (hall c hc)

end BasicSet

/-- An **ω-semialgebraic set**: a countable union of basic rational-
polynomial pieces.  The intermediate stratum between semialgebraic sets
(finitely many pieces) and c-analytic sets (countably many analytic
pieces): the exactness-maximal composition-closed dial. -/
def IsOmegaSA {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ F : ℕ → List (PolyCond n), S = ⋃ i, BasicSet (F i)

namespace IsOmegaSA

variable {n : ℕ} {S T : Set (Fin n → ℝ)}

lemma of_basic (L : List (PolyCond n)) : IsOmegaSA (BasicSet L) :=
  ⟨fun _ => L, (Set.iUnion_const _).symm⟩

lemma empty : IsOmegaSA (∅ : Set (Fin n → ℝ)) := by
  simpa using of_basic [PolyCond.false' n]

lemma univ : IsOmegaSA (univ : Set (Fin n → ℝ)) := by
  simpa using of_basic ([] : List (PolyCond n))

/-- Countable unions of ω-semialgebraic sets are ω-semialgebraic — the
axis that separates this class from the semialgebraic one. -/
lemma iUnion {S : ℕ → Set (Fin n → ℝ)} (hS : ∀ i, IsOmegaSA (S i)) :
    IsOmegaSA (⋃ i, S i) := by
  choose F hF using hS
  refine ⟨fun k => F (Nat.pairEquiv.symm k).1 (Nat.pairEquiv.symm k).2, ?_⟩
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    rw [hF i] at hi
    obtain ⟨j, hj⟩ := mem_iUnion.mp hi
    exact ⟨Nat.pairEquiv (i, j), by simpa using hj⟩
  · rintro ⟨k, hk⟩
    refine ⟨(Nat.pairEquiv.symm k).1, ?_⟩
    rw [hF _]
    exact mem_iUnion.mpr ⟨(Nat.pairEquiv.symm k).2, hk⟩

lemma union (hS : IsOmegaSA S) (hT : IsOmegaSA T) : IsOmegaSA (S ∪ T) := by
  have hrw : S ∪ T = ⋃ i : ℕ, (if i = 0 then S else T) := by
    ext x
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro (h | h)
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    · rintro ⟨i, hi⟩
      by_cases h : i = 0
      · exact Or.inl (by simpa [h] using hi)
      · exact Or.inr (by simpa [h] using hi)
  rw [hrw]
  exact iUnion fun i => by split <;> assumption

lemma inter (hS : IsOmegaSA S) (hT : IsOmegaSA T) : IsOmegaSA (S ∩ T) := by
  obtain ⟨F, rfl⟩ := hS
  obtain ⟨G, rfl⟩ := hT
  refine ⟨fun k => F (Nat.pairEquiv.symm k).1 ++ G (Nat.pairEquiv.symm k).2, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_iUnion, basicSet_append]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨Nat.pairEquiv (i, j), by simpa using ⟨hi, hj⟩⟩
  · rintro ⟨k, hk₁, hk₂⟩
    exact ⟨⟨(Nat.pairEquiv.symm k).1, hk₁⟩, ⟨(Nat.pairEquiv.symm k).2, hk₂⟩⟩

/-- The complement of a *basic* set is ω-semialgebraic (indeed a finite
union of basic sets).  Complements of general ω-semialgebraic sets are
not in the class; only this basic-level complement is used, for
disjointification and difference constructions. -/
lemma compl_basic (L : List (PolyCond n)) : IsOmegaSA (BasicSet L)ᶜ := by
  rw [compl_basicSet_eq]
  induction L with
  | nil => simpa using empty (n := n)
  | cons c L ih =>
      have hrw : (⋃ d ∈ (c :: L), BasicSet [d.neg]) =
          BasicSet [c.neg] ∪ ⋃ d ∈ L, BasicSet [d.neg] := by
        ext x
        simp [List.mem_cons, exists_eq_or_imp]
      rw [hrw]
      exact (of_basic _).union ih

/-- Set difference with a basic set stays in the class. -/
lemma diff_basic (hS : IsOmegaSA S) (L : List (PolyCond n)) :
    IsOmegaSA (S \ BasicSet L) :=
  hS.inter (compl_basic L)

end IsOmegaSA

end

end SuFunctor.StateSpace
