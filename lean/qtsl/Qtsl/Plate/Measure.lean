import Qtsl.Plate.TDesc
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fin.VecNotation

/-!
# Plates: the measure face of descent

`Qtsl.Plate.TDesc` is the *denotational* face of the count quotient:
outputs carrying no plate axis are permutation-invariant, so they
descend from words (`List B`) to markings (`Multiset B`, the bag space
`∐ₙ Symⁿ(B)`) — that is `bagDenot`, built by `Quot.liftOn` with `T_DESC`
discharging well-definedness.

This module is the *measure* face of the same quotient. An i.i.d.
product weight on words is permutation-invariant for the same structural
reason (`iidWeight_perm`), hence descends to the bag space by the same
`Quot.liftOn` (`bagWeight`). The pushforward of the product measure onto
a marking factors as fiber-cardinality × descended-weight
(`pushMass_eq_card_mul`), and the fiber of the quotient over a marking
has multinomial cardinality (`card_descFiber`, the main theorem). Two
corollaries compute the descended measure on the two sectors that
matter for exchangeable-family certificates:

* two-colour bodies (`pushMass_bern`): the count-`k` marking receives
  mass `n.choose k * p^k * (1-p)^(n-k)` — the binomial distribution;
* many-colour bodies (`pushMass_vecMarking`): the count-vector marking
  receives mass `multinomial k * ∏ j, q j ^ k j`.

So count weights arrive from the presentation — plate descent — rather
than as bespoke certificate data; a checker that trusts the quotient
already knows the weights.

All weights are exact rationals and every identity is polynomial in
them: no `[0,1]` hypotheses appear, and the normalization statements
(`sum_binomial_mass`, `sum_iidWeight`) are ring identities. The fixture
section evaluates reference tail values with kernel-checked arithmetic;
the asymmetric fixture (weight `1/3`) is included deliberately, because
a symmetric weight cannot distinguish a success/failure exponent swap.
-/

namespace PPLC
namespace Plate

open Finset

/-! ## The product weight and its descent -/

variable {B : Type*}

/-- The i.i.d. product weight of a word: each letter contributes its
weight, independently. -/
def iidWeight (μ : B → ℚ) (l : List B) : ℚ := (l.map μ).prod

/-- Permutation invariance: the product weight is a symmetric function
of the word — the measure-side twin of `T_DESC`'s invariance. -/
theorem iidWeight_perm (μ : B → ℚ) {l l' : List B} (h : l.Perm l') :
    iidWeight μ l = iidWeight μ l' :=
  (h.map μ).prod_eq

/-- The descended weight on the bag space, by the same `Quot.liftOn`
that carries `bagDenot`: permutation invariance is the well-definedness
obligation. -/
def bagWeight (μ : B → ℚ) (m : Multiset B) : ℚ :=
  Quot.liftOn m (iidWeight μ) fun _ _ h => iidWeight_perm μ h

/-- Computation rule on a represented marking. -/
@[simp] theorem bagWeight_coe (μ : B → ℚ) (l : List B) :
    bagWeight μ (l : Multiset B) = iidWeight μ l := rfl

/-- The descended weight is the multiset product of letter weights. -/
theorem bagWeight_eq_prod (μ : B → ℚ) (m : Multiset B) :
    bagWeight μ m = (m.map μ).prod :=
  Quot.inductionOn m fun l => by
    simp [bagWeight_coe, iidWeight]

/-! ## Words, markings, and the pushforward -/

variable {n : ℕ}

/-- The marking of a word indexed by `Fin n`: forget the order, keep
the letters — the count quotient, applied pointwise. -/
def marking (ω : Fin n → B) : Multiset B := (List.ofFn ω : Multiset B)

@[simp] theorem card_marking (ω : Fin n → B) : (marking ω).card = n := by
  simp [marking]

/-- On a word, the descended weight reads back as the product weight. -/
@[simp] theorem bagWeight_marking (μ : B → ℚ) (ω : Fin n → B) :
    bagWeight μ (marking ω) = iidWeight μ (List.ofFn ω) := rfl

theorem iidWeight_ofFn (μ : B → ℚ) (ω : Fin n → B) :
    iidWeight μ (List.ofFn ω) = ∏ i, μ (ω i) := by
  rw [iidWeight, List.map_ofFn, List.prod_ofFn]
  simp [Function.comp]

theorem marking_cons (a : B) (ω : Fin n → B) :
    marking (Fin.cons a ω) = a ::ₘ marking ω := by
  simp [marking, List.ofFn_succ]

section Fintype

variable [Fintype B] [DecidableEq B]

/-- The fiber of the count quotient over a marking, inside the words of
length `n`. -/
def descFiber (n : ℕ) (m : Multiset B) : Finset (Fin n → B) :=
  Finset.univ.filter fun ω => marking ω = m

@[simp] theorem mem_descFiber {m : Multiset B} {ω : Fin n → B} :
    ω ∈ descFiber n m ↔ marking ω = m := by
  simp [descFiber]

/-- The pushforward of the i.i.d. product measure onto the bag space:
the mass a marking receives from the words of length `n`. -/
def pushMass (μ : B → ℚ) (n : ℕ) (m : Multiset B) : ℚ :=
  ∑ ω : Fin n → B, if marking ω = m then iidWeight μ (List.ofFn ω) else 0

/-- The pushforward factors through the fiber: mass = (number of words
realizing the marking) × (descended weight). The weight is constant on
fibers — permutation invariance doing the work. -/
theorem pushMass_eq_card_mul (μ : B → ℚ) (n : ℕ) (m : Multiset B) :
    pushMass μ n m = ((descFiber n m).card : ℚ) * bagWeight μ m := by
  rw [pushMass, ← Finset.sum_filter]
  have h : ∀ ω ∈ descFiber n m,
      iidWeight μ (List.ofFn ω) = bagWeight μ m := fun ω hω => by
    rw [← mem_descFiber.mp hω]; rfl
  rw [show Finset.univ.filter (fun ω : Fin n → B => marking ω = m)
        = descFiber n m from rfl,
    Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]

/-! ## The fiber has multinomial cardinality -/

omit [Fintype B] in
theorem cons_eq_iff {a : B} {s m : Multiset B} :
    a ::ₘ s = m ↔ a ∈ m ∧ s = m.erase a := by
  constructor
  · rintro rfl
    exact ⟨Multiset.mem_cons_self a s, (Multiset.erase_cons_head a s).symm⟩
  · rintro ⟨ha, rfl⟩
    exact Multiset.cons_erase ha

/-- Splitting a word at its first letter splits the fiber: a marking is
realized by `Fin.cons a ω` exactly when it contains `a` and its
`a`-erasure is realized by `ω`. -/
theorem card_descFiber_succ (n : ℕ) (m : Multiset B) :
    (descFiber (n + 1) m).card
      = ∑ a : B, if a ∈ m then (descFiber n (m.erase a)).card else 0 := by
  rw [descFiber, Finset.card_filter]
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) => B)
    fun ω : Fin (n + 1) → B => if marking ω = m then (1 : ℕ) else 0]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  have happ : ∀ ω : Fin n → B,
      (Fin.consEquiv fun _ : Fin (n + 1) => B) (a, ω) = Fin.cons a ω :=
    fun ω => rfl
  by_cases ha : a ∈ m
  · rw [if_pos ha, descFiber, Finset.card_filter]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [happ, marking_cons]
    simp [cons_eq_iff, ha]
  · rw [if_neg ha]
    refine Finset.sum_eq_zero fun ω _ => ?_
    rw [happ, marking_cons]
    simp [cons_eq_iff, ha]

theorem sum_count_univ (m : Multiset B) : ∑ b : B, m.count b = m.card := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      simp [Multiset.count_cons, Finset.sum_add_distrib, ih,
        Multiset.card_cons]

/-- `countPerms` as a multinomial over the whole (finite) alphabet:
letters outside the marking contribute multiplicity `0`, hence
factorial `1`. -/
theorem countPerms_eq_multinomial_univ (m : Multiset B) :
    m.countPerms = Nat.multinomial Finset.univ m.count := by
  rw [Multiset.countPerms,
    ← Finsupp.multinomial_of_support_subset
      (Finset.subset_univ m.toFinsupp.support)]
  exact (Nat.multinomial_congr fun a _ => (Multiset.toFinsupp_apply m a)).symm

/-- The defining identity of the multinomial, over the alphabet. -/
theorem countPerms_mul_prod_factorial (m : Multiset B) :
    m.countPerms * ∏ b : B, Nat.factorial (m.count b)
      = Nat.factorial m.card := by
  rw [countPerms_eq_multinomial_univ, mul_comm, ← sum_count_univ m]
  exact Nat.multinomial_spec _ _

/-- One step of the factorial ledger: erasing one copy of `a` divides
the permutation count by the multiplicity of `a` — stated
multiplicatively, in `ℕ`. -/
theorem countPerms_erase_mul (m : Multiset B) {a : B} (ha : a ∈ m) :
    (m.erase a).countPerms * ∏ b : B, Nat.factorial (m.count b)
      = m.count a * Nat.factorial (m.card - 1) := by
  have hpos : 1 ≤ m.count a := Multiset.one_le_count_iff_mem.mpr ha
  have herase_count : ∀ b : B,
      (m.erase a).count b = if b = a then m.count a - 1 else m.count b := by
    intro b
    by_cases hb : b = a
    · rw [if_pos hb, hb]
      exact Multiset.count_erase_self a m
    · rw [if_neg hb]
      exact Multiset.count_erase_of_ne hb m
  -- split both factorial products at `a`
  have hsplit : ∏ b : B, Nat.factorial (m.count b)
      = Nat.factorial (m.count a)
          * ∏ b ∈ Finset.univ.erase a, Nat.factorial (m.count b) :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)).symm
  have hsplit' : ∏ b : B, Nat.factorial ((m.erase a).count b)
      = Nat.factorial (m.count a - 1)
          * ∏ b ∈ Finset.univ.erase a, Nat.factorial (m.count b) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun b => Nat.factorial ((m.erase a).count b)) (Finset.mem_univ a),
      herase_count a, if_pos rfl]
    congr 1
    exact Finset.prod_congr rfl fun b hb => by
      rw [herase_count b, if_neg (Finset.mem_erase.mp hb).1]
  have hspec : (m.erase a).countPerms
      * ∏ b : B, Nat.factorial ((m.erase a).count b)
      = Nat.factorial (m.card - 1) := by
    rw [countPerms_mul_prod_factorial, Multiset.card_erase_of_mem ha]
    rfl
  have hfac : Nat.factorial (m.count a)
      = m.count a * Nat.factorial (m.count a - 1) :=
    (Nat.mul_factorial_pred (Nat.pos_iff_ne_zero.mp hpos)).symm
  calc (m.erase a).countPerms * ∏ b : B, Nat.factorial (m.count b)
      = m.count a * ((m.erase a).countPerms
          * (Nat.factorial (m.count a - 1)
              * ∏ b ∈ Finset.univ.erase a, Nat.factorial (m.count b))) := by
        rw [hsplit, hfac]; ring
    _ = m.count a * Nat.factorial (m.card - 1) := by
        rw [← hsplit', hspec]

/-- Pascal's rule for permutation counts: summing the erasures over the
alphabet recovers the count — the recursion the fiber satisfies. -/
theorem sum_countPerms_erase (m : Multiset B) (hm : m ≠ 0) :
    ∑ a : B, (if a ∈ m then (m.erase a).countPerms else 0)
      = m.countPerms := by
  have hD : 0 < ∏ b : B, Nat.factorial (m.count b) :=
    Finset.prod_pos fun b _ => Nat.factorial_pos _
  apply Nat.eq_of_mul_eq_mul_right hD
  rw [Finset.sum_mul, countPerms_mul_prod_factorial]
  have hterm : ∀ a : B,
      (if a ∈ m then (m.erase a).countPerms else 0)
          * ∏ b : B, Nat.factorial (m.count b)
        = m.count a * Nat.factorial (m.card - 1) := by
    intro a
    by_cases ha : a ∈ m
    · rw [if_pos ha, countPerms_erase_mul m ha]
    · rw [if_neg ha, zero_mul, Multiset.count_eq_zero.mpr ha, zero_mul]
  rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_mul,
    sum_count_univ]
  exact Nat.mul_factorial_pred
    (Nat.pos_iff_ne_zero.mp (Multiset.card_pos.mpr hm))

/-- **The fiber-count theorem**: the number of words of length `m.card`
realizing a marking `m` is its permutation count — the multinomial
coefficient of its multiplicities. This is the entire measure content
of descent: together with `pushMass_eq_card_mul` it computes the
descended measure on every sector. -/
theorem card_descFiber (m : Multiset B) :
    (descFiber m.card m).card = m.countPerms := by
  suffices h : ∀ (n : ℕ) (m : Multiset B), m.card = n →
      (descFiber n m).card = m.countPerms from h m.card m rfl
  intro n
  induction n with
  | zero =>
      intro m hm
      obtain rfl : m = 0 := Multiset.card_eq_zero.mp hm
      have huniv : descFiber (B := B) 0 0 = Finset.univ := by
        ext ω
        simp [mem_descFiber, marking, List.ofFn_zero]
        exact Subsingleton.elim _ _
      rw [huniv, Finset.card_univ, Multiset.countPerms_zero]
      simp
  | succ n ih =>
      intro m hm
      rw [card_descFiber_succ]
      have hstep : ∀ a : B,
          (if a ∈ m then (descFiber n (m.erase a)).card else 0)
            = (if a ∈ m then (m.erase a).countPerms else 0) := fun a => by
        by_cases ha : a ∈ m
        · rw [if_pos ha, if_pos ha, ih (m.erase a)
            (by rw [Multiset.card_erase_of_mem ha, hm]; rfl)]
        · rw [if_neg ha, if_neg ha]
      rw [Finset.sum_congr rfl fun a _ => hstep a,
        sum_countPerms_erase m (by rintro rfl; simp at hm)]

end Fintype

/-! ## The two-colour sector: binomial -/

theorem count_true_add_count_false (m : Multiset Bool) :
    m.count true + m.count false = m.card := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | cons b s ih => cases b <;> simp <;> omega

/-- On a two-letter alphabet the multinomial is a binomial. -/
theorem countPerms_bool (m : Multiset Bool) :
    m.countPerms = m.card.choose (m.count true) := by
  rw [countPerms_eq_multinomial_univ,
    show (Finset.univ : Finset Bool) = {true, false} by decide,
    Nat.binomial_eq_choose (by decide : true ≠ false),
    count_true_add_count_false]

/-- The two-colour marking with `k` successes among `n`. -/
def boolMarking (n k : ℕ) : Multiset Bool :=
  Multiset.replicate k true + Multiset.replicate (n - k) false

@[simp] theorem count_true_boolMarking (n k : ℕ) :
    (boolMarking n k).count true = k := by
  simp [boolMarking, Multiset.count_replicate]

@[simp] theorem count_false_boolMarking (n k : ℕ) :
    (boolMarking n k).count false = n - k := by
  simp [boolMarking, Multiset.count_replicate]

theorem card_boolMarking {n k : ℕ} (hk : k ≤ n) :
    (boolMarking n k).card = n := by
  simp only [boolMarking, Multiset.card_add, Multiset.card_replicate]
  omega

/-- The two-colour descent sector is `{0..n}`: a marking of card `n` is
determined by its success count. -/
theorem eq_boolMarking_of_card {m : Multiset Bool} {n : ℕ}
    (h : m.card = n) : m = boolMarking n (m.count true) := by
  have hc := count_true_add_count_false m
  refine Multiset.ext.mpr fun b => ?_
  cases b
  · rw [count_false_boolMarking]; omega
  · rw [count_true_boolMarking]

/-- **The binomial fiber**: `n.choose k` words realize the count-`k`
marking. -/
theorem card_descFiber_boolMarking {n k : ℕ} (hk : k ≤ n) :
    (descFiber n (boolMarking n k)).card = n.choose k := by
  have hcard := card_boolMarking (n := n) (k := k) hk
  have h := card_descFiber (boolMarking n k)
  rw [hcard] at h
  rw [h, countPerms_bool, hcard, count_true_boolMarking]

/-- The Bernoulli weight: `p` on success, `1 - p` on failure. -/
def bern (p : ℚ) : Bool → ℚ := fun b => if b then p else 1 - p

@[simp] theorem bern_true (p : ℚ) : bern p true = p := rfl

@[simp] theorem bern_false (p : ℚ) : bern p false = 1 - p := rfl

/-- **The measure face of two-colour descent**: the i.i.d. Bernoulli
product measure pushes forward along the count quotient to the binomial
distribution — identically in `p`, as polynomials. -/
theorem pushMass_bern (p : ℚ) {n k : ℕ} (hk : k ≤ n) :
    pushMass (bern p) n (boolMarking n k)
      = (n.choose k : ℚ) * (p ^ k * (1 - p) ^ (n - k)) := by
  rw [pushMass_eq_card_mul, card_descFiber_boolMarking hk,
    bagWeight_eq_prod]
  congr 1
  simp [boolMarking, Multiset.map_replicate, Multiset.prod_replicate]

/-! ## The many-colour sector: multinomial -/

variable {c : ℕ}

private theorem prod_finsetSum {ι M : Type*} [CommMonoid M]
    (s : Finset ι) (f : ι → Multiset M) :
    (∑ i ∈ s, f i).prod = ∏ i ∈ s, (f i).prod := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.prod_cons, Multiset.prod_add, ih]

private theorem map_finsetSum {ι α β : Type*} (s : Finset ι)
    (f : ι → Multiset α) (g : α → β) :
    (∑ i ∈ s, f i).map g = ∑ i ∈ s, (f i).map g := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, Multiset.map_add, ih]

private theorem card_finsetSum {ι α : Type*} (s : Finset ι)
    (f : ι → Multiset α) :
    (∑ i ∈ s, f i).card = ∑ i ∈ s, (f i).card := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, Multiset.card_add, ih]

/-- The marking with `k j` tokens of colour `j`. -/
def vecMarking (k : Fin c → ℕ) : Multiset (Fin c) :=
  ∑ j, Multiset.replicate (k j) j

@[simp] theorem count_vecMarking (k : Fin c → ℕ) (j : Fin c) :
    (vecMarking k).count j = k j := by
  rw [vecMarking, Multiset.count_sum']
  simp [Multiset.count_replicate]

theorem card_vecMarking (k : Fin c → ℕ) :
    (vecMarking k).card = ∑ j, k j := by
  rw [vecMarking, card_finsetSum]
  simp [Multiset.card_replicate]

theorem countPerms_vecMarking (k : Fin c → ℕ) :
    (vecMarking k).countPerms = Nat.multinomial Finset.univ k := by
  rw [countPerms_eq_multinomial_univ]
  exact Nat.multinomial_congr fun j _ => count_vecMarking k j

/-- **The measure face of many-colour descent**: the i.i.d. product
measure pushes forward to the multinomial distribution — the
switch-family case. -/
theorem pushMass_vecMarking (q : Fin c → ℚ) {n : ℕ} {k : Fin c → ℕ}
    (hn : ∑ j, k j = n) :
    pushMass q n (vecMarking k)
      = (Nat.multinomial Finset.univ k : ℚ) * ∏ j, q j ^ k j := by
  have hcard : (vecMarking k).card = n := by rw [card_vecMarking, hn]
  have h := card_descFiber (vecMarking k)
  rw [hcard] at h
  rw [pushMass_eq_card_mul, h, countPerms_vecMarking, bagWeight_eq_prod]
  congr 1
  have hmap : (vecMarking k).map q = ∑ j, Multiset.replicate (k j) (q j) := by
    rw [vecMarking, map_finsetSum]
    exact Finset.sum_congr rfl fun j _ => by rw [Multiset.map_replicate]
  rw [hmap, prod_finsetSum]
  exact Finset.prod_congr rfl fun j _ => Multiset.prod_replicate _ _

/-! ## Normalization -/

/-- Total binomial mass is `1`, identically in `p` — a ring identity,
not a probability axiom. -/
theorem sum_binomial_mass (p : ℚ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℚ) * (p ^ k * (1 - p) ^ (n - k)) = 1 := by
  calc ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℚ) * (p ^ k * (1 - p) ^ (n - k))
      = ∑ k ∈ Finset.range (n + 1),
          p ^ k * (1 - p) ^ (n - k) * (n.choose k : ℚ) :=
        Finset.sum_congr rfl fun k _ => by ring
    _ = (p + (1 - p)) ^ n := (add_pow p (1 - p) n).symm
    _ = 1 := by rw [show p + (1 - p) = 1 by ring, one_pow]

/-- Total mass of the product measure over all words is the `n`-th
power of the total letter mass. -/
theorem sum_iidWeight [Fintype B] (μ : B → ℚ) (n : ℕ) :
    ∑ ω : Fin n → B, iidWeight μ (List.ofFn ω) = (∑ b : B, μ b) ^ n := by
  simp_rw [iidWeight_ofFn]
  rw [show (∑ b : B, μ b) ^ n = ∏ _i : Fin n, ∑ b : B, μ b by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
  rw [Finset.prod_univ_sum]
  rw [Fintype.piFinset_univ]

/-! ## Fixtures: kernel-checked reference tails

Reference values for tail events over the two sectors, evaluated from
the closed forms proven above (so each fixture pins the *definitional*
pushforward by transitivity). The asymmetric fixture (`p = 1/3`) is in
the battery deliberately: at `p = 1/2` a success/failure exponent swap
is invisible, at `p = 1/3` it is not. -/

/-- Evaluation rule for binomial coefficients: a multiplicative witness
against factorials, checked by the kernel (the direct recursion would
be exponential; the factorial route is linear). -/
private theorem choose_eq_of_mul_eq {n k v : ℕ} (hk : k ≤ n)
    (h : v * (Nat.factorial k * Nat.factorial (n - k)) = Nat.factorial n) :
    n.choose k = v := by
  have h₂ := Nat.choose_mul_factorial_mul_factorial hk
  have hpos : 0 < Nat.factorial k * Nat.factorial (n - k) :=
    Nat.mul_pos (Nat.factorial_pos k) (Nat.factorial_pos (n - k))
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h, ← h₂]
  ring

/-- Tail `count ≥ 3` of six coins at weight `1/3`: exactly `233/729`.
Hand check: `20·8 + 15·4 + 6·2 + 1 = 233` over `3⁶ = 729`. -/
theorem tail_three_of_six :
    ∑ e ∈ Finset.Icc 3 6,
        ((6).choose e : ℚ) * ((1/3 : ℚ) ^ e * (2/3 : ℚ) ^ (6 - e))
      = 233 / 729 := by
  rw [show (Finset.Icc 3 6 : Finset ℕ) = {3, 4, 5, 6} by decide]
  norm_num [Finset.sum_insert, Finset.mem_insert,
    show (6).choose 3 = 20 by decide, show (6).choose 4 = 15 by decide,
    show (6).choose 5 = 6 by decide, show (6).choose 6 = 1 by decide]

/-- The same tail through the pushforward itself: the descended measure
of the sector `{count ≥ 3}` under six `1/3`-coins. -/
theorem tail_three_of_six_pushMass :
    ∑ e ∈ Finset.Icc 3 6, pushMass (bern (1/3)) 6 (boolMarking 6 e)
      = 233 / 729 := by
  rw [Finset.sum_congr rfl fun e he =>
    pushMass_bern (1/3) (Finset.mem_Icc.mp he).2,
    show (1 - 1/3 : ℚ) = 2/3 by norm_num]
  exact tail_three_of_six

/-- Tail `count ≥ 20` of forty fair coins: exactly
`309339539149 / 549755813888` (`= 618679078298 / 2⁴⁰`). -/
theorem tail_twenty_of_forty :
    ∑ e ∈ Finset.Icc 20 40,
        ((40).choose e : ℚ) * ((1/2 : ℚ) ^ e * (1/2 : ℚ) ^ (40 - e))
      = 309339539149 / 549755813888 := by
  -- the evaluation ladder: each coefficient witnessed multiplicatively
  -- against factorials, kernel-checked
  have h20 : Nat.choose 40 20 = 137846528820 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h21 : Nat.choose 40 21 = 131282408400 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h22 : Nat.choose 40 22 = 113380261800 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h23 : Nat.choose 40 23 = 88732378800 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h24 : Nat.choose 40 24 = 62852101650 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h25 : Nat.choose 40 25 = 40225345056 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h26 : Nat.choose 40 26 = 23206929840 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h27 : Nat.choose 40 27 = 12033222880 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h28 : Nat.choose 40 28 = 5586853480 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h29 : Nat.choose 40 29 = 2311801440 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h30 : Nat.choose 40 30 = 847660528 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h31 : Nat.choose 40 31 = 273438880 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h32 : Nat.choose 40 32 = 76904685 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h33 : Nat.choose 40 33 = 18643560 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h34 : Nat.choose 40 34 = 3838380 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h35 : Nat.choose 40 35 = 658008 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h36 : Nat.choose 40 36 = 91390 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h37 : Nat.choose 40 37 = 9880 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h38 : Nat.choose 40 38 = 780 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h39 : Nat.choose 40 39 = 40 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  have h40 : Nat.choose 40 40 = 1 :=
    choose_eq_of_mul_eq (by norm_num) (by decide)
  rw [show (Finset.Icc 20 40 : Finset ℕ)
      = {20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
         36, 37, 38, 39, 40} by decide]
  norm_num [Finset.sum_insert, Finset.mem_insert, h20, h21, h22, h23,
    h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36,
    h37, h38, h39, h40]

/-- Three-colour fixture: the multinomial coefficient of `(2, 1, 1)`. -/
theorem multinomial_two_one_one :
    Nat.multinomial Finset.univ ![2, 1, 1] = 12 := by
  decide

/-- Three-colour mass fixture: four tokens over weights
`(1/2, 1/3, 1/6)` land on the count vector `(2, 1, 1)` with mass
`12 · (1/2)² · (1/3) · (1/6) = 1/6`. -/
theorem mixed_mass_fixture :
    pushMass ![(1 : ℚ)/2, 1/3, 1/6] 4 (vecMarking ![2, 1, 1]) = 1 / 6 := by
  rw [pushMass_vecMarking _ (by decide), multinomial_two_one_one]
  norm_num [Fin.prod_univ_three,
    show (![(1 : ℚ)/2, 1/3, 1/6]) 0 = 1/2 from rfl,
    show (![(1 : ℚ)/2, 1/3, 1/6]) 1 = 1/3 from rfl,
    show (![(1 : ℚ)/2, 1/3, 1/6]) 2 = 1/6 from rfl,
    show (![2, 1, 1] : Fin 3 → ℕ) 0 = 2 from rfl,
    show (![2, 1, 1] : Fin 3 → ℕ) 1 = 1 from rfl,
    show (![2, 1, 1] : Fin 3 → ℕ) 2 = 1 from rfl]

end Plate
end PPLC

-- Axiom receipts (std-three expected): the headline theorems.
#print axioms PPLC.Plate.iidWeight_perm
#print axioms PPLC.Plate.bagWeight
#print axioms PPLC.Plate.pushMass_eq_card_mul
#print axioms PPLC.Plate.card_descFiber
#print axioms PPLC.Plate.pushMass_bern
#print axioms PPLC.Plate.pushMass_vecMarking
#print axioms PPLC.Plate.sum_binomial_mass
#print axioms PPLC.Plate.sum_iidWeight
#print axioms PPLC.Plate.tail_three_of_six_pushMass
#print axioms PPLC.Plate.tail_twenty_of_forty
#print axioms PPLC.Plate.mixed_mass_fixture
