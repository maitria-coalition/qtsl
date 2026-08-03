import QtslAux.DyadicCore
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Ring.Subring.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith

/-! # Dyadic rationals, directed rounding, and finite floating-point values

This module develops the theory of dyadic rationals over the core
definitions of `QtslAux.DyadicCore`.

Main definitions:

* `Dyadic`: the dyadic rationals `{m * 2^e | m e : ℤ}` as a `Subring ℚ`,
  with the inherited `CommRing`, `LinearOrder`, and strict ordered-ring
  structure.
* `Dyadic.roundDown p q` / `Dyadic.roundUp p q`: rounding `q : ℚ` down/up to
  the grid of multiples of `2^(-p)`.
* `Dyadic.IsRepresentable p q`: `q` is an integer multiple of `2^(-p)`.

Main results:

* correctness of directed rounding: `roundDown_le`, `le_roundUp`,
  monotonicity (`roundDown_mono`, `roundUp_mono`), idempotence, exactness on
  representable inputs (`roundDown_eq_self`, `roundUp_eq_self`), the
  Galois-connection style characterizations `le_roundDown_iff` and
  `roundUp_le_iff`, error bounds `sub_roundDown_lt`, `roundUp_sub_lt`,
  `roundUp_sub_roundDown_le` (gap at most `2^(-p)`), negation symmetry
  (`roundDown_neg`, `roundUp_neg`), and precision monotonicity
  (`roundDown_le_roundDown`, `roundUp_le_roundUp`).
* facts about `FiniteFloat prec emin emax`: its rational value is dyadic
  (`FiniteFloat.toRat_isDyadic`), bounded in magnitude
  (`FiniteFloat.abs_toRat_le`), exactly representable at precision `-emin`
  (`FiniteFloat.toRat_isRepresentable`, hence fixed by rounding at any finer
  precision), and `toRat` is injective on normalized values
  (`FiniteFloat.toRat_inj_of_normalized`, `FiniteFloat.injOn_toRat_normalized`).
* `FiniteDouble` corollaries: `FiniteDouble.abs_toRat_le` and
  `FiniteDouble.exists_int_div_two_pow` (every finite double is
  `k / 2^1074`).
-/

namespace Qtsl

namespace Dyadic

theorem two_zpow_pos (p : ℤ) : (0 : ℚ) < 2 ^ p := zpow_pos (by norm_num) p

theorem two_zpow_ne_zero (p : ℤ) : (2 : ℚ) ^ p ≠ 0 := (two_zpow_pos p).ne'

theorem div_two_zpow (a : ℚ) (p : ℤ) : a / 2 ^ p = a * 2 ^ (-p) := by
  rw [zpow_neg, div_eq_mul_inv]

theorem intCast_mul_zpow (m a b : ℤ) (h : b ≤ a) :
    ((m * 2 ^ (a - b).toNat : ℤ) : ℚ) * 2 ^ b = (m : ℚ) * 2 ^ a := by
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have hab : a - b + b = a := by omega
  push_cast
  rw [mul_assoc, ← zpow_natCast (2 : ℚ) (a - b).toNat, Int.toNat_of_nonneg (sub_nonneg.mpr h),
    ← zpow_add₀ h2, hab]

theorem div_le_div_of_le {a b c : ℚ} (h : a ≤ b) (hc : 0 < c) : a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (inv_pos.mpr hc).le

end Dyadic

theorem isDyadic_zero : IsDyadic 0 := ⟨0, 0, by norm_num⟩

theorem isDyadic_one : IsDyadic 1 := ⟨1, 0, by norm_num⟩

theorem isDyadic_intCast (m : ℤ) : IsDyadic (m : ℚ) := ⟨m, 0, by norm_num⟩

protected theorem IsDyadic.add {q r : ℚ} (hq : IsDyadic q) (hr : IsDyadic r) :
    IsDyadic (q + r) := by
  obtain ⟨m₁, e₁, rfl⟩ := hq
  obtain ⟨m₂, e₂, rfl⟩ := hr
  rcases le_total e₁ e₂ with h | h
  · refine ⟨m₁ + m₂ * 2 ^ (e₂ - e₁).toNat, e₁, ?_⟩
    rw [← Dyadic.intCast_mul_zpow m₂ e₂ e₁ h]
    push_cast
    ring
  · refine ⟨m₁ * 2 ^ (e₁ - e₂).toNat + m₂, e₂, ?_⟩
    rw [← Dyadic.intCast_mul_zpow m₁ e₁ e₂ h]
    push_cast
    ring

protected theorem IsDyadic.mul {q r : ℚ} (hq : IsDyadic q) (hr : IsDyadic r) :
    IsDyadic (q * r) := by
  obtain ⟨m₁, e₁, rfl⟩ := hq
  obtain ⟨m₂, e₂, rfl⟩ := hr
  refine ⟨m₁ * m₂, e₁ + e₂, ?_⟩
  rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  push_cast
  ring

protected theorem IsDyadic.neg {q : ℚ} (hq : IsDyadic q) : IsDyadic (-q) := by
  obtain ⟨m, e, rfl⟩ := hq
  exact ⟨-m, e, by push_cast; ring⟩

def Dyadic : Subring ℚ where
  carrier := {q | IsDyadic q}
  zero_mem' := isDyadic_zero
  one_mem' := isDyadic_one
  add_mem' := IsDyadic.add
  mul_mem' := IsDyadic.mul
  neg_mem' := IsDyadic.neg

namespace Dyadic

theorem mem_iff {q : ℚ} : q ∈ Dyadic ↔ IsDyadic q := Iff.rfl

instance : CommRing Dyadic := inferInstance

instance : LinearOrder Dyadic := inferInstance

instance : IsStrictOrderedRing Dyadic := inferInstance

theorem coe_le_coe {a b : Dyadic} : (a : ℚ) ≤ (b : ℚ) ↔ a ≤ b := Iff.rfl

def roundDown (p : ℤ) (q : ℚ) : ℚ := ⌊q * 2 ^ p⌋ / 2 ^ p

def roundUp (p : ℤ) (q : ℚ) : ℚ := ⌈q * 2 ^ p⌉ / 2 ^ p

theorem roundDown_def (p : ℤ) (q : ℚ) : roundDown p q = ⌊q * 2 ^ p⌋ / 2 ^ p := rfl

theorem roundUp_def (p : ℤ) (q : ℚ) : roundUp p q = ⌈q * 2 ^ p⌉ / 2 ^ p := rfl

example : roundDown 3 (5 / 7 : ℚ) = 5 / 8 := by
  have h : ⌊(5 / 7 : ℚ) * 2 ^ (3 : ℤ)⌋ = 5 := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num
  rw [roundDown_def, h]
  norm_num

example : roundUp 3 (5 / 7 : ℚ) = 3 / 4 := by
  have h : ⌈(5 / 7 : ℚ) * 2 ^ (3 : ℤ)⌉ = 6 := by
    rw [Int.ceil_eq_iff]
    constructor <;> norm_num
  rw [roundUp_def, h]
  norm_num

example : roundDown 2 (-1 / 3 : ℚ) = -1 / 2 := by
  have h : ⌊(-1 / 3 : ℚ) * 2 ^ (2 : ℤ)⌋ = -2 := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num
  rw [roundDown_def, h]
  norm_num

example : roundUp 2 (-1 / 3 : ℚ) = -1 / 4 := by
  have h : ⌈(-1 / 3 : ℚ) * 2 ^ (2 : ℤ)⌉ = -1 := by
    rw [Int.ceil_eq_iff]
    constructor <;> norm_num
  rw [roundUp_def, h]
  norm_num

example : roundDown 3 (5 / 7 : ℚ) = 5 / 8 := by native_decide

theorem isDyadic_roundDown (p : ℤ) (q : ℚ) : IsDyadic (roundDown p q) :=
  ⟨⌊q * 2 ^ p⌋, -p, by rw [roundDown_def, div_two_zpow]⟩

theorem isDyadic_roundUp (p : ℤ) (q : ℚ) : IsDyadic (roundUp p q) :=
  ⟨⌈q * 2 ^ p⌉, -p, by rw [roundUp_def, div_two_zpow]⟩

theorem roundDown_mem (p : ℤ) (q : ℚ) : roundDown p q ∈ Dyadic := isDyadic_roundDown p q

theorem roundUp_mem (p : ℤ) (q : ℚ) : roundUp p q ∈ Dyadic := isDyadic_roundUp p q

theorem roundDown_le (p : ℤ) (q : ℚ) : roundDown p q ≤ q := by
  rw [roundDown_def, div_le_iff₀ (two_zpow_pos p)]
  exact Int.floor_le _

theorem le_roundUp (p : ℤ) (q : ℚ) : q ≤ roundUp p q := by
  rw [roundUp_def, le_div_iff₀ (two_zpow_pos p)]
  exact Int.le_ceil _

theorem roundDown_le_roundUp (p : ℤ) (q : ℚ) : roundDown p q ≤ roundUp p q :=
  (roundDown_le p q).trans (le_roundUp p q)

theorem roundDown_mono (p : ℤ) : Monotone (roundDown p) := by
  intro q r h
  have hfloor : ((⌊q * 2 ^ p⌋ : ℤ) : ℚ) ≤ (⌊r * 2 ^ p⌋ : ℤ) :=
    Int.cast_le.mpr (Int.floor_mono (mul_le_mul_of_nonneg_right h (two_zpow_pos p).le))
  rw [roundDown_def, roundDown_def]
  exact div_le_div_of_le hfloor (two_zpow_pos p)

theorem roundUp_mono (p : ℤ) : Monotone (roundUp p) := by
  intro q r h
  have hceil : ((⌈q * 2 ^ p⌉ : ℤ) : ℚ) ≤ (⌈r * 2 ^ p⌉ : ℤ) :=
    Int.cast_le.mpr (Int.ceil_mono (mul_le_mul_of_nonneg_right h (two_zpow_pos p).le))
  rw [roundUp_def, roundUp_def]
  exact div_le_div_of_le hceil (two_zpow_pos p)

def IsRepresentable (p : ℤ) (q : ℚ) : Prop := ∃ m : ℤ, q = m / 2 ^ p

theorem isRepresentable_iff_exists_int {p : ℤ} {q : ℚ} :
    IsRepresentable p q ↔ ∃ m : ℤ, q * 2 ^ p = m := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, div_mul_cancel₀ _ (two_zpow_ne_zero p)⟩
  · rintro ⟨m, h⟩
    exact ⟨m, by rw [← h, mul_div_cancel_right₀ _ (two_zpow_ne_zero p)]⟩

theorem IsRepresentable.isDyadic {p : ℤ} {q : ℚ} (h : IsRepresentable p q) : IsDyadic q := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨m, -p, div_two_zpow _ p⟩

theorem IsDyadic.isRepresentable {q : ℚ} (h : IsDyadic q) : ∃ p : ℤ, IsRepresentable p q := by
  obtain ⟨m, e, rfl⟩ := h
  exact ⟨-e, m, by rw [div_two_zpow, neg_neg]⟩

theorem IsRepresentable.mono {p p' : ℤ} {q : ℚ} (h : IsRepresentable p q) (hpp : p ≤ p') :
    IsRepresentable p' q := by
  obtain ⟨m, rfl⟩ := h
  refine ⟨m * 2 ^ (-p - -p').toNat, ?_⟩
  rw [div_two_zpow, div_two_zpow]
  exact (intCast_mul_zpow m (-p) (-p') (neg_le_neg hpp)).symm

theorem isRepresentable_roundDown (p : ℤ) (q : ℚ) : IsRepresentable p (roundDown p q) :=
  ⟨⌊q * 2 ^ p⌋, rfl⟩

theorem isRepresentable_roundUp (p : ℤ) (q : ℚ) : IsRepresentable p (roundUp p q) :=
  ⟨⌈q * 2 ^ p⌉, rfl⟩

theorem roundDown_eq_self {p : ℤ} {q : ℚ} (h : IsRepresentable p q) : roundDown p q = q := by
  obtain ⟨m, rfl⟩ := h
  rw [roundDown_def, div_mul_cancel₀ _ (two_zpow_ne_zero p), Int.floor_intCast]

theorem roundUp_eq_self {p : ℤ} {q : ℚ} (h : IsRepresentable p q) : roundUp p q = q := by
  obtain ⟨m, rfl⟩ := h
  rw [roundUp_def, div_mul_cancel₀ _ (two_zpow_ne_zero p), Int.ceil_intCast]

theorem roundDown_roundDown (p : ℤ) (q : ℚ) :
    roundDown p (roundDown p q) = roundDown p q :=
  roundDown_eq_self (isRepresentable_roundDown p q)

theorem roundUp_roundUp (p : ℤ) (q : ℚ) : roundUp p (roundUp p q) = roundUp p q :=
  roundUp_eq_self (isRepresentable_roundUp p q)

theorem le_roundDown_iff {p : ℤ} {d q : ℚ} (hd : IsRepresentable p d) :
    d ≤ roundDown p q ↔ d ≤ q := by
  obtain ⟨m, rfl⟩ := hd
  constructor
  · intro h
    exact h.trans (roundDown_le p q)
  · intro h
    rw [roundDown_def]
    have hm : (m : ℚ) ≤ ((⌊q * 2 ^ p⌋ : ℤ) : ℚ) :=
      Int.cast_le.mpr (Int.le_floor.mpr ((div_le_iff₀ (two_zpow_pos p)).mp h))
    exact div_le_div_of_le hm (two_zpow_pos p)

theorem roundUp_le_iff {p : ℤ} {d q : ℚ} (hd : IsRepresentable p d) :
    roundUp p q ≤ d ↔ q ≤ d := by
  obtain ⟨m, rfl⟩ := hd
  constructor
  · intro h
    exact (le_roundUp p q).trans h
  · intro h
    rw [roundUp_def]
    have hm : ((⌈q * 2 ^ p⌉ : ℤ) : ℚ) ≤ (m : ℚ) :=
      Int.cast_le.mpr (Int.ceil_le.mpr ((le_div_iff₀ (two_zpow_pos p)).mp h))
    exact div_le_div_of_le hm (two_zpow_pos p)

theorem sub_roundDown_lt (p : ℤ) (q : ℚ) : q - roundDown p q < 2 ^ (-p) := by
  have h1 : q < ((⌊q * 2 ^ p⌋ : ℤ) + 1 : ℚ) / 2 ^ p :=
    (lt_div_iff₀ (two_zpow_pos p)).mpr (Int.lt_floor_add_one _)
  have h2 : ((⌊q * 2 ^ p⌋ : ℤ) + 1 : ℚ) / 2 ^ p = roundDown p q + 2 ^ (-p) := by
    rw [add_div, roundDown_def, zpow_neg, one_div]
  linarith

theorem roundUp_sub_lt (p : ℤ) (q : ℚ) : roundUp p q - q < 2 ^ (-p) := by
  have hcancel : (2 : ℚ) ^ (-p) * 2 ^ p = 1 := by
    rw [zpow_neg, inv_mul_cancel₀ (two_zpow_ne_zero p)]
  have h1 : roundUp p q < q + 2 ^ (-p) := by
    rw [roundUp_def, div_lt_iff₀ (two_zpow_pos p), add_mul, hcancel]
    exact Int.ceil_lt_add_one _
  linarith

theorem roundUp_sub_roundDown_le (p : ℤ) (q : ℚ) :
    roundUp p q - roundDown p q ≤ 2 ^ (-p) := by
  have hcancel : (2 : ℚ) ^ (-p) * 2 ^ p = 1 := by
    rw [zpow_neg, inv_mul_cancel₀ (two_zpow_ne_zero p)]
  have hint : ((⌈q * 2 ^ p⌉ : ℤ) : ℚ) ≤ ((⌊q * 2 ^ p⌋ : ℤ) : ℚ) + 1 := by
    exact_mod_cast Int.ceil_le_floor_add_one _
  have h1 : roundUp p q ≤ roundDown p q + 2 ^ (-p) := by
    rw [roundUp_def, roundDown_def, div_le_iff₀ (two_zpow_pos p), add_mul, hcancel,
      div_mul_cancel₀ _ (two_zpow_ne_zero p)]
    exact hint
  linarith

theorem roundDown_neg (p : ℤ) (q : ℚ) : roundDown p (-q) = -(roundUp p q) := by
  rw [roundDown_def, roundUp_def, neg_mul, Int.floor_neg, Int.cast_neg, neg_div]

theorem roundUp_neg (p : ℤ) (q : ℚ) : roundUp p (-q) = -(roundDown p q) := by
  rw [roundUp_def, roundDown_def, neg_mul, Int.ceil_neg, Int.cast_neg, neg_div]

theorem roundUp_eq_neg_roundDown_neg (p : ℤ) (q : ℚ) :
    roundUp p q = -(roundDown p (-q)) := by
  rw [roundDown_neg, neg_neg]

theorem roundDown_le_roundDown {p p' : ℤ} (hpp : p ≤ p') (q : ℚ) :
    roundDown p q ≤ roundDown p' q :=
  (le_roundDown_iff ((isRepresentable_roundDown p q).mono hpp)).mpr (roundDown_le p q)

theorem roundUp_le_roundUp {p p' : ℤ} (hpp : p ≤ p') (q : ℚ) :
    roundUp p' q ≤ roundUp p q :=
  (roundUp_le_iff ((isRepresentable_roundUp p q).mono hpp)).mpr (le_roundUp p q)

namespace FiniteFloat

variable {prec : ℕ} {emin emax : ℤ}

protected theorem ext {x y : FiniteFloat prec emin emax} (hm : x.m = y.m) (he : x.e = y.e) :
    x = y := by
  cases x
  cases y
  simp only [mk.injEq]
  exact ⟨hm, he⟩

theorem toRat_isDyadic (x : FiniteFloat prec emin emax) : IsDyadic x.toRat :=
  ⟨x.m, x.e, toRat_def x⟩

theorem toRat_mem_dyadic (x : FiniteFloat prec emin emax) : x.toRat ∈ Dyadic :=
  toRat_isDyadic x

theorem toRat_eq_zero_iff {x : FiniteFloat prec emin emax} : x.toRat = 0 ↔ x.m = 0 := by
  rw [toRat_def, mul_eq_zero]
  simp [two_zpow_ne_zero x.e, Int.cast_eq_zero]

theorem abs_toRat_le (x : FiniteFloat prec emin emax) :
    |x.toRat| ≤ ((2 : ℚ) ^ prec - 1) * 2 ^ emax := by
  have habs : |x.toRat| = |(x.m : ℚ)| * 2 ^ x.e := by
    rw [toRat_def, abs_mul, abs_of_pos (two_zpow_pos x.e)]
  have h3 : |x.m| < (2 : ℤ) ^ prec := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast x.mantissa_bound
  have h1 : |x.m| ≤ (2 : ℤ) ^ prec - 1 := by linarith
  have hm : |(x.m : ℚ)| ≤ (2 : ℚ) ^ prec - 1 := by
    have h4 : ((|x.m| : ℤ) : ℚ) ≤ (((2 : ℤ) ^ prec - 1 : ℤ) : ℚ) := Int.cast_le.mpr h1
    rw [Int.cast_abs] at h4
    push_cast at h4
    exact h4
  have he : (2 : ℚ) ^ x.e ≤ 2 ^ emax := zpow_le_zpow_right₀ (by norm_num) x.exp_ub
  rw [habs]
  exact mul_le_mul hm he (two_zpow_pos x.e).le ((abs_nonneg _).trans hm)

theorem toRat_isRepresentable (x : FiniteFloat prec emin emax) :
    IsRepresentable (-emin) x.toRat := by
  refine ⟨x.m * 2 ^ (x.e - emin).toNat, ?_⟩
  rw [div_two_zpow, neg_neg, toRat_def]
  exact (intCast_mul_zpow x.m x.e emin x.exp_lb).symm

theorem roundDown_toRat (x : FiniteFloat prec emin emax) {p : ℤ} (hp : -emin ≤ p) :
    roundDown p x.toRat = x.toRat :=
  roundDown_eq_self ((toRat_isRepresentable x).mono hp)

theorem roundUp_toRat (x : FiniteFloat prec emin emax) {p : ℤ} (hp : -emin ≤ p) :
    roundUp p x.toRat = x.toRat :=
  roundUp_eq_self ((toRat_isRepresentable x).mono hp)

def Normalized (x : FiniteFloat prec emin emax) : Prop :=
  Odd x.m ∨ (x.m = 0 ∧ x.e = emin)

private theorem cancel_of_le {m₁ m₂ e₁ e₂ : ℤ}
    (h : (m₁ : ℚ) * 2 ^ e₁ = (m₂ : ℚ) * 2 ^ e₂) (hle : e₁ ≤ e₂) :
    m₁ = m₂ * 2 ^ (e₂ - e₁).toNat := by
  rw [← intCast_mul_zpow m₂ e₂ e₁ hle] at h
  exact_mod_cast mul_right_cancel₀ (two_zpow_ne_zero e₁) h

private theorem odd_case {m₁ m₂ e₁ e₂ : ℤ}
    (h : (m₁ : ℚ) * 2 ^ e₁ = (m₂ : ℚ) * 2 ^ e₂) (hle : e₁ ≤ e₂) (ho : Odd m₁) :
    m₁ = m₂ ∧ e₁ = e₂ := by
  have hk : m₁ = m₂ * 2 ^ (e₂ - e₁).toNat := cancel_of_le h hle
  rcases Nat.eq_zero_or_pos (e₂ - e₁).toNat with h0 | hpos
  · have he : e₁ = e₂ := by omega
    rw [hk, h0, pow_zero, mul_one]
    exact ⟨rfl, he⟩
  · exfalso
    have hsplit : (2 : ℤ) ^ (e₂ - e₁).toNat = 2 ^ ((e₂ - e₁).toNat - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    have heven : ∃ j : ℤ, m₁ = j * 2 :=
      ⟨m₂ * 2 ^ ((e₂ - e₁).toNat - 1), by rw [hk, hsplit]; ring⟩
    obtain ⟨j, hj⟩ := heven
    obtain ⟨k, hks⟩ := ho
    omega

theorem toRat_inj_of_normalized {x y : FiniteFloat prec emin emax}
    (hx : x.Normalized) (hy : y.Normalized) (h : x.toRat = y.toRat) : x = y := by
  have hq : (x.m : ℚ) * 2 ^ x.e = (y.m : ℚ) * 2 ^ y.e := by
    rw [← toRat_def x, ← toRat_def y]
    exact h
  rcases hx with hox | ⟨hxm, hxe⟩
  · rcases hy with hoy | ⟨hym, _⟩
    · rcases le_total x.e y.e with hle | hle
      · obtain ⟨hm, he⟩ := odd_case hq hle hox
        exact FiniteFloat.ext hm he
      · obtain ⟨hm, he⟩ := odd_case hq.symm hle hoy
        exact FiniteFloat.ext hm.symm he.symm
    · exfalso
      have hx0 : x.m = 0 := toRat_eq_zero_iff.mp (h.trans (toRat_eq_zero_iff.mpr hym))
      rw [hx0] at hox
      obtain ⟨k, hk⟩ := hox
      omega
  · rcases hy with hoy | ⟨hym, hye⟩
    · exfalso
      have hy0 : y.m = 0 := toRat_eq_zero_iff.mp (h.symm.trans (toRat_eq_zero_iff.mpr hxm))
      rw [hy0] at hoy
      obtain ⟨k, hk⟩ := hoy
      omega
    · exact FiniteFloat.ext (hxm.trans hym.symm) (hxe.trans hye.symm)

theorem injOn_toRat_normalized :
    Set.InjOn (toRat : FiniteFloat prec emin emax → ℚ) {x | x.Normalized} :=
  fun _x hx _y hy h => toRat_inj_of_normalized hx hy h

end FiniteFloat

namespace FiniteDouble

theorem abs_toRat_le (x : FiniteDouble) :
    |x.toRat| ≤ ((2 : ℚ) ^ 53 - 1) * 2 ^ (971 : ℤ) :=
  FiniteFloat.abs_toRat_le x

theorem exists_int_div_two_pow (x : FiniteDouble) :
    ∃ k : ℤ, x.toRat = k / 2 ^ (1074 : ℤ) := by
  obtain ⟨k, hk⟩ := FiniteFloat.toRat_isRepresentable x
  exact ⟨k, by rw [hk]; norm_num⟩

end FiniteDouble

example :
    (({ m := 5, e := -1, mantissa_bound := by norm_num, exp_lb := by norm_num,
        exp_ub := by norm_num } : FiniteDouble)).toRat = 5 / 2 := by
  norm_num [FiniteFloat.toRat_def]

end Dyadic

end Qtsl
