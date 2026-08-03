import QtslAux.Imprecise.MarginalCompat
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FieldSimp

/-! # Penalties and credal sets: the mass–direction decomposition

Finite rational sub-probability vectors decompose as mass times direction
(`smul_prob_mass_eq`, `smul_prob_dir_eq`, `normalize`), giving the
isomorphism between penalty-functional and credal-set presentations of
imprecise probability at the finite-support rational tier — and the
negative results (`stepGrade_not_mulConvex`, `gapSet_violates_C4`,
`mutant_c4_gap_uncompilable`) showing which candidate grades fall outside
the compilable convex class. -/

namespace Qtsl.Imprecise

open Finset

variable {X : Type*} [Fintype X]

def IsSubProb (v : X → ℚ) : Prop := (∀ x, 0 ≤ v x) ∧ ∑ x, v x ≤ 1

@[ext] theorem FinPMF.ext {μ₁ μ₂ : FinPMF X} (h : ∀ x, μ₁.prob x = μ₂.prob x) :
    μ₁ = μ₂ := by
  cases μ₁ with | mk p₁ hn₁ ht₁ =>
  cases μ₂ with | mk p₂ hn₂ ht₂ =>
  have hp : p₁ = p₂ := funext h
  subst hp
  rfl

theorem sum_smul_prob (γ : ℚ) (μ : FinPMF X) : ∑ x, (γ • μ.prob) x = γ := by
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, μ.total, mul_one]

theorem smul_prob_mass_eq {γ₁ γ₂ : ℚ} {μ₁ μ₂ : FinPMF X}
    (h : γ₁ • μ₁.prob = γ₂ • μ₂.prob) : γ₁ = γ₂ := by
  have h₁ := sum_smul_prob γ₁ μ₁
  rw [h, sum_smul_prob] at h₁
  exact h₁.symm

theorem smul_prob_dir_eq {γ : ℚ} (hγ : γ ≠ 0) {μ₁ μ₂ : FinPMF X}
    (h : γ • μ₁.prob = γ • μ₂.prob) : μ₁ = μ₂ := by
  apply FinPMF.ext
  intro x
  have hx := congrFun h x
  simp only [Pi.smul_apply, smul_eq_mul] at hx
  exact mul_left_cancel₀ hγ hx

def FinPMF.uniform (X : Type*) [Fintype X] [Nonempty X] : FinPMF X where
  prob := fun _ => (Fintype.card X : ℚ)⁻¹
  nonneg := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

def normalize (v : X → ℚ) (hnn : ∀ x, 0 ≤ v x) (hm : 0 < ∑ x, v x) : FinPMF X where
  prob := fun x => v x / ∑ y, v y
  nonneg := fun x => div_nonneg (hnn x) (le_of_lt hm)
  total := by rw [← Finset.sum_div, div_self (ne_of_gt hm)]

@[simp] theorem normalize_prob (v : X → ℚ) (hnn : ∀ x, 0 ≤ v x)
    (hm : 0 < ∑ x, v x) (x : X) :
    (normalize v hnn hm).prob x = v x / ∑ y, v y := rfl

theorem smul_normalize (v : X → ℚ) (hnn : ∀ x, 0 ≤ v x) (hm : 0 < ∑ x, v x) :
    (∑ x, v x) • (normalize v hnn hm).prob = v := by
  funext x
  simp only [normalize_prob, Pi.smul_apply, smul_eq_mul]
  rw [mul_comm]
  exact div_mul_cancel₀ (v x) (ne_of_gt hm)

theorem eq_zero_of_sum_eq_zero {v : X → ℚ} (hnn : ∀ x, 0 ≤ v x)
    (h : ∑ x, v x = 0) : v = 0 := by
  funext x
  have hx : v x ≤ 0 := by
    have := Finset.single_le_sum (f := v) (fun y _ => hnn y) (mem_univ x)
    rw [h] at this
    exact this
  exact le_antisymm hx (hnn x)

def FinPMF.mix (μ₁ μ₂ : FinPMF X) (t : ℚ) (h₀ : 0 ≤ t) (h₁ : t ≤ 1) : FinPMF X where
  prob := fun x => t * μ₁.prob x + (1 - t) * μ₂.prob x
  nonneg := fun x =>
    add_nonneg (mul_nonneg h₀ (μ₁.nonneg x))
      (mul_nonneg (by linarith) (μ₂.nonneg x))
  total := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      μ₁.total, μ₂.total]
    ring

@[simp] theorem FinPMF.mix_prob (μ₁ μ₂ : FinPMF X) (t : ℚ) (h₀ : 0 ≤ t)
    (h₁ : t ≤ 1) (x : X) :
    (μ₁.mix μ₂ t h₀ h₁).prob x = t * μ₁.prob x + (1 - t) * μ₂.prob x := rfl

structure GradeFunction (X : Type*) [Fintype X] where

  toFun : FinPMF X → ℚ

  nonneg : ∀ μ, 0 ≤ toFun μ

  le_one : ∀ μ, toFun μ ≤ 1

instance : CoeFun (GradeFunction X) (fun _ => FinPMF X → ℚ) :=
  ⟨GradeFunction.toFun⟩

@[simp] theorem GradeFunction.toFun_eq_coe (g : GradeFunction X) (μ : FinPMF X) :
    g.toFun μ = g μ := rfl

@[ext] theorem GradeFunction.ext {g₁ g₂ : GradeFunction X}
    (h : ∀ μ, g₁ μ = g₂ μ) : g₁ = g₂ := by
  cases g₁ with | mk f₁ hn₁ hl₁ =>
  cases g₂ with | mk f₂ hn₂ hl₂ =>
  have hf : f₁ = f₂ := funext h
  subst hf
  rfl

def MulConvex (g : GradeFunction X) : Prop :=
  ∀ (μ₁ μ₂ : FinPMF X) (t : ℚ) (h₀ : 0 ≤ t) (h₁ : t ≤ 1),
    g μ₁ * g μ₂ ≤ g (μ₁.mix μ₂ t h₀ h₁) * ((1 - t) * g μ₁ + t * g μ₂)

def GradeFunction.compile (g : GradeFunction X) : Set (X → ℚ) :=
  {v | ∃ (μ : FinPMF X) (γ : ℚ), 0 ≤ γ ∧ γ ≤ g μ ∧ v = γ • μ.prob}

theorem GradeFunction.smul_prob_mem_compile (g : GradeFunction X)
    (μ : FinPMF X) {γ : ℚ} (h0 : 0 ≤ γ) (hle : γ ≤ g μ) :
    γ • μ.prob ∈ g.compile :=
  ⟨μ, γ, h0, hle, rfl⟩

theorem GradeFunction.mem_compile_smul_iff (g : GradeFunction X)
    (μ : FinPMF X) {γ : ℚ} (hγ : 0 ≤ γ) :
    γ • μ.prob ∈ g.compile ↔ γ ≤ g μ := by
  constructor
  · rintro ⟨μ', γ', hγ'0, hγ'le, heq⟩
    rcases eq_or_lt_of_le hγ with hz | hpos
    · exact hz ▸ g.nonneg μ
    · have hmass : γ = γ' := smul_prob_mass_eq heq
      rw [← hmass] at heq hγ'le
      have hdir : μ = μ' := smul_prob_dir_eq hpos.ne' heq
      rw [hdir]
      exact hγ'le
  · intro hle
    exact ⟨μ, γ, hγ, hle, rfl⟩

theorem GradeFunction.compile_injective :
    Function.Injective (GradeFunction.compile (X := X)) := by
  intro g₁ g₂ h
  ext μ
  apply le_antisymm
  · have h₁ := g₁.smul_prob_mem_compile μ (g₁.nonneg μ) le_rfl
    rw [h] at h₁
    exact (g₂.mem_compile_smul_iff μ (g₁.nonneg μ)).mp h₁
  · have h₂ := g₂.smul_prob_mem_compile μ (g₂.nonneg μ) le_rfl
    rw [← h] at h₂
    exact (g₁.mem_compile_smul_iff μ (g₂.nonneg μ)).mp h₂

theorem GradeFunction.compile_subprob (g : GradeFunction X) :
    ∀ v ∈ g.compile, IsSubProb v := by
  rintro v ⟨μ, γ, h0, hle, rfl⟩
  constructor
  · intro x
    rw [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg h0 (μ.nonneg x)
  · rw [sum_smul_prob]
    exact hle.trans (g.le_one μ)

theorem GradeFunction.zero_mem_compile [Nonempty X] (g : GradeFunction X) :
    (0 : X → ℚ) ∈ g.compile :=
  ⟨FinPMF.uniform X, 0, le_rfl, g.nonneg _, (zero_smul ℚ _).symm⟩

theorem GradeFunction.scale_mem_compile (g : GradeFunction X) {v : X → ℚ}
    (hv : v ∈ g.compile) {lam : ℚ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    lam • v ∈ g.compile := by
  obtain ⟨μ, γ, hγ0, hγle, rfl⟩ := hv
  rw [smul_smul]
  exact ⟨μ, lam * γ, mul_nonneg h0 hγ0,
    (mul_le_of_le_one_left hγ0 h1).trans hγle, rfl⟩

theorem GradeFunction.compile_convex [Nonempty X] (g : GradeFunction X)
    (hg : MulConvex g) :
    ∀ v ∈ g.compile, ∀ w ∈ g.compile, ∀ s : ℚ, 0 ≤ s → s ≤ 1 →
      s • v + (1 - s) • w ∈ g.compile := by
  rintro v ⟨μ₁, γ₁, hγ₁0, hγ₁le, rfl⟩ w ⟨μ₂, γ₂, hγ₂0, hγ₂le, rfl⟩ s hs0 hs1
  have hs1' : 0 ≤ 1 - s := by linarith
  rw [smul_smul, smul_smul]
  set a := s * γ₁ with ha
  set b := (1 - s) * γ₂ with hb
  have ha0 : 0 ≤ a := mul_nonneg hs0 hγ₁0
  have hb0 : 0 ≤ b := mul_nonneg hs1' hγ₂0
  rcases eq_or_lt_of_le (add_nonneg ha0 hb0) with hm0 | hmpos
  ·
    have haz : a = 0 := by linarith
    have hbz : b = 0 := by linarith
    rw [haz, hbz, zero_smul, zero_smul, add_zero]
    exact g.zero_mem_compile
  ·
    set m := a + b with hm
    set t := a / m with ht
    have ht0 : 0 ≤ t := div_nonneg ha0 hmpos.le
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one hmpos]
      linarith
    have hmt : m * t = a := by
      rw [ht, mul_comm]
      exact div_mul_cancel₀ a hmpos.ne'
    have hmt' : m * (1 - t) = b := by
      rw [mul_sub, mul_one, hmt, hm]
      ring
    have hvec : a • μ₁.prob + b • μ₂.prob = m • (μ₁.mix μ₂ t ht0 ht1).prob := by
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, FinPMF.mix_prob]
      rw [mul_add, ← mul_assoc, ← mul_assoc, hmt, hmt']
    rw [hvec]
    refine g.smul_prob_mem_compile _ hmpos.le ?_

    rcases eq_or_lt_of_le ht0 with ht0eq | htpos
    ·
      have haz : a = 0 := by rw [← hmt, ← ht0eq, mul_zero]
      have hmb : m = b := by rw [hm, haz, zero_add]
      have hμeq : μ₁.mix μ₂ t ht0 ht1 = μ₂ := by
        apply FinPMF.ext
        intro x
        rw [FinPMF.mix_prob, ← ht0eq]
        ring
      rw [hμeq, hmb, hb]
      exact (mul_le_of_le_one_left hγ₂0 (by linarith)).trans hγ₂le
    rcases eq_or_lt_of_le ht1 with ht1eq | htlt1
    ·
      have hbz : b = 0 := by rw [← hmt', ht1eq]; ring
      have hma : m = a := by rw [hm, hbz, add_zero]
      have hμeq : μ₁.mix μ₂ t ht0 ht1 = μ₁ := by
        apply FinPMF.ext
        intro x
        rw [FinPMF.mix_prob, ht1eq]
        ring
      rw [hμeq, hma, ha]
      exact (mul_le_of_le_one_left hγ₁0 hs1).trans hγ₁le
    ·
      have hγ₁pos : 0 < γ₁ := by
        rcases eq_or_lt_of_le hγ₁0 with h | h
        · exfalso
          have haz : a = 0 := by rw [ha, ← h, mul_zero]
          rw [ht, haz, zero_div] at htpos
          exact lt_irrefl 0 htpos
        · exact h
      have hg₁pos : 0 < g μ₁ := lt_of_lt_of_le hγ₁pos hγ₁le
      have hDpos : 0 < (1 - t) * g μ₁ + t * g μ₂ := by
        have h1 : 0 < (1 - t) * g μ₁ := mul_pos (by linarith) hg₁pos
        have h2 : 0 ≤ t * g μ₂ := mul_nonneg htpos.le (g.nonneg μ₂)
        linarith
      have hmc := hg μ₁ μ₂ t ht0 ht1
      have hkey : m * ((1 - t) * g μ₁ + t * g μ₂) ≤ g μ₁ * g μ₂ := by
        have e1 : m * ((1 - t) * g μ₁ + t * g μ₂)
            = b * g μ₁ + a * g μ₂ := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, hmt, hmt']
        rw [e1]
        have h1 : b * g μ₁ ≤ (1 - s) * (g μ₂ * g μ₁) := by
          rw [hb, mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hγ₂le (g.nonneg μ₁)) hs1'
        have h2 : a * g μ₂ ≤ s * (g μ₁ * g μ₂) := by
          rw [ha, mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hγ₁le (g.nonneg μ₂)) hs0
        calc b * g μ₁ + a * g μ₂
            ≤ (1 - s) * (g μ₂ * g μ₁) + s * (g μ₁ * g μ₂) := add_le_add h1 h2
          _ = g μ₁ * g μ₂ := by ring
      exact le_of_mul_le_mul_right (hkey.trans hmc) hDpos

structure CredalDenotation (X : Type*) [Fintype X] where

  carrier : Set (X → ℚ)

  grade : FinPMF X → ℚ

  subprob : ∀ v ∈ carrier, IsSubProb v

  zero_mem : (0 : X → ℚ) ∈ carrier

  convex : ∀ v ∈ carrier, ∀ w ∈ carrier, ∀ s : ℚ, 0 ≤ s → s ≤ 1 →
    s • v + (1 - s) • w ∈ carrier

  grade_mem : ∀ μ : FinPMF X, grade μ • μ.prob ∈ carrier

  grade_max : ∀ (μ : FinPMF X) (γ : ℚ), 0 ≤ γ → γ • μ.prob ∈ carrier →
    γ ≤ grade μ

namespace CredalDenotation

theorem grade_nonneg (S : CredalDenotation X) (μ : FinPMF X) :
    0 ≤ S.grade μ :=
  S.grade_max μ 0 le_rfl (by rw [zero_smul]; exact S.zero_mem)

theorem grade_le_one (S : CredalDenotation X) (μ : FinPMF X) :
    S.grade μ ≤ 1 := by
  have h := (S.subprob _ (S.grade_mem μ)).2
  rwa [sum_smul_prob] at h

theorem scale_mem (S : CredalDenotation X) {v : X → ℚ} (hv : v ∈ S.carrier)
    {lam : ℚ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : lam • v ∈ S.carrier := by
  have h := S.convex v hv 0 S.zero_mem lam h0 h1
  simpa using h

theorem grade_unique (S T : CredalDenotation X) (h : S.carrier = T.carrier) :
    S.grade = T.grade := by
  funext μ
  refine le_antisymm
    (T.grade_max μ _ (S.grade_nonneg μ) (h ▸ S.grade_mem μ))
    (S.grade_max μ _ (T.grade_nonneg μ) (h.symm ▸ T.grade_mem μ))

@[ext] theorem ext {S T : CredalDenotation X} (h : S.carrier = T.carrier) :
    S = T := by
  have hg := grade_unique S T h
  cases S with | mk c₁ g₁ p₁ p₂ p₃ p₄ p₅ =>
  cases T with | mk c₂ g₂ q₁ q₂ q₃ q₄ q₅ =>
  simp only at h hg
  subst h
  subst hg
  rfl

def gradeFn (S : CredalDenotation X) : GradeFunction X where
  toFun := S.grade
  nonneg := S.grade_nonneg
  le_one := S.grade_le_one

@[simp] theorem gradeFn_apply (S : CredalDenotation X) (μ : FinPMF X) :
    S.gradeFn μ = S.grade μ := rfl

theorem compile_gradeFn [Nonempty X] (S : CredalDenotation X) :
    S.gradeFn.compile = S.carrier := by
  ext v
  constructor
  · rintro ⟨μ, γ, hγ0, hγle, rfl⟩
    rw [gradeFn_apply] at hγle
    by_cases hG : S.grade μ = 0
    · have hγz : γ = 0 := le_antisymm (hG ▸ hγle) hγ0
      rw [hγz, zero_smul]
      exact S.zero_mem
    · have hGpos : 0 < S.grade μ :=
        lt_of_le_of_ne (S.grade_nonneg μ) (Ne.symm hG)
      have hkey : γ • μ.prob = (γ / S.grade μ) • (S.grade μ • μ.prob) := by
        rw [smul_smul, div_mul_cancel₀ γ hGpos.ne']
      rw [hkey]
      exact S.scale_mem (S.grade_mem μ) (div_nonneg hγ0 hGpos.le)
        ((div_le_one hGpos).mpr hγle)
  · intro hv
    obtain ⟨hnn, _⟩ := S.subprob v hv
    rcases eq_or_lt_of_le (Finset.sum_nonneg fun x _ => hnn x) with hm | hm
    · have hv0 : v = 0 := eq_zero_of_sum_eq_zero hnn hm.symm
      rw [hv0]
      exact S.gradeFn.zero_mem_compile
    · refine ⟨normalize v hnn hm, ∑ x, v x, hm.le, ?_,
        (smul_normalize v hnn hm).symm⟩
      rw [gradeFn_apply]
      exact S.grade_max _ _ hm.le (by rw [smul_normalize]; exact hv)

theorem mulConvex_gradeFn (S : CredalDenotation X) : MulConvex S.gradeFn := by
  intro μ₁ μ₂ t ht0 ht1
  simp only [gradeFn_apply]
  by_cases hG₁ : S.grade μ₁ = 0
  · have hzero : S.grade μ₁ * S.grade μ₂ = 0 := by rw [hG₁, zero_mul]
    rw [hzero]
    exact mul_nonneg (S.grade_nonneg _)
      (add_nonneg (mul_nonneg (by linarith) (S.grade_nonneg μ₁))
        (mul_nonneg ht0 (S.grade_nonneg μ₂)))
  by_cases hG₂ : S.grade μ₂ = 0
  · have hzero : S.grade μ₁ * S.grade μ₂ = 0 := by rw [hG₂, mul_zero]
    rw [hzero]
    exact mul_nonneg (S.grade_nonneg _)
      (add_nonneg (mul_nonneg (by linarith) (S.grade_nonneg μ₁))
        (mul_nonneg ht0 (S.grade_nonneg μ₂)))
  have hG₁pos : 0 < S.grade μ₁ :=
    lt_of_le_of_ne (S.grade_nonneg μ₁) (Ne.symm hG₁)
  have hG₂pos : 0 < S.grade μ₂ :=
    lt_of_le_of_ne (S.grade_nonneg μ₂) (Ne.symm hG₂)
  set D := (1 - t) * S.grade μ₁ + t * S.grade μ₂ with hD
  have hDpos : 0 < D := by
    rcases eq_or_lt_of_le ht1 with h1 | h1
    · have hDeq : D = S.grade μ₂ := by rw [hD, h1]; ring
      rw [hDeq]
      exact hG₂pos
    · have ha : 0 < (1 - t) * S.grade μ₁ := mul_pos (by linarith) hG₁pos
      have hb : 0 ≤ t * S.grade μ₂ := mul_nonneg ht0 hG₂pos.le
      linarith
  set s := t * S.grade μ₂ / D with hs
  have hs0 : 0 ≤ s := div_nonneg (mul_nonneg ht0 hG₂pos.le) hDpos.le
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one hDpos, hD]
    have : 0 ≤ (1 - t) * S.grade μ₁ := mul_nonneg (by linarith) hG₁pos.le
    linarith
  have hu := S.convex _ (S.grade_mem μ₁) _ (S.grade_mem μ₂) s hs0 hs1
  have hvec : s • (S.grade μ₁ • μ₁.prob) + (1 - s) • (S.grade μ₂ • μ₂.prob)
      = (S.grade μ₁ * S.grade μ₂ / D) • (μ₁.mix μ₂ t ht0 ht1).prob := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, FinPMF.mix_prob, hs]
    field_simp
    ring
  rw [hvec] at hu
  have hle := S.grade_max _ _
    (div_nonneg (mul_nonneg hG₁pos.le hG₂pos.le) hDpos.le) hu
  rw [div_le_iff₀ hDpos] at hle
  exact hle

end CredalDenotation

def GradeFunction.toCredal [Nonempty X] (g : GradeFunction X)
    (hg : MulConvex g) : CredalDenotation X where
  carrier := g.compile
  grade := g.toFun
  subprob := g.compile_subprob
  zero_mem := g.zero_mem_compile
  convex := g.compile_convex hg
  grade_mem := fun μ => g.smul_prob_mem_compile μ (g.nonneg μ) le_rfl
  grade_max := fun μ _ h0 hmem => (g.mem_compile_smul_iff μ h0).mp hmem

@[simp] theorem GradeFunction.gradeFn_toCredal [Nonempty X]
    (g : GradeFunction X) (hg : MulConvex g) :
    (g.toCredal hg).gradeFn = g := rfl

theorem CredalDenotation.toCredal_gradeFn [Nonempty X]
    (S : CredalDenotation X) :
    (S.gradeFn.toCredal S.mulConvex_gradeFn).carrier = S.carrier :=
  S.compile_gradeFn

theorem GradeFunction.compile_subset_iff (g₁ g₂ : GradeFunction X) :
    g₁.compile ⊆ g₂.compile ↔ ∀ μ, g₁ μ ≤ g₂ μ := by
  constructor
  · intro h μ
    have hm := h (g₁.smul_prob_mem_compile μ (g₁.nonneg μ) le_rfl)
    exact (g₂.mem_compile_smul_iff μ (g₁.nonneg μ)).mp hm
  · rintro h v ⟨μ, γ, h0, hle, rfl⟩
    exact ⟨μ, γ, h0, hle.trans (h μ), rfl⟩

def GradeFunction.bot (X : Type*) [Fintype X] : GradeFunction X :=
  ⟨fun _ => 0, fun _ => le_rfl, fun _ => zero_le_one⟩

theorem GradeFunction.compile_bot [Nonempty X] :
    (GradeFunction.bot X).compile = {(0 : X → ℚ)} := by
  ext v
  constructor
  · rintro ⟨μ, γ, h0, hle, rfl⟩
    have hγz : γ = 0 := le_antisymm hle h0
    rw [hγz, zero_smul]
    rfl
  · intro hv
    rw [Set.mem_singleton_iff] at hv
    rw [hv]
    exact (GradeFunction.bot X).zero_mem_compile

theorem GradeFunction.compile_eq_bot_iff [Nonempty X] (g : GradeFunction X) :
    g.compile = {(0 : X → ℚ)} ↔ ∀ μ, g μ = 0 := by
  constructor
  · intro h μ
    have hm := g.smul_prob_mem_compile μ (g.nonneg μ) le_rfl
    rw [h, Set.mem_singleton_iff] at hm
    have h₁ := sum_smul_prob (g μ) μ
    rw [hm] at h₁
    simpa using h₁.symm
  · intro h
    have hg : g = GradeFunction.bot X := GradeFunction.ext fun μ => h μ
    rw [hg, GradeFunction.compile_bot]

section Naturality

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

def vecMap (h : X → Y) (v : X → ℚ) : Y → ℚ :=
  fun y => ∑ x ∈ univ.filter fun x => h x = y, v x

theorem vecMap_prob (h : X → Y) (μ : FinPMF X) :
    vecMap h μ.prob = (μ.map h).prob := rfl

omit [Fintype Y] in
theorem vecMap_smul (h : X → Y) (γ : ℚ) (v : X → ℚ) :
    vecMap h (γ • v) = γ • vecMap h v := by
  funext y
  simp only [vecMap, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

def GradeFunction.pullback (g : GradeFunction Y) (h : X → Y) :
    GradeFunction X :=
  ⟨fun μ => g (μ.map h), fun _ => g.nonneg _, fun _ => g.le_one _⟩

@[simp] theorem GradeFunction.pullback_apply (g : GradeFunction Y)
    (h : X → Y) (μ : FinPMF X) : g.pullback h μ = g (μ.map h) := rfl

theorem GradeFunction.compile_pullback [Nonempty X] (g : GradeFunction Y)
    (h : X → Y) :
    (g.pullback h).compile = {v | IsSubProb v ∧ vecMap h v ∈ g.compile} := by
  ext v
  constructor
  · rintro ⟨μ, γ, h0, hle, rfl⟩
    refine ⟨(g.pullback h).compile_subprob _ ⟨μ, γ, h0, hle, rfl⟩, ?_⟩
    rw [vecMap_smul, vecMap_prob]
    exact ⟨μ.map h, γ, h0, hle, rfl⟩
  · rintro ⟨⟨hnn, _⟩, hmem⟩
    rcases eq_or_lt_of_le (Finset.sum_nonneg fun x _ => hnn x) with hm | hm
    · have hv0 : v = 0 := eq_zero_of_sum_eq_zero hnn hm.symm
      rw [hv0]
      exact (g.pullback h).zero_mem_compile
    · refine ⟨normalize v hnn hm, ∑ x, v x, hm.le, ?_,
        (smul_normalize v hnn hm).symm⟩
      rw [GradeFunction.pullback_apply]
      have hv : vecMap h v = (∑ x, v x) • ((normalize v hnn hm).map h).prob := by
        conv_lhs => rw [← smul_normalize v hnn hm]
        rw [vecMap_smul, vecMap_prob]
      rw [hv] at hmem
      exact (g.mem_compile_smul_iff _ hm.le).mp hmem

end Naturality

section Composite

variable {ι : Type*} [Fintype ι] {Xi : ι → Type*} [∀ i, Fintype (Xi i)]

def prodGrade (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (g : ∀ i, GradeFunction (Xi i)) : GradeFunction X :=
  ⟨fun μ => ∏ i, g i (m i μ),
   fun _ => Finset.prod_nonneg fun i _ => (g i).nonneg _,
   fun _ => Finset.prod_le_one (fun i _ => (g i).nonneg _)
     (fun i _ => (g i).le_one _)⟩

@[simp] theorem prodGrade_apply (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (g : ∀ i, GradeFunction (Xi i)) (μ : FinPMF X) :
    prodGrade m g μ = ∏ i, g i (m i μ) := rfl

theorem prodGrade_le (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (g : ∀ i, GradeFunction (Xi i)) (μ : FinPMF X) (i : ι) :
    prodGrade m g μ ≤ g i (m i μ) := by
  classical
  rw [prodGrade_apply, ← Finset.mul_prod_erase univ _ (mem_univ i)]
  exact mul_le_of_le_one_right ((g i).nonneg _)
    (Finset.prod_le_one (fun j _ => (g j).nonneg _)
      (fun j _ => (g j).le_one _))

theorem compile_prodGrade_ray (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (g : ∀ i, GradeFunction (Xi i)) (μ : FinPMF X) {γ : ℚ} (hγ : 0 ≤ γ) :
    γ • μ.prob ∈ (prodGrade m g).compile ↔ γ ≤ ∏ i, g i (m i μ) :=
  (prodGrade m g).mem_compile_smul_iff μ hγ

theorem prodGrade_marginal_mem (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (g : ∀ i, GradeFunction (Xi i)) (μ : FinPMF X) {γ : ℚ} (hγ : 0 ≤ γ)
    (hmem : γ • μ.prob ∈ (prodGrade m g).compile) (i : ι) :
    γ • (m i μ).prob ∈ (g i).compile :=
  ((g i).mem_compile_smul_iff _ hγ).mpr
    ((((prodGrade m g).mem_compile_smul_iff μ hγ).mp hmem).trans
      (prodGrade_le m g μ i))

theorem expHom_finsetSum {E : ENNRat → ℚ} (hone : E 0 = 1)
    (hmul : ∀ a b, E (a + b) = E a * E b) {κ : Type*} (s : Finset κ)
    (f : κ → ENNRat) :
    E (∑ i ∈ s, f i) = ∏ i ∈ s, E (f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using hone
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, hmul, ih]

def gradeOfPenalty (E : ENNRat → ℚ) (h0 : ∀ a, 0 ≤ E a)
    (h1 : ∀ a, E a ≤ 1) (f : FinPMF X → ENNRat) : GradeFunction X :=
  ⟨fun μ => E (f μ), fun _ => h0 _, fun _ => h1 _⟩

@[simp] theorem gradeOfPenalty_apply (E : ENNRat → ℚ) (h0 : ∀ a, 0 ≤ E a)
    (h1 : ∀ a, E a ≤ 1) (f : FinPMF X → ENNRat) (μ : FinPMF X) :
    gradeOfPenalty E h0 h1 f μ = E (f μ) := rfl

theorem gradeOfPenalty_compositePenalty (E : ENNRat → ℚ)
    (h0 : ∀ a, 0 ≤ E a) (h1 : ∀ a, E a ≤ 1) (hone : E 0 = 1)
    (hmul : ∀ a b, E (a + b) = E a * E b)
    (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (f : ∀ i, FinPMF (Xi i) → ENNRat) :
    gradeOfPenalty E h0 h1 (compositePenalty m f)
      = prodGrade m (fun i => gradeOfPenalty E h0 h1 (f i)) := by
  apply GradeFunction.ext
  intro μ
  rw [gradeOfPenalty_apply, prodGrade_apply]
  exact expHom_finsetSum hone hmul univ _

theorem compositePenalty_marginal_mem (E : ENNRat → ℚ)
    (h0 : ∀ a, 0 ≤ E a) (h1 : ∀ a, E a ≤ 1) (hone : E 0 = 1)
    (hmul : ∀ a b, E (a + b) = E a * E b)
    (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (f : ∀ i, FinPMF (Xi i) → ENNRat) (μ : FinPMF X) {γ : ℚ} (hγ : 0 ≤ γ)
    (hmem : γ • μ.prob ∈ (gradeOfPenalty E h0 h1 (compositePenalty m f)).compile)
    (i : ι) :
    γ • (m i μ).prob ∈ (gradeOfPenalty E h0 h1 (f i)).compile := by
  rw [gradeOfPenalty_compositePenalty E h0 h1 hone hmul m f] at hmem
  exact prodGrade_marginal_mem _ _ μ hγ hmem i

theorem compositePenalty_marginal_mem_of_antitone (E : ENNRat → ℚ)
    (h0 : ∀ a, 0 ≤ E a) (h1 : ∀ a, E a ≤ 1)
    (hanti : ∀ a b, a ≤ b → E b ≤ E a)
    (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (f : ∀ i, FinPMF (Xi i) → ENNRat) (μ : FinPMF X) {γ : ℚ} (hγ : 0 ≤ γ)
    (hmem : γ • μ.prob ∈ (gradeOfPenalty E h0 h1 (compositePenalty m f)).compile)
    (i : ι) :
    γ • (m i μ).prob ∈ (gradeOfPenalty E h0 h1 (f i)).compile := by
  have hdom := penalty_marginal_domination m f μ i
  have hE : E (compositePenalty m f μ) ≤ E (f i (m i μ)) :=
    hanti _ _ hdom
  refine ((gradeOfPenalty E h0 h1 (f i)).mem_compile_smul_iff _ hγ).mpr ?_
  have hγle := ((gradeOfPenalty E h0 h1
    (compositePenalty m f)).mem_compile_smul_iff μ hγ).mp hmem
  rw [gradeOfPenalty_apply] at hγle
  rw [gradeOfPenalty_apply]
  exact hγle.trans hE

end Composite

section TwoPoint

def deltaZero : FinPMF (Fin 2) where
  prob := fun j => if j = 0 then 1 else 0
  nonneg := fun j => by by_cases hj : j = 0 <;> simp [hj]
  total := by simp

theorem FinPMF.fin2_prob_one (μ : FinPMF (Fin 2)) :
    μ.prob 1 = 1 - μ.prob 0 := by
  have h := μ.total
  rw [Fin.sum_univ_two] at h
  linarith

theorem FinPMF.fin2_prob_zero_le_one (μ : FinPMF (Fin 2)) : μ.prob 0 ≤ 1 := by
  have h := μ.nonneg 1
  rw [μ.fin2_prob_one] at h
  linarith

def twoPointGrade : GradeFunction (Fin 2) where
  toFun := fun μ => 1 / (2 - μ.prob 0)
  nonneg := fun μ =>
    le_of_lt (div_pos one_pos (by linarith [μ.fin2_prob_zero_le_one]))
  le_one := fun μ => by
    rw [div_le_one (by linarith [μ.fin2_prob_zero_le_one])]
    linarith [μ.fin2_prob_zero_le_one]

@[simp] theorem twoPointGrade_apply (μ : FinPMF (Fin 2)) :
    twoPointGrade μ = 1 / (2 - μ.prob 0) := rfl

theorem twoPointGrade_recip_affine (μ₁ μ₂ : FinPMF (Fin 2)) (t : ℚ)
    (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
    2 - (μ₁.mix μ₂ t h₀ h₁).prob 0
      = t * (2 - μ₁.prob 0) + (1 - t) * (2 - μ₂.prob 0) := by
  rw [FinPMF.mix_prob]
  ring

theorem twoPointGrade_mulConvex : MulConvex twoPointGrade := by
  intro μ₁ μ₂ t h₀ h₁
  have ha₁ : (0:ℚ) < 2 - μ₁.prob 0 := by linarith [μ₁.fin2_prob_zero_le_one]
  have ha₂ : (0:ℚ) < 2 - μ₂.prob 0 := by linarith [μ₂.fin2_prob_zero_le_one]
  have hmixpos : (0:ℚ) < t * (2 - μ₁.prob 0) + (1 - t) * (2 - μ₂.prob 0) := by
    rw [← twoPointGrade_recip_affine μ₁ μ₂ t h₀ h₁]
    linarith [(μ₁.mix μ₂ t h₀ h₁).fin2_prob_zero_le_one]
  apply le_of_eq
  simp only [twoPointGrade_apply, twoPointGrade_recip_affine μ₁ μ₂ t h₀ h₁]
  rw [div_mul_div_comm, mul_one_div, mul_one_div,
    div_add_div _ _ ha₁.ne' ha₂.ne', div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero ha₁.ne' ha₂.ne')
      (mul_ne_zero hmixpos.ne' (mul_ne_zero ha₁.ne' ha₂.ne'))]
  ring

theorem twoPointGrade_compile :
    twoPointGrade.compile
      = {v : Fin 2 → ℚ | IsSubProb v ∧ v 0 + 2 * v 1 ≤ 1} := by
  ext v
  constructor
  · rintro ⟨μ, γ, h0, hle, rfl⟩
    refine ⟨twoPointGrade.compile_subprob _ ⟨μ, γ, h0, hle, rfl⟩, ?_⟩
    rw [twoPointGrade_apply] at hle
    have hpos : (0:ℚ) < 2 - μ.prob 0 := by linarith [μ.fin2_prob_zero_le_one]
    rw [le_div_iff₀ hpos] at hle
    have hp1 : μ.prob 1 = 1 - μ.prob 0 := μ.fin2_prob_one
    simp only [Pi.smul_apply, smul_eq_mul]
    have hexp : γ * μ.prob 0 + 2 * (γ * μ.prob 1)
        = γ * (2 - μ.prob 0) := by
      rw [hp1]
      ring
    rw [hexp]
    exact hle
  · rintro ⟨⟨hnn, _⟩, hhalf⟩
    rcases eq_or_lt_of_le (Finset.sum_nonneg fun x _ => hnn x) with hm | hm
    · have hv0 : v = 0 := eq_zero_of_sum_eq_zero hnn hm.symm
      rw [hv0]
      exact twoPointGrade.zero_mem_compile
    · refine ⟨normalize v hnn hm, ∑ x, v x, hm.le, ?_,
        (smul_normalize v hnn hm).symm⟩
      rw [twoPointGrade_apply]
      have hpos : (0:ℚ) < 2 - (normalize v hnn hm).prob 0 := by
        linarith [(normalize v hnn hm).fin2_prob_zero_le_one]
      rw [le_div_iff₀ hpos, normalize_prob]
      have hcancel : (∑ y, v y) * (v 0 / ∑ y, v y) = v 0 := by
        rw [mul_comm]
        exact div_mul_cancel₀ (v 0) (ne_of_gt hm)
      have hkey : (∑ x, v x) * (2 - v 0 / ∑ y, v y)
          = 2 * (∑ x, v x) - v 0 := by
        rw [mul_sub, hcancel]
        ring
      rw [hkey]
      have hsum : ∑ x, v x = v 0 + v 1 := by rw [Fin.sum_univ_two]
      rw [hsum]
      linarith

theorem twoPointGrade_strict_witness :
    twoPointGrade (deltaZero.mix deltaOne (1/2) (by norm_num) (by norm_num)) ^ 2
      < twoPointGrade deltaZero * twoPointGrade deltaOne := by
  norm_num [twoPointGrade_apply, FinPMF.mix_prob, deltaZero, deltaOne]

end TwoPoint

section Mutants

def GradeFunction.top (X : Type*) [Fintype X] : GradeFunction X :=
  ⟨fun _ => 1, fun _ => zero_le_one, fun _ => le_rfl⟩

theorem prodGrade_marginal_control :
    ((1:ℚ)/4) • deltaOne.prob ∈ twoPointGrade.compile := by
  have hmem : ((1:ℚ)/4) • deltaOne.prob
      ∈ (prodGrade (fun _ : Fin 2 => id)
          (fun _ => twoPointGrade)).compile := by
    rw [compile_prodGrade_ray _ _ deltaOne (by norm_num)]
    rw [Fin.prod_univ_two]
    norm_num [twoPointGrade_apply, deltaOne]
  exact prodGrade_marginal_mem (fun _ : Fin 2 => id)
    (fun _ => twoPointGrade) deltaOne (by norm_num) hmem 0

theorem mutant_forged_composite_fails :
    ¬ ∀ (μ : FinPMF (Fin 2)) (γ : ℚ), 0 ≤ γ →
        γ • μ.prob ∈ (GradeFunction.top (Fin 2)).compile →
        γ • μ.prob ∈ twoPointGrade.compile := by
  intro hforall
  have hmem : (1:ℚ) • deltaOne.prob
      ∈ (GradeFunction.top (Fin 2)).compile :=
    (GradeFunction.top (Fin 2)).smul_prob_mem_compile deltaOne
      zero_le_one le_rfl
  have h := hforall deltaOne 1 zero_le_one hmem
  rw [twoPointGrade.mem_compile_smul_iff deltaOne zero_le_one] at h
  rw [twoPointGrade_apply] at h
  norm_num [deltaOne] at h

def stepGrade : GradeFunction (Fin 2) where
  toFun := fun μ => if μ.prob 0 = 1 ∨ μ.prob 0 = 0 then 1 else 1/2
  nonneg := fun μ => by split_ifs <;> norm_num
  le_one := fun μ => by split_ifs <;> norm_num

@[simp] theorem stepGrade_apply (μ : FinPMF (Fin 2)) :
    stepGrade μ = if μ.prob 0 = 1 ∨ μ.prob 0 = 0 then 1 else 1/2 := rfl

theorem stepGrade_not_mulConvex : ¬ MulConvex stepGrade := by
  intro h
  have hc := h deltaZero deltaOne (1/2) (by norm_num) (by norm_num)
  rw [stepGrade_apply, stepGrade_apply, stepGrade_apply] at hc
  norm_num [FinPMF.mix_prob, deltaZero, deltaOne] at hc

theorem stepGrade_compile_not_convex :
    ¬ ∀ v ∈ stepGrade.compile, ∀ w ∈ stepGrade.compile, ∀ s : ℚ,
        0 ≤ s → s ≤ 1 → s • v + (1 - s) • w ∈ stepGrade.compile := by
  intro h
  have hv : (1:ℚ) • deltaZero.prob ∈ stepGrade.compile := by
    refine stepGrade.smul_prob_mem_compile deltaZero zero_le_one ?_
    rw [stepGrade_apply]
    norm_num [deltaZero]
  have hw : (1:ℚ) • deltaOne.prob ∈ stepGrade.compile := by
    refine stepGrade.smul_prob_mem_compile deltaOne zero_le_one ?_
    rw [stepGrade_apply]
    norm_num [deltaOne]
  have hmix := h _ hv _ hw (1/2) (by norm_num) (by norm_num)
  have hvec : ((1:ℚ)/2) • ((1:ℚ) • deltaZero.prob)
      + (1 - (1:ℚ)/2) • ((1:ℚ) • deltaOne.prob)
      = (1:ℚ) • (deltaZero.mix deltaOne (1/2) (by norm_num)
          (by norm_num)).prob := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, FinPMF.mix_prob]
    ring
  rw [hvec] at hmix
  rw [stepGrade.mem_compile_smul_iff _ zero_le_one, stepGrade_apply] at hmix
  norm_num [FinPMF.mix_prob, deltaZero, deltaOne] at hmix

def gapSet : Set (Fin 1 → ℚ) :=
  {v | v = 0 ∨ v = (FinPMF.uniform (Fin 1)).prob}

theorem gapSet_violates_C4 :
    ¬ ∀ v ∈ gapSet, ∀ lam : ℚ, 0 ≤ lam → lam ≤ 1 → lam • v ∈ gapSet := by
  intro h
  have hmem : (FinPMF.uniform (Fin 1)).prob ∈ gapSet := Or.inr rfl
  have h2 := h _ hmem (1/2) (by norm_num) (by norm_num)
  rcases h2 with h2 | h2 <;>
  · have hx := congrFun h2 0
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, FinPMF.uniform,
      Fintype.card_fin] at hx
    norm_num at hx

theorem mutant_c4_gap_uncompilable :
    ¬ ∃ g : GradeFunction (Fin 1), g.compile = gapSet := by
  rintro ⟨g, hg⟩
  have h1 : (1:ℚ) • (FinPMF.uniform (Fin 1)).prob ∈ g.compile := by
    rw [hg, one_smul]
    exact Or.inr rfl
  have hge : (1:ℚ) ≤ g (FinPMF.uniform (Fin 1)) :=
    (g.mem_compile_smul_iff _ zero_le_one).mp h1
  have hhalf : ((1:ℚ)/2) • (FinPMF.uniform (Fin 1)).prob ∈ g.compile :=
    (g.mem_compile_smul_iff _ (by norm_num)).mpr (by linarith)
  rw [hg] at hhalf
  rcases hhalf with h2 | h2 <;>
  · have hx := congrFun h2 0
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, FinPMF.uniform,
      Fintype.card_fin] at hx
    norm_num at hx

end Mutants

#print axioms GradeFunction.mem_compile_smul_iff
#print axioms GradeFunction.compile_injective
#print axioms GradeFunction.compile_convex
#print axioms CredalDenotation.compile_gradeFn
#print axioms CredalDenotation.mulConvex_gradeFn
#print axioms GradeFunction.toCredal
#print axioms CredalDenotation.toCredal_gradeFn
#print axioms GradeFunction.compile_subset_iff
#print axioms GradeFunction.compile_bot
#print axioms GradeFunction.compile_eq_bot_iff
#print axioms GradeFunction.compile_pullback
#print axioms compile_prodGrade_ray
#print axioms prodGrade_marginal_mem
#print axioms gradeOfPenalty_compositePenalty
#print axioms compositePenalty_marginal_mem
#print axioms compositePenalty_marginal_mem_of_antitone
#print axioms twoPointGrade_mulConvex
#print axioms twoPointGrade_compile
#print axioms twoPointGrade_strict_witness
#print axioms prodGrade_marginal_control
#print axioms mutant_forged_composite_fails
#print axioms stepGrade_not_mulConvex
#print axioms stepGrade_compile_not_convex
#print axioms gapSet_violates_C4
#print axioms mutant_c4_gap_uncompilable

end Qtsl.Imprecise
