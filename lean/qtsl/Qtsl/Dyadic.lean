import Qtsl.Core.Dyadic
import Qtsl.CoreBridge
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Int.Log
import QtslAux.Dyadic

/-!
# Dyadic-rational float model: theorems

The theorems about the float model whose definitions live in
`Qtsl.Core.Dyadic`: representability of the rounding maps'
outputs (`rep_*`), directedness (`rdn_le`, `le_rup`), grid-exponent
bounds, and compile-time receipts checking the four standard binary
formats against their IEEE parameters.
-/

namespace PPLC

namespace FloatFmt

variable (fmt : FloatFmt)

theorem rep_mk {m e : ℤ} (hm : |m| < 2 ^ fmt.prec) (he1 : fmt.eMin ≤ e)
    (he2 : e ≤ fmt.eMax) : fmt.Rep ((m : ℚ) * 2 ^ e) := by
  refine ⟨⟨m, e, ?_, he1, he2⟩, rfl⟩
  have h : (m.natAbs : ℤ) < (2 : ℤ) ^ fmt.prec := by rwa [Int.natCast_natAbs]
  exact_mod_cast h

theorem Rep.exists_rep {fmt : FloatFmt} {q : ℚ} (h : fmt.Rep q) :
    ∃ m e : ℤ, q = (m : ℚ) * 2 ^ e ∧ |m| < 2 ^ fmt.prec ∧ fmt.eMin ≤ e ∧ e ≤ fmt.eMax := by
  obtain ⟨x, hx⟩ := h
  refine ⟨x.m, x.e, by rw [← hx]; exact x.toRat_def, ?_, x.exp_lb, x.exp_ub⟩
  have h2 : (x.m.natAbs : ℤ) < (2 : ℤ) ^ fmt.prec := by exact_mod_cast x.mantissa_bound
  rwa [Int.natCast_natAbs] at h2

theorem Rep.isDyadic {fmt : FloatFmt} {q : ℚ} (h : fmt.Rep q) :
    Qtsl.IsDyadic q := by
  obtain ⟨x, hx⟩ := h
  exact hx ▸ x.toRat_isDyadic

theorem maxFin_pos : 0 < fmt.maxFin := by
  have h1 : (1 : ℚ) < 2 ^ fmt.prec := by
    calc (1:ℚ) < 2 := one_lt_two
    _ = 2 ^ (1:ℕ) := (pow_one 2).symm
    _ ≤ 2 ^ fmt.prec := pow_le_pow_right₀ one_le_two fmt.prec_pos
  exact mul_pos (by linarith) (zpow_pos two_pos _)

theorem rep_zero : fmt.Rep 0 := by
  have h : (0 : ℚ) = ((0 : ℤ) : ℚ) * 2 ^ fmt.eMin := by norm_num
  rw [h]
  exact fmt.rep_mk (by positivity) (le_refl _) fmt.eMin_le_eMax

theorem rep_neg {q : ℚ} (h : fmt.Rep q) : fmt.Rep (-q) := by
  obtain ⟨x, hx⟩ := h
  refine ⟨⟨-x.m, x.e, by simpa using x.mantissa_bound, x.exp_lb, x.exp_ub⟩, ?_⟩
  rw [← hx]
  simp only [Qtsl.Dyadic.FiniteFloat.toRat_def]
  push_cast
  ring

theorem rep_maxFin : fmt.Rep fmt.maxFin := by
  have h : fmt.maxFin = (((2 : ℤ) ^ fmt.prec - 1 : ℤ) : ℚ) * 2 ^ fmt.eMax := by
    unfold maxFin; push_cast; ring
  rw [h]
  have h1 : (1 : ℤ) ≤ 2 ^ fmt.prec := one_le_pow₀ one_le_two
  exact fmt.rep_mk (by rw [abs_of_nonneg (by omega)]; omega) fmt.eMin_le_eMax (le_refl _)

theorem rep_mk' {m e : ℤ} (hm : |m| ≤ 2 ^ fmt.prec) (he1 : fmt.eMin ≤ e)
    (he2 : e ≤ fmt.eMax) (hedge : |m| = 2 ^ fmt.prec → e < fmt.eMax) :
    fmt.Rep ((m : ℚ) * 2 ^ e) := by
  rcases lt_or_eq_of_le hm with hlt | heq
  · exact fmt.rep_mk hlt he1 he2
  ·
    have hpow : (2 : ℤ) ^ fmt.prec = 2 ^ (fmt.prec - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      have := fmt.prec_pos
      omega
    have habs : |(2 : ℤ) ^ (fmt.prec - 1)| < 2 ^ fmt.prec := by
      have hp : (0:ℤ) < 2 ^ (fmt.prec - 1) := by positivity
      rw [abs_of_nonneg hp.le]
      omega
    have heMax : e + 1 ≤ fmt.eMax := by have := hedge heq; omega
    have heMin : fmt.eMin ≤ e + 1 := by omega
    rcases abs_eq (by positivity : (0:ℤ) ≤ 2 ^ fmt.prec) |>.mp heq with h | h
    · have hv : (m : ℚ) * 2 ^ e = (((2:ℤ) ^ (fmt.prec - 1) : ℤ) : ℚ) * 2 ^ (e + 1) := by
        rw [h, hpow]
        push_cast
        rw [zpow_add₀ (two_ne_zero : (2:ℚ) ≠ 0) e 1]
        ring
      rw [hv]
      exact fmt.rep_mk habs heMin heMax
    · have hv : (m : ℚ) * 2 ^ e = ((-((2:ℤ) ^ (fmt.prec - 1)) : ℤ) : ℚ) * 2 ^ (e + 1) := by
        rw [h, hpow]
        push_cast
        rw [zpow_add₀ (two_ne_zero : (2:ℚ) ≠ 0) e 1]
        ring
      rw [hv]
      exact fmt.rep_mk (by simpa using habs) heMin heMax

theorem gridExp_def (q : ℚ) :
    fmt.gridExp q = max fmt.eMin (Int.log 2 |q| + 1 - fmt.prec) := by
  unfold gridExp
  rw [Prim.intLog2_eq, Prim.ratAbs_eq]

theorem gridExp_ge_eMin (q : ℚ) : fmt.eMin ≤ fmt.gridExp q := by
  rw [gridExp_def]; exact le_max_left _ _

theorem abs_lt_zpow_gridExp_add (q : ℚ) (hq : q ≠ 0) :
    |q| < 2 ^ (fmt.gridExp q + fmt.prec) := by
  have h0 : (0 : ℚ) < |q| := abs_pos.mpr hq
  have hlog : |q| < (2 : ℚ) ^ (Int.log 2 |q| + 1) := Int.lt_zpow_succ_log_self one_lt_two _
  have hexp : Int.log 2 |q| + 1 ≤ fmt.gridExp q + fmt.prec := by
    have h := le_max_right fmt.eMin (Int.log 2 |q| + 1 - fmt.prec)
    rw [gridExp_def]
    omega
  calc |q| < (2 : ℚ) ^ (Int.log 2 |q| + 1) := hlog
  _ ≤ 2 ^ (fmt.gridExp q + fmt.prec) := zpow_le_zpow_right₀ one_le_two hexp

theorem gridExp_le_eMax {q : ℚ} (hq : q ≠ 0) (h : |q| ≤ fmt.maxFin) :
    fmt.gridExp q ≤ fmt.eMax := by
  have h0 : (0 : ℚ) < |q| := abs_pos.mpr hq
  have hlt : |q| < (2 : ℚ) ^ (fmt.eMax + fmt.prec) := by
    have : fmt.maxFin < (2 : ℚ) ^ (fmt.eMax + fmt.prec) := by
      rw [zpow_add₀ (two_ne_zero), maxFin]
      have hpow : ((2:ℚ) ^ fmt.prec : ℚ) = (2:ℚ) ^ (fmt.prec : ℤ) := (zpow_natCast 2 fmt.prec).symm
      rw [mul_comm ((2:ℚ) ^ fmt.eMax) _, ← hpow]
      exact mul_lt_mul_of_pos_right (by linarith) (zpow_pos two_pos _)
    linarith
  have hlog : Int.log 2 |q| < fmt.eMax + fmt.prec := by
    by_contra hcon
    have hcon' : fmt.eMax + fmt.prec ≤ Int.log 2 |q| := not_lt.mp hcon
    have : (2 : ℚ) ^ (fmt.eMax + fmt.prec) ≤ |q| :=
      le_trans (zpow_le_zpow_right₀ one_le_two hcon') (Int.zpow_log_le_self one_lt_two h0)
    linarith
  rw [gridExp_def]
  simp only [max_le_iff]
  exact ⟨fmt.eMin_le_eMax, by omega⟩

theorem rep_rdnRaw {q : ℚ} (h_lo : -fmt.maxFin ≤ q) (h_hi : q < fmt.maxFin) :
    fmt.Rep (fmt.rdnRaw q) := by
  by_cases hq0 : q = 0
  · subst hq0
    simpa [rdnRaw, Prim.ratFloor_eq] using fmt.rep_zero
  · unfold rdnRaw
    rw [Prim.ratFloor_eq]
    set e := fmt.gridExp q with he_def
    set m := ⌊q / 2 ^ e⌋ with hm_def
    have he2pos : (0 : ℚ) < 2 ^ e := zpow_pos two_pos _
    have habs_q : |q| ≤ fmt.maxFin := abs_le.mpr ⟨h_lo, le_of_lt h_hi⟩
    have he_max : e ≤ fmt.eMax := fmt.gridExp_le_eMax hq0 habs_q
    have he_min : fmt.eMin ≤ e := fmt.gridExp_ge_eMin q

    have habs : |q / 2 ^ e| < (2 : ℚ) ^ (fmt.prec : ℤ) := by
      rw [abs_div, abs_of_pos he2pos, div_lt_iff₀ he2pos]
      have := fmt.abs_lt_zpow_gridExp_add q hq0
      rwa [zpow_add₀ (two_ne_zero) e (fmt.prec : ℤ), mul_comm ((2:ℚ) ^ e) _] at this
    have hq_ub : q / 2 ^ e < (2 : ℚ) ^ (fmt.prec : ℤ) := (abs_lt.mp habs).2
    have hq_lb : -((2 : ℚ) ^ (fmt.prec : ℤ)) < q / 2 ^ e := (abs_lt.mp habs).1

    have hm_ub : m < 2 ^ fmt.prec := by
      have h1 : (m : ℚ) ≤ q / 2 ^ e := Int.floor_le _
      have hlt : (m : ℚ) < (2 : ℚ) ^ (fmt.prec : ℤ) := lt_of_le_of_lt h1 hq_ub
      rw [zpow_natCast] at hlt
      exact_mod_cast hlt
    have hm_lb : -(2 ^ fmt.prec) ≤ m := by
      apply Int.le_floor.mpr
      push_cast
      rw [← zpow_natCast (2:ℚ) fmt.prec]
      linarith
    have hm_abs : |m| ≤ 2 ^ fmt.prec := abs_le.mpr ⟨hm_lb, le_of_lt hm_ub⟩

    refine fmt.rep_mk' hm_abs he_min he_max (fun hedge => ?_)
    have hm_eq : m = -(2 ^ fmt.prec) := by
      rcases abs_eq (by positivity : (0:ℤ) ≤ 2 ^ fmt.prec) |>.mp hedge with h | h
      · exact absurd (h ▸ hm_ub) (lt_irrefl _)
      · exact h
    rcases lt_or_eq_of_le he_max with h | h
    · exact h
    · exfalso

      have hfloor : q / 2 ^ e < (m : ℚ) + 1 := Int.lt_floor_add_one _
      have hql : q < ((m : ℚ) + 1) * 2 ^ e := by
        rwa [div_lt_iff₀ he2pos] at hfloor
      have : ((m : ℚ) + 1) * 2 ^ e = -fmt.maxFin := by
        rw [hm_eq, h, maxFin]
        push_cast
        ring
      rw [this] at hql
      linarith

theorem rep_rdn (q : ℚ) : fmt.Rep (fmt.rdn q) := by
  unfold rdn
  split
  · exact fmt.rep_maxFin
  · split
    · exact fmt.rep_neg fmt.rep_maxFin
    · next h1 h2 => exact fmt.rep_rdnRaw (not_lt.mp h2) (not_le.mp h1)

theorem rep_rup (q : ℚ) : fmt.Rep (fmt.rup q) := fmt.rep_neg (fmt.rep_rdn (-q))

theorem rep_rtz (q : ℚ) : fmt.Rep (fmt.rtz q) := by
  unfold rtz; split
  · exact fmt.rep_rdn q
  · exact fmt.rep_rup q

theorem rep_rne (q : ℚ) : fmt.Rep (fmt.rne q) := by
  unfold rne
  split
  · exact fmt.rep_rdn q
  · split
    · exact fmt.rep_rup q
    · split
      · exact fmt.rep_rdn q
      · exact fmt.rep_rup q

theorem rdn_le {q : ℚ} (h : -fmt.maxFin ≤ q) : fmt.rdn q ≤ q := by
  unfold rdn
  split
  · assumption
  · split
    · next h2 => exact absurd h2 (not_lt.mpr h)
    · unfold rdnRaw
      rw [Prim.ratFloor_eq]
      have he2pos : (0 : ℚ) < 2 ^ fmt.gridExp q := zpow_pos two_pos _
      calc (⌊q / 2 ^ fmt.gridExp q⌋ : ℚ) * 2 ^ fmt.gridExp q
          ≤ (q / 2 ^ fmt.gridExp q) * 2 ^ fmt.gridExp q :=
            mul_le_mul_of_nonneg_right (Int.floor_le _) (le_of_lt he2pos)
        _ = q := div_mul_cancel₀ q (ne_of_gt he2pos)

theorem le_rup {q : ℚ} (h : q ≤ fmt.maxFin) : q ≤ fmt.rup q := by
  have := fmt.rdn_le (q := -q) (by linarith)
  unfold rup
  linarith

#guard FloatFmt.f64.rdn (1/3) = 6004799503160661 / 2 ^ 54
#guard FloatFmt.f64.rup (1/3) = 6004799503160662 / 2 ^ 54
#guard FloatFmt.f64.rdn (1/10) = 7205759403792793 / 2 ^ 56
#guard FloatFmt.f64.rne (1/10) = 7205759403792794 / 2 ^ 56
#guard FloatFmt.f64.rdn ((2:ℚ) ^ (-1075 : ℤ)) = 0
#guard FloatFmt.f64.rup ((2:ℚ) ^ (-1075 : ℤ)) = (2:ℚ) ^ (-1074 : ℤ)
#guard FloatFmt.f64.rdn (2 ^ 2000) = FloatFmt.f64.maxFin
#guard FloatFmt.f64.rup (-(2 ^ 2000)) = -FloatFmt.f64.maxFin
#guard FloatFmt.f64.rdn (3/4) = 3/4
#guard FloatFmt.f64.rne (3/4) = 3/4

#guard (⟨3, -4, 4, by decide, by decide⟩ : FloatFmt).rne (9/4) = 2
#guard (⟨3, -4, 4, by decide, by decide⟩ : FloatFmt).rne (11/4) = 3

end FloatFmt

end PPLC
