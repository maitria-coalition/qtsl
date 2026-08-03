import Qtsl.Dyadic

/-!
# Bit-level IEEE 754 refinement of the float model

The set of finite values decoded from IEEE 754 §3.4 bit patterns (with
`we` exponent bits and `wm` trailing-significand bits) is exactly
`(fmtOfBits we wm).Rep`, the value set of the dyadic model
(`finiteVal_iff_rep`) — in particular the standard formats' parameters
become theorems (`fmtOfBits_f64` and kin). Also proves the
order-theoretic §4.3 characterizations of the rounding maps:
`isGreatest_rdn`/`rdn_unique`, `isLeast_rup`/`rup_unique`, and the
round-toward-zero characterization.
-/

namespace PPLC

private theorem exists_grid_mantissa {v : ℚ} (m e g : ℤ) (hveq : v = (m:ℚ) * 2 ^ e)
    (hge : g ≤ e) : ∃ k : ℤ, v = (k:ℚ) * 2 ^ g := by
  refine ⟨m * 2 ^ (e - g).toNat, ?_⟩
  rw [hveq]
  push_cast
  rw [mul_assoc, ← zpow_natCast (2:ℚ) (e - g).toNat,
    Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ e - g),
    ← zpow_add₀ (two_ne_zero : (2:ℚ) ≠ 0)]
  congr 2
  omega

namespace FloatFmt

theorem Rep.abs_le {fmt : FloatFmt} {q : ℚ} (h : fmt.Rep q) : |q| ≤ fmt.maxFin := by
  obtain ⟨x, hx⟩ := h
  simpa [maxFin, hx] using Qtsl.Dyadic.FiniteFloat.abs_toRat_le x

variable (fmt : FloatFmt)

theorem grid_le_rdnRaw {q : ℚ} (k : ℤ)
    (h : (k:ℚ) * 2 ^ fmt.gridExp q ≤ q) :
    (k:ℚ) * 2 ^ fmt.gridExp q ≤ fmt.rdnRaw q := by
  unfold rdnRaw
  rw [Prim.ratFloor_eq]
  have hgpos : (0:ℚ) < 2 ^ fmt.gridExp q := zpow_pos two_pos _
  have hk_le : (k:ℚ) ≤ q / 2 ^ fmt.gridExp q := (le_div_iff₀ hgpos).mpr h
  have hfl : k ≤ ⌊q / 2 ^ fmt.gridExp q⌋ := Int.le_floor.mpr hk_le
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfl) hgpos.le

theorem le_rdn_of_rep_of_le {q v : ℚ} (hq : -fmt.maxFin ≤ q)
    (hv : fmt.Rep v) (hvq : v ≤ q) : v ≤ fmt.rdn q := by
  unfold rdn
  split
  ·
    exact le_trans (le_abs_self v) hv.abs_le
  · split
    · next h2 => exact absurd h2 (not_lt.mpr hq)
    ·
      by_cases hq0 : q = 0
      · subst hq0
        have hz : fmt.rdnRaw 0 = 0 := by
          unfold rdnRaw
          rw [Prim.ratFloor_eq]
          simp
        rw [hz]
        exact hvq
      · obtain ⟨m, e, hveq, hm, he1, he2⟩ := hv.exists_rep
        set g := fmt.gridExp q with hg
        by_cases heg : g ≤ e
        ·
          obtain ⟨k, hvk⟩ := exists_grid_mantissa m e g hveq heg
          rw [hvk]
          exact fmt.grid_le_rdnRaw k (hvk ▸ hvq)
        ·
          have he_lt : e < g := not_le.mp heg
          have hgd : g = max fmt.eMin (Int.log 2 |q| + 1 - fmt.prec) := fmt.gridExp_def q
          have hglog : g = Int.log 2 |q| + 1 - fmt.prec := by
            rcases max_cases fmt.eMin (Int.log 2 |q| + 1 - fmt.prec) with ⟨hcase, _⟩ | ⟨hcase, _⟩
            · exfalso
              have := hgd.trans hcase
              omega
            · exact hgd.trans hcase

          have hv_small : |v| < 2 ^ (g - 1 + fmt.prec) := by
            rw [hveq, abs_mul]
            have h2e : |(2:ℚ) ^ e| = 2 ^ e := abs_of_pos (zpow_pos two_pos e)
            rw [h2e]
            have hmq : |(m:ℚ)| < 2 ^ (fmt.prec : ℤ) := by
              rw [← Int.cast_abs]
              have : ((|m| : ℤ) : ℚ) < ((2 ^ fmt.prec : ℤ) : ℚ) := by exact_mod_cast hm
              simpa [zpow_natCast] using this
            calc |(m:ℚ)| * 2 ^ e < 2 ^ (fmt.prec : ℤ) * 2 ^ e :=
              mul_lt_mul_of_pos_right hmq (zpow_pos two_pos e)
            _ = 2 ^ ((fmt.prec : ℤ) + e) := by
              rw [← zpow_add₀ (two_ne_zero : (2:ℚ) ≠ 0)]
            _ ≤ 2 ^ (g - 1 + fmt.prec) :=
              zpow_le_zpow_right₀ one_le_two (by omega)
          have hq_big : (2:ℚ) ^ (g - 1 + fmt.prec) ≤ |q| := by
            have hlogeq : g - 1 + (fmt.prec : ℤ) = Int.log 2 |q| := by omega
            rw [hlogeq]
            exact Int.zpow_log_le_self one_lt_two (abs_pos.mpr hq0)
          by_cases hqpos : 0 < q
          ·
            have habs_q : |q| = q := abs_of_pos hqpos
            have hc : (((2:ℤ) ^ (fmt.prec - 1) : ℤ) : ℚ) * 2 ^ g
                = 2 ^ (g - 1 + fmt.prec) := by
              have h1 : (((2:ℤ) ^ (fmt.prec - 1) : ℤ) : ℚ)
                  = (2:ℚ) ^ ((fmt.prec - 1 : ℕ) : ℤ) := by
                push_cast
                rw [zpow_natCast]
              rw [h1, ← zpow_add₀ (two_ne_zero : (2:ℚ) ≠ 0)]
              congr 1
              have := fmt.prec_pos
              omega
            have hcq : (((2:ℤ) ^ (fmt.prec - 1) : ℤ) : ℚ) * 2 ^ g ≤ q := by
              rw [hc]
              linarith [hq_big, habs_q.symm.le]
            have hlt : v < fmt.rdnRaw q := by
              calc v ≤ |v| := le_abs_self v
              _ < 2 ^ (g - 1 + fmt.prec) := hv_small
              _ = (((2:ℤ) ^ (fmt.prec - 1) : ℤ) : ℚ) * 2 ^ g := hc.symm
              _ ≤ fmt.rdnRaw q := fmt.grid_le_rdnRaw _ hcq
            exact hlt.le
          ·
            exfalso
            have hqneg : q < 0 := lt_of_le_of_ne (not_lt.mp hqpos) hq0
            have habs_q : |q| = -q := abs_of_neg hqneg
            have h1 : -v ≤ |v| := neg_le_abs v
            linarith [hv_small, hq_big]

theorem isGreatest_rdn {q : ℚ} (hq : -fmt.maxFin ≤ q) :
    IsGreatest {v : ℚ | fmt.Rep v ∧ v ≤ q} (fmt.rdn q) :=
  ⟨⟨fmt.rep_rdn q, fmt.rdn_le hq⟩, fun _ hv => fmt.le_rdn_of_rep_of_le hq hv.1 hv.2⟩

theorem rdn_unique {q r : ℚ} (hq : -fmt.maxFin ≤ q)
    (hr : IsGreatest {v : ℚ | fmt.Rep v ∧ v ≤ q} r) : fmt.rdn q = r :=
  (fmt.isGreatest_rdn hq).unique hr

theorem isLeast_rup {q : ℚ} (hq : q ≤ fmt.maxFin) :
    IsLeast {v : ℚ | fmt.Rep v ∧ q ≤ v} (fmt.rup q) := by
  constructor
  · exact ⟨fmt.rep_rup q, fmt.le_rup hq⟩
  · intro v hv
    have h1 : fmt.Rep (-v) := fmt.rep_neg hv.1
    have h2 : -v ≤ -q := neg_le_neg hv.2
    have h3 : -fmt.maxFin ≤ -q := neg_le_neg hq
    have := fmt.le_rdn_of_rep_of_le h3 h1 h2
    unfold rup
    linarith

theorem rup_unique {q r : ℚ} (hq : q ≤ fmt.maxFin)
    (hr : IsLeast {v : ℚ | fmt.Rep v ∧ q ≤ v} r) : fmt.rup q = r :=
  (fmt.isLeast_rup hq).unique hr

theorem rne_nearest {q : ℚ} (hq : |q| ≤ fmt.maxFin) {v : ℚ} (hv : fmt.Rep v) :
    |fmt.rne q - q| ≤ |v - q| := by
  obtain ⟨hqlo, hqhi⟩ := abs_le.mp hq
  have hdn_le : fmt.rdn q ≤ q := fmt.rdn_le hqlo
  have hup_ge : q ≤ fmt.rup q := fmt.le_rup hqhi
  have habs_dn : |fmt.rdn q - q| = q - fmt.rdn q := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  have habs_up : |fmt.rup q - q| = fmt.rup q - q := abs_of_nonneg (by linarith)
  rcases le_total v q with hc | hc
  ·
    have hb : v ≤ fmt.rdn q := fmt.le_rdn_of_rep_of_le hqlo hv hc
    have habs_v : |v - q| = q - v := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    unfold rne
    split_ifs with h1 h2 h3
    · rw [habs_dn, habs_v]; linarith
    · rw [habs_up, habs_v]
      have := not_lt.mp h1
      linarith
    · rw [habs_dn, habs_v]; linarith
    · rw [habs_up, habs_v]
      have := not_lt.mp h1
      linarith
  ·
    have hb : fmt.rup q ≤ v := (fmt.isLeast_rup hqhi).2 ⟨hv, hc⟩
    have habs_v : |v - q| = v - q := abs_of_nonneg (by linarith)
    unfold rne
    split_ifs with h1 h2 h3
    · rw [habs_dn, habs_v]; linarith
    · rw [habs_up, habs_v]; linarith
    · rw [habs_dn, habs_v]
      have := not_lt.mp h2
      linarith
    · rw [habs_up, habs_v]; linarith

theorem isGreatest_abs_rtz {q : ℚ} (hq : |q| ≤ fmt.maxFin) :
    IsGreatest {v : ℚ | fmt.Rep v ∧ |v| ≤ |q|} |fmt.rtz q| := by
  obtain ⟨hqlo, hqhi⟩ := abs_le.mp hq
  by_cases hqs : 0 ≤ q
  ·
    have hval : fmt.rtz q = fmt.rdn q := by
      unfold rtz
      rw [if_pos hqs]
    have h0 : (0:ℚ) ≤ fmt.rdn q :=
      fmt.le_rdn_of_rep_of_le hqlo fmt.rep_zero hqs
    have hle : fmt.rdn q ≤ q := fmt.rdn_le hqlo
    have habs_q : |q| = q := abs_of_nonneg hqs
    have habs_rtz : |fmt.rtz q| = fmt.rdn q := by
      rw [hval]
      exact abs_of_nonneg h0
    constructor
    · constructor
      · rw [habs_rtz]
        exact fmt.rep_rdn q
      · rw [habs_rtz, abs_of_nonneg h0, habs_q]
        exact hle
    · intro v hv
      rw [habs_rtz]
      have hvq : v ≤ q := le_trans (le_abs_self v) (hv.2.trans habs_q.le)
      exact fmt.le_rdn_of_rep_of_le hqlo hv.1 hvq
  ·

    have hqneg : q < 0 := not_le.mp hqs
    have hval : fmt.rtz q = fmt.rup q := by
      unfold rtz
      rw [if_neg hqs]
    have h0 : fmt.rup q ≤ 0 :=
      (fmt.isLeast_rup hqhi).2 ⟨fmt.rep_zero, hqneg.le⟩
    have hge : q ≤ fmt.rup q := fmt.le_rup hqhi
    have habs_q : |q| = -q := abs_of_neg hqneg
    have habs_rtz : |fmt.rtz q| = -(fmt.rup q) := by
      rw [hval]
      exact abs_of_nonpos h0
    constructor
    · constructor
      · rw [habs_rtz]
        exact fmt.rep_neg (fmt.rep_rup q)
      · rw [habs_rtz, abs_neg, abs_of_nonpos h0, habs_q]
        linarith
    · intro v hv
      rw [habs_rtz]
      have h2 : q ≤ -v := by
        have h3 := le_abs_self v
        have h4 := hv.2
        rw [habs_q] at h4
        linarith
      have h5 : fmt.rup q ≤ -v := (fmt.isLeast_rup hqhi).2 ⟨fmt.rep_neg hv.1, h2⟩
      linarith

end FloatFmt

namespace IEEE

inductive Val where
  | nan : Val
  | inf (sign : Bool) : Val
  | finite (q : ℚ) : Val
  deriving DecidableEq

def bias (we : Nat) : ℤ := 2 ^ (we - 1) - 1

structure Pattern (we wm : Nat) where
  sign : Bool
  biasedExp : BitVec we
  trailing : BitVec wm

namespace Pattern

variable {we wm : Nat}

def sgn (p : Pattern we wm) : ℤ := if p.sign then -1 else 1

def decode (p : Pattern we wm) : Val :=
  if p.biasedExp.toNat = 2 ^ we - 1 then
    if p.trailing.toNat = 0 then .inf p.sign else .nan
  else if p.biasedExp.toNat = 0 then
    .finite ((p.sgn * p.trailing.toNat : ℤ) * (2 : ℚ) ^ (1 - bias we - wm))
  else
    .finite ((p.sgn * (2 ^ wm + p.trailing.toNat) : ℤ)
      * (2 : ℚ) ^ ((p.biasedExp.toNat : ℤ) - bias we - wm))

theorem decode_normal_eq (p : Pattern we wm)
    (h1 : p.biasedExp.toNat ≠ 2 ^ we - 1) (h0 : p.biasedExp.toNat ≠ 0) :
    p.decode = .finite ((if p.sign then (-1 : ℚ) else 1)
      * 2 ^ ((p.biasedExp.toNat : ℤ) - bias we)
      * (1 + (p.trailing.toNat : ℚ) / 2 ^ wm)) := by
  rw [decode, if_neg h1, if_neg h0]
  simp only [Val.finite.injEq]
  have key : ((2 : ℚ)) ^ ((p.biasedExp.toNat : ℤ) - bias we - wm)
      = 2 ^ ((p.biasedExp.toNat : ℤ) - bias we) / 2 ^ wm := by
    rw [zpow_sub₀ (two_ne_zero : (2:ℚ) ≠ 0), zpow_natCast]
  have hne : ((2 : ℚ)) ^ wm ≠ 0 := by positivity
  rw [key, sgn]
  by_cases hs : p.sign <;> simp only [hs, reduceIte] <;>
    push_cast <;> field_simp

theorem decode_subnormal_eq (p : Pattern we wm)
    (h1 : p.biasedExp.toNat ≠ 2 ^ we - 1) (h0 : p.biasedExp.toNat = 0) :
    p.decode = .finite ((if p.sign then (-1 : ℚ) else 1)
      * 2 ^ (1 - bias we)
      * ((p.trailing.toNat : ℚ) / 2 ^ wm)) := by
  rw [decode, if_neg h1, if_pos h0]
  simp only [Val.finite.injEq]
  have key : ((2 : ℚ)) ^ (1 - bias we - wm)
      = 2 ^ (1 - bias we) / 2 ^ wm := by
    rw [zpow_sub₀ (two_ne_zero : (2:ℚ) ≠ 0), zpow_natCast]
  have hne : ((2 : ℚ)) ^ wm ≠ 0 := by positivity
  rw [key, sgn]
  by_cases hs : p.sign <;> simp only [hs, reduceIte] <;>
    push_cast <;> field_simp

end Pattern

def FiniteVal (we wm : Nat) (q : ℚ) : Prop :=
  ∃ p : Pattern we wm, p.decode = .finite q

def fmtOfBits (we wm : Nat) (hwe : 2 ≤ we) : FloatFmt where
  prec := wm + 1
  eMin := 1 - bias we - wm
  eMax := ((2 : ℤ) ^ we - 2) - bias we - wm
  prec_pos := Nat.succ_pos wm
  eMin_le_eMax := by
    have h4 : (4 : ℤ) ≤ 2 ^ we := by
      calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ we := pow_le_pow_right₀ one_le_two hwe
    omega

theorem _root_.PPLC.FloatFmt.ext' {a b : FloatFmt} (h1 : a.prec = b.prec)
    (h2 : a.eMin = b.eMin) (h3 : a.eMax = b.eMax) : a = b := by
  cases a; cases b; simp_all

theorem fmtOfBits_f16 : fmtOfBits 5 10 (by norm_num) = FloatFmt.f16 :=
  FloatFmt.ext' (by rfl) (by simp [fmtOfBits, bias, FloatFmt.f16]) (by simp [fmtOfBits, bias, FloatFmt.f16])

theorem fmtOfBits_bf16 : fmtOfBits 8 7 (by norm_num) = FloatFmt.bf16 :=
  FloatFmt.ext' (by rfl) (by simp [fmtOfBits, bias, FloatFmt.bf16]) (by simp [fmtOfBits, bias, FloatFmt.bf16])

theorem fmtOfBits_f32 : fmtOfBits 8 23 (by norm_num) = FloatFmt.f32 :=
  FloatFmt.ext' (by rfl) (by simp [fmtOfBits, bias, FloatFmt.f32]) (by simp [fmtOfBits, bias, FloatFmt.f32])

theorem fmtOfBits_f64 : fmtOfBits 11 52 (by norm_num) = FloatFmt.f64 :=
  FloatFmt.ext' (by rfl) (by simp [fmtOfBits, bias, FloatFmt.f64]) (by simp [fmtOfBits, bias, FloatFmt.f64])

@[simp] theorem fmtOfBits_prec (we wm : Nat) (hwe : 2 ≤ we) :
    (fmtOfBits we wm hwe).prec = wm + 1 := rfl

@[simp] theorem fmtOfBits_eMin (we wm : Nat) (hwe : 2 ≤ we) :
    (fmtOfBits we wm hwe).eMin = 1 - bias we - wm := rfl

@[simp] theorem fmtOfBits_eMax (we wm : Nat) (hwe : 2 ≤ we) :
    (fmtOfBits we wm hwe).eMax = ((2 : ℤ) ^ we - 2) - bias we - wm := rfl

private theorem sign_mul_abs (m : ℤ) :
    (if decide (m < 0) = true then (-1 : ℤ) else 1) * |m| = m := by
  by_cases h : m < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (not_lt.mp h)]

private theorem abs_sgn (p : Pattern we wm) : |p.sgn| = 1 := by
  unfold Pattern.sgn
  split <;> decide

theorem rep_of_decode {we wm : Nat} (hwe : 2 ≤ we) {p : Pattern we wm} {q : ℚ}
    (h : p.decode = .finite q) : (fmtOfBits we wm hwe).Rep q := by
  have hT : p.trailing.toNat < 2 ^ wm := p.trailing.isLt
  have hE : p.biasedExp.toNat < 2 ^ we := p.biasedExp.isLt
  rw [Pattern.decode] at h
  split at h
  · split at h <;> exact absurd h (by simp)
  · next h1 =>
    split at h
    · next h0 =>

      injection h with hq
      refine hq ▸ FloatFmt.rep_mk _ ?_ (le_refl _) (fmtOfBits we wm hwe).eMin_le_eMax
      rw [abs_mul, abs_sgn, one_mul, fmtOfBits_prec]
      have : |(p.trailing.toNat : ℤ)| = (p.trailing.toNat : ℤ) := abs_of_nonneg (by positivity)
      rw [this]
      calc (p.trailing.toNat : ℤ) < 2 ^ wm := by exact_mod_cast hT
      _ ≤ 2 ^ (wm + 1) := by
          have : (2:ℤ) ^ wm ≤ 2 ^ (wm+1) := pow_le_pow_right₀ one_le_two (by omega)
          omega
    · next h0 =>

      injection h with hq
      have hE2 : p.biasedExp.toNat ≤ 2 ^ we - 2 := by
        have hpos : 1 ≤ 2 ^ we := Nat.one_le_two_pow
        omega
      have hE1 : 1 ≤ p.biasedExp.toNat := Nat.one_le_iff_ne_zero.mpr h0
      refine hq ▸ FloatFmt.rep_mk _ ?_ ?_ ?_
      · rw [abs_mul, abs_sgn, one_mul, fmtOfBits_prec]
        have hnn : (0:ℤ) ≤ 2 ^ wm + p.trailing.toNat := by positivity
        rw [abs_of_nonneg hnn, pow_succ]
        have : (p.trailing.toNat : ℤ) < 2 ^ wm := by exact_mod_cast hT
        omega
      · rw [fmtOfBits_eMin]
        have : (1 : ℤ) ≤ p.biasedExp.toNat := by exact_mod_cast hE1
        omega
      · rw [fmtOfBits_eMax]
        have h2we : ((2 : ℤ)) ^ we = ((2 ^ we : ℕ) : ℤ) := by push_cast; ring
        have hle : ((p.biasedExp.toNat : ℤ)) ≤ ((2 ^ we - 2 : ℕ) : ℤ) := by
          exact_mod_cast hE2
        have hsub : ((2 ^ we - 2 : ℕ) : ℤ) = ((2 ^ we : ℕ) : ℤ) - 2 := by
          have h2 : (2:ℕ) ≤ 2 ^ we := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hwe)
          omega
        omega

theorem finiteVal_of_rep {we wm : Nat} (hwe : 2 ≤ we) {q : ℚ}
    (h : (fmtOfBits we wm hwe).Rep q) : FiniteVal we wm q := by
  set fmt := fmtOfBits we wm hwe with hfmt
  have h2we1 : (3 : ℕ) ≤ 2 ^ we := by
    calc (3:ℕ) ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ we := Nat.pow_le_pow_right (by norm_num) hwe
  by_cases hq0 : q = 0
  ·
    refine ⟨⟨false, BitVec.ofNat we 0, BitVec.ofNat wm 0⟩, ?_⟩
    rw [Pattern.decode]
    have hEz : (BitVec.ofNat we 0).toNat = 0 := by simp [BitVec.toNat_ofNat]
    have hTz : (BitVec.ofNat wm 0).toNat = 0 := by simp [BitVec.toNat_ofNat]
    rw [hEz, hTz, if_neg (by omega), if_pos rfl]
    simp [hq0]
  ·
    obtain ⟨m, e, hq, hm, he1, he2⟩ := h.exists_rep
    set g := fmt.gridExp q with hg
    have hg_min : fmt.eMin ≤ g := fmt.gridExp_ge_eMin q
    have hg_max : g ≤ fmt.eMax :=
      fmt.gridExp_le_eMax hq0 (FloatFmt.Rep.abs_le h)
    have hm0 : m ≠ 0 := by
      intro hz
      exact hq0 (by simpa [hz] using hq)

    have he_ge : g ≤ e := by
      by_cases h' : g ≤ e
      · exact h'
      · exfalso
        have h'' : e < g := not_le.mp h'
        have hgd : g = max fmt.eMin (Int.log 2 |q| + 1 - fmt.prec) := fmt.gridExp_def q
        rcases max_cases fmt.eMin (Int.log 2 |q| + 1 - fmt.prec) with ⟨hcase, _⟩ | ⟨hcase, _⟩
        ·
          have hge : g = fmt.eMin := hgd.trans hcase
          omega
        ·
          have hge : g = Int.log 2 |q| + 1 - fmt.prec := hgd.trans hcase
          have habs' : |q| < 2 ^ (e + fmt.prec) := by
            rw [hq, abs_mul]
            have h2e : |(2:ℚ) ^ e| = 2 ^ e := abs_of_pos (zpow_pos two_pos e)
            rw [h2e, zpow_add₀ (two_ne_zero : (2:ℚ) ≠ 0)]
            have hmq : |(m:ℚ)| < 2 ^ (fmt.prec : ℤ) := by
              rw [← Int.cast_abs]
              have : ((|m| : ℤ) : ℚ) < ((2 ^ fmt.prec : ℤ) : ℚ) := by exact_mod_cast hm
              simpa [zpow_natCast] using this
            have h2epos := zpow_pos (two_pos (α := ℚ)) e
            calc |(m:ℚ)| * 2 ^ e < 2 ^ (fmt.prec : ℤ) * 2 ^ e := by nlinarith
            _ = 2 ^ e * 2 ^ (fmt.prec : ℤ) := by ring
          have hlog_le : (2:ℚ) ^ (Int.log 2 |q|) ≤ |q| :=
            Int.zpow_log_le_self one_lt_two (abs_pos.mpr hq0)
          have hloglt : Int.log 2 |q| < e + fmt.prec := by
            by_contra hc
            have : (2:ℚ) ^ (e + (fmt.prec:ℤ)) ≤ 2 ^ (Int.log 2 |q|) :=
              zpow_le_zpow_right₀ one_le_two (not_lt.mp hc)
            linarith
          omega

    obtain ⟨k, hkq⟩ := exists_grid_mantissa m e g hq he_ge
    have h2g_abs : |(2:ℚ) ^ g| = 2 ^ g := abs_of_pos (zpow_pos two_pos g)
    have habs2 : |q| = ((|k| : ℤ) : ℚ) * 2 ^ g := by
      rw [hkq, abs_mul, h2g_abs, Int.cast_abs]
    have hk_lt : |k| < 2 ^ fmt.prec := by
      have habs : |q| < 2 ^ (g + fmt.prec) := fmt.abs_lt_zpow_gridExp_add q hq0
      rw [habs2, zpow_add₀ (two_ne_zero : (2:ℚ) ≠ 0)] at habs
      have hgpos := zpow_pos (two_pos (α := ℚ)) g
      have hlt : ((|k| : ℤ) : ℚ) < 2 ^ (fmt.prec : ℤ) := by nlinarith
      rw [zpow_natCast] at hlt
      exact_mod_cast hlt
    have hk0 : k ≠ 0 := by
      intro hz
      exact hq0 (by simpa [hz] using hkq)

    have hEbounds : ∀ E : ℤ, 1 ≤ E → E ≤ 2 ^ we - 2 →
        (BitVec.ofNat we E.toNat).toNat = E.toNat ∧ E.toNat ≠ 2 ^ we - 1 ∧ E.toNat ≠ 0 := by
      intro E hE1 hE2
      have h2 : ((2:ℤ) ^ we) = ((2 ^ we : ℕ) : ℤ) := by push_cast; ring
      have hE2' : E.toNat ≤ 2 ^ we - 2 := by omega
      have hlt : E.toNat < 2 ^ we := by omega
      exact ⟨by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt], by omega, by omega⟩
    by_cases hnorm : 2 ^ wm ≤ |k|
    ·
      set E : ℤ := g + bias we + wm with hE
      have hE1 : 1 ≤ E := by
        have := hg_min
        rw [hfmt, fmtOfBits_eMin] at this
        omega
      have hE2 : E ≤ 2 ^ we - 2 := by
        have := hg_max
        rw [hfmt, fmtOfBits_eMax] at this
        omega
      obtain ⟨hEt, hEne1, hEne0⟩ := hEbounds E hE1 hE2
      have hT_lt : |k| - 2 ^ wm < 2 ^ wm := by
        have : (2:ℤ) ^ (wm + 1) = 2 ^ wm * 2 := pow_succ 2 wm
        rw [hfmt, fmtOfBits_prec] at hk_lt
        omega
      have hT_nn : (0:ℤ) ≤ |k| - 2 ^ wm := by omega
      have hTcast : (((|k| - 2 ^ wm).toNat : ℤ)) = |k| - 2 ^ wm :=
        Int.toNat_of_nonneg hT_nn
      refine ⟨⟨decide (k < 0), BitVec.ofNat we E.toNat, BitVec.ofNat wm (|k| - 2 ^ wm).toNat⟩, ?_⟩
      rw [Pattern.decode]
      simp only [hEt]
      rw [if_neg hEne1, if_neg hEne0]
      have hTt : (BitVec.ofNat wm (|k| - 2 ^ wm).toNat).toNat = (|k| - 2 ^ wm).toNat := by
        have hb : (((2:ℕ) ^ wm : ℕ) : ℤ) = (2:ℤ) ^ wm := by push_cast; ring
        have : (|k| - 2 ^ wm).toNat < 2 ^ wm := by omega
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]
      rw [hTt]
      congr 1
      rw [hkq]
      have hsgn : (Pattern.sgn ⟨decide (k < 0), BitVec.ofNat we E.toNat,
          BitVec.ofNat wm (|k| - 2 ^ wm).toNat⟩) = if decide (k < 0) = true then -1 else 1 := rfl
      have hint : ((if decide (k < 0) = true then (-1:ℤ) else 1))
          * ((2:ℤ) ^ wm + ((|k| - 2 ^ wm).toNat : ℤ)) = k := by
        have hmant : ((2:ℤ) ^ wm + ((|k| - 2 ^ wm).toNat : ℤ)) = |k| := by omega
        rw [hmant]
        exact sign_mul_abs k
      have hEcast : ((E.toNat : ℤ)) = E := Int.toNat_of_nonneg (by omega)
      have hexp : ((E.toNat : ℤ)) - bias we - wm = g := by
        rw [hEcast]
        omega
      rw [hsgn, hexp, hint]
    ·
      have hnorm' : |k| < 2 ^ wm := not_le.mp hnorm
      have hgeMin : g = fmt.eMin := by
        have hgd : g = max fmt.eMin (Int.log 2 |q| + 1 - fmt.prec) := fmt.gridExp_def q
        rcases max_cases fmt.eMin (Int.log 2 |q| + 1 - fmt.prec) with ⟨hcase, _⟩ | ⟨hcase, _⟩
        · exact hgd.trans hcase
        ·
          exfalso
          have hge : g = Int.log 2 |q| + 1 - fmt.prec := hgd.trans hcase
          have hlog_le : (2:ℚ) ^ (Int.log 2 |q|) ≤ |q| :=
            Int.zpow_log_le_self one_lt_two (abs_pos.mpr hq0)
          have hlogval : Int.log 2 |q| = g + fmt.prec - 1 := by omega
          rw [hlogval, habs2] at hlog_le
          have hsplit : (2:ℚ) ^ (g + (fmt.prec:ℤ) - 1) = 2 ^ ((fmt.prec:ℤ) - 1) * 2 ^ g := by
            rw [← zpow_add₀ (two_ne_zero : (2:ℚ) ≠ 0)]
            congr 1
            ring
          have hkbig : (2:ℚ) ^ ((fmt.prec:ℤ) - 1) ≤ ((|k| : ℤ) : ℚ) := by
            rw [hsplit] at hlog_le
            have hgpos := zpow_pos (two_pos (α := ℚ)) g
            nlinarith
          have hwm : ((fmt.prec:ℤ) - 1) = (wm : ℤ) := by
            rw [hfmt, fmtOfBits_prec]
            push_cast
            ring
          rw [hwm, zpow_natCast] at hkbig
          have : (2:ℤ) ^ wm ≤ |k| := by exact_mod_cast hkbig
          omega
      have hTn_lt : |k|.toNat < 2 ^ wm := by
        have hb : (((2:ℕ) ^ wm : ℕ) : ℤ) = (2:ℤ) ^ wm := by push_cast; ring
        have hk_nn : (0:ℤ) ≤ |k| := abs_nonneg k
        omega
      refine ⟨⟨decide (k < 0), BitVec.ofNat we 0, BitVec.ofNat wm |k|.toNat⟩, ?_⟩
      rw [Pattern.decode]
      have hEz : (BitVec.ofNat we 0).toNat = 0 := by simp [BitVec.toNat_ofNat]
      have hTt : (BitVec.ofNat wm |k|.toNat).toNat = |k|.toNat := by
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hTn_lt]
      rw [hEz, if_neg (by omega), if_pos rfl, hTt]
      congr 1
      rw [hkq]
      have hsgn : (Pattern.sgn ⟨decide (k < 0), BitVec.ofNat we 0,
          BitVec.ofNat wm |k|.toNat⟩) = if decide (k < 0) = true then -1 else 1 := rfl
      have hint : ((if decide (k < 0) = true then (-1:ℤ) else 1)) * ((|k|.toNat : ℤ)) = k := by
        rw [Int.toNat_of_nonneg (abs_nonneg k)]
        exact sign_mul_abs k
      have hexp : (1 : ℤ) - bias we - wm = g := by
        rw [hgeMin, hfmt, fmtOfBits_eMin]
      rw [hsgn, hexp, hint]

theorem finiteVal_iff_rep (we wm : Nat) (hwe : 2 ≤ we) (q : ℚ) :
    FiniteVal we wm q ↔ (fmtOfBits we wm hwe).Rep q :=
  ⟨fun ⟨_, hp⟩ => rep_of_decode hwe hp, finiteVal_of_rep hwe⟩

theorem finiteVal_iff_rep_f64 (q : ℚ) : FiniteVal 11 52 q ↔ FloatFmt.f64.Rep q := by
  rw [finiteVal_iff_rep 11 52 (by norm_num), fmtOfBits_f64]

theorem finiteVal_iff_rep_f32 (q : ℚ) : FiniteVal 8 23 q ↔ FloatFmt.f32.Rep q := by
  rw [finiteVal_iff_rep 8 23 (by norm_num), fmtOfBits_f32]

theorem finiteVal_iff_rep_f16 (q : ℚ) : FiniteVal 5 10 q ↔ FloatFmt.f16.Rep q := by
  rw [finiteVal_iff_rep 5 10 (by norm_num), fmtOfBits_f16]

theorem finiteVal_iff_rep_bf16 (q : ℚ) : FiniteVal 8 7 q ↔ FloatFmt.bf16.Rep q := by
  rw [finiteVal_iff_rep 8 7 (by norm_num), fmtOfBits_bf16]

end IEEE

end PPLC
