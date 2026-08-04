import SuFunctor.Adequacy.DtmcTemplate

/-! # Product-profile templates collapse to finitely many inequalities

The d-dimensional face of the template collapse (`DtmcTemplate` is the
1-D geometric face): the checker-side warrant for contraction
certificates on the uniform-axis ±1 walk family over `Fin d → ℕ` with
monus at zero and absorption exactly at the origin.  Outside a finite
stored-row window the weight function is presented as a PRODUCT
PROFILE `V x = ∏ i, u (x i)`: one per-coordinate profile `u` with
`u 0 = 1`, a finite ramp of ratios `g`, then a constant geometric
ratio `ρ`.

Three obligations discharge the transfer inequality at every
window-exterior state at once — the statements a pattern-face checker
recomputes finitely:

(i) **per-coordinate factorization** (`aliveStep_factor`): where no
    single down-move reaches the origin, the alive one-step transfer
    of `V` factorizes as `(∑ i, r (x i)) / d · V x`, with `r v` the
    per-coordinate transfer ratio
    `p·u(v+1)/u(v) + (1−p)·u(v−1)/u(v)` — `ℕ`-monus in the index, so
    the `v = 0` case IS the walk's monus bounce:
    `r 0 = p·u 1 + (1−p)` (`transferRatio_zero`).  The move-indexed
    sum equals the destination-merged kernel sum (regrouping a finite
    weighted sum by destination), and equals the alive-restricted
    transfer because, under the hypothesis, no move is absorbed.

(ii) **profile stabilization** (`transferRatio_of_ge`): past the ramp
    (`v ≥ g.length + 1`) the ratio is the constant
    `rInf = p·ρ + (1−p)/ρ`.

(iii) **class bound** (`productProfile_collapse`): the finitely many
    class inequalities `(d−k)·rMax + k·rInf ≤ d·c` (`k = 1..d`) imply
    the per-state contraction `aliveStep x ≤ c · V x` at every state
    owning a geometric-regime coordinate (`x j ≥ g.length + 1`, with
    `x j ≥ 2` keeping absorption out of reach).  Since `rInf ≤ rMax`
    by construction, the `k = 1` class is the binding one and implies
    the rest; a checker verifying all `d` classes loses nothing.

`productProfile_collapse_window` restates the composition in window
vocabulary: every state outside a stored-row window of radius
`box + 1` (some coordinate `≥ box + 2`) contracts, PROVIDED
`g.length ≤ box + 1`.  That proviso is load-bearing, not decorative:
without it a window-exterior state can sit entirely on the ramp,
where no class inequality constrains the ratio sum — any checker
admitting this collapse must enforce `profile length ≤ box + 1`
alongside window coverage at radius `box + 1`.
`rampProfile_needs_window_reach` witnesses the necessity on a
concrete admissible ramp profile: all class inequalities hold, yet an
all-ramp state's ratio sum exceeds `d·c`.

The `d = 1` relationship: `genFormTemplate_collapse` is the `d = 1`
face of (iii) under a pure-geometric profile (`g = []`, offset family
`±1`), where the single class inequality reads `rInf ≤ c`; it is not
re-proved here.

Only the checker-to-instance direction is a soundness obligation, as
in the 1-D face.  The weights `p, 1−p` carry no probability
hypothesis and the profile needs only positivity: the collapse is
pure exact-rational algebra, and the stochastic reading (with its
`0 < p < 1` demand) and the `κ = 1/min V` floor (with its unit-floor
`1 ≤` demands on ratios and growth) belong to the certificate's other
faces. -/

namespace SuFunctor
namespace Adequacy

open Finset

/-! ## The per-coordinate profile -/

/-- The ratio applied at index `v`: the ramp entry while
`v < g.length`, the geometric rate `ρ` beyond. -/
def stepRatio (g : List ℚ) (ρ : ℚ) (v : ℕ) : ℚ :=
  if h : v < g.length then g[v] else ρ

theorem stepRatio_of_ge (g : List ℚ) (ρ : ℚ) {v : ℕ}
    (h : g.length ≤ v) : stepRatio g ρ v = ρ :=
  dif_neg (by omega)

theorem stepRatio_pos {g : List ℚ} {ρ : ℚ} (hg : ∀ q ∈ g, 0 < q)
    (hρ : 0 < ρ) (v : ℕ) : 0 < stepRatio g ρ v := by
  unfold stepRatio
  by_cases h : v < g.length
  · rw [dif_pos h]
    exact hg _ (List.getElem_mem h)
  · rw [dif_neg h]
    exact hρ

/-- The per-coordinate profile: `u 0 = 1`,
`u (v+1) = u v · stepRatio v` — the ramp entries while they last,
then the geometric rate. -/
def profileU (g : List ℚ) (ρ : ℚ) : ℕ → ℚ
  | 0 => 1
  | v + 1 => profileU g ρ v * stepRatio g ρ v

@[simp] theorem profileU_zero (g : List ℚ) (ρ : ℚ) :
    profileU g ρ 0 = 1 := rfl

theorem profileU_succ (g : List ℚ) (ρ : ℚ) (v : ℕ) :
    profileU g ρ (v + 1) = profileU g ρ v * stepRatio g ρ v := rfl

theorem profileU_pos {g : List ℚ} {ρ : ℚ} (hg : ∀ q ∈ g, 0 < q)
    (hρ : 0 < ρ) : ∀ v, 0 < profileU g ρ v
  | 0 => one_pos
  | v + 1 => by
    rw [profileU_succ]
    exact mul_pos (profileU_pos hg hρ v) (stepRatio_pos hg hρ v)

/-! ## The product weight and the walk's moves -/

/-- The product-profile weight: `V x = ∏ i, u (x i)`. -/
def prodProfileV (g : List ℚ) (ρ : ℚ) {d : ℕ} (x : Fin d → ℕ) : ℚ :=
  ∏ i, profileU g ρ (x i)

theorem prodProfileV_pos {g : List ℚ} {ρ : ℚ} (hg : ∀ q ∈ g, 0 < q)
    (hρ : 0 < ρ) {d : ℕ} (x : Fin d → ℕ) :
    0 < prodProfileV g ρ x :=
  Finset.prod_pos fun i _ => profileU_pos hg hρ (x i)

/-- Coordinate `i` moves up by one. -/
def upMove {d : ℕ} (x : Fin d → ℕ) (i : Fin d) : Fin d → ℕ :=
  Function.update x i (x i + 1)

/-- Coordinate `i` moves down by one, with monus at zero: at
`x i = 0` the state is unchanged (`ℕ`-subtraction saturates). -/
def downMove {d : ℕ} (x : Fin d → ℕ) (i : Fin d) : Fin d → ℕ :=
  Function.update x i (x i - 1)

/-- A single-coordinate update scales the product weight by the
profile ratio at that coordinate, in denominator-free form. -/
theorem prodProfileV_update_mul (g : List ℚ) (ρ : ℚ) {d : ℕ}
    (x : Fin d → ℕ) (i : Fin d) (w : ℕ) :
    prodProfileV g ρ (Function.update x i w) * profileU g ρ (x i)
      = prodProfileV g ρ x * profileU g ρ w := by
  unfold prodProfileV
  have hL : (∏ j, profileU g ρ (Function.update x i w j))
      = profileU g ρ w
          * ∏ j ∈ Finset.univ.erase i, profileU g ρ (x j) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => profileU g ρ (Function.update x i w j))
      (Finset.mem_univ i)]
    simp only [Function.update_self]
    exact congrArg (profileU g ρ w * ·)
      (Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  have hR : (∏ j, profileU g ρ (x j))
      = profileU g ρ (x i)
          * ∏ j ∈ Finset.univ.erase i, profileU g ρ (x j) :=
    (Finset.mul_prod_erase Finset.univ
      (fun j => profileU g ρ (x j)) (Finset.mem_univ i)).symm
  rw [hL, hR]
  ring

/-! ## The transfer ratio -/

/-- The per-coordinate transfer ratio
`r v = p·u(v+1)/u(v) + (1−p)·u(v−1)/u(v)`, with `ℕ`-monus in the
index: the down-ratio at `v = 0` is `u 0 / u 0`, exactly the walk's
monus bounce staying in place. -/
def transferRatio (g : List ℚ) (ρ p : ℚ) (v : ℕ) : ℚ :=
  p * profileU g ρ (v + 1) / profileU g ρ v
    + (1 - p) * profileU g ρ (v - 1) / profileU g ρ v

/-- The `v = 0` special form a checker states separately —
`r 0 = p·u 1/u 0 + (1−p)` — is the index-monus definition evaluated,
since `u 0 = 1`. -/
theorem transferRatio_zero (g : List ℚ) (ρ p : ℚ) :
    transferRatio g ρ p 0 = p * profileU g ρ 1 + (1 - p) := by
  unfold transferRatio
  norm_num

/-- The geometric-regime transfer ratio. -/
def rInf (ρ p : ℚ) : ℚ := p * ρ + (1 - p) / ρ

/-- **(ii) Profile stabilization**: past the ramp — both ratios in
the geometric regime, `v ≥ g.length + 1` — the transfer ratio is the
constant `rInf`. -/
theorem transferRatio_of_ge {g : List ℚ} {ρ : ℚ} (hg : ∀ q ∈ g, 0 < q)
    (hρ : 0 < ρ) (p : ℚ) {v : ℕ} (hv : g.length + 1 ≤ v) :
    transferRatio g ρ p v = rInf ρ p := by
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
  have hu : profileU g ρ w ≠ 0 := ne_of_gt (profileU_pos hg hρ w)
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  have h2 : profileU g ρ (w + 1 + 1) = profileU g ρ (w + 1) * ρ := by
    rw [profileU_succ, stepRatio_of_ge g ρ (by omega)]
  have h1 : profileU g ρ (w + 1) = profileU g ρ w * ρ := by
    rw [profileU_succ, stepRatio_of_ge g ρ (by omega)]
  unfold transferRatio rInf
  rw [Nat.add_sub_cancel, h2, h1]
  field_simp

/-- The class ceiling: the maximum of `rInf` and the finitely many
ramp-region ratios `r 0 .. r g.length` — every transfer ratio at any
index is bounded by it (`transferRatio_le_rMax`). -/
def rMax (g : List ℚ) (ρ p : ℚ) : ℚ :=
  max (rInf ρ p)
    ((Finset.range (g.length + 1)).sup'
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
      (transferRatio g ρ p))

theorem rInf_le_rMax (g : List ℚ) (ρ p : ℚ) : rInf ρ p ≤ rMax g ρ p :=
  le_max_left _ _

theorem transferRatio_le_rMax {g : List ℚ} {ρ : ℚ} (hg : ∀ q ∈ g, 0 < q)
    (hρ : 0 < ρ) (p : ℚ) (v : ℕ) :
    transferRatio g ρ p v ≤ rMax g ρ p := by
  by_cases hv : v ≤ g.length
  · exact le_trans
      (Finset.le_sup' (transferRatio g ρ p)
        (Finset.mem_range.mpr (by omega)))
      (le_max_right _ _)
  · rw [transferRatio_of_ge hg hρ p (by omega)]
    exact le_max_left _ _

/-! ## The alive one-step transfer -/

/-- The alive one-step transfer of `V` under the uniform-axis kernel:
each coordinate moves up at weight `p/d`, down (with monus) at weight
`(1−p)/d`, and a down-move that reaches the origin is absorbed — it
carries no `V`.  Up-moves never reach the origin.  Grouping this
move-indexed sum by destination recovers the merged kernel row a
checker stores. -/
def aliveStep (g : List ℚ) (ρ p : ℚ) {d : ℕ} (x : Fin d → ℕ) : ℚ :=
  ∑ i, (p / (d : ℚ) * prodProfileV g ρ (upMove x i)
    + if downMove x i = 0 then 0
      else (1 - p) / (d : ℚ) * prodProfileV g ρ (downMove x i))

/-- One coordinate's un-divided transfer identity: monus in the state
and monus in the ratio index are the same subtraction, so no case
split on `x i = 0` occurs. -/
theorem coord_transfer {g : List ℚ} {ρ : ℚ} (hg : ∀ q ∈ g, 0 < q)
    (hρ : 0 < ρ) (p : ℚ) {d : ℕ} (x : Fin d → ℕ) (i : Fin d) :
    p * prodProfileV g ρ (upMove x i)
        + (1 - p) * prodProfileV g ρ (downMove x i)
      = transferRatio g ρ p (x i) * prodProfileV g ρ x := by
  have hu : profileU g ρ (x i) ≠ 0 := ne_of_gt (profileU_pos hg hρ (x i))
  have hup := prodProfileV_update_mul g ρ x i (x i + 1)
  have hdn := prodProfileV_update_mul g ρ x i (x i - 1)
  unfold upMove downMove
  unfold transferRatio
  field_simp
  linear_combination p * hup + (1 - p) * hdn

/-- No single down-move reaches the origin when some coordinate is at
least `2`: that coordinate survives every down-move positive. -/
theorem downMove_ne_zero {d : ℕ} (x : Fin d → ℕ) {j : Fin d}
    (hj : 2 ≤ x j) (i : Fin d) : downMove x i ≠ 0 := by
  intro h
  have hz : downMove x i j = 0 := by simpa using congrFun h j
  unfold downMove at hz
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self] at hz
    omega
  · rw [Function.update_of_ne (Ne.symm hij)] at hz
    omega

/-- **(i) Per-coordinate factorization**: where no down-move reaches
the origin, the alive one-step transfer of the product-profile weight
is `(∑ i, r (x i)) / d · V x` — the infinite-region transfer
inequality reduces to a statement about the coordinate ratios. -/
theorem aliveStep_factor {g : List ℚ} {ρ : ℚ} (hg : ∀ q ∈ g, 0 < q)
    (hρ : 0 < ρ) (p : ℚ) {d : ℕ} (x : Fin d → ℕ)
    (hx : ∀ i, downMove x i ≠ 0) :
    aliveStep g ρ p x
      = (∑ i, transferRatio g ρ p (x i)) / (d : ℚ)
          * prodProfileV g ρ x := by
  have hterm : ∀ i : Fin d,
      p / (d : ℚ) * prodProfileV g ρ (upMove x i)
        + (if downMove x i = 0 then 0
           else (1 - p) / (d : ℚ) * prodProfileV g ρ (downMove x i))
      = transferRatio g ρ p (x i) / (d : ℚ) * prodProfileV g ρ x := by
    intro i
    rw [if_neg (hx i)]
    have h := coord_transfer hg hρ p x i
    linear_combination h / (d : ℚ)
  unfold aliveStep
  simp only [hterm]
  rw [← Finset.sum_mul, ← Finset.sum_div]

/-! ## The collapse -/

/-- **(iii) The product-profile collapse**: the finitely many class
inequalities `(d−k)·rMax + k·rInf ≤ d·c`, `k = 1..d` — exactly the
exact-rational facts a pattern-face checker verifies — discharge the
per-state contraction `aliveStep x ≤ c · V x` at every state with a
geometric-regime coordinate (`x j ≥ g.length + 1`; `x j ≥ 2` keeps
absorption out of reach — automatic whenever `g.length ≥ 1`).

The proof factors through the `k = 1` class: `rInf ≤ rMax` by
construction, so `(d−k)·rMax + k·rInf` is nonincreasing in `k` and
the `k ≥ 2` classes are implied.  This is the d-dimensional
warranted-consequence twin of `genFormTemplate_collapse`, which is
its `d = 1`, pure-geometric face. -/
theorem productProfile_collapse {g : List ℚ} {ρ : ℚ}
    (hg : ∀ q ∈ g, 0 < q) (hρ : 0 < ρ) (p : ℚ) {d : ℕ} {c : ℚ}
    (hclass : ∀ k ∈ Finset.Icc 1 d,
      ((d : ℚ) - (k : ℚ)) * rMax g ρ p + (k : ℚ) * rInf ρ p
        ≤ (d : ℚ) * c)
    (x : Fin d → ℕ) (j : Fin d) (hgeo : g.length + 1 ≤ x j)
    (h2 : 2 ≤ x j) :
    aliveStep g ρ p x ≤ c * prodProfileV g ρ x := by
  have hd : 0 < d := j.pos
  have hdQ : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hV : 0 < prodProfileV g ρ x := prodProfileV_pos hg hρ x
  have h1 := hclass 1 (Finset.mem_Icc.mpr ⟨le_refl 1, hd⟩)
  push_cast at h1
  have herase : (∑ i ∈ Finset.univ.erase j, transferRatio g ρ p (x i))
      ≤ ((d : ℚ) - 1) * rMax g ρ p := by
    have hb := Finset.sum_le_card_nsmul (Finset.univ.erase j)
      (fun i => transferRatio g ρ p (x i)) (rMax g ρ p)
      (fun i _ => transferRatio_le_rMax hg hρ p (x i))
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hd,
      Nat.cast_one] at hb
    exact hb
  have hsum : (∑ i, transferRatio g ρ p (x i)) ≤ (d : ℚ) * c := by
    have hsplit : (∑ i, transferRatio g ρ p (x i))
        = transferRatio g ρ p (x j)
            + ∑ i ∈ Finset.univ.erase j, transferRatio g ρ p (x i) :=
      (Finset.add_sum_erase Finset.univ
        (fun i => transferRatio g ρ p (x i)) (Finset.mem_univ j)).symm
    rw [hsplit, transferRatio_of_ge hg hρ p hgeo]
    linarith [herase, h1]
  rw [aliveStep_factor hg hρ p x (downMove_ne_zero x h2)]
  have hdiv : (∑ i, transferRatio g ρ p (x i)) / (d : ℚ) ≤ c := by
    rw [div_le_iff₀ hdQ]
    linarith [hsum]
  exact mul_le_mul_of_nonneg_right hdiv (le_of_lt hV)

/-- The collapse in window vocabulary: every state outside the
stored-row window — some coordinate `≥ box + 2`, where window
coverage at radius `box + 1` guarantees the state and all its
neighbors carry template `V` — contracts, given the class
inequalities AND the reach side condition `g.length ≤ box + 1`.

The reach condition is load-bearing: it is what puts a
geometric-regime coordinate inside every window-exterior state.  A
checker that verifies window coverage and the class inequalities but
not `profile length ≤ box + 1` admits certificates whose exterior
states sit entirely on the ramp, where the collapse says nothing
(`rampProfile_needs_window_reach`). -/
theorem productProfile_collapse_window {g : List ℚ} {ρ : ℚ}
    (hg : ∀ q ∈ g, 0 < q) (hρ : 0 < ρ) (p : ℚ) {d : ℕ} {c : ℚ}
    (hclass : ∀ k ∈ Finset.Icc 1 d,
      ((d : ℚ) - (k : ℚ)) * rMax g ρ p + (k : ℚ) * rInf ρ p
        ≤ (d : ℚ) * c)
    {box : ℕ} (hbox : 1 ≤ box) (hlen : g.length ≤ box + 1)
    (x : Fin d → ℕ) (j : Fin d) (hout : box + 2 ≤ x j) :
    aliveStep g ρ p x ≤ c * prodProfileV g ρ x :=
  productProfile_collapse hg hρ p hclass x j (by omega) (by omega)

/-! ## Necessity of the reach side condition -/

/-- A concrete admissible ramp profile (every entry `≥ 1`, growth
`7/4 ≥ 1`): flat, then ramping to the geometric rate. -/
private def rampG : List ℚ := [1, 21/20, 23/20, 27/20, 31/20, 7/4]

/-- **The reach condition cannot be dropped**: for the ramp profile
above at `p = 1/4`, `ρ = 7/4`, `c = 193/200`, every class inequality
`(3−k)·rMax + k·rInf ≤ 3c` holds (`k = 1, 2, 3` — the checks a
3-dimensional checker runs), yet the ratio sum at a state with
coordinates `(1, 1, 5)` — window-exterior for `box = 3`, which
violates `g.length ≤ box + 1` since `6 > 4` — exceeds `3c`.  By the
factorization (i), the alive transfer at that state strictly exceeds
`c · V`: the class inequalities alone do not cover ramp-resident
exterior states. -/
theorem rampProfile_needs_window_reach :
    (∀ k ∈ Finset.Icc (1 : ℕ) 3,
      ((3 : ℚ) - (k : ℚ)) * rMax rampG (7/4) (1/4)
        + (k : ℚ) * rInf (7/4) (1/4) ≤ (3 : ℚ) * (193/200)) ∧
    (3 : ℚ) * (193/200)
      < 2 * transferRatio rampG (7/4) (1/4) 1
          + transferRatio rampG (7/4) (1/4) 5 := by
  -- step ratios of the ramp profile
  have hs0 : stepRatio rampG (7/4) 0 = 1 := by norm_num [stepRatio, rampG]
  have hs1 : stepRatio rampG (7/4) 1 = 21/20 := by
    norm_num [stepRatio, rampG]
  have hs2 : stepRatio rampG (7/4) 2 = 23/20 := by
    norm_num [stepRatio, rampG]
  have hs3 : stepRatio rampG (7/4) 3 = 27/20 := by
    norm_num [stepRatio, rampG]
  have hs4 : stepRatio rampG (7/4) 4 = 31/20 := by
    norm_num [stepRatio, rampG]
  have hs5 : stepRatio rampG (7/4) 5 = 7/4 := by
    norm_num [stepRatio, rampG]
  have hs6 : stepRatio rampG (7/4) 6 = 7/4 :=
    stepRatio_of_ge rampG (7/4) (by norm_num [rampG])
  -- the profile values
  have hu0 : profileU rampG (7/4) 0 = 1 := rfl
  have hu1 : profileU rampG (7/4) 1 = 1 := by
    show profileU rampG (7/4) (0 + 1) = 1
    rw [profileU_succ, hu0, hs0]; norm_num
  have hu2 : profileU rampG (7/4) 2 = 21/20 := by
    show profileU rampG (7/4) (1 + 1) = 21/20
    rw [profileU_succ, hu1, hs1]; norm_num
  have hu3 : profileU rampG (7/4) 3 = 483/400 := by
    show profileU rampG (7/4) (2 + 1) = 483/400
    rw [profileU_succ, hu2, hs2]; norm_num
  have hu4 : profileU rampG (7/4) 4 = 13041/8000 := by
    show profileU rampG (7/4) (3 + 1) = 13041/8000
    rw [profileU_succ, hu3, hs3]; norm_num
  have hu5 : profileU rampG (7/4) 5 = 404271/160000 := by
    show profileU rampG (7/4) (4 + 1) = 404271/160000
    rw [profileU_succ, hu4, hs4]; norm_num
  have hu6 : profileU rampG (7/4) 6 = 2829897/640000 := by
    show profileU rampG (7/4) (5 + 1) = 2829897/640000
    rw [profileU_succ, hu5, hs5]; norm_num
  have hu7 : profileU rampG (7/4) 7 = 19809279/2560000 := by
    show profileU rampG (7/4) (6 + 1) = 19809279/2560000
    rw [profileU_succ, hu6, hs6]; norm_num
  -- the transfer ratios
  have hr0 : transferRatio rampG (7/4) (1/4) 0 = 1 := by
    unfold transferRatio
    norm_num [hu0, hu1]
  have hr1 : transferRatio rampG (7/4) (1/4) 1 = 81/80 := by
    unfold transferRatio
    norm_num [hu0, hu1, hu2]
  have hr2 : transferRatio rampG (7/4) (1/4) 2 = 561/560 := by
    unfold transferRatio
    norm_num [hu1, hu2, hu3]
  have hr3 : transferRatio rampG (7/4) (1/4) 3 = 1821/1840 := by
    unfold transferRatio
    norm_num [hu2, hu3, hu4]
  have hr4 : transferRatio rampG (7/4) (1/4) 4 = 679/720 := by
    unfold transferRatio
    norm_num [hu3, hu4, hu5]
  have hr5 : transferRatio rampG (7/4) (1/4) 5 = 457/496 := by
    unfold transferRatio
    norm_num [hu4, hu5, hu6]
  have hr6 : transferRatio rampG (7/4) (1/4) 6 = 97/112 := by
    unfold transferRatio
    norm_num [hu5, hu6, hu7]
  have hrinf : rInf (7/4) (1/4) = 97/112 := by
    unfold rInf
    norm_num
  -- the class ceiling evaluates to r 1
  have hrmax : rMax rampG (7/4) (1/4) = 81/80 := by
    unfold rMax
    have hsup : (Finset.range (rampG.length + 1)).sup'
        ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
        (transferRatio rampG (7/4) (1/4))
        = 81/80 := by
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun v hv => ?_
        have hv7 : v < 7 := by
          simpa [rampG] using Finset.mem_range.mp hv
        rcases (by omega :
            v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6)
          with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hr0]; norm_num
        · exact hr1.le
        · rw [hr2]; norm_num
        · rw [hr3]; norm_num
        · rw [hr4]; norm_num
        · rw [hr5]; norm_num
        · rw [hr6]; norm_num
      · calc (81/80 : ℚ)
            = transferRatio rampG (7/4) (1/4) 1 := hr1.symm
          _ ≤ _ := Finset.le_sup' (transferRatio rampG (7/4) (1/4))
              (Finset.mem_range.mpr (by norm_num [rampG]))
    rw [hsup, hrinf,
      max_eq_right (by norm_num : (97/112 : ℚ) ≤ 81/80)]
  constructor
  · intro k hk
    have hk3 : 1 ≤ k ∧ k ≤ 3 := Finset.mem_Icc.mp hk
    rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl
    all_goals (rw [hrmax, hrinf]; push_cast; norm_num)
  · rw [hr1, hr5]
    norm_num

end Adequacy
end SuFunctor
