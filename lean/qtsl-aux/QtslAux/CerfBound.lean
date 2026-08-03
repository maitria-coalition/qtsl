import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # A uniform Chernoff bound for empirical distributions of finite Markov chains

For a row-stochastic matrix `P` on a finite state space, this module bounds
the probability that the empirical distribution of the first `n` steps of the
chain falls in a compact convex set `C`, uniformly over some starting state.
The rate is expressed through the Donsker-Varadhan-type functional
`dvF P u y = log (u y) - log (stepAvg P u y)` and its pairing
`dvPairing P u ν = ∑ y, ν y * dvF P u y` with a distribution `ν`.

Main definitions:

* `pathE P n x f`: the expectation of a path functional `f` over `n` steps of
  the chain started at `x`, defined by finite recursion (no measure theory).
* `pathProb`, `empDist`: path probabilities and the empirical distribution of
  a finite path.

Main results:

* `pathE_dv_identity`, `exists_pathE_ratio_le_one`: the multiplicative
  martingale identity for the ratio `u / stepAvg P u` along paths, and the
  existence of a starting state where its path expectation is at most one.
* `chernoff_row`: a single test function `u = exp φ` with
  `dvPairing P u ν ≥ b` for all `ν ∈ C` yields
  `pathProb P n x₀ {empDist ∈ C} ≤ exp (-n * b)` for some `x₀`.
* `exists_convex_weights_of_forall_exists_lt`: a minimax step via geometric
  Hahn-Banach separation, producing convex weights that turn a family of
  pointwise-winning tests into one uniformly-winning test.
* `sum_mul_exp_combination_le`, `dvPairing_exp_combination_ge`: Hölder's
  inequality and the resulting concavity of the rate functional under
  geometric combination of test functions.
* `cerf_bound`: the main theorem — if every `μ ∈ C` admits some test `φ` with
  rate at least `c`, then for every `n` there is a starting state `x₀` with
  `pathProb P n x₀ {empDist ∈ C} ≤ exp (-n * c)`.
-/

open Finset

namespace Qtsl.Cerf

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

def stepAvg (P : S → S → ℝ) (u : S → ℝ) (x : S) : ℝ := ∑ y, P x y * u y

def pathE (P : S → S → ℝ) : (n : ℕ) → S → ((Fin (n + 1) → S) → ℝ) → ℝ
  | 0, x, f => f fun _ => x
  | n + 1, x, f => ∑ y, P x y * pathE P n y fun ω => f (Fin.cons x ω)

noncomputable def pathProb (P : S → S → ℝ) (n : ℕ) (x : S) (E : Set (Fin (n + 1) → S)) : ℝ :=
  pathE P n x (E.indicator 1)

section PathE

variable {P : S → S → ℝ}

omit [DecidableEq S] [Nonempty S] in
theorem pathE_nonneg (hP0 : ∀ x y, 0 ≤ P x y) :
    ∀ (n : ℕ) (x : S) (f : (Fin (n + 1) → S) → ℝ), (∀ ω, 0 ≤ f ω) → 0 ≤ pathE P n x f := by
  intro n
  induction n with
  | zero => exact fun x f hf => hf _
  | succ n ih =>
    intro x f hf
    exact Finset.sum_nonneg fun y _ => mul_nonneg (hP0 x y) (ih y _ fun ω => hf _)

omit [DecidableEq S] [Nonempty S] in
theorem pathE_mono (hP0 : ∀ x y, 0 ≤ P x y) :
    ∀ (n : ℕ) (x : S) (f g : (Fin (n + 1) → S) → ℝ), (∀ ω, f ω ≤ g ω) →
      pathE P n x f ≤ pathE P n x g := by
  intro n
  induction n with
  | zero => exact fun x f g hfg => hfg _
  | succ n ih =>
    intro x f g hfg
    exact Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (ih y _ _ fun ω => hfg _) (hP0 x y)

omit [DecidableEq S] [Nonempty S] in
theorem pathE_const_mul :
    ∀ (n : ℕ) (x : S) (c : ℝ) (f : (Fin (n + 1) → S) → ℝ),
      pathE P n x (fun ω => c * f ω) = c * pathE P n x f := by
  intro n
  induction n with
  | zero => intro x c f; rfl
  | succ n ih =>
    intro x c f
    simp only [pathE]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [ih y c fun ω => f (Fin.cons x ω)]
    ring

omit [DecidableEq S] [Nonempty S] in
theorem pathE_zero : ∀ (n : ℕ) (x : S), pathE P n x (fun _ => 0) = 0 := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    simp only [pathE, ih, mul_zero, Finset.sum_const_zero]

end PathE

section DV

variable {P : S → S → ℝ}

omit [DecidableEq S] in
theorem stepAvg_pos (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y = 1)
    {u : S → ℝ} (hu : ∀ y, 0 < u y) (x : S) : 0 < stepAvg P u x := by
  obtain ⟨y₀, -, hy₀⟩ := Finset.exists_min_image Finset.univ u Finset.univ_nonempty
  calc (0 : ℝ) < u y₀ := hu y₀
    _ = ∑ y, P x y * u y₀ := by rw [← Finset.sum_mul, hP1, one_mul]
    _ ≤ ∑ y, P x y * u y :=
        Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (hy₀ y (Finset.mem_univ y)) (hP0 x y)
    _ = stepAvg P u x := rfl

private theorem cons_prod_aux {T : Type*} (g : T → ℝ) (x : T) {n : ℕ}
    (ω : Fin (n + 1) → T) :
    ∏ k : Fin (n + 1), g ((Fin.cons x ω : Fin (n + 2) → T) k.castSucc)
      = g x * ∏ k : Fin n, g (ω k.castSucc) := by
  rw [Fin.prod_univ_succ]
  have h0 : (Fin.cons x ω : Fin (n + 2) → T) ((0 : Fin (n + 1)).castSucc) = x := by simp
  have hsucc : ∀ k : Fin n,
      (Fin.cons x ω : Fin (n + 2) → T) ((k.succ).castSucc) = ω k.castSucc := by
    intro k
    have h : (k.succ).castSucc = (k.castSucc).succ := by ext; simp
    rw [h, Fin.cons_succ]
  simp only [h0, hsucc]

private theorem cons_last_aux {T : Type*} (x : T) {n : ℕ} (ω : Fin (n + 1) → T) :
    (Fin.cons x ω : Fin (n + 2) → T) (Fin.last (n + 1)) = ω (Fin.last n) := by
  have h : Fin.last (n + 1) = (Fin.last n).succ := by ext; simp
  rw [h, Fin.cons_succ]

omit [DecidableEq S] in

theorem pathE_dv_identity (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y = 1)
    {u : S → ℝ} (hu : ∀ y, 0 < u y) :
    ∀ (n : ℕ) (x : S),
      pathE P n x (fun ω =>
        (∏ k : Fin n, u (ω k.castSucc) / stepAvg P u (ω k.castSucc)) * u (ω (Fin.last n)))
        = u x := by
  intro n
  induction n with
  | zero => intro x; simp [pathE]
  | succ n ih =>
    intro x
    have hA : stepAvg P u x ≠ 0 := (stepAvg_pos hP0 hP1 hu x).ne'
    have step : ∀ y : S,
        pathE P n y (fun ω =>
          (∏ k : Fin (n + 1),
            u ((Fin.cons x ω : Fin (n + 2) → S) k.castSucc)
              / stepAvg P u ((Fin.cons x ω : Fin (n + 2) → S) k.castSucc))
            * u ((Fin.cons x ω : Fin (n + 2) → S) (Fin.last (n + 1))))
          = u x / stepAvg P u x * u y := by
      intro y
      have hfun : (fun ω : Fin (n + 1) → S =>
          (∏ k : Fin (n + 1),
            u ((Fin.cons x ω : Fin (n + 2) → S) k.castSucc)
              / stepAvg P u ((Fin.cons x ω : Fin (n + 2) → S) k.castSucc))
            * u ((Fin.cons x ω : Fin (n + 2) → S) (Fin.last (n + 1))))
          = fun ω : Fin (n + 1) → S =>
            (u x / stepAvg P u x) *
              ((∏ k : Fin n, u (ω k.castSucc) / stepAvg P u (ω k.castSucc))
                * u (ω (Fin.last n))) := by
        funext ω
        rw [cons_prod_aux (fun z => u z / stepAvg P u z) x ω, cons_last_aux x ω]
        ring
      rw [hfun, pathE_const_mul, ih y]
    calc pathE P (n + 1) x _
        = ∑ y, P x y * (u x / stepAvg P u x * u y) := by
          simp only [pathE]
          exact Finset.sum_congr rfl fun y _ => by rw [step y]
      _ = u x / stepAvg P u x * ∑ y, P x y * u y := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ = u x := by
          rw [show ∑ y, P x y * u y = stepAvg P u x from rfl, div_mul_cancel₀ _ hA]

omit [DecidableEq S] in

theorem exists_pathE_ratio_le_one (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y = 1)
    {u : S → ℝ} (hu : ∀ y, 0 < u y) (n : ℕ) :
    ∃ x₀ : S,
      pathE P n x₀ (fun ω => ∏ k : Fin n, u (ω k.castSucc) / stepAvg P u (ω k.castSucc)) ≤ 1 := by
  obtain ⟨x₀, -, hx₀⟩ := Finset.exists_min_image Finset.univ u Finset.univ_nonempty
  refine ⟨x₀, ?_⟩
  have hratio : ∀ ω : Fin (n + 1) → S,
      0 ≤ ∏ k : Fin n, u (ω k.castSucc) / stepAvg P u (ω k.castSucc) := fun ω =>
    Finset.prod_nonneg fun k _ =>
      div_nonneg (hu _).le (stepAvg_pos hP0 hP1 hu _).le
  have h1 : u x₀ * pathE P n x₀
      (fun ω => ∏ k : Fin n, u (ω k.castSucc) / stepAvg P u (ω k.castSucc)) ≤ u x₀ := by
    calc u x₀ * pathE P n x₀ (fun ω => ∏ k : Fin n, u (ω k.castSucc) / stepAvg P u (ω k.castSucc))
        = pathE P n x₀ (fun ω =>
            u x₀ * ∏ k : Fin n, u (ω k.castSucc) / stepAvg P u (ω k.castSucc)) :=
          (pathE_const_mul n x₀ (u x₀) _).symm
      _ ≤ pathE P n x₀ (fun ω =>
            (∏ k : Fin n, u (ω k.castSucc) / stepAvg P u (ω k.castSucc))
              * u (ω (Fin.last n))) := by
          refine pathE_mono hP0 n x₀ _ _ fun ω => ?_
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (hx₀ _ (Finset.mem_univ _)) (hratio ω)
      _ = u x₀ := pathE_dv_identity hP0 hP1 hu n x₀
  have h1' : u x₀ * pathE P n x₀
      (fun ω => ∏ k : Fin n, u (ω k.castSucc) / stepAvg P u (ω k.castSucc)) ≤ u x₀ * 1 := by
    rwa [mul_one]
  exact le_of_mul_le_mul_left h1' (hu x₀)

end DV

noncomputable def dvF (P : S → S → ℝ) (u : S → ℝ) (y : S) : ℝ :=
  Real.log (u y) - Real.log (stepAvg P u y)

noncomputable def dvPairing (P : S → S → ℝ) (u : S → ℝ) (ν : S → ℝ) : ℝ :=
  ∑ y, ν y * dvF P u y

omit [DecidableEq S] [Nonempty S] in

theorem dvF_exp (P : S → S → ℝ) (φ : S → ℝ) (y : S) :
    dvF P (fun z => Real.exp (φ z)) y
      = φ y - Real.log (∑ z, P y z * Real.exp (φ z)) := by
  simp [dvF, Real.log_exp, stepAvg]

noncomputable def empDist {n : ℕ} (ω : Fin (n + 1) → S) : S → ℝ := fun y =>
  (∑ k : Fin n, if ω k.castSucc = y then (1 : ℝ) else 0) / n

omit [Fintype S] [Nonempty S] in
theorem empDist_nonneg {n : ℕ} (ω : Fin (n + 1) → S) (y : S) : 0 ≤ empDist ω y :=
  div_nonneg (Finset.sum_nonneg fun k _ => by split <;> norm_num) (Nat.cast_nonneg n)

omit [Nonempty S] in
theorem empDist_sum {n : ℕ} (hn : 0 < n) (ω : Fin (n + 1) → S) :
    ∑ y, empDist ω y = 1 := by
  simp only [empDist, ← Finset.sum_div]
  rw [Finset.sum_comm]
  have h : ∀ k : Fin n, ∑ y, (if ω k.castSucc = y then (1 : ℝ) else 0) = 1 := by
    intro k
    rw [Finset.sum_ite_eq]
    simp
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (Nat.cast_ne_zero.2 hn.ne')

section Chernoff

variable {P : S → S → ℝ}

theorem prod_ratio_eq_exp (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y = 1)
    {u : S → ℝ} (hu : ∀ y, 0 < u y) {n : ℕ} (ω : Fin (n + 1) → S) :
    ∏ k : Fin n, u (ω k.castSucc) / stepAvg P u (ω k.castSucc)
      = Real.exp (∑ y,
          (∑ k : Fin n, if ω k.castSucc = y then (1 : ℝ) else 0) * dvF P u y) := by
  have h1 : ∀ z : S, u z / stepAvg P u z = Real.exp (dvF P u z) := fun z => by
    rw [dvF, Real.exp_sub, Real.exp_log (hu z), Real.exp_log (stepAvg_pos hP0 hP1 hu z)]
  simp only [h1, ← Real.exp_sum]
  congr 1
  calc ∑ k : Fin n, dvF P u (ω k.castSucc)
      = ∑ k : Fin n, ∑ y, (if ω k.castSucc = y then (1 : ℝ) else 0) * dvF P u y := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [eq_comm]
        simp only [ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ y, (∑ k : Fin n, if ω k.castSucc = y then (1 : ℝ) else 0) * dvF P u y := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ => by rw [Finset.sum_mul]

theorem chernoff_row (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y = 1)
    {u : S → ℝ} (hu : ∀ y, 0 < u y) (n : ℕ) {C : Set (S → ℝ)} {b : ℝ}
    (hb : ∀ ν ∈ C, (∀ y, 0 ≤ ν y) → (∑ y, ν y) = 1 → b ≤ dvPairing P u ν) :
    ∃ x₀ : S, pathProb P n x₀ {ω | empDist ω ∈ C} ≤ Real.exp (-(n : ℝ) * b) := by
  obtain ⟨x₀, hx₀⟩ := exists_pathE_ratio_le_one hP0 hP1 hu n
  refine ⟨x₀, ?_⟩
  have hpoint : ∀ ω : Fin (n + 1) → S,
      Real.exp ((n : ℝ) * b) * ({ω | empDist ω ∈ C}.indicator 1 ω)
        ≤ ∏ k : Fin n, u (ω k.castSucc) / stepAvg P u (ω k.castSucc) := by
    intro ω
    by_cases hω : empDist ω ∈ C
    · have hmem : ω ∈ {ω' : Fin (n + 1) → S | empDist ω' ∈ C} := hω
      rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one,
        prod_ratio_eq_exp hP0 hP1 hu ω, Real.exp_le_exp]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · have hν1 := empDist_sum hn ω
        have hle := hb _ hω (empDist_nonneg ω) hν1
        have hcast : ∀ y : S,
            (n : ℝ) * (empDist ω y * dvF P u y)
              = (∑ k : Fin n, if ω k.castSucc = y then (1 : ℝ) else 0) * dvF P u y := by
          intro y
          have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
          rw [empDist]
          field_simp
        calc (n : ℝ) * b ≤ (n : ℝ) * dvPairing P u (empDist ω) :=
              mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg n)
          _ = ∑ y, (∑ k : Fin n, if ω k.castSucc = y then (1 : ℝ) else 0) * dvF P u y := by
              rw [dvPairing, Finset.mul_sum]
              exact Finset.sum_congr rfl fun y _ => hcast y
    · have hmem : ω ∉ {ω' : Fin (n + 1) → S | empDist ω' ∈ C} := hω
      rw [Set.indicator_of_notMem hmem, mul_zero]
      exact Finset.prod_nonneg fun k _ =>
        div_nonneg (hu _).le (stepAvg_pos hP0 hP1 hu _).le
  have h2 : Real.exp ((n : ℝ) * b) * pathProb P n x₀ {ω | empDist ω ∈ C} ≤ 1 := by
    calc Real.exp ((n : ℝ) * b) * pathProb P n x₀ {ω | empDist ω ∈ C}
        = pathE P n x₀ (fun ω =>
            Real.exp ((n : ℝ) * b) * ({ω | empDist ω ∈ C}.indicator 1 ω)) :=
          (pathE_const_mul n x₀ _ _).symm
      _ ≤ pathE P n x₀
            (fun ω => ∏ k : Fin n, u (ω k.castSucc) / stepAvg P u (ω k.castSucc)) :=
          pathE_mono hP0 n x₀ _ _ hpoint
      _ ≤ 1 := hx₀
  rw [neg_mul, Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos _), mul_comm]
  exact h2

end Chernoff

section Minimax

theorem exists_convex_weights_of_forall_exists_lt {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : Set (ι → ℝ)} (hKcpt : IsCompact K) (hKcvx : Convex ℝ K) {d : ℝ}
    (h : ∀ v ∈ K, ∃ i, d < v i) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ ∀ v ∈ K, d ≤ ∑ i, w i * v i := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · refine ⟨fun _ => (Fintype.card ι : ℝ)⁻¹, fun i => by positivity, ?_, by simp⟩
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]
  set O : Set (ι → ℝ) := {v | ∀ i, v i ≤ d} with hO
  have hOmem : ∀ (T : ℝ) (i : ι), 0 ≤ T → (fun j => d - T * if i = j then 1 else 0) ∈ O := by
    intro T i hT
    rw [hO]
    simp only [Set.mem_setOf_eq]
    intro j
    split
    · linarith
    · simp
  have hOeq : O = ⋂ i, {v : ι → ℝ | v i ≤ d} := by
    ext v; simp [hO, Set.mem_iInter]
  have hOcl : IsClosed O := by
    rw [hOeq]
    exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const
  have hOcvx : Convex ℝ O := by
    rw [hOeq]
    exact convex_iInter fun i =>
      convex_halfSpace_le ⟨fun _ _ => rfl, fun _ _ => rfl⟩ d
  have hdisj : Disjoint O K := by
    rw [Set.disjoint_right]
    intro v hv hvO
    obtain ⟨i, hi⟩ := h v hv
    exact absurd (hvO i) (not_le.2 hi)
  obtain ⟨f, s, t, hfO, hst, hfK⟩ :=
    geometric_hahn_banach_closed_compact hOcvx hOcl hKcvx hKcpt hdisj
  set g : ι → ℝ := fun i => f fun j => if i = j then 1 else 0 with hg
  have hrep : ∀ x : ι → ℝ, f x = ∑ i, x i * g i := by
    intro x
    have := LinearMap.pi_apply_eq_sum_univ (f.toLinearMap) x
    simpa [smul_eq_mul, hg] using this
  have hd1O : (fun _ : ι => d) ∈ O := by
    rw [hO]
    simp only [Set.mem_setOf_eq]
    exact fun i => le_rfl
  have hd1 : f (fun _ => d) = d * ∑ i, g i := by
    simp only [hrep]
    rw [Finset.mul_sum]
  have hg0 : ∀ i, 0 ≤ g i := by
    intro i
    by_contra hneg
    push Not at hneg
    set T : ℝ := max 0 ((s - d * ∑ j, g j) / (-g i)) with hT
    have hT0 : 0 ≤ T := le_max_left _ _
    have hmem := hOmem T i hT0
    have hite : ∑ j, (if i = j then (1 : ℝ) else 0) * g j = g i := by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp
    have hval : f (fun j => d - T * if i = j then 1 else 0) = d * ∑ j, g j - T * g i := by
      simp only [hrep]
      calc ∑ j, (d - T * if i = j then 1 else 0) * g j
          = ∑ j, (d * g j - T * ((if i = j then (1 : ℝ) else 0) * g j)) :=
            Finset.sum_congr rfl fun j _ => by ring
        _ = d * ∑ j, g j - T * ∑ j, (if i = j then (1 : ℝ) else 0) * g j := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = d * ∑ j, g j - T * g i := by rw [hite]
    have hTle : (s - d * ∑ j, g j) / (-g i) ≤ T := le_max_right _ _
    have hgi : 0 < -g i := by linarith
    have hprod : s - d * ∑ j, g j ≤ T * (-g i) := by
      rw [div_le_iff₀ hgi] at hTle
      linarith [hTle]
    have hcontra := hfO _ hmem
    rw [hval] at hcontra
    linarith
  have hGpos : 0 < ∑ i, g i := by
    rcases hKne with ⟨v₀, hv₀⟩
    have h1 : f (fun _ => d) < s := hfO _ hd1O
    have h2 : t < f v₀ := hfK v₀ hv₀
    rcases (Finset.sum_nonneg fun i _ => hg0 i).lt_or_eq with hpos | hzero
    · exact hpos
    · exfalso
      have hall : ∀ i ∈ Finset.univ, g i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hg0 i).1 hzero.symm
      have hf0 : ∀ x : ι → ℝ, f x = 0 := fun x => by
        rw [hrep]
        exact Finset.sum_eq_zero fun i _ => by
          rw [hall i (Finset.mem_univ i), mul_zero]
      rw [hf0] at h1 h2
      linarith
  refine ⟨fun i => g i / ∑ j, g j, fun i => div_nonneg (hg0 i) hGpos.le, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hGpos.ne']
  · intro v hv
    have h1 : f (fun _ => d) < s := hfO _ hd1O
    have h2 : t < f v := hfK v hv
    have hle : d * ∑ i, g i ≤ ∑ i, v i * g i := by
      rw [← hd1, ← hrep]
      linarith
    have heq : ∑ i, g i / (∑ j, g j) * v i = (∑ i, v i * g i) / ∑ j, g j := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [heq, le_div_iff₀ hGpos]
    linarith [hle]

end Minimax

section Hoelder

theorem sum_mul_exp_combination_le {ι : Type*} [Fintype ι] {α : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ z, 0 ≤ p z) (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (a : ι → α → ℝ) :
    ∑ z, p z * Real.exp (∑ i, w i * a i z)
      ≤ ∏ i, (∑ z, p z * Real.exp (a i z)) ^ (w i) := by
  have hA0 : ∀ i, (0 : ℝ) ≤ ∑ z, p z * Real.exp (a i z) := fun i =>
    Finset.sum_nonneg fun z _ => mul_nonneg (hp z) (Real.exp_pos _).le
  have hexp : ∀ z, Real.exp (∑ i, w i * a i z) = ∏ i, Real.exp (a i z) ^ (w i) := by
    intro z
    rw [show (∑ i, w i * a i z) = ∑ i, a i z * w i from
        Finset.sum_congr rfl fun i _ => mul_comm _ _,
      Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => Real.exp_mul _ _
  by_cases hpos : ∀ i, (0 : ℝ) < ∑ z, p z * Real.exp (a i z)
  · have hB : (0 : ℝ) ≤ ∏ i, (∑ z, p z * Real.exp (a i z)) ^ (w i) :=
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hA0 i) _
    calc ∑ z, p z * Real.exp (∑ i, w i * a i z)
        = ∑ z, p z * ∏ i, Real.exp (a i z) ^ (w i) :=
          Finset.sum_congr rfl fun z _ => by rw [hexp z]
      _ ≤ ∑ z, p z * ((∑ i, w i * (Real.exp (a i z) / ∑ z', p z' * Real.exp (a i z')))
            * ∏ i, (∑ z', p z' * Real.exp (a i z')) ^ (w i)) := by
          refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (hp z)
          have hfact : ∀ i : ι, Real.exp (a i z) ^ (w i)
              = (Real.exp (a i z) / ∑ z', p z' * Real.exp (a i z')) ^ (w i)
                * (∑ z', p z' * Real.exp (a i z')) ^ (w i) := by
            intro i
            rw [← Real.mul_rpow (div_nonneg (Real.exp_pos _).le (hA0 i)) (hA0 i),
              div_mul_cancel₀ _ (hpos i).ne']
          calc ∏ i, Real.exp (a i z) ^ (w i)
              = (∏ i, (Real.exp (a i z) / ∑ z', p z' * Real.exp (a i z')) ^ (w i))
                  * ∏ i, (∑ z', p z' * Real.exp (a i z')) ^ (w i) := by
                rw [← Finset.prod_mul_distrib]
                exact Finset.prod_congr rfl fun i _ => hfact i
            _ ≤ (∑ i, w i * (Real.exp (a i z) / ∑ z', p z' * Real.exp (a i z')))
                  * ∏ i, (∑ z', p z' * Real.exp (a i z')) ^ (w i) := by
                refine mul_le_mul_of_nonneg_right ?_
                  (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hA0 i) _)
                exact Real.geom_mean_le_arith_mean_weighted Finset.univ w _
                  (fun i _ => hw0 i) hw1 fun i _ => div_nonneg (Real.exp_pos _).le (hA0 i)
      _ = (∑ z, p z * ∑ i, w i * (Real.exp (a i z) / ∑ z', p z' * Real.exp (a i z')))
            * ∏ i, (∑ z', p z' * Real.exp (a i z')) ^ (w i) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun z _ => by ring
      _ = 1 * ∏ i, (∑ z', p z' * Real.exp (a i z')) ^ (w i) := by
          congr 1
          calc ∑ z, p z * ∑ i, w i * (Real.exp (a i z) / ∑ z', p z' * Real.exp (a i z'))
              = ∑ z, ∑ i, p z * (w i * (Real.exp (a i z) / ∑ z', p z' * Real.exp (a i z'))) :=
                Finset.sum_congr rfl fun z _ => Finset.mul_sum _ _ _
            _ = ∑ i, ∑ z, p z * (w i * (Real.exp (a i z) / ∑ z', p z' * Real.exp (a i z'))) :=
                Finset.sum_comm
            _ = ∑ i, w i / (∑ z', p z' * Real.exp (a i z')) * ∑ z, p z * Real.exp (a i z) := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun z _ => by ring
            _ = ∑ i, w i := by
                refine Finset.sum_congr rfl fun i _ => ?_
                exact div_mul_cancel₀ (w i) (hpos i).ne'
            _ = 1 := hw1
      _ = ∏ i, (∑ z', p z' * Real.exp (a i z')) ^ (w i) := one_mul _
  · push Not at hpos
    obtain ⟨i₀, hi₀⟩ := hpos
    have hAz : ∑ z, p z * Real.exp (a i₀ z) = 0 := le_antisymm hi₀ (hA0 i₀)
    have hp0 : ∀ z, p z = 0 := by
      intro z
      have hall := (Finset.sum_eq_zero_iff_of_nonneg fun z _ =>
        mul_nonneg (hp z) (Real.exp_pos (a i₀ z)).le).1 hAz
      rcases mul_eq_zero.1 (hall z (Finset.mem_univ z)) with h | h
      · exact h
      · exact absurd h (Real.exp_ne_zero _)
    have hLHS : ∑ z, p z * Real.exp (∑ i, w i * a i z) = 0 :=
      Finset.sum_eq_zero fun z _ => by rw [hp0 z, zero_mul]
    rw [hLHS]
    exact Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hA0 i) _

end Hoelder

section Concavity

variable {P : S → S → ℝ}

omit [DecidableEq S] in

theorem log_stepAvg_exp_combination_le (hP0 : ∀ x y, 0 ≤ P x y)
    (hP1 : ∀ x, ∑ y, P x y = 1) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (φ : ι → S → ℝ) (y : S) :
    Real.log (stepAvg P (fun z => Real.exp (∑ i, w i * φ i z)) y)
      ≤ ∑ i, w i * Real.log (stepAvg P (fun z => Real.exp (φ i z)) y) := by
  have hApos : ∀ i, (0 : ℝ) < ∑ z, P y z * Real.exp (φ i z) := by
    intro i
    have := stepAvg_pos hP0 hP1 (u := fun z => Real.exp (φ i z))
      (fun z => Real.exp_pos _) y
    simpa [stepAvg] using this
  have hL : (0 : ℝ) < ∑ z, P y z * Real.exp (∑ i, w i * φ i z) := by
    have := stepAvg_pos hP0 hP1 (u := fun z => Real.exp (∑ i, w i * φ i z))
      (fun z => Real.exp_pos _) y
    simpa [stepAvg] using this
  have hmain := sum_mul_exp_combination_le (P y) (hP0 y) w hw0 hw1 fun i z => φ i z
  calc Real.log (stepAvg P (fun z => Real.exp (∑ i, w i * φ i z)) y)
      = Real.log (∑ z, P y z * Real.exp (∑ i, w i * φ i z)) := by simp [stepAvg]
    _ ≤ Real.log (∏ i, (∑ z, P y z * Real.exp (φ i z)) ^ (w i)) :=
        Real.log_le_log hL hmain
    _ = ∑ i, Real.log ((∑ z, P y z * Real.exp (φ i z)) ^ (w i)) :=
        Real.log_prod fun i _ => (Real.rpow_pos_of_pos (hApos i) _).ne'
    _ = ∑ i, w i * Real.log (∑ z, P y z * Real.exp (φ i z)) :=
        Finset.sum_congr rfl fun i _ => Real.log_rpow (hApos i) _
    _ = ∑ i, w i * Real.log (stepAvg P (fun z => Real.exp (φ i z)) y) := by
        simp [stepAvg]

omit [DecidableEq S] in

theorem dvPairing_exp_combination_ge (hP0 : ∀ x y, 0 ≤ P x y)
    (hP1 : ∀ x, ∑ y, P x y = 1) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (φ : ι → S → ℝ) {ν : S → ℝ} (hν : ∀ y, 0 ≤ ν y) :
    ∑ i, w i * dvPairing P (fun z => Real.exp (φ i z)) ν
      ≤ dvPairing P (fun z => Real.exp (∑ i, w i * φ i z)) ν := by
  have hswap : ∑ i, w i * dvPairing P (fun z => Real.exp (φ i z)) ν
      = ∑ y, ν y * ∑ i, w i * dvF P (fun z => Real.exp (φ i z)) y := by
    simp only [dvPairing]
    calc ∑ i, w i * ∑ y, ν y * dvF P (fun z => Real.exp (φ i z)) y
        = ∑ i, ∑ y, w i * (ν y * dvF P (fun z => Real.exp (φ i z)) y) :=
          Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
      _ = ∑ y, ∑ i, w i * (ν y * dvF P (fun z => Real.exp (φ i z)) y) :=
          Finset.sum_comm
      _ = ∑ y, ν y * ∑ i, w i * dvF P (fun z => Real.exp (φ i z)) y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  rw [hswap, dvPairing]
  refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (hν y)
  simp only [dvF_exp]
  have hlog := log_stepAvg_exp_combination_le hP0 hP1 w hw0 hw1 φ y
  simp only [stepAvg] at hlog
  have hexpand : ∑ i, w i * (φ i y - Real.log (∑ z, P y z * Real.exp (φ i z)))
      = ∑ i, w i * φ i y - ∑ i, w i * Real.log (∑ z, P y z * Real.exp (φ i z)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hexpand]
  linarith [hlog]

end Concavity

section Main

variable {P : S → S → ℝ}

omit [DecidableEq S] in

theorem exists_uniform_test (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y = 1)
    {C : Set (S → ℝ)} (hCcpt : IsCompact C) (hCcvx : Convex ℝ C)
    (hCpos : ∀ ν ∈ C, ∀ y, 0 ≤ ν y) (hCne : C.Nonempty) {c ε : ℝ} (hε : 0 < ε)
    (hc : ∀ μ ∈ C, ∃ φ : S → ℝ, c ≤ dvPairing P (fun z => Real.exp (φ z)) μ) :
    ∃ φ : S → ℝ, ∀ μ ∈ C, c - ε ≤ dvPairing P (fun z => Real.exp (φ z)) μ := by
  have hUopen : ∀ φ : S → ℝ,
      IsOpen {ν : S → ℝ | c - ε < dvPairing P (fun z => Real.exp (φ z)) ν} := by
    intro φ
    have hcont : Continuous fun ν : S → ℝ =>
        dvPairing P (fun z => Real.exp (φ z)) ν := by
      simp only [dvPairing]
      exact continuous_finsetSum _ fun y _ => (continuous_apply y).mul continuous_const
    exact isOpen_lt continuous_const hcont
  have hcover : C ⊆ ⋃ φ : S → ℝ,
      {ν : S → ℝ | c - ε < dvPairing P (fun z => Real.exp (φ z)) ν} := by
    intro μ hμ
    obtain ⟨φ, hφ⟩ := hc μ hμ
    exact Set.mem_iUnion.2 ⟨φ, by simp only [Set.mem_setOf_eq]; linarith⟩
  obtain ⟨t, ht⟩ := hCcpt.elim_finite_subcover _ hUopen hcover
  have htne : t.Nonempty := by
    obtain ⟨μ₀, hμ₀⟩ := hCne
    obtain ⟨φ, hφt, -⟩ := Set.mem_iUnion₂.1 (ht hμ₀)
    exact ⟨φ, hφt⟩
  haveI : Nonempty {φ : S → ℝ // φ ∈ t} := ⟨⟨htne.choose, htne.choose_spec⟩⟩
  set h : (S → ℝ) → ({φ : S → ℝ // φ ∈ t} → ℝ) := fun ν i =>
    dvPairing P (fun z => Real.exp ((i : S → ℝ) z)) ν with hh
  have hcont : Continuous h := by
    refine continuous_pi fun i => ?_
    simp only [hh, dvPairing]
    exact continuous_finsetSum _ fun y _ => (continuous_apply y).mul continuous_const
  have hKcvx : Convex ℝ (h '' C) := by
    rintro - ⟨ν₁, hν₁, rfl⟩ - ⟨ν₂, hν₂, rfl⟩ a b ha hb hab
    refine ⟨a • ν₁ + b • ν₂, hCcvx hν₁ hν₂ ha hb hab, ?_⟩
    funext i
    simp only [hh, dvPairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hKlt : ∀ v ∈ h '' C, ∃ i : {φ : S → ℝ // φ ∈ t}, c - ε < v i := by
    rintro - ⟨ν, hν, rfl⟩
    obtain ⟨φ, hφt, hφU⟩ := Set.mem_iUnion₂.1 (ht hν)
    exact ⟨⟨φ, hφt⟩, hφU⟩
  obtain ⟨w, hw0, hw1, hwle⟩ :=
    exists_convex_weights_of_forall_exists_lt (hCcpt.image hcont) hKcvx hKlt
  refine ⟨fun z => ∑ i : {φ : S → ℝ // φ ∈ t}, w i * (i : S → ℝ) z, ?_⟩
  intro μ hμ
  calc c - ε ≤ ∑ i, w i * h μ i := hwle (h μ) ⟨μ, hμ, rfl⟩
    _ = ∑ i, w i * dvPairing P (fun z => Real.exp ((i : S → ℝ) z)) μ := by
        simp only [hh]
    _ ≤ dvPairing P (fun z => Real.exp (∑ i, w i * (i : S → ℝ) z)) μ :=
        dvPairing_exp_combination_ge hP0 hP1 w hw0 hw1 (fun i => (i : S → ℝ))
          (hCpos μ hμ)

theorem cerf_bound (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y = 1)
    {C : Set (S → ℝ)} (hCcpt : IsCompact C) (hCcvx : Convex ℝ C)
    (hCpos : ∀ ν ∈ C, ∀ y, 0 ≤ ν y) {c : ℝ}
    (hc : ∀ μ ∈ C, ∃ φ : S → ℝ, c ≤ dvPairing P (fun z => Real.exp (φ z)) μ)
    (n : ℕ) :
    ∃ x₀ : S, pathProb P n x₀ {ω | empDist ω ∈ C} ≤ Real.exp (-(n : ℝ) * c) := by
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · refine ⟨Classical.arbitrary S, ?_⟩
    have hind : ({ω : Fin (n + 1) → S | empDist ω ∈ (∅ : Set (S → ℝ))}.indicator
        (1 : (Fin (n + 1) → S) → ℝ)) = fun _ => 0 := by
      funext ω
      simp
    rw [pathProb, hind, pathE_zero]
    exact (Real.exp_pos _).le
  · obtain ⟨x₀, -, hx₀min⟩ := Finset.exists_min_image Finset.univ
      (fun x => pathProb P n x {ω | empDist ω ∈ C}) Finset.univ_nonempty
    refine ⟨x₀, ?_⟩
    have hmain : ∀ ε : ℝ, 0 < ε →
        pathProb P n x₀ {ω | empDist ω ∈ C} ≤ Real.exp (-(n : ℝ) * (c - ε)) := by
      intro ε hε
      obtain ⟨φ, hφ⟩ := exists_uniform_test hP0 hP1 hCcpt hCcvx hCpos hCne hε hc
      obtain ⟨x₁, hx₁⟩ := chernoff_row hP0 hP1 (fun z => Real.exp_pos (φ z)) n
        (C := C) (b := c - ε) fun ν hν _ _ => hφ ν hν
      exact le_trans (hx₀min x₁ (Finset.mem_univ x₁)) hx₁
    have hlim : Filter.Tendsto (fun ε : ℝ => Real.exp (-(n : ℝ) * (c - ε)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp (-(n : ℝ) * c))) := by
      have hcont : Continuous fun ε : ℝ => Real.exp (-(n : ℝ) * (c - ε)) := by
        continuity
      have h0 := hcont.tendsto 0
      simp only [sub_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto hlim
      (Filter.eventually_iff_exists_mem.2
        ⟨Set.Ioi 0, self_mem_nhdsWithin, fun ε hε => hmain ε hε⟩)

end Main

end Qtsl.Cerf
