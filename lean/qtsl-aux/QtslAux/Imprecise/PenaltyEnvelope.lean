import QtslAux.Imprecise.Credal

/-! # Penalty-tilted envelopes: the convex-prevision tier at finite support

The family-presented **penalty kernel** stratum: a finite nonempty family of
laws `M : ι → FinPMF X` together with a signed cost `c : ι → ℚ` presents the
convex upper prevision

  `penUpperE M c f = max_i ((M i).exp f - c i)`

(Föllmer–Schied's sup-of-tilted-expectations representation of a convex risk
measure, restricted to finitely presented penalties), and dually
`penLowerE M c f = min_i ((M i).exp f + c i)`.  The credal (wall) tier of
`Imprecise.Credal` is the `c = 0` face — `penUpperE_zero_cost` is
definitional-grade — and the precise tier is the `[Unique ι]` face.  Costs are
deliberately *signed*: walls are carried by family membership (a law absent
from the family is excluded outright), never by infinite costs, so the
scored-sample tier with multiplicative weights above one (negative
log-weight) stays representable, and the Föllmer–Schied normalisation
`min c = 0` becomes the *calibration hypothesis* of the lemmas that want it
(`penUpperE_const` shows exactly how uncalibrated presentations shift
constants) rather than a carrier constraint.

Main results:

* Envelope calculus mirroring the credal tier: attainment
  (`exists_eq_penUpperE`), member bounds, monotonicity, translation
  equivariance (`penUpperE_add_const`), conjugacy
  (`penUpperE_eq_neg_penLowerE_neg`).
* **Convexity replaces coherence**: `penUpperE_mix_le` (a mixture of gambles
  is over-priced by the mixture of prices), while positive homogeneity
  *fails* off the calibrated face (`penUpperE_not_posHomogeneous`, a
  one-point witness) — the tier is convex-prevision, strictly wider than
  Walley-coherent.  What replaces homogeneity is the joint rate-scaling
  `penUpperE_smul` (scaling gamble *and* penalty together — the
  large-deviations `ε`-scaling of a rate function).
* **The tropical face**: `penUpperE_dirac_family` — the Dirac family with a
  pointwise gate `w` prices a gamble as the max-plus contraction
  `max_m (g m - w m)` (idempotent integration against the density `-w`), and
  the affinity bound `exp_sub_exp_le_sup_sub` with its Dirac attainment shows
  the all-laws affine-cost presentation generates the *same* prevision: the
  sup over laws of an affine objective sits at the Diracs (Varadhan-style
  value/law agreement at finite support).
* **The finite Legendre transform**: `penUpperE_eq_sup_levelProfile` — the
  scalar prevision is recovered from the threshold profile
  `t ↦ max_{c j ≤ t} exp_j` as `max_t (profile t - t)`, thresholds ranging
  over attained costs.  Sublevel bodies of the penalty are exactly the
  credal-tier data, so the convex tier needs no new judgment vocabulary:
  the scalar is the Legendre transform of the profile the wall tier already
  carries.
-/

namespace Qtsl.Imprecise

open Finset

section Dirac

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The Dirac (point-mass) law at `x₀`. -/
def FinPMF.dirac (x₀ : X) : FinPMF X where
  prob := fun x => if x = x₀ then 1 else 0
  nonneg := fun x => by by_cases h : x = x₀ <;> simp [h]
  total := by simp [Finset.sum_ite_eq']

@[simp] theorem FinPMF.exp_dirac (x₀ : X) (f : X → ℚ) :
    (FinPMF.dirac x₀).exp f = f x₀ := by
  have h : ∀ x ∈ univ, (FinPMF.dirac x₀).prob x * f x
      = if x = x₀ then f x else 0 := fun x _ => by
    show (if x = x₀ then (1 : ℚ) else 0) * f x = if x = x₀ then f x else 0
    by_cases hx : x = x₀ <;> simp [hx]
  unfold FinPMF.exp
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' univ x₀ f]
  simp

end Dirac

section ExpSub

variable {X : Type*} [Fintype X]

theorem FinPMF.exp_sub (p : FinPMF X) (f g : X → ℚ) :
    p.exp (fun x => f x - g x) = p.exp f - p.exp g := by
  have h := p.exp_add f (fun x => -g x)
  rw [p.exp_neg g] at h
  calc p.exp (fun x => f x - g x)
      = p.exp (fun x => f x + -g x) := p.exp_congr fun x => sub_eq_add_neg _ _
    _ = p.exp f - p.exp g := by rw [h, sub_eq_add_neg]

end ExpSub

section PenaltyEnvelope

variable {X : Type*} [Fintype X] {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The penalty-tilted upper envelope: the upper prevision presented by the
family `M` of laws with signed costs `c`.  The `c = 0` face is the credal
`upperE`; a `[Unique ι]` family is the precise face. -/
def penUpperE (M : ι → FinPMF X) (c : ι → ℚ) (f : X → ℚ) : ℚ :=
  univ.sup' univ_nonempty fun i => (M i).exp f - c i

/-- The penalty-tilted lower envelope (costs enter with the opposite sign:
a costly member can only *raise* the pessimistic price). -/
def penLowerE (M : ι → FinPMF X) (c : ι → ℚ) (f : X → ℚ) : ℚ :=
  univ.inf' univ_nonempty fun i => (M i).exp f + c i

theorem exp_sub_le_penUpperE (M : ι → FinPMF X) (c : ι → ℚ) (f : X → ℚ)
    (i : ι) : (M i).exp f - c i ≤ penUpperE M c f :=
  Finset.le_sup' (fun j => (M j).exp f - c j) (mem_univ i)

theorem penLowerE_le_exp_add (M : ι → FinPMF X) (c : ι → ℚ) (f : X → ℚ)
    (i : ι) : penLowerE M c f ≤ (M i).exp f + c i :=
  Finset.inf'_le _ (mem_univ i)

theorem penUpperE_le {M : ι → FinPMF X} {c : ι → ℚ} {f : X → ℚ} {a : ℚ}
    (h : ∀ i, (M i).exp f - c i ≤ a) : penUpperE M c f ≤ a :=
  Finset.sup'_le _ _ fun i _ => h i

theorem le_penLowerE {M : ι → FinPMF X} {c : ι → ℚ} {f : X → ℚ} {a : ℚ}
    (h : ∀ i, a ≤ (M i).exp f + c i) : a ≤ penLowerE M c f :=
  Finset.le_inf' _ _ fun i _ => h i

theorem exists_eq_penUpperE (M : ι → FinPMF X) (c : ι → ℚ) (f : X → ℚ) :
    ∃ i, penUpperE M c f = (M i).exp f - c i := by
  obtain ⟨i, _, h⟩ := Finset.exists_mem_eq_sup' (univ_nonempty)
    fun i => (M i).exp f - c i
  exact ⟨i, h⟩

theorem exists_eq_penLowerE (M : ι → FinPMF X) (c : ι → ℚ) (f : X → ℚ) :
    ∃ i, penLowerE M c f = (M i).exp f + c i := by
  obtain ⟨i, _, h⟩ := Finset.exists_mem_eq_inf' (univ_nonempty)
    fun i => (M i).exp f + c i
  exact ⟨i, h⟩

/-- **The credal face is the zero-cost face**: the wall tier of
`Imprecise.Credal` embeds definitionally. -/
theorem penUpperE_zero_cost (M : ι → FinPMF X) (f : X → ℚ) :
    penUpperE M 0 f = upperE M f := by
  unfold penUpperE upperE
  exact Finset.sup'_congr _ rfl fun i _ => by simp

theorem penLowerE_zero_cost (M : ι → FinPMF X) (f : X → ℚ) :
    penLowerE M 0 f = lowerE M f := by
  unfold penLowerE lowerE
  exact Finset.inf'_congr _ rfl fun i _ => by simp

/-- **The precise face**: a one-member family prices by its expectation,
shifted by its (uncalibrated) cost. -/
theorem penUpperE_unique {ι' : Type*} [Fintype ι'] [Unique ι']
    (M : ι' → FinPMF X) (c : ι' → ℚ) (f : X → ℚ) :
    penUpperE M c f = (M default).exp f - c default := by
  apply le_antisymm
  · exact penUpperE_le fun i => by rw [Unique.eq_default i]
  · exact exp_sub_le_penUpperE M c f default

theorem penLowerE_unique {ι' : Type*} [Fintype ι'] [Unique ι']
    (M : ι' → FinPMF X) (c : ι' → ℚ) (f : X → ℚ) :
    penLowerE M c f = (M default).exp f + c default := by
  apply le_antisymm
  · exact penLowerE_le_exp_add M c f default
  · exact le_penLowerE fun i => by rw [Unique.eq_default i]

theorem penUpperE_congr {M : ι → FinPMF X} {c : ι → ℚ} {f g : X → ℚ}
    (h : ∀ x, f x = g x) : penUpperE M c f = penUpperE M c g := by
  unfold penUpperE
  exact Finset.sup'_congr _ rfl fun i _ => by rw [(M i).exp_congr h]

theorem penLowerE_congr {M : ι → FinPMF X} {c : ι → ℚ} {f g : X → ℚ}
    (h : ∀ x, f x = g x) : penLowerE M c f = penLowerE M c g := by
  unfold penLowerE
  exact Finset.inf'_congr _ rfl fun i _ => by rw [(M i).exp_congr h]

theorem penUpperE_mono (M : ι → FinPMF X) (c : ι → ℚ) {f g : X → ℚ}
    (h : ∀ x, f x ≤ g x) : penUpperE M c f ≤ penUpperE M c g := by
  refine penUpperE_le fun i => ?_
  have := (M i).exp_mono h
  have hb := exp_sub_le_penUpperE M c g i
  linarith

theorem penLowerE_mono (M : ι → FinPMF X) (c : ι → ℚ) {f g : X → ℚ}
    (h : ∀ x, f x ≤ g x) : penLowerE M c f ≤ penLowerE M c g := by
  refine le_penLowerE fun i => ?_
  have := (M i).exp_mono h
  have hb := penLowerE_le_exp_add M c f i
  linarith

/-- Conjugacy: the two envelopes of one penalty presentation are mutually
determined, exactly as in the wall tier. -/
theorem penUpperE_eq_neg_penLowerE_neg (M : ι → FinPMF X) (c : ι → ℚ)
    (f : X → ℚ) : penUpperE M c f = -penLowerE M c (fun x => -f x) := by
  apply le_antisymm
  · refine penUpperE_le fun i => ?_
    have h := penLowerE_le_exp_add M c (fun x => -f x) i
    rw [(M i).exp_neg] at h
    linarith
  · obtain ⟨i, hi⟩ := exists_eq_penLowerE M c (fun x => -f x)
    rw [hi, (M i).exp_neg]
    have := exp_sub_le_penUpperE M c f i
    linarith

/-- Translation equivariance (the cash-invariance axiom of convex risk
measures): constants pass through at face value regardless of calibration. -/
theorem penUpperE_add_const (M : ι → FinPMF X) (c : ι → ℚ) (f : X → ℚ)
    (a : ℚ) : penUpperE M c (fun x => f x + a) = penUpperE M c f + a := by
  apply le_antisymm
  · refine penUpperE_le fun i => ?_
    rw [(M i).exp_add, (M i).exp_const]
    have := exp_sub_le_penUpperE M c f i
    linarith
  · obtain ⟨i, hi⟩ := exists_eq_penUpperE M c f
    have hb := exp_sub_le_penUpperE M c (fun x => f x + a) i
    rw [(M i).exp_add, (M i).exp_const] at hb
    linarith

/-- **Convexity in the gamble** — the axiom that replaces coherence on the
penalty tier: a mixture of gambles is over-priced by the mixture of prices.
Each member prices affinely; a max of affine functionals is convex. -/
theorem penUpperE_mix_le (M : ι → FinPMF X) (c : ι → ℚ) (f g : X → ℚ)
    {t : ℚ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
    penUpperE M c (fun x => t * f x + (1 - t) * g x)
      ≤ t * penUpperE M c f + (1 - t) * penUpperE M c g := by
  refine penUpperE_le fun i => ?_
  rw [(M i).exp_add, (M i).exp_smul, (M i).exp_smul]
  have hf := exp_sub_le_penUpperE M c f i
  have hg := exp_sub_le_penUpperE M c g i
  have hf' := mul_le_mul_of_nonneg_left hf h₀
  have hg' := mul_le_mul_of_nonneg_left hg (by linarith : (0:ℚ) ≤ 1 - t)
  nlinarith [hf', hg']

/-- **Joint rate-scaling** (what survives of positive homogeneity): scaling
the gamble *and* the penalty together scales the prevision — the
large-deviations `ε`-scaling of a rate function.  Homogeneity in the gamble
alone fails off the calibrated face (`penUpperE_not_posHomogeneous`). -/
theorem penUpperE_smul (M : ι → FinPMF X) (c : ι → ℚ) (f : X → ℚ)
    {t : ℚ} (ht : 0 ≤ t) :
    penUpperE M (fun i => t * c i) (fun x => t * f x) = t * penUpperE M c f := by
  apply le_antisymm
  · refine penUpperE_le fun i => ?_
    rw [(M i).exp_smul]
    have := exp_sub_le_penUpperE M c f i
    nlinarith [mul_le_mul_of_nonneg_left this ht]
  · obtain ⟨i, hi⟩ := exists_eq_penUpperE M c f
    have hb := exp_sub_le_penUpperE M (fun j => t * c j) (fun x => t * f x) i
    rw [(M i).exp_smul] at hb
    rw [hi]
    nlinarith [hb]

/-- Constants price at face value minus the penalty floor: the presentation
is normalised (prices constants at themselves) exactly when it is
*calibrated*, `min c = 0` — the Föllmer–Schied normalisation, here a
hypothesis rather than a carrier constraint. -/
theorem penUpperE_const (M : ι → FinPMF X) (c : ι → ℚ) (a : ℚ) :
    penUpperE M c (fun _ => a) = a - univ.inf' univ_nonempty c := by
  apply le_antisymm
  · refine penUpperE_le fun i => ?_
    rw [(M i).exp_const]
    have : univ.inf' univ_nonempty c ≤ c i := Finset.inf'_le _ (mem_univ i)
    linarith
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (univ_nonempty) c
    have hb := exp_sub_le_penUpperE M c (fun _ => a) i
    rw [(M i).exp_const] at hb
    rw [hi]
    exact hb

end PenaltyEnvelope

section Tropical

variable {M : Type*} [Fintype M] [Nonempty M]

/-- **The affinity bound** (the law-level half of the value/law agreement):
against an affine cost `ν ↦ ν.exp w`, every law is dominated by the best
point — the sup of an affine objective over the simplex sits at the Diracs.
With `FinPMF.exp_dirac` supplying attainment, the all-laws affine-cost
presentation and the Dirac pointwise-gate presentation generate one and the
same prevision. -/
theorem exp_sub_exp_le_sup_sub (ν : FinPMF M) (g w : M → ℚ) :
    ν.exp g - ν.exp w ≤ univ.sup' univ_nonempty (fun m => g m - w m) := by
  rw [← ν.exp_sub g w]
  calc ν.exp (fun m => g m - w m)
      ≤ ν.exp (fun _ => univ.sup' univ_nonempty (fun m => g m - w m)) :=
        ν.exp_mono fun m =>
          Finset.le_sup' (fun m' => g m' - w m') (mem_univ m)
    _ = univ.sup' univ_nonempty (fun m => g m - w m) := ν.exp_const _

variable [DecidableEq M]

/-- **The tropical face**: the Dirac family with pointwise gate `w` prices a
gamble as the max-plus contraction with density `-w` — idempotent (Maslov)
integration, the value-level face of the penalty tier. -/
theorem penUpperE_dirac_family (w : M → ℚ) (g : M → ℚ) :
    penUpperE (fun m => FinPMF.dirac m) w g
      = univ.sup' univ_nonempty (fun m => g m - w m) := by
  unfold penUpperE
  exact Finset.sup'_congr _ rfl fun m _ => by rw [FinPMF.exp_dirac]

/-- Dirac attainment for the affinity bound: the bound
`exp_sub_exp_le_sup_sub` is met with equality on the Dirac at the best
point, so the sup over all laws *is* the max over points. -/
theorem dirac_attains_sup_sub (g w : M → ℚ) :
    ∃ m₀ : M, (FinPMF.dirac m₀).exp g - (FinPMF.dirac m₀).exp w
      = univ.sup' univ_nonempty (fun m => g m - w m) := by
  obtain ⟨m₀, _, h⟩ := Finset.exists_mem_eq_sup' (univ_nonempty)
    fun m => g m - w m
  exact ⟨m₀, by rw [FinPMF.exp_dirac, FinPMF.exp_dirac, h]⟩

end Tropical

section Legendre

variable {X : Type*} [Fintype X] {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
private theorem sublevel_nonempty (c : ι → ℚ) (i₀ : ι) :
    (univ.filter fun j => c j ≤ c i₀).Nonempty :=
  ⟨i₀, by simp⟩

/-- The threshold profile of a penalty presentation: the credal (wall-tier)
upper envelope over the sublevel family `{j | c j ≤ c i₀}`.  Sublevel bodies
are ordinary credal data — this is the object the wall tier already
carries. -/
def levelProfile (M : ι → FinPMF X) (c : ι → ℚ) (f : X → ℚ) (i₀ : ι) : ℚ :=
  (univ.filter fun j => c j ≤ c i₀).sup' (sublevel_nonempty c i₀)
    fun j => (M j).exp f

/-- **The finite Legendre transform**: the convex-prevision scalar is
recovered from the threshold profile as `max_t (profile t - t)`, thresholds
ranging over attained costs.  The soft tier therefore needs no new judgment
vocabulary: its scalar is derivable from the sublevel (wall-tier) profile in
one transform. -/
theorem penUpperE_eq_sup_levelProfile (M : ι → FinPMF X) (c : ι → ℚ)
    (f : X → ℚ) :
    penUpperE M c f
      = univ.sup' univ_nonempty (fun i₀ => levelProfile M c f i₀ - c i₀) := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := exists_eq_penUpperE M c f
    have hmem : i ∈ univ.filter fun j => c j ≤ c i := by simp
    have hprof : (M i).exp f ≤ levelProfile M c f i :=
      Finset.le_sup' (fun j => (M j).exp f) hmem
    calc penUpperE M c f = (M i).exp f - c i := hi
      _ ≤ levelProfile M c f i - c i := by linarith
      _ ≤ univ.sup' univ_nonempty (fun i₀ => levelProfile M c f i₀ - c i₀) :=
          Finset.le_sup' (fun i₀ => levelProfile M c f i₀ - c i₀) (mem_univ i)
  · refine Finset.sup'_le _ _ fun i₀ _ => ?_
    obtain ⟨j, hj_mem, hj_eq⟩ := Finset.exists_mem_eq_sup'
      (sublevel_nonempty c i₀) fun j => (M j).exp f
    have hcj : c j ≤ c i₀ := (Finset.mem_filter.mp hj_mem).2
    have hb := exp_sub_le_penUpperE M c f j
    rw [levelProfile, hj_eq]
    linarith

end Legendre

namespace Mutants

/-- **Positive homogeneity fails off the calibrated face**: with a single
member of cost `1` and the zero gamble, doubling the gamble does not double
the price (`-1 ≠ -2`).  The penalty tier is convex-prevision, strictly wider
than the coherent (positively homogeneous) tier; calibration is exactly what
the failure witnesses. -/
theorem penUpperE_not_posHomogeneous :
    penUpperE (fun _ : Unit => FinPMF.dirac (default : Unit)) (fun _ => 1)
        (fun x => (2 : ℚ) * (fun _ : Unit => (0 : ℚ)) x)
      ≠ 2 * penUpperE (fun _ : Unit => FinPMF.dirac (default : Unit))
          (fun _ => 1) (fun _ : Unit => (0 : ℚ)) := by
  rw [penUpperE_unique, penUpperE_unique, FinPMF.exp_dirac, FinPMF.exp_dirac]
  norm_num

end Mutants

end Qtsl.Imprecise
