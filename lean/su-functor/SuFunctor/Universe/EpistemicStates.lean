import SuFunctor.Universe.HausdorffKL
import SuFunctor.Universe.CredalPoset.Defs
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence

/-! # Epistemic states on a product record space: conditional beliefs,
independence beliefs, and what composition does not assume

The Semantic Universe chapter's epistemic-states example, mechanized at
the finite stratum.  The record space factors, `A × B`; the two
epistemic states of everyday modelling practice are compiled as penalty
functionals on the flat carrier `ProbState (A × B)` of
`SuFunctor.Universe.ProbCarrier`, with relative entropy `klq` from
`SuFunctor.Universe.HausdorffKL`.

Main results (all on finite `A`, `B`; penalties `ℝ≥0∞`-valued, so
nonnegativity holds by type and the substantive "zero iff" content is
the zero-set characterizations):

**Independence beliefs** — `indepPenalty β μ = β · D(μ ‖ μ_X ⊗ μ_Y)`,
the mutual-information penalty:

* `absCont_prodMarg` / `mutualInfoQ_ne_top` — a joint law is always
  absolutely continuous in its own marginal product: no wall;
* `mutualInfoQ_eq_zero_iff` — zero exactly on the product laws
  (strict Gibbs);
* `continuous_mutualInfoQ` — on the finite stratum the mutual
  information is continuous *outright* (entropy decomposition into
  `x ↦ x · log x` sums);
* `Witness.not_penaltyConvex_indepPenalty` — **nothing here is
  convex**: mixing `δ_{(0,0)}` with `δ_{(1,1)}` in equal parts
  manufactures perfect correlation from two deterministic
  independencies (exact rationals);
* `isCredalBody_indepBody` / `not_convexBody_indepBody` /
  `indepBody_credalBody_not_convex` — the crisp independence body (the
  radial compile of the product-law wall) is a credal body and **not**
  a convex credal body: independence beliefs are the ordinary
  inhabitant of CB ∖ CV in the credal-body atlas.

**Conditional beliefs** — `condPenalty β k μ = β · D(μ ‖ μ_Y ⋉ k)`,
the scaled conditional relative entropy of Richardson's weakening:

* `bindState` / `sndMarg_bindState` — the joint `μ_Y ⋉ k` with
  `Y`-marginal `μ_Y` and conditional `k`;
* `condTarget_mix` — `μ ↦ μ_Y ⋉ k` is affine (proved, not assumed);
* `klq_condTarget_eq_zero_iff` / `condPenalty_eq_zero_iff` — zero
  exactly when the disintegration along `Y` agrees with `k` at every
  `y` of positive `μ_Y`-mass; the joint-coordinate form
  `klq_condTarget_eq_zero_iff'` absorbs the null-`y` clause, since the
  reconstruction charges null columns nothing;
* `klq_mix_mix_le` — **joint convexity of relative entropy** on the
  finite simplex (via the two-point log-sum inequality
  `two_point_log_sum`, from convexity of `x ↦ x · log x`);
* `penaltyConvex_condPenalty` — the conditional penalty is convex:
  joint convexity through the affine target map;
* `lowerSemicontinuous_klq_pair` — relative entropy is jointly lower
  semicontinuous on the finite stratum (`klq` is the supremum of the
  continuous denominator-smoothed approximants `klBelow`);
* `lowerSemicontinuous_condPenalty` — the conditional penalty is a
  citizen; the wall is real when `k` has zeros, so lower
  semicontinuity, not continuity, is the honest statement.

**What composition does not assume** — penalties that read only their
own factor's marginal:

* `marginalSum_eq_zero_iff` — a sum of marginal-reading penalties
  vanishes exactly when each marginal lies in its own zero set: the
  composite constrains marginals, jointly, and nothing else;
* `marginalWallSum_eq_probWall_frechet` / `compile_marginalWallSum` —
  at the crisp level the composite body is the radial embedding of the
  whole **Fréchet class** `frechetClass M_X M_Y`; the independent
  coupling only witnesses its nonemptiness;
* `Witness.frechet_does_not_imply_independence` — the correlated
  coupling of two uniform marginals has zero composite penalty under
  the two singleton-uniform walls while failing independence with
  strictly positive mutual information: sums of marginal-reading
  penalties cannot manufacture a correlation constraint.

Everything is elementary finite-sum bookkeeping over `Real.log`,
following the conventions of `SuFunctor.Universe.HausdorffKL`
(`Real.log 0 = 0`, the `⊤`-guards written into `klq`). -/

namespace SuFunctor.Universe

open scoped ENNReal
open Finset

namespace EpistemicStates

open HausdorffKL CredalPoset

/-! ## Marginals, product laws, and the kernel bind -/

section Marginals

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The first (`X`-)marginal of a joint law on `A × B`. -/
def fstMarg (μ : ProbState (A × B)) : ProbState A :=
  ⟨fun a => ∑ b, (μ : A × B → ℝ) (a, b),
    ⟨fun a => Finset.sum_nonneg fun b _ => μ.nonneg (a, b), by
      rw [← Fintype.sum_prod_type]
      exact μ.sum_eq_one⟩⟩

/-- The second (`Y`-)marginal of a joint law on `A × B`. -/
def sndMarg (μ : ProbState (A × B)) : ProbState B :=
  ⟨fun b => ∑ a, (μ : A × B → ℝ) (a, b),
    ⟨fun b => Finset.sum_nonneg fun a _ => μ.nonneg (a, b), by
      rw [← Fintype.sum_prod_type_right]
      exact μ.sum_eq_one⟩⟩

@[simp] theorem fstMarg_apply (μ : ProbState (A × B)) (a : A) :
    (fstMarg μ : A → ℝ) a = ∑ b, (μ : A × B → ℝ) (a, b) := rfl

@[simp] theorem sndMarg_apply (μ : ProbState (A × B)) (b : B) :
    (sndMarg μ : B → ℝ) b = ∑ a, (μ : A × B → ℝ) (a, b) := rfl

/-- A joint coordinate is dominated by its first marginal. -/
theorem apply_le_fstMarg (μ : ProbState (A × B)) (a : A) (b : B) :
    (μ : A × B → ℝ) (a, b) ≤ (fstMarg μ : A → ℝ) a :=
  Finset.single_le_sum (f := fun b => (μ : A × B → ℝ) (a, b))
    (fun b _ => μ.nonneg (a, b)) (Finset.mem_univ b)

/-- A joint coordinate is dominated by its second marginal. -/
theorem apply_le_sndMarg (μ : ProbState (A × B)) (a : A) (b : B) :
    (μ : A × B → ℝ) (a, b) ≤ (sndMarg μ : B → ℝ) b :=
  Finset.single_le_sum (f := fun a => (μ : A × B → ℝ) (a, b))
    (fun a _ => μ.nonneg (a, b)) (Finset.mem_univ a)

theorem continuous_fstMarg :
    Continuous (fstMarg (A := A) (B := B)) := by
  refine Continuous.subtype_mk (continuous_pi fun a => ?_) _
  exact continuous_finset_sum _ fun b _ =>
    (continuous_apply (a, b)).comp continuous_subtype_val

theorem continuous_sndMarg :
    Continuous (sndMarg (A := A) (B := B)) := by
  refine Continuous.subtype_mk (continuous_pi fun b => ?_) _
  exact continuous_finset_sum _ fun a _ =>
    (continuous_apply (a, b)).comp continuous_subtype_val

/-- The product law `p ⊗ q` on `A × B`. -/
def prodState (p : ProbState A) (q : ProbState B) : ProbState (A × B) :=
  ⟨fun x => (p : A → ℝ) x.1 * (q : B → ℝ) x.2,
    ⟨fun x => mul_nonneg (p.nonneg x.1) (q.nonneg x.2), by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, ProbState.sum_eq_one, mul_one]⟩⟩

@[simp] theorem prodState_apply (p : ProbState A) (q : ProbState B)
    (x : A × B) :
    (prodState p q : A × B → ℝ) x
      = (p : A → ℝ) x.1 * (q : B → ℝ) x.2 := rfl

/-- The marginals of a product law are its factors (first). -/
theorem fstMarg_prodState (p : ProbState A) (q : ProbState B) :
    fstMarg (prodState p q) = p := by
  refine Subtype.ext (funext fun a => ?_)
  show ∑ b, (p : A → ℝ) a * (q : B → ℝ) b = (p : A → ℝ) a
  rw [← Finset.mul_sum, q.sum_eq_one, mul_one]

/-- The marginals of a product law are its factors (second). -/
theorem sndMarg_prodState (p : ProbState A) (q : ProbState B) :
    sndMarg (prodState p q) = q := by
  refine Subtype.ext (funext fun b => ?_)
  show ∑ a, (p : A → ℝ) a * (q : B → ℝ) b = (q : B → ℝ) b
  rw [← Finset.sum_mul, p.sum_eq_one, one_mul]

/-- A joint law is a **product law** when it factors through some pair
of marginal laws. -/
def IsProductLaw (μ : ProbState (A × B)) : Prop :=
  ∃ (p : ProbState A) (q : ProbState B), μ = prodState p q

/-- A joint law is a product law iff it is the product of its *own*
marginals. -/
theorem isProductLaw_iff (μ : ProbState (A × B)) :
    IsProductLaw μ ↔ μ = prodState (fstMarg μ) (sndMarg μ) := by
  constructor
  · rintro ⟨p, q, rfl⟩
    rw [fstMarg_prodState, sndMarg_prodState]
  · intro h
    exact ⟨fstMarg μ, sndMarg μ, h⟩

/-- Point masses are product laws. -/
theorem dirac_prodState [DecidableEq A] [DecidableEq B] (a : A) (b : B) :
    ProbState.dirac (a, b)
      = prodState (ProbState.dirac a) (ProbState.dirac b) := by
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨x₁, x₂⟩ := x
  rw [prodState_apply]
  by_cases h₁ : x₁ = a
  · by_cases h₂ : x₂ = b
    · subst h₁; subst h₂
      rw [ProbState.dirac_apply_same, ProbState.dirac_apply_same,
        ProbState.dirac_apply_same, mul_one]
    · have hne : (x₁, x₂) ≠ (a, b) := fun hc => h₂ (congrArg Prod.snd hc)
      rw [ProbState.dirac_apply_of_ne hne,
        ProbState.dirac_apply_of_ne h₂, mul_zero]
  · have hne : (x₁, x₂) ≠ (a, b) := fun hc => h₁ (congrArg Prod.fst hc)
    rw [ProbState.dirac_apply_of_ne hne,
      ProbState.dirac_apply_of_ne h₁, zero_mul]

theorem isProductLaw_dirac [DecidableEq A] [DecidableEq B] (v : A × B) :
    IsProductLaw (ProbState.dirac v) :=
  ⟨ProbState.dirac v.1, ProbState.dirac v.2, by
    obtain ⟨a, b⟩ := v
    exact dirac_prodState a b⟩

/-- The product-of-own-marginals map is continuous. -/
theorem continuous_prodMarg :
    Continuous fun μ : ProbState (A × B) =>
      prodState (fstMarg μ) (sndMarg μ) := by
  refine Continuous.subtype_mk (continuous_pi fun x => ?_) _
  exact (continuous_finset_sum _ fun b _ =>
      (continuous_apply (x.1, b)).comp continuous_subtype_val).mul
    (continuous_finset_sum _ fun a _ =>
      (continuous_apply (a, x.2)).comp continuous_subtype_val)

/-- The set of product laws is closed: the crisp independence belief is
wall-able. -/
theorem isClosed_productLaws :
    IsClosed {μ : ProbState (A × B) | IsProductLaw μ} := by
  have h : {μ : ProbState (A × B) | IsProductLaw μ}
      = {μ : ProbState (A × B) | μ = prodState (fstMarg μ) (sndMarg μ)} :=
    Set.ext fun μ => isProductLaw_iff μ
  rw [h]
  exact isClosed_eq continuous_id continuous_prodMarg

/-- The joint `μ_Y ⋉ k` with second marginal `q` and conditional `k`:
the kernel bind of the epistemic-states example. -/
def bindState (q : ProbState B) (k : B → ProbState A) :
    ProbState (A × B) :=
  ⟨fun x => (q : B → ℝ) x.2 * (k x.2 : A → ℝ) x.1,
    ⟨fun x => mul_nonneg (q.nonneg x.2) ((k x.2).nonneg x.1), by
      rw [Fintype.sum_prod_type_right]
      simp only [← Finset.mul_sum, ProbState.sum_eq_one, mul_one]⟩⟩

@[simp] theorem bindState_apply (q : ProbState B) (k : B → ProbState A)
    (x : A × B) :
    (bindState q k : A × B → ℝ) x
      = (q : B → ℝ) x.2 * (k x.2 : A → ℝ) x.1 := rfl

/-- The bind has the prescribed second marginal. -/
theorem sndMarg_bindState (q : ProbState B) (k : B → ProbState A) :
    sndMarg (bindState q k) = q := by
  refine Subtype.ext (funext fun b => ?_)
  show ∑ a, (q : B → ℝ) b * (k b : A → ℝ) a = (q : B → ℝ) b
  rw [← Finset.mul_sum, (k b).sum_eq_one, mul_one]

/-- Marginalization is affine (second coordinate). -/
theorem sndMarg_mix {μ ν : ProbState (A × B)} {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    sndMarg (ProbState.mix s t hs ht hst μ ν)
      = ProbState.mix s t hs ht hst (sndMarg μ) (sndMarg ν) := by
  refine Subtype.ext (funext fun b => ?_)
  show ∑ a, (s • (μ : A × B → ℝ) + t • (ν : A × B → ℝ)) (a, b)
      = (s • (sndMarg μ : B → ℝ) + t • (sndMarg ν : B → ℝ)) b
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sndMarg_apply,
    Finset.mul_sum]
  rw [Finset.sum_add_distrib]

/-- Marginalization is affine (first coordinate). -/
theorem fstMarg_mix {μ ν : ProbState (A × B)} {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    fstMarg (ProbState.mix s t hs ht hst μ ν)
      = ProbState.mix s t hs ht hst (fstMarg μ) (fstMarg ν) := by
  refine Subtype.ext (funext fun a => ?_)
  show ∑ b, (s • (μ : A × B → ℝ) + t • (ν : A × B → ℝ)) (a, b)
      = (s • (fstMarg μ : A → ℝ) + t • (fstMarg ν : A → ℝ)) a
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, fstMarg_apply,
    Finset.mul_sum]
  rw [Finset.sum_add_distrib]

end Marginals

/-! ## The two-point log-sum inequality, and joint convexity of `klq`

The engine of the conditional family: relative entropy is jointly
convex on the finite simplex.  The pointwise fact is the two-term
log-sum inequality, which is convexity of `x ↦ x · log x` (Jensen with
weights `b₁/(b₁+b₂)`, `b₂/(b₁+b₂)`); summing coordinatewise and
bookkeeping the `⊤`-guards gives the `ℝ≥0∞` statement in exactly the
`PenaltyConvex` shape of `SuFunctor.Universe.CredalPoset`. -/

section Convexity

variable {V : Type*} [Fintype V]

/-- **The two-point log-sum inequality**: for nonnegative masses with
the null-domination side conditions,
`(a₁+a₂) log((a₁+a₂)/(b₁+b₂)) ≤ a₁ log(a₁/b₁) + a₂ log(a₂/b₂)`. -/
theorem two_point_log_sum {a₁ a₂ b₁ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (h₁ : b₁ = 0 → a₁ = 0) (h₂ : b₂ = 0 → a₂ = 0) :
    (a₁ + a₂) * Real.log ((a₁ + a₂) / (b₁ + b₂))
      ≤ a₁ * Real.log (a₁ / b₁) + a₂ * Real.log (a₂ / b₂) := by
  rcases hb₁.eq_or_lt with hb₁0 | hb₁pos
  · obtain rfl : b₁ = 0 := hb₁0.symm
    obtain rfl : a₁ = 0 := h₁ rfl
    simp
  · rcases hb₂.eq_or_lt with hb₂0 | hb₂pos
    · obtain rfl : b₂ = 0 := hb₂0.symm
      obtain rfl : a₂ = 0 := h₂ rfl
      simp
    · have hB : 0 < b₁ + b₂ := by linarith
      have hw : b₁ / (b₁ + b₂) + b₂ / (b₁ + b₂) = 1 := by
        rw [← add_div, div_self hB.ne']
      have key := (Real.convexOn_mul_log).2
        (Set.mem_Ici.mpr (div_nonneg ha₁ hb₁pos.le))
        (Set.mem_Ici.mpr (div_nonneg ha₂ hb₂pos.le))
        (div_nonneg hb₁ hB.le) (div_nonneg hb₂ hB.le) hw
      simp only [smul_eq_mul] at key
      have harg : b₁ / (b₁ + b₂) * (a₁ / b₁) + b₂ / (b₁ + b₂) * (a₂ / b₂)
          = (a₁ + a₂) / (b₁ + b₂) := by
        field_simp
      rw [harg] at key
      have hmul := mul_le_mul_of_nonneg_left key hB.le
      calc (a₁ + a₂) * Real.log ((a₁ + a₂) / (b₁ + b₂))
          = (b₁ + b₂) * ((a₁ + a₂) / (b₁ + b₂)
              * Real.log ((a₁ + a₂) / (b₁ + b₂))) := by
            field_simp
        _ ≤ (b₁ + b₂) * (b₁ / (b₁ + b₂)
              * (a₁ / b₁ * Real.log (a₁ / b₁))
            + b₂ / (b₁ + b₂) * (a₂ / b₂ * Real.log (a₂ / b₂))) := hmul
        _ = a₁ * Real.log (a₁ / b₁) + a₂ * Real.log (a₂ / b₂) := by
            field_simp

/-- Scaling both entries of a KL term by a common nonnegative factor
scales the term, under the null-domination guard. -/
private theorem scale_kl_term {s x y : ℝ} (hs : 0 ≤ s)
    (hxy : y = 0 → x = 0) :
    s * x * Real.log (s * x / (s * y)) = s * (x * Real.log (x / y)) := by
  rcases hs.eq_or_lt with hs0 | hspos
  · obtain rfl : s = 0 := hs0.symm
    simp
  · rcases eq_or_ne y 0 with hy0 | hy0
    · obtain rfl : x = 0 := hxy hy0
      simp
    · have hdiv : s * x / (s * y) = x / y := by
        field_simp
      rw [hdiv]
      ring

/-- **Joint convexity of the real KL sum** on the finite simplex, both
pairs absolutely continuous. -/
theorem klReal_mix_mix_le {μ ν ρ σ : ProbState V}
    (hμρ : AbsCont μ ρ) (hνσ : AbsCont ν σ) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    klReal (ProbState.mix s t hs ht hst μ ν)
        (ProbState.mix s t hs ht hst ρ σ)
      ≤ s * klReal μ ρ + t * klReal ν σ := by
  have hterm : ∀ v : V,
      (s * (μ : V → ℝ) v + t * (ν : V → ℝ) v)
          * Real.log ((s * (μ : V → ℝ) v + t * (ν : V → ℝ) v)
            / (s * (ρ : V → ℝ) v + t * (σ : V → ℝ) v))
        ≤ s * ((μ : V → ℝ) v * Real.log ((μ : V → ℝ) v / (ρ : V → ℝ) v))
          + t * ((ν : V → ℝ) v
              * Real.log ((ν : V → ℝ) v / (σ : V → ℝ) v)) := by
    intro v
    have h2p := two_point_log_sum
      (mul_nonneg hs (μ.nonneg v)) (mul_nonneg ht (ν.nonneg v))
      (mul_nonneg hs (ρ.nonneg v)) (mul_nonneg ht (σ.nonneg v))
      (fun h => by
        rcases mul_eq_zero.mp h with h | h
        · rw [h, zero_mul]
        · rw [hμρ v h, mul_zero])
      (fun h => by
        rcases mul_eq_zero.mp h with h | h
        · rw [h, zero_mul]
        · rw [hνσ v h, mul_zero])
    calc (s * (μ : V → ℝ) v + t * (ν : V → ℝ) v)
          * Real.log ((s * (μ : V → ℝ) v + t * (ν : V → ℝ) v)
            / (s * (ρ : V → ℝ) v + t * (σ : V → ℝ) v))
        ≤ s * (μ : V → ℝ) v
            * Real.log (s * (μ : V → ℝ) v / (s * (ρ : V → ℝ) v))
          + t * (ν : V → ℝ) v
            * Real.log (t * (ν : V → ℝ) v / (t * (σ : V → ℝ) v)) := h2p
      _ = s * ((μ : V → ℝ) v * Real.log ((μ : V → ℝ) v / (ρ : V → ℝ) v))
          + t * ((ν : V → ℝ) v
              * Real.log ((ν : V → ℝ) v / (σ : V → ℝ) v)) := by
          rw [scale_kl_term hs (hμρ v), scale_kl_term ht (hνσ v)]
  show ∑ v, ((ProbState.mix s t hs ht hst μ ν : ProbState V) : V → ℝ) v
      * Real.log
        (((ProbState.mix s t hs ht hst μ ν : ProbState V) : V → ℝ) v
          / ((ProbState.mix s t hs ht hst ρ σ : ProbState V) : V → ℝ) v)
    ≤ s * klReal μ ρ + t * klReal ν σ
  simp only [ProbState.coe_mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc ∑ v, (s * (μ : V → ℝ) v + t * (ν : V → ℝ) v)
        * Real.log ((s * (μ : V → ℝ) v + t * (ν : V → ℝ) v)
          / (s * (ρ : V → ℝ) v + t * (σ : V → ℝ) v))
      ≤ ∑ v, (s * ((μ : V → ℝ) v
            * Real.log ((μ : V → ℝ) v / (ρ : V → ℝ) v))
          + t * ((ν : V → ℝ) v
            * Real.log ((ν : V → ℝ) v / (σ : V → ℝ) v))) :=
        Finset.sum_le_sum fun v _ => hterm v
    _ = s * klReal μ ρ + t * klReal ν σ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rfl

/-- Strictly interior mixtures preserve absolute continuity pairwise. -/
theorem absCont_mix {μ ν ρ σ : ProbState V}
    (hμρ : AbsCont μ ρ) (hνσ : AbsCont ν σ) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1) :
    AbsCont (ProbState.mix s t hs.le ht.le hst μ ν)
      (ProbState.mix s t hs.le ht.le hst ρ σ) := by
  intro v hv
  simp only [ProbState.coe_mix, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at hv ⊢
  have hsρ : s * (ρ : V → ℝ) v = 0 :=
    le_antisymm (by nlinarith [mul_nonneg ht.le (σ.nonneg v)])
      (mul_nonneg hs.le (ρ.nonneg v))
  have htσ : t * (σ : V → ℝ) v = 0 :=
    le_antisymm (by nlinarith [mul_nonneg hs.le (ρ.nonneg v)])
      (mul_nonneg ht.le (σ.nonneg v))
  have hρ0 : (ρ : V → ℝ) v = 0 := by
    rcases mul_eq_zero.mp hsρ with h | h
    · exact absurd h hs.ne'
    · exact h
  have hσ0 : (σ : V → ℝ) v = 0 := by
    rcases mul_eq_zero.mp htσ with h | h
    · exact absurd h ht.ne'
    · exact h
  rw [hμρ v hρ0, hνσ v hσ0, mul_zero, mul_zero, add_zero]

/-- **Joint convexity of relative entropy**, total in `ℝ≥0∞`, strictly
interior weights (the `PenaltyConvex` shape): every `⊤` case
included. -/
theorem klq_mix_mix_le {μ ν ρ σ : ProbState V} {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1) :
    klq (ProbState.mix s t hs.le ht.le hst μ ν)
        (ProbState.mix s t hs.le ht.le hst ρ σ)
      ≤ ENNReal.ofReal s * klq μ ρ + ENNReal.ofReal t * klq ν σ := by
  by_cases hμρ : AbsCont μ ρ
  · by_cases hνσ : AbsCont ν σ
    · have hmix := absCont_mix hμρ hνσ hs ht hst
      rw [klq, if_pos hmix, klq, if_pos hμρ, klq, if_pos hνσ]
      calc ENNReal.ofReal
            (klReal (ProbState.mix s t hs.le ht.le hst μ ν)
              (ProbState.mix s t hs.le ht.le hst ρ σ))
          ≤ ENNReal.ofReal (s * klReal μ ρ + t * klReal ν σ) :=
            ENNReal.ofReal_le_ofReal
              (klReal_mix_mix_le hμρ hνσ hs.le ht.le hst)
        _ = ENNReal.ofReal (s * klReal μ ρ)
              + ENNReal.ofReal (t * klReal ν σ) :=
            ENNReal.ofReal_add
              (mul_nonneg hs.le (klReal_nonneg hμρ))
              (mul_nonneg ht.le (klReal_nonneg hνσ))
        _ = ENNReal.ofReal s * ENNReal.ofReal (klReal μ ρ)
              + ENNReal.ofReal t * ENNReal.ofReal (klReal ν σ) := by
            rw [ENNReal.ofReal_mul hs.le, ENNReal.ofReal_mul ht.le]
    · have htop : klq ν σ = ⊤ := by rw [klq, if_neg hνσ]
      rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr ht).ne', add_top]
      exact le_top
  · have htop : klq μ ρ = ⊤ := by rw [klq, if_neg hμρ]
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hs).ne', top_add]
    exact le_top

end Convexity

/-! ## Joint lower semicontinuity of `klq`

Relative entropy is the supremum of its denominator-smoothed
approximants `klBelow n μ ν = ∑ᵥ (μᵥ log μᵥ − μᵥ log (νᵥ + 1/(n+1)))`,
each of which is (jointly) continuous; a supremum of continuous
functions is lower semicontinuous.  The identity holds walls included:
at a violation of absolute continuity the approximants grow without
bound. -/

section Lsc

variable {V : Type*} [Fintype V]

/-- The denominator-smoothed KL approximant (entropy-split form: no
division, hence total and continuous). -/
noncomputable def klBelow (n : ℕ) (μ ν : ProbState V) : ℝ :=
  ∑ v, ((μ : V → ℝ) v * Real.log ((μ : V → ℝ) v)
    - (μ : V → ℝ) v * Real.log ((ν : V → ℝ) v + ((n : ℝ) + 1)⁻¹))

theorem klBelow_mono (μ ν : ProbState V) :
    Monotone fun n => klBelow n μ ν := by
  intro m n hmn
  refine Finset.sum_le_sum fun v _ => ?_
  have hcast : ((m : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hden : (ν : V → ℝ) v + ((n : ℝ) + 1)⁻¹
      ≤ (ν : V → ℝ) v + ((m : ℝ) + 1)⁻¹ := by
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hle : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
    have h := one_div_le_one_div_of_le hm hle
    rw [one_div, one_div] at h
    linarith
  have hpos : (0 : ℝ) < (ν : V → ℝ) v + ((n : ℝ) + 1)⁻¹ :=
    add_pos_of_nonneg_of_pos (ν.nonneg v) (by positivity)
  have hlog := Real.log_le_log hpos hden
  have := mul_le_mul_of_nonneg_left hlog (μ.nonneg v)
  linarith

/-- Each approximant is jointly continuous. -/
theorem continuous_klBelow (n : ℕ) :
    Continuous fun p : ProbState V × ProbState V =>
      klBelow n p.1 p.2 := by
  refine continuous_finset_sum _ fun v _ => ?_
  have hμ : Continuous fun p : ProbState V × ProbState V =>
      (p.1 : V → ℝ) v :=
    (continuous_apply v).comp (continuous_subtype_val.comp continuous_fst)
  have hν : Continuous fun p : ProbState V × ProbState V =>
      (p.2 : V → ℝ) v :=
    (continuous_apply v).comp (continuous_subtype_val.comp continuous_snd)
  have hden : Continuous fun p : ProbState V × ProbState V =>
      (p.2 : V → ℝ) v + ((n : ℝ) + 1)⁻¹ := hν.add continuous_const
  have hlogden : Continuous fun p : ProbState V × ProbState V =>
      Real.log ((p.2 : V → ℝ) v + ((n : ℝ) + 1)⁻¹) := by
    rw [continuous_iff_continuousAt]
    intro p
    have hpos : (0 : ℝ) < (p.2 : V → ℝ) v + ((n : ℝ) + 1)⁻¹ :=
      add_pos_of_nonneg_of_pos (p.2.nonneg v) (by positivity)
    exact ContinuousAt.comp (g := Real.log)
      (f := fun p : ProbState V × ProbState V =>
        (p.2 : V → ℝ) v + ((n : ℝ) + 1)⁻¹)
      (x := p) (Real.continuousAt_log hpos.ne') hden.continuousAt
  exact (Real.continuous_mul_log.comp hμ).sub (hμ.mul hlogden)

/-- Under absolute continuity, the real KL sum splits into entropy
differences. -/
theorem klReal_eq_split {μ ν : ProbState V} (h : AbsCont μ ν) :
    klReal μ ν = ∑ v, ((μ : V → ℝ) v * Real.log ((μ : V → ℝ) v)
      - (μ : V → ℝ) v * Real.log ((ν : V → ℝ) v)) := by
  refine Finset.sum_congr rfl fun v _ => ?_
  rcases (μ.nonneg v).eq_or_lt with hz | hpos
  · rw [← hz]
    ring
  · have hν0 : (ν : V → ℝ) v ≠ 0 := fun e => hpos.ne' (h v e)
    rw [Real.log_div hpos.ne' hν0]
    ring

/-- The approximants sit below the KL sum (absolutely continuous
case). -/
theorem klBelow_le_klReal {μ ν : ProbState V} (h : AbsCont μ ν) (n : ℕ) :
    klBelow n μ ν ≤ klReal μ ν := by
  rw [klReal_eq_split h]
  refine Finset.sum_le_sum fun v _ => ?_
  rcases (μ.nonneg v).eq_or_lt with hz | hpos
  · rw [← hz]
    simp
  · have hν0 : (ν : V → ℝ) v ≠ 0 := fun e => hpos.ne' (h v e)
    have hνpos : 0 < (ν : V → ℝ) v := (ν.nonneg v).lt_of_ne (Ne.symm hν0)
    have hlog := Real.log_le_log hνpos
      (le_add_of_nonneg_right
        (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹))
    have := mul_le_mul_of_nonneg_left hlog hpos.le
    linarith

/-- The approximants converge to the KL sum (absolutely continuous
case). -/
theorem tendsto_klBelow {μ ν : ProbState V} (h : AbsCont μ ν) :
    Filter.Tendsto (fun n => klBelow n μ ν) Filter.atTop
      (nhds (klReal μ ν)) := by
  rw [klReal_eq_split h]
  refine tendsto_finset_sum _ fun v _ => ?_
  rcases (μ.nonneg v).eq_or_lt with hz | hpos
  · rw [← hz]
    simpa using tendsto_const_nhds
  · have hν0 : (ν : V → ℝ) v ≠ 0 := fun e => hpos.ne' (h v e)
    have hνpos : 0 < (ν : V → ℝ) v := (ν.nonneg v).lt_of_ne (Ne.symm hν0)
    have hinv : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹)
        Filter.atTop (nhds 0) := by
      have h1 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa [one_div] using h1
    have hden : Filter.Tendsto
        (fun n : ℕ => (ν : V → ℝ) v + ((n : ℝ) + 1)⁻¹)
        Filter.atTop (nhds ((ν : V → ℝ) v)) := by
      have h2 := hinv.const_add ((ν : V → ℝ) v)
      simpa using h2
    have hlog : Filter.Tendsto
        (fun n : ℕ => Real.log ((ν : V → ℝ) v + ((n : ℝ) + 1)⁻¹))
        Filter.atTop (nhds (Real.log ((ν : V → ℝ) v))) :=
      ((Real.continuousAt_log hνpos.ne').tendsto).comp hden
    exact tendsto_const_nhds.sub (hlog.const_mul _)

/-- Every approximant term is bounded below by `−2` on the carrier. -/
private theorem klBelow_term_lb (μ ν : ProbState V) (n : ℕ) (v : V) :
    (-2 : ℝ) ≤ (μ : V → ℝ) v * Real.log ((μ : V → ℝ) v)
      - (μ : V → ℝ) v * Real.log ((ν : V → ℝ) v + ((n : ℝ) + 1)⁻¹) := by
  have hself : (-1 : ℝ) ≤ (μ : V → ℝ) v * Real.log ((μ : V → ℝ) v) := by
    have h1 := Real.self_sub_one_le_mul_log (μ.nonneg v)
    have h2 := μ.nonneg v
    linarith
  have hinv1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
    have h0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hc := mul_inv_cancel₀ h0.ne'
    nlinarith [inv_nonneg.mpr h0.le, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  have hden2 : (ν : V → ℝ) v + ((n : ℝ) + 1)⁻¹ ≤ 2 := by
    have := ν.apply_le_one v
    linarith
  have hdenpos : (0 : ℝ) < (ν : V → ℝ) v + ((n : ℝ) + 1)⁻¹ :=
    add_pos_of_nonneg_of_pos (ν.nonneg v) (by positivity)
  have hlog2 : Real.log ((ν : V → ℝ) v + ((n : ℝ) + 1)⁻¹) ≤ 1 := by
    have h := Real.log_le_log hdenpos hden2
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have hupper : (μ : V → ℝ) v
      * Real.log ((ν : V → ℝ) v + ((n : ℝ) + 1)⁻¹) ≤ 1 := by
    rcases le_or_gt (Real.log ((ν : V → ℝ) v + ((n : ℝ) + 1)⁻¹)) 0 with
      hL | hL
    · have := mul_nonpos_of_nonneg_of_nonpos (μ.nonneg v) hL
      linarith
    · calc (μ : V → ℝ) v * Real.log ((ν : V → ℝ) v + ((n : ℝ) + 1)⁻¹)
          ≤ 1 * Real.log ((ν : V → ℝ) v + ((n : ℝ) + 1)⁻¹) :=
            mul_le_mul_of_nonneg_right (μ.apply_le_one v) hL.le
        _ ≤ 1 := by
            rw [one_mul]
            exact hlog2
  linarith

/-- At a violation of absolute continuity the approximants are
unbounded: quantitative lower bound through the offending atom. -/
private theorem klBelow_lb_of_atom {μ ν : ProbState V} {v₀ : V}
    (hν0 : (ν : V → ℝ) v₀ = 0) (n : ℕ) :
    (-1 : ℝ) - 2 * Fintype.card V
        + (μ : V → ℝ) v₀ * Real.log ((n : ℝ) + 1)
      ≤ klBelow n μ ν := by
  classical
  have hmain : (μ : V → ℝ) v₀ * Real.log ((μ : V → ℝ) v₀)
      - (μ : V → ℝ) v₀ * Real.log ((ν : V → ℝ) v₀ + ((n : ℝ) + 1)⁻¹)
      = (μ : V → ℝ) v₀ * Real.log ((μ : V → ℝ) v₀)
        + (μ : V → ℝ) v₀ * Real.log ((n : ℝ) + 1) := by
    rw [hν0, zero_add, Real.log_inv]
    ring
  have hself : (-1 : ℝ) ≤ (μ : V → ℝ) v₀ * Real.log ((μ : V → ℝ) v₀) := by
    have h1 := Real.self_sub_one_le_mul_log (μ.nonneg v₀)
    have h2 := μ.nonneg v₀
    linarith
  have hsplit : klBelow n μ ν
      = ((μ : V → ℝ) v₀ * Real.log ((μ : V → ℝ) v₀)
          - (μ : V → ℝ) v₀
            * Real.log ((ν : V → ℝ) v₀ + ((n : ℝ) + 1)⁻¹))
        + ∑ v ∈ Finset.univ.erase v₀,
          ((μ : V → ℝ) v * Real.log ((μ : V → ℝ) v)
            - (μ : V → ℝ) v
              * Real.log ((ν : V → ℝ) v + ((n : ℝ) + 1)⁻¹)) := by
    rw [klBelow, ← Finset.add_sum_erase _ _ (Finset.mem_univ v₀)]
  have hrest : (-2 : ℝ) * Fintype.card V
      ≤ ∑ v ∈ Finset.univ.erase v₀,
        ((μ : V → ℝ) v * Real.log ((μ : V → ℝ) v)
          - (μ : V → ℝ) v
            * Real.log ((ν : V → ℝ) v + ((n : ℝ) + 1)⁻¹)) := by
    have h1 : ∑ _v ∈ Finset.univ.erase v₀, (-2 : ℝ)
        ≤ ∑ v ∈ Finset.univ.erase v₀,
          ((μ : V → ℝ) v * Real.log ((μ : V → ℝ) v)
            - (μ : V → ℝ) v
              * Real.log ((ν : V → ℝ) v + ((n : ℝ) + 1)⁻¹)) :=
      Finset.sum_le_sum fun v _ => klBelow_term_lb μ ν n v
    have h2 : ∑ _v ∈ Finset.univ.erase v₀, (-2 : ℝ)
        = -2 * ((Finset.univ.erase v₀).card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    have h3 : ((Finset.univ.erase v₀).card : ℝ) ≤ Fintype.card V := by
      have h4 := Finset.card_erase_le (a := v₀) (s := Finset.univ)
      have h5 : (Finset.univ : Finset V).card = Fintype.card V :=
        Finset.card_univ
      exact_mod_cast le_trans h4 (le_of_eq h5)
    linarith
  rw [hsplit, hmain]
  linarith

/-- **`klq` is the supremum of its continuous approximants**, walls
included. -/
theorem klq_eq_iSup_klBelow (μ ν : ProbState V) :
    klq μ ν = ⨆ n, ENNReal.ofReal (klBelow n μ ν) := by
  by_cases hac : AbsCont μ ν
  · rw [klq, if_pos hac]
    have hmono : Monotone fun n => ENNReal.ofReal (klBelow n μ ν) :=
      fun m n hmn => ENNReal.ofReal_le_ofReal (klBelow_mono μ ν hmn)
    have h1 : Filter.Tendsto (fun n => ENNReal.ofReal (klBelow n μ ν))
        Filter.atTop (nhds (ENNReal.ofReal (klReal μ ν))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_klBelow hac)
    have h2 : Filter.Tendsto (fun n => ENNReal.ofReal (klBelow n μ ν))
        Filter.atTop (nhds (⨆ n, ENNReal.ofReal (klBelow n μ ν))) :=
      tendsto_atTop_iSup hmono
    exact tendsto_nhds_unique h1 h2
  · rw [klq, if_neg hac]
    symm
    rw [iSup_eq_top]
    intro b hb
    have hex : ∃ v, (ν : V → ℝ) v = 0 ∧ (μ : V → ℝ) v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hac fun v hv => hcon v hv
    obtain ⟨v₀, hν0, hμ0⟩ := hex
    have hμpos : 0 < (μ : V → ℝ) v₀ :=
      (μ.nonneg v₀).lt_of_ne (Ne.symm hμ0)
    set M : ℝ := max b.toReal 0 with hM
    set K : ℝ := (M + 2 * Fintype.card V + 2) / (μ : V → ℝ) v₀ with hK
    obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp K)
    refine ⟨n, ?_⟩
    have hexp : Real.exp K < (n : ℝ) + 1 := by linarith
    have hlogn : K < Real.log ((n : ℝ) + 1) := by
      calc K = Real.log (Real.exp K) := (Real.log_exp K).symm
        _ < Real.log ((n : ℝ) + 1) :=
          Real.log_lt_log (Real.exp_pos K) hexp
    have hmulK : (μ : V → ℝ) v₀ * K = M + 2 * Fintype.card V + 2 := by
      rw [hK]
      field_simp
    have hmain : M + 2 * Fintype.card V + 2
        < (μ : V → ℝ) v₀ * Real.log ((n : ℝ) + 1) := by
      calc M + 2 * Fintype.card V + 2 = (μ : V → ℝ) v₀ * K := hmulK.symm
        _ < (μ : V → ℝ) v₀ * Real.log ((n : ℝ) + 1) :=
          mul_lt_mul_of_pos_left hlogn hμpos
    have hlb := klBelow_lb_of_atom (μ := μ) hν0 n
    have hklb : M < klBelow n μ ν := by linarith
    have hb' : b ≠ ⊤ := hb.ne
    calc b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hb').symm
      _ < ENNReal.ofReal (klBelow n μ ν) := by
        rw [ENNReal.ofReal_lt_ofReal_iff
          (lt_of_le_of_lt (le_max_right _ _) hklb)]
        exact lt_of_le_of_lt (le_max_left _ _) hklb

/-- **Relative entropy is jointly lower semicontinuous** on the finite
stratum: the topological half of citizenship for every KL-built
penalty. -/
theorem lowerSemicontinuous_klq_pair :
    LowerSemicontinuous fun p : ProbState V × ProbState V =>
      klq p.1 p.2 := by
  have h : (fun p : ProbState V × ProbState V => klq p.1 p.2)
      = fun p => ⨆ n, ENNReal.ofReal (klBelow n p.1 p.2) :=
    funext fun p => klq_eq_iSup_klBelow p.1 p.2
  rw [h]
  exact lowerSemicontinuous_iSup fun n =>
    (ENNReal.continuous_ofReal.comp
      (continuous_klBelow n)).lowerSemicontinuous

/-- Lower semicontinuity composes with continuous state maps: the form
in which KL penalties enter the universe. -/
theorem lowerSemicontinuous_klq_comp {X : Type*} [TopologicalSpace X]
    {F G : X → ProbState V} (hF : Continuous F) (hG : Continuous G) :
    LowerSemicontinuous fun x => klq (F x) (G x) :=
  lowerSemicontinuous_klq_pair.comp_continuous (hF.prodMk hG)

end Lsc

/-! ## Independence beliefs: the mutual-information penalty -/

section Independence

variable {A B : Type*} [Fintype A] [Fintype B]

/-- A joint law is always absolutely continuous in the product of its
own marginals: the mutual-information penalty has no wall. -/
theorem absCont_prodMarg (μ : ProbState (A × B)) :
    AbsCont μ (prodState (fstMarg μ) (sndMarg μ)) := by
  intro x hx
  obtain ⟨a, b⟩ := x
  rcases mul_eq_zero.mp hx with h | h
  · exact le_antisymm (h ▸ apply_le_fstMarg μ a b) (μ.nonneg (a, b))
  · exact le_antisymm (h ▸ apply_le_sndMarg μ a b) (μ.nonneg (a, b))

/-- The mutual information of a joint law, as a penalty height:
`I(X;Y) = D(μ ‖ μ_X ⊗ μ_Y)`. -/
noncomputable def mutualInfoQ (μ : ProbState (A × B)) : ℝ≥0∞ :=
  klq μ (prodState (fstMarg μ) (sndMarg μ))

/-- The independence belief, graded: the mutual-information penalty at
confidence weight `β`. -/
noncomputable def indepPenalty (β : ℝ≥0∞) : ProbPenalty (A × B) :=
  fun μ => β * mutualInfoQ μ

/-- The real mutual information as an entropy difference:
`I = −H(μ) + H(μ_X) + H(μ_Y)`, written with `x · log x` sums (total,
continuous, division-free). -/
noncomputable def miReal (μ : ProbState (A × B)) : ℝ :=
  (∑ x : A × B, (μ : A × B → ℝ) x * Real.log ((μ : A × B → ℝ) x))
    - (∑ a, (fstMarg μ : A → ℝ) a * Real.log ((fstMarg μ : A → ℝ) a))
    - (∑ b, (sndMarg μ : B → ℝ) b * Real.log ((sndMarg μ : B → ℝ) b))

/-- The KL sum against the marginal product is the entropy
decomposition. -/
theorem klReal_prodMarg_eq_miReal (μ : ProbState (A × B)) :
    klReal μ (prodState (fstMarg μ) (sndMarg μ)) = miReal μ := by
  have hsplit : ∀ x : A × B,
      (μ : A × B → ℝ) x
          * Real.log ((μ : A × B → ℝ) x
            / ((fstMarg μ : A → ℝ) x.1 * (sndMarg μ : B → ℝ) x.2))
        = (μ : A × B → ℝ) x * Real.log ((μ : A × B → ℝ) x)
          - (μ : A × B → ℝ) x * Real.log ((fstMarg μ : A → ℝ) x.1)
          - (μ : A × B → ℝ) x * Real.log ((sndMarg μ : B → ℝ) x.2) := by
    intro x
    obtain ⟨a, b⟩ := x
    rcases (μ.nonneg (a, b)).eq_or_lt with hz | hpos
    · rw [← hz]
      ring
    · have hfa : 0 < (fstMarg μ : A → ℝ) a :=
        lt_of_lt_of_le hpos (apply_le_fstMarg μ a b)
      have hsb : 0 < (sndMarg μ : B → ℝ) b :=
        lt_of_lt_of_le hpos (apply_le_sndMarg μ a b)
      rw [Real.log_div hpos.ne' (mul_ne_zero hfa.ne' hsb.ne'),
        Real.log_mul hfa.ne' hsb.ne']
      ring
  have hgroupX : ∑ x : A × B,
      (μ : A × B → ℝ) x * Real.log ((fstMarg μ : A → ℝ) x.1)
      = ∑ a, (fstMarg μ : A → ℝ) a
          * Real.log ((fstMarg μ : A → ℝ) a) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    show ∑ y, (μ : A × B → ℝ) (a, y) * Real.log ((fstMarg μ : A → ℝ) a)
        = (fstMarg μ : A → ℝ) a * Real.log ((fstMarg μ : A → ℝ) a)
    rw [← Finset.sum_mul]
    rfl
  have hgroupY : ∑ x : A × B,
      (μ : A × B → ℝ) x * Real.log ((sndMarg μ : B → ℝ) x.2)
      = ∑ b, (sndMarg μ : B → ℝ) b
          * Real.log ((sndMarg μ : B → ℝ) b) := by
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    show ∑ x, (μ : A × B → ℝ) (x, b) * Real.log ((sndMarg μ : B → ℝ) b)
        = (sndMarg μ : B → ℝ) b * Real.log ((sndMarg μ : B → ℝ) b)
    rw [← Finset.sum_mul]
    rfl
  calc klReal μ (prodState (fstMarg μ) (sndMarg μ))
      = ∑ x : A × B, ((μ : A × B → ℝ) x * Real.log ((μ : A × B → ℝ) x)
          - (μ : A × B → ℝ) x * Real.log ((fstMarg μ : A → ℝ) x.1)
          - (μ : A × B → ℝ) x * Real.log ((sndMarg μ : B → ℝ) x.2)) := by
        rw [klReal]
        exact Finset.sum_congr rfl fun x _ => hsplit x
    _ = miReal μ := by
        rw [miReal, ← hgroupX, ← hgroupY,
          Finset.sum_sub_distrib, Finset.sum_sub_distrib]

/-- The mutual information in `ℝ≥0∞` is the clamped entropy
decomposition — in particular it is finite everywhere. -/
theorem mutualInfoQ_eq_ofReal (μ : ProbState (A × B)) :
    mutualInfoQ μ = ENNReal.ofReal (miReal μ) := by
  rw [mutualInfoQ, klq, if_pos (absCont_prodMarg μ),
    klReal_prodMarg_eq_miReal]

theorem mutualInfoQ_ne_top (μ : ProbState (A × B)) :
    mutualInfoQ μ ≠ ⊤ := by
  rw [mutualInfoQ_eq_ofReal]
  exact ENNReal.ofReal_ne_top

/-- **Strict Gibbs for independence**: the mutual information vanishes
exactly on the product laws. -/
theorem mutualInfoQ_eq_zero_iff (μ : ProbState (A × B)) :
    mutualInfoQ μ = 0 ↔ IsProductLaw μ := by
  rw [mutualInfoQ, klq_eq_zero_iff, ← isProductLaw_iff]

/-- The graded independence penalty vanishes exactly on the product
laws (any nonzero confidence weight). -/
theorem indepPenalty_eq_zero_iff {β : ℝ≥0∞} (hβ : β ≠ 0)
    (μ : ProbState (A × B)) :
    indepPenalty β μ = 0 ↔ IsProductLaw μ := by
  rw [indepPenalty, mul_eq_zero, mutualInfoQ_eq_zero_iff]
  exact or_iff_right hβ

/-- The entropy decomposition is continuous. -/
theorem continuous_miReal :
    Continuous (miReal (A := A) (B := B)) := by
  have hjoint : Continuous fun μ : ProbState (A × B) =>
      ∑ x : A × B, (μ : A × B → ℝ) x * Real.log ((μ : A × B → ℝ) x) :=
    continuous_finset_sum _ fun x _ =>
      Real.continuous_mul_log.comp
        ((continuous_apply x).comp continuous_subtype_val)
  have hX : Continuous fun μ : ProbState (A × B) =>
      ∑ a, (fstMarg μ : A → ℝ) a * Real.log ((fstMarg μ : A → ℝ) a) :=
    continuous_finset_sum _ fun a _ =>
      Real.continuous_mul_log.comp
        (continuous_finset_sum _ fun b _ =>
          (continuous_apply (a, b)).comp continuous_subtype_val)
  have hY : Continuous fun μ : ProbState (A × B) =>
      ∑ b, (sndMarg μ : B → ℝ) b * Real.log ((sndMarg μ : B → ℝ) b) :=
    continuous_finset_sum _ fun b _ =>
      Real.continuous_mul_log.comp
        (continuous_finset_sum _ fun a _ =>
          (continuous_apply (a, b)).comp continuous_subtype_val)
  exact (hjoint.sub hX).sub hY

/-- **On the finite stratum the mutual information is continuous
outright** (not merely lower semicontinuous): the joint dominates its
own marginal product, so no wall interrupts the entropy
decomposition. -/
theorem continuous_mutualInfoQ :
    Continuous (mutualInfoQ (A := A) (B := B)) := by
  have h : mutualInfoQ (A := A) (B := B)
      = fun μ => ENNReal.ofReal (miReal μ) :=
    funext fun μ => mutualInfoQ_eq_ofReal μ
  rw [h]
  exact ENNReal.continuous_ofReal.comp continuous_miReal

/-- The graded independence penalty is continuous for any finite
confidence weight. -/
theorem continuous_indepPenalty {β : ℝ≥0∞} (hβ : β ≠ ⊤) :
    Continuous (indepPenalty (A := A) (B := B) β) :=
  (ENNReal.continuous_const_mul hβ).comp continuous_mutualInfoQ

/-- Citizenship of the graded independence belief. -/
theorem lowerSemicontinuous_indepPenalty {β : ℝ≥0∞} (hβ : β ≠ ⊤) :
    LowerSemicontinuous (indepPenalty (A := A) (B := B) β) :=
  (continuous_indepPenalty hβ).lowerSemicontinuous

/-- Citizenship of the crisp independence belief (the `β → ∞` wall). -/
theorem lowerSemicontinuous_probWall_productLaws :
    LowerSemicontinuous
      (probWall {μ : ProbState (A × B) | IsProductLaw μ}) :=
  lowerSemicontinuous_probWall_iff.mpr isClosed_productLaws

end Independence

/-! ## Conditional beliefs: the conditional relative-entropy penalty -/

section Conditional

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The believed joint reconstructed from a conceived joint's own
`Y`-marginal and the believed conditional: `μ ↦ μ_Y ⋉ k`. -/
def condTarget (k : B → ProbState A) (μ : ProbState (A × B)) :
    ProbState (A × B) :=
  bindState (sndMarg μ) k

@[simp] theorem condTarget_apply (k : B → ProbState A)
    (μ : ProbState (A × B)) (x : A × B) :
    (condTarget k μ : A × B → ℝ) x
      = (sndMarg μ : B → ℝ) x.2 * (k x.2 : A → ℝ) x.1 := rfl

/-- The conditional belief "`X` given `Y` has conditional law `k`",
graded at confidence weight `β`: the scaled conditional relative
entropy `β · D(μ ‖ μ_Y ⋉ k)`. -/
noncomputable def condPenalty (β : ℝ≥0∞) (k : B → ProbState A) :
    ProbPenalty (A × B) :=
  fun μ => β * klq μ (condTarget k μ)

/-- **The target map is affine** (proved, not assumed): marginalization
is linear and the bind is linear in the marginal. -/
theorem condTarget_mix (k : B → ProbState A) {μ ν : ProbState (A × B)}
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    condTarget k (ProbState.mix s t hs ht hst μ ν)
      = ProbState.mix s t hs ht hst (condTarget k μ)
          (condTarget k ν) := by
  refine Subtype.ext (funext fun x => ?_)
  show (sndMarg (ProbState.mix s t hs ht hst μ ν) : B → ℝ) x.2
        * (k x.2 : A → ℝ) x.1
      = (s • (condTarget k μ : A × B → ℝ)
          + t • (condTarget k ν : A × B → ℝ)) x
  rw [sndMarg_mix hs ht hst]
  show (s • (sndMarg μ : B → ℝ) + t • (sndMarg ν : B → ℝ)) x.2
        * (k x.2 : A → ℝ) x.1 = _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, condTarget_apply]
  ring

/-- Zero-set of the conditional penalty, joint-coordinate form: the
conceived joint *is* the reconstruction.  (No positivity guard is
needed in this form: at a null column the reconstruction charges
nothing, so the coordinate equation is automatic there.) -/
theorem klq_condTarget_eq_zero_iff' (k : B → ProbState A)
    (μ : ProbState (A × B)) :
    klq μ (condTarget k μ) = 0
      ↔ ∀ a b, (μ : A × B → ℝ) (a, b)
          = (sndMarg μ : B → ℝ) b * (k b : A → ℝ) a := by
  rw [klq_eq_zero_iff]
  constructor
  · intro h a b
    exact congrArg
      (fun ν : ProbState (A × B) => (ν : A × B → ℝ) (a, b)) h
  · intro h
    exact Subtype.ext (funext fun x => h x.1 x.2)

/-- **Zero-set of the conditional penalty, disintegration form**: the
penalty vanishes exactly when the disintegration of `μ` along `Y`
agrees with `k` at every `y` of positive `μ_Y`-mass.  Here the
positivity guard is load-bearing: at a null `y` the conceived
conditional is the junk value `0/0 = 0`, and no agreement with `k` is
(or could be) demanded. -/
theorem klq_condTarget_eq_zero_iff (k : B → ProbState A)
    (μ : ProbState (A × B)) :
    klq μ (condTarget k μ) = 0
      ↔ ∀ b, 0 < (sndMarg μ : B → ℝ) b
          → ∀ a, (μ : A × B → ℝ) (a, b) / (sndMarg μ : B → ℝ) b
              = (k b : A → ℝ) a := by
  rw [klq_condTarget_eq_zero_iff' k μ]
  constructor
  · intro h b hb a
    rw [h a b]
    exact mul_div_cancel_left₀ _ hb.ne'
  · intro h a b
    rcases ((sndMarg μ).nonneg b).eq_or_lt with hz | hpos
    · have hμ0 : (μ : A × B → ℝ) (a, b) = 0 :=
        le_antisymm (hz ▸ apply_le_sndMarg μ a b) (μ.nonneg (a, b))
      rw [hμ0, ← hz, zero_mul]
    · have hd := h b hpos a
      rw [div_eq_iff hpos.ne'] at hd
      rw [hd]
      ring

/-- The graded conditional penalty vanishes exactly on disintegration
agreement (any nonzero confidence weight). -/
theorem condPenalty_eq_zero_iff {β : ℝ≥0∞} (hβ : β ≠ 0)
    (k : B → ProbState A) (μ : ProbState (A × B)) :
    condPenalty β k μ = 0
      ↔ ∀ b, 0 < (sndMarg μ : B → ℝ) b
          → ∀ a, (μ : A × B → ℝ) (a, b) / (sndMarg μ : B → ℝ) b
              = (k b : A → ℝ) a := by
  rw [condPenalty, mul_eq_zero, klq_condTarget_eq_zero_iff]
  exact or_iff_right hβ

/-- **The conditional penalty is convex**: relative entropy is jointly
convex and the target map is affine. -/
theorem penaltyConvex_klq_condTarget (k : B → ProbState A) :
    PenaltyConvex
      fun μ : ProbState (A × B) => klq μ (condTarget k μ) := by
  intro μ ν s t hs ht hst
  show klq (ProbState.mix s t hs.le ht.le hst μ ν)
      (condTarget k (ProbState.mix s t hs.le ht.le hst μ ν))
    ≤ ENNReal.ofReal s * klq μ (condTarget k μ)
      + ENNReal.ofReal t * klq ν (condTarget k ν)
  rw [condTarget_mix k hs.le ht.le hst]
  exact klq_mix_mix_le hs ht hst

/-- Convexity survives the confidence weight. -/
theorem penaltyConvex_condPenalty (β : ℝ≥0∞) (k : B → ProbState A) :
    PenaltyConvex (condPenalty β k) := by
  intro μ ν s t hs ht hst
  have h := penaltyConvex_klq_condTarget k μ ν s t hs ht hst
  calc condPenalty β k (ProbState.mix s t hs.le ht.le hst μ ν)
      ≤ β * (ENNReal.ofReal s * klq μ (condTarget k μ)
          + ENNReal.ofReal t * klq ν (condTarget k ν)) :=
        mul_le_mul_left' h β
    _ = ENNReal.ofReal s * condPenalty β k μ
          + ENNReal.ofReal t * condPenalty β k ν := by
        show β * (ENNReal.ofReal s * klq μ (condTarget k μ)
            + ENNReal.ofReal t * klq ν (condTarget k ν))
          = ENNReal.ofReal s * (β * klq μ (condTarget k μ))
            + ENNReal.ofReal t * (β * klq ν (condTarget k ν))
        ring

/-- The target map is continuous. -/
theorem continuous_condTarget (k : B → ProbState A) :
    Continuous (condTarget k) := by
  refine Continuous.subtype_mk (continuous_pi fun x => ?_) _
  exact (continuous_finset_sum _ fun a _ =>
    (continuous_apply (a, x.2)).comp continuous_subtype_val).mul
      continuous_const

/-- The conditional relative entropy is a citizen: lower
semicontinuous, by joint lower semicontinuity of relative entropy
through the continuous target map. -/
theorem lowerSemicontinuous_klq_condTarget (k : B → ProbState A) :
    LowerSemicontinuous
      fun μ : ProbState (A × B) => klq μ (condTarget k μ) :=
  lowerSemicontinuous_klq_comp continuous_id (continuous_condTarget k)

/-- **The conditional penalty is a citizen** (finite confidence
weight).  The wall is real whenever `k` has zeros, so lower
semicontinuity — not continuity — is the honest statement for this
family. -/
theorem lowerSemicontinuous_condPenalty {β : ℝ≥0∞} (hβ : β ≠ ⊤)
    (k : B → ProbState A) :
    LowerSemicontinuous (condPenalty β k) := by
  have h : condPenalty β k
      = fun μ => (β * ·) (klq μ (condTarget k μ)) := rfl
  rw [h]
  exact (ENNReal.continuous_const_mul hβ).comp_lowerSemicontinuous
    (lowerSemicontinuous_klq_condTarget k)
    fun x y hxy => mul_le_mul_left' hxy β

end Conditional

/-! ## What composition does not assume: marginal-reading penalties and
the Fréchet class -/

section Composition

variable {A B : Type*} [Fintype A] [Fintype B]

/-- A sum of penalties that each read only their own factor's marginal
vanishes exactly when each marginal lies in its own zero set — the
composite constrains the marginals, jointly, and *nothing else*. -/
theorem marginalSum_eq_zero_iff (g : ProbState A → ℝ≥0∞)
    (h : ProbState B → ℝ≥0∞) (μ : ProbState (A × B)) :
    g (fstMarg μ) + h (sndMarg μ) = 0
      ↔ g (fstMarg μ) = 0 ∧ h (sndMarg μ) = 0 := by
  constructor
  · intro hz
    exact ⟨le_zero_iff.mp (le_self_add.trans_eq hz),
      le_zero_iff.mp (le_add_self.trans_eq hz)⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2, add_zero]

/-- The **Fréchet class** of a pair of marginal constraint sets: every
joint whose marginals lie in the respective sets. -/
def frechetClass (MX : Set (ProbState A)) (MY : Set (ProbState B)) :
    Set (ProbState (A × B)) :=
  {μ | fstMarg μ ∈ MX ∧ sndMarg μ ∈ MY}

/-- At the crisp level, the sum of two marginal-reading walls is the
wall of the Fréchet class. -/
theorem marginalWallSum_eq_probWall_frechet (MX : Set (ProbState A))
    (MY : Set (ProbState B)) :
    (fun μ : ProbState (A × B) =>
        probWall MX (fstMarg μ) + probWall MY (sndMarg μ))
      = probWall (frechetClass MX MY) := by
  funext μ
  by_cases hX : fstMarg μ ∈ MX
  · by_cases hY : sndMarg μ ∈ MY
    · rw [probWall_apply_of_mem hX, probWall_apply_of_mem hY,
        probWall_apply_of_mem
          (show μ ∈ frechetClass MX MY from ⟨hX, hY⟩), add_zero]
    · rw [probWall_apply_of_not_mem hY,
        probWall_apply_of_not_mem
          (show μ ∉ frechetClass MX MY from fun hc => hY hc.2), add_top]
  · rw [probWall_apply_of_not_mem hX,
      probWall_apply_of_not_mem
        (show μ ∉ frechetClass MX MY from fun hc => hX hc.1), top_add]

/-- The compile of a wall is the radial embedding of its set (nonempty
case): the body-side form of crispness. -/
theorem compile_probWall {V : Type*} [Fintype V]
    {C : Set (ProbState V)} (hC : C.Nonempty) :
    compile (probWall C)
      = {x : BelState V | ∃ μ ∈ C, ∃ γ : ℝ,
          0 ≤ γ ∧ γ ≤ 1 ∧ (x : V → ℝ) = γ • (μ : V → ℝ)} := by
  ext x
  constructor
  · rintro ⟨μ, γ, h0, hle, he⟩
    by_cases hμ : μ ∈ C
    · refine ⟨μ, hμ, γ, h0, ?_, he⟩
      rw [probWall_apply_of_mem hμ, grade_zero] at hle
      exact hle
    · rw [probWall_apply_of_not_mem hμ, grade_top] at hle
      obtain ⟨μ₀, hμ₀⟩ := hC
      obtain rfl : γ = 0 := le_antisymm hle h0
      refine ⟨μ₀, hμ₀, 0, le_rfl, zero_le_one, ?_⟩
      rw [he]
      funext v
      simp
  · rintro ⟨μ, hμ, γ, h0, h1, he⟩
    refine ⟨μ, γ, h0, ?_, he⟩
    rw [probWall_apply_of_mem hμ, grade_zero]
    exact h1

/-- **What composition does not assume**: the compile of a sum of
marginal-reading walls is the radial embedding of the *whole* Fréchet
class of couplings — not the independent coupling.  The independent
coupling only witnesses nonemptiness. -/
theorem compile_marginalWallSum {MX : Set (ProbState A)}
    {MY : Set (ProbState B)} (hX : MX.Nonempty) (hY : MY.Nonempty) :
    compile (fun μ : ProbState (A × B) =>
        probWall MX (fstMarg μ) + probWall MY (sndMarg μ))
      = {x : BelState (A × B) | ∃ μ ∈ frechetClass MX MY, ∃ γ : ℝ,
          0 ≤ γ ∧ γ ≤ 1 ∧ (x : A × B → ℝ) = γ • (μ : A × B → ℝ)} := by
  rw [marginalWallSum_eq_probWall_frechet]
  refine compile_probWall ?_
  obtain ⟨p, hp⟩ := hX
  obtain ⟨q, hq⟩ := hY
  exact ⟨prodState p q, by
    show fstMarg (prodState p q) ∈ MX ∧ sndMarg (prodState p q) ∈ MY
    rw [fstMarg_prodState, sndMarg_prodState]
    exact ⟨hp, hq⟩⟩

end Composition

/-! ## The exact witnesses, in exact rationals

The record space `Fin 2 × Fin 2`; the two perfectly-correlated point
masses `δ_{(0,0)}`, `δ_{(1,1)}`; their equal mixture `chi`.  Both
endpoints are product laws; the mixture has uniform marginals and is
not a product law — perfect correlation manufactured from two
deterministic independencies. -/

namespace Witness

/-- The equal mixture of the two perfectly-correlated point masses on
`Fin 2 × Fin 2`. -/
noncomputable def chi : ProbState (Fin 2 × Fin 2) :=
  ProbState.mix (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
    (ProbState.dirac (0, 0)) (ProbState.dirac (1, 1))

theorem chi_apply_ne {x : Fin 2 × Fin 2} (h₀ : x ≠ (0, 0))
    (h₁ : x ≠ (1, 1)) : (chi : Fin 2 × Fin 2 → ℝ) x = 0 := by
  show (1/2 : ℝ) • (ProbState.dirac ((0 : Fin 2), (0 : Fin 2))
        : Fin 2 × Fin 2 → ℝ) x
      + (1/2 : ℝ) • (ProbState.dirac ((1 : Fin 2), (1 : Fin 2))
        : Fin 2 × Fin 2 → ℝ) x = 0
  rw [smul_eq_mul, smul_eq_mul, ProbState.dirac_apply_of_ne h₀,
    ProbState.dirac_apply_of_ne h₁]
  norm_num

theorem chi_apply_00 : (chi : Fin 2 × Fin 2 → ℝ) (0, 0) = 1/2 := by
  show (1/2 : ℝ) • (ProbState.dirac ((0 : Fin 2), (0 : Fin 2))
        : Fin 2 × Fin 2 → ℝ) (0, 0)
      + (1/2 : ℝ) • (ProbState.dirac ((1 : Fin 2), (1 : Fin 2))
        : Fin 2 × Fin 2 → ℝ) (0, 0) = 1/2
  rw [smul_eq_mul, smul_eq_mul, ProbState.dirac_apply_same,
    ProbState.dirac_apply_of_ne (by decide)]
  norm_num

theorem chi_apply_11 : (chi : Fin 2 × Fin 2 → ℝ) (1, 1) = 1/2 := by
  show (1/2 : ℝ) • (ProbState.dirac ((0 : Fin 2), (0 : Fin 2))
        : Fin 2 × Fin 2 → ℝ) (1, 1)
      + (1/2 : ℝ) • (ProbState.dirac ((1 : Fin 2), (1 : Fin 2))
        : Fin 2 × Fin 2 → ℝ) (1, 1) = 1/2
  rw [smul_eq_mul, smul_eq_mul, ProbState.dirac_apply_same,
    ProbState.dirac_apply_of_ne (by decide)]
  norm_num

/-- The first marginal of the diagonal mixture is uniform. -/
theorem fstMarg_chi_apply (a : Fin 2) :
    (fstMarg chi : Fin 2 → ℝ) a = 1/2 := by
  show ∑ b, (chi : Fin 2 × Fin 2 → ℝ) (a, b) = 1/2
  rw [Fin.sum_univ_two]
  fin_cases a
  · show (chi : Fin 2 × Fin 2 → ℝ) (0, 0)
        + (chi : Fin 2 × Fin 2 → ℝ) (0, 1) = 1/2
    rw [chi_apply_00, chi_apply_ne (by decide) (by decide)]
    norm_num
  · show (chi : Fin 2 × Fin 2 → ℝ) (1, 0)
        + (chi : Fin 2 × Fin 2 → ℝ) (1, 1) = 1/2
    rw [chi_apply_11, chi_apply_ne (by decide) (by decide)]
    norm_num

/-- The second marginal of the diagonal mixture is uniform. -/
theorem sndMarg_chi_apply (b : Fin 2) :
    (sndMarg chi : Fin 2 → ℝ) b = 1/2 := by
  show ∑ a, (chi : Fin 2 × Fin 2 → ℝ) (a, b) = 1/2
  rw [Fin.sum_univ_two]
  fin_cases b
  · show (chi : Fin 2 × Fin 2 → ℝ) (0, 0)
        + (chi : Fin 2 × Fin 2 → ℝ) (1, 0) = 1/2
    rw [chi_apply_00, chi_apply_ne (by decide) (by decide)]
    norm_num
  · show (chi : Fin 2 × Fin 2 → ℝ) (0, 1)
        + (chi : Fin 2 × Fin 2 → ℝ) (1, 1) = 1/2
    rw [chi_apply_11, chi_apply_ne (by decide) (by decide)]
    norm_num

/-- **The diagonal mixture is not a product law**: at coordinate
`(0, 1)` it carries no mass while its marginal product carries `1/4` —
in exact rationals. -/
theorem chi_not_isProductLaw : ¬ IsProductLaw chi := by
  rw [isProductLaw_iff]
  intro h
  have h01 := congrArg
    (fun μ : ProbState (Fin 2 × Fin 2) =>
      (μ : Fin 2 × Fin 2 → ℝ) (0, 1)) h
  rw [chi_apply_ne (by decide) (by decide),
    show (prodState (fstMarg chi) (sndMarg chi)
        : Fin 2 × Fin 2 → ℝ) (0, 1)
      = (fstMarg chi : Fin 2 → ℝ) 0 * (sndMarg chi : Fin 2 → ℝ) 1
      from rfl,
    fstMarg_chi_apply, sndMarg_chi_apply] at h01
  norm_num at h01

/-- The mutual information of the diagonal mixture is strictly
positive. -/
theorem mutualInfoQ_chi_ne_zero : mutualInfoQ chi ≠ 0 := by
  rw [Ne, mutualInfoQ_eq_zero_iff]
  exact chi_not_isProductLaw

/-- **The independence penalty is not convex** (any nonzero confidence
weight): both endpoints of the diagonal mixture are product laws with
zero penalty, while the mixture has strictly positive penalty. -/
theorem not_penaltyConvex_indepPenalty {β : ℝ≥0∞} (hβ : β ≠ 0) :
    ¬ PenaltyConvex (indepPenalty (A := Fin 2) (B := Fin 2) β) := by
  intro hconv
  have h := hconv (ProbState.dirac (0, 0)) (ProbState.dirac (1, 1))
    (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
  have h00 : indepPenalty β
      (ProbState.dirac ((0 : Fin 2), (0 : Fin 2))) = 0 := by
    rw [indepPenalty,
      (mutualInfoQ_eq_zero_iff _).mpr (isProductLaw_dirac _), mul_zero]
  have h11 : indepPenalty β
      (ProbState.dirac ((1 : Fin 2), (1 : Fin 2))) = 0 := by
    rw [indepPenalty,
      (mutualInfoQ_eq_zero_iff _).mpr (isProductLaw_dirac _), mul_zero]
  rw [h00, h11, mul_zero, add_zero] at h
  have hchi : indepPenalty β chi = 0 := le_antisymm h zero_le
  rw [indepPenalty, mul_eq_zero] at hchi
  rcases hchi with hc | hc
  · exact hβ hc
  · exact mutualInfoQ_chi_ne_zero hc

/-- Mixing two product laws can leave the product laws: the crisp
independence belief has no mixed reading. -/
theorem productLaws_not_mix_closed :
    ∃ (μ ν : ProbState (Fin 2 × Fin 2)),
      IsProductLaw μ ∧ IsProductLaw ν
        ∧ ¬ IsProductLaw
          (ProbState.mix (1/2) (1/2) (by norm_num) (by norm_num)
            (by norm_num) μ ν) :=
  ⟨ProbState.dirac (0, 0), ProbState.dirac (1, 1),
    isProductLaw_dirac _, isProductLaw_dirac _, chi_not_isProductLaw⟩

/-- The uniform law on two outcomes. -/
noncomputable def uniform2 : ProbState (Fin 2) :=
  ProbState.ofPair (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)

theorem uniform2_apply (v : Fin 2) :
    (uniform2 : Fin 2 → ℝ) v = 1/2 := by
  fin_cases v <;> rfl

theorem fstMarg_chi : fstMarg chi = uniform2 := by
  refine Subtype.ext (funext fun a => ?_)
  rw [fstMarg_chi_apply, uniform2_apply]

theorem sndMarg_chi : sndMarg chi = uniform2 := by
  refine Subtype.ext (funext fun b => ?_)
  rw [sndMarg_chi_apply, uniform2_apply]

/-- The diagonal mixture is a coupling of two uniform marginals. -/
theorem chi_mem_frechet :
    chi ∈ frechetClass {uniform2} {uniform2} :=
  ⟨by rw [Set.mem_singleton_iff]; exact fstMarg_chi,
    by rw [Set.mem_singleton_iff]; exact sndMarg_chi⟩

/-- **Sums of marginal-reading penalties cannot manufacture a
correlation constraint**: the correlated coupling of two uniform
marginals has zero composite penalty under the two singleton-uniform
walls, while it fails independence and pays strictly positive mutual
information.  Independence is a belief, asserted when it is asserted —
not a consequence of placing two Systems side by side. -/
theorem frechet_does_not_imply_independence :
    (probWall {uniform2} (fstMarg chi)
        + probWall {uniform2} (sndMarg chi) = 0)
      ∧ ¬ IsProductLaw chi ∧ mutualInfoQ chi ≠ 0 := by
  refine ⟨?_, chi_not_isProductLaw, mutualInfoQ_chi_ne_zero⟩
  rw [probWall_apply_of_mem
      (show fstMarg chi ∈ ({uniform2} : Set (ProbState (Fin 2)))
        from Set.mem_singleton_iff.mpr fstMarg_chi),
    probWall_apply_of_mem
      (show sndMarg chi ∈ ({uniform2} : Set (ProbState (Fin 2)))
        from Set.mem_singleton_iff.mpr sndMarg_chi), add_zero]

end Witness

/-! ## The crisp independence body in the atlas: CB ∖ CV

The compile of the product-law wall is a credal body — nonempty,
closed, radial — and not a convex credal body: the two correlated
point masses are full-mass members whose real midpoint escapes.  This
is the atlas's ordinary inhabitant of CB ∖ CV: the universe's stock
demands closedness and radiality but not convexity, because one of the
most common beliefs in the modelling vocabulary would otherwise not
denote. -/

section Atlas

/-- The crisp independence body: the radial compile of the product-law
wall. -/
noncomputable def indepBody (A B : Type*) [Fintype A] [Fintype B] :
    Set (BelState (A × B)) :=
  compile (probWall {μ : ProbState (A × B) | IsProductLaw μ})

/-- The crisp independence body is a credal body (any nonempty finite
factors). -/
theorem isCredalBody_indepBody (A B : Type*) [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    IsCredalBody (indepBody A B) :=
  ⟨⟨_, zero_mem_compile _⟩,
    isClosed_compile_iff.mpr lowerSemicontinuous_probWall_productLaws,
    isRadial_compile _⟩

/-- A full-mass member of a compile pins its penalty to zero. -/
private theorem exists_zero_of_mass_one {V : Type*} [Fintype V]
    {f : ProbPenalty V} {x : BelState V} (hx : x ∈ compile f)
    (hmass : ∑ v, (x : V → ℝ) v = 1) :
    ∃ μ : ProbState V, f μ = 0 ∧ (x : V → ℝ) = (μ : V → ℝ) := by
  obtain ⟨μ, γ, h0, hle, he⟩ := hx
  have hγ : γ = 1 := by
    have hsum : ∑ v, (x : V → ℝ) v = ∑ v, (γ • (μ : V → ℝ)) v := by
      rw [he]
    rw [hmass, sum_smul_coe] at hsum
    exact hsum.symm
  subst hγ
  have hgrade : grade (f μ) = 1 := le_antisymm (grade_le_one _) hle
  have hf0 : f μ = 0 := by
    by_contra hne
    have hpos : 0 < f μ := pos_iff_ne_zero.mpr hne
    have hlt := grade_strictAnti hpos
    rw [grade_zero, hgrade] at hlt
    exact lt_irrefl 1 hlt
  refine ⟨μ, hf0, ?_⟩
  rw [he, one_smul]

/-- **The crisp independence body is not convex**: the two correlated
point masses are members at full mass, and their midpoint is the
diagonal mixture, which is not a product law. -/
theorem not_convexBody_indepBody :
    ¬ ConvexBody (indepBody (Fin 2) (Fin 2)) := by
  intro hconv
  have hmem : ∀ v : Fin 2 × Fin 2,
      (ProbState.dirac v).toBel ∈ indepBody (Fin 2) (Fin 2) := by
    intro v
    exact ⟨ProbState.dirac v, 1, zero_le_one, by
      rw [probWall_apply_of_mem
        (show ProbState.dirac v
            ∈ {μ : ProbState (Fin 2 × Fin 2) | IsProductLaw μ}
          from isProductLaw_dirac v), grade_zero], by
      rw [one_smul, ProbState.toBel_coe]⟩
  have hmid := hconv
    (mem_carrierImage (hmem (0, 0))) (mem_carrierImage (hmem (1, 1)))
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num)
  obtain ⟨z, hzS, hzeq⟩ := hmid
  have hzeq' : (z : Fin 2 × Fin 2 → ℝ)
      = (1/2 : ℝ) • ((ProbState.dirac ((0 : Fin 2), (0 : Fin 2))).toBel
          : Fin 2 × Fin 2 → ℝ)
        + (1/2 : ℝ) • ((ProbState.dirac ((1 : Fin 2), (1 : Fin 2))).toBel
          : Fin 2 × Fin 2 → ℝ) := hzeq
  have hzcoe : (z : Fin 2 × Fin 2 → ℝ)
      = (Witness.chi : Fin 2 × Fin 2 → ℝ) := by
    rw [hzeq']
    show (1/2 : ℝ) • ((ProbState.dirac ((0 : Fin 2), (0 : Fin 2))).toBel
          : Fin 2 × Fin 2 → ℝ)
        + (1/2 : ℝ) • ((ProbState.dirac ((1 : Fin 2), (1 : Fin 2))).toBel
          : Fin 2 × Fin 2 → ℝ)
      = (Witness.chi : Fin 2 × Fin 2 → ℝ)
    rw [ProbState.toBel_coe, ProbState.toBel_coe]
    rfl
  have hmass : ∑ v, (z : Fin 2 × Fin 2 → ℝ) v = 1 := by
    rw [hzcoe]
    exact Witness.chi.sum_eq_one
  obtain ⟨μ, hf0, hμcoe⟩ := exists_zero_of_mass_one hzS hmass
  have hμP : IsProductLaw μ := by
    by_contra hne
    rw [probWall_apply_of_not_mem hne] at hf0
    exact ENNReal.top_ne_zero hf0
  have hμchi : μ = Witness.chi :=
    Subtype.ext (hμcoe.symm.trans hzcoe)
  exact Witness.chi_not_isProductLaw (hμchi ▸ hμP)

/-- **Independence beliefs are the ordinary inhabitant of CB ∖ CV**:
the crisp independence body is a credal body and not a convex credal
body — the atlas separation, witnessed by the diagonal mixture in
exact rationals. -/
theorem indepBody_credalBody_not_convex :
    IsCredalBody (indepBody (Fin 2) (Fin 2))
      ∧ ¬ IsConvexCredalBody (indepBody (Fin 2) (Fin 2)) :=
  ⟨isCredalBody_indepBody (Fin 2) (Fin 2),
    fun h => not_convexBody_indepBody h.2⟩

end Atlas

end EpistemicStates

end SuFunctor.Universe
