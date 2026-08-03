import QtslAux.Imprecise.PenaltyCredalIso

/-! # Containment, not identity: the finite stratum

The additive composition law on penalties is *more committal* than the
least-committal glue of the component credal sets: at the finite-rational
stratum, $S(f_1 \boxplus f_2) \subseteq \mathrm{NE}(S_1, S_2)$, with the
t-norm identity
$f_1\pi_1 + f_2\pi_2 = \max(f_1\pi_1, f_2\pi_2) + \min(f_1\pi_1, f_2\pi_2)$,
equality precisely on the crisp locus, and a compact exact-rational
two-graph witness making the containment strict.

**Coordinates**: grade space, exp-free, exactly as `PenaltyCredalIso`
(which this module consumes): the additive law is the **product t-norm**
on grades, the least-committal glue is the **minimum t-norm**, and the
containment is the pointwise inequality `a·b ≤ min a b` on `[0,1]` pushed
through the radial compile's order dictionary (`compile_subset_iff`).

**The glue at this stratum** (`naturalExtension`): the set of
subprobability vectors whose pushforwards along the two marginal maps land
in the components' compiled credal sets — the *greatest* set satisfying
the marginal constraints (`subset_naturalExtension`), which is what
"least-committal" denotes on the credal side. It is itself a compile
(`naturalExtension_eq_compile`: the compile of the pointwise minimum of the
pulled-back grades), hence a credal denotation when the components are
admissible (`naturalExtension_isCredal`, via `MulConvex.inf` — minimum
preserves the harmonic-mean law, proved through the credal side, where it
is intersection-of-convex-sets). Relation to `NaturalExtension.lean`: that
file mechanizes natural extension on the *prevision* side (real scalars,
envelope theorems); here the same least-committal-glue concept is stated
directly on the credal-vector side where the compile lives. The two
spellings meet through the envelope correspondence; no theorem of this
file consumes that bridge.

**Delivered**:
1. the t-norm identity `ENNRat.add_eq_max_add_min` and its `⊞` display
   `boxplus_eq_max_add_min` (penalty side), plus the grade-space twin
   `mul_eq_min_mul_max`;
2. **containment** — `compile_mul_pullback_subset_naturalExtension`
   (grade side, arbitrary grade functions, no admissibility consumed) and
   `compile_boxplus_subset_naturalExtension` (the `ENNRat` additive law
   read through an abstract exponential: the literal
   $S(f_1 \boxplus f_2) \subseteq \mathrm{NE}(S_1, S_2)$);
3. **crisp locus** — the scalar characterization `mul_eq_min_iff_crisp`
   (`a·b = min a b` on `[0,1]` iff a side is `0` or `1`, i.e. iff a side's
   penalty is `∞` or `0`), lifted to a set-level *iff* through
   `compile_injective`: `crisp_locus_iff`. Indicator corollary
   (`compile_mul_eq_of_indicator` + `naturalExtension_eq_inter`): on crisp
   penalties both operations compute intersection of behaviors, exactly;
4. **strictness** — general engine (`compile_mul_ssubset_of_noncrisp`,
   with the explicit separating ray point `witness_mem_glue_not_composite`)
   and the two-graph witness at the finite-rational stratum
   (`witness_containment_strict`, natural-extension costume
   `witness_containment_strict_naturalExtension`).

**The witness numbers, honestly** (fence): the motivating two-graph
witness — two single-edge dependency-graph models disagreeing about a
shared binary variable — has component grades
$2\sqrt{p(0)p(1)} = \tfrac{2\sqrt2}{3}$ at the uniform
shared marginal — irrational, so not a value of a `ℚ` grade function. Its
two *decisive comparisons* are rational: the
exclusion $\tfrac{9}{10} > \tfrac{8}{9}$ ($81 > 80$,
`witness_exclusion_81_gt_80`) and the inclusion
$\tfrac{9}{10} \le \tfrac{2\sqrt2}{3} \iff (\tfrac{9}{10})^2 \le \tfrac89$
($729 \le 800$, `witness_inclusion_729_le_800`, licensed by the square
dictionary `witness_sq_dictionary`). The kernel-checked strict instance
realizes the same two integer comparisons with rational grades
$\tfrac{9}{10}$ and $\tfrac{80}{81}$ (product $\tfrac89$ — the true
witness's product of grades — with $\tfrac{80}{81} = \tfrac89 / \tfrac9{10}$
the rational split of the same product): exclusion of the
$\tfrac{9}{10}$-scaled uniform is again $81 > 80$, inclusion in the glue is
again $729 \le 800$. Both component grades are constant, hence `MulConvex`,
so both sides of the strict inclusion are credal denotations — no closure
operation rescues equality.

**Mutants** (kernel-checked ¬-theorems):
`mutant_identity_fails` (the law *is not* the glue — composing the strict
witness), `mutant_glue_not_subset_composite` (the reverse containment is
refused: certificates on the glue bound the composite, never conversely —
the direction of soundness), with `crisp_control_top` as the paired
positive control (a crisp side restores equality, per the crisp-locus
theorem). -/

namespace Qtsl.Imprecise

open Finset

variable {X : Type*} [Fintype X]

/-! ## The t-norm identity: `a + b = max + min`

The identity
$f_1\pi_1 + f_2\pi_2 = \max(f_1\pi_1, f_2\pi_2) + \min(f_1\pi_1, f_2\pi_2)$
— the additive law differs from the glue (the max, in penalty space) by
exactly the lesser penalty. Stated once for `ENNRat`, displayed for `⊞`,
and twinned in grade space. -/

/-- `a + b = max a b + min a b` in `ENNRat`: the additive composition law
is the glue plus the lesser penalty. -/
theorem ENNRat.add_eq_max_add_min (a b : ENNRat) :
    a + b = max a b + min a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h, add_comm]
  · rw [max_eq_left h, min_eq_right h]

/-- The `⊞` display of the t-norm identity: for a binary wiring with
marginal maps `h₁, h₂`, the composite penalty at every joint is the
pointwise max (the glue, in penalty space) plus the pointwise min (the
conservatism gap — "off the crisp locus they differ by the lesser
penalty"). -/
theorem boxplus_eq_max_add_min {Y₁ Y₂ : Type*} [Fintype Y₁] [Fintype Y₂]
    [DecidableEq Y₁] [DecidableEq Y₂]
    (f₁ : FinPMF Y₁ → ENNRat) (f₂ : FinPMF Y₂ → ENNRat)
    (h₁ : X → Y₁) (h₂ : X → Y₂) (ν : FinPMF X) :
    f₁ (ν.map h₁) + f₂ (ν.map h₂)
      = max (f₁ (ν.map h₁)) (f₂ (ν.map h₂))
        + min (f₁ (ν.map h₁)) (f₂ (ν.map h₂)) :=
  ENNRat.add_eq_max_add_min _ _

/-- Grade-space twin: `a · b = min a b · max a b` — the product t-norm is
the minimum t-norm scaled by the greater grade. -/
theorem mul_eq_min_mul_max (a b : ℚ) : a * b = min a b * max a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, mul_comm]

/-! ## The two t-norms as grade functions -/

/-- Pointwise product of grade functions: the grade-space costume of the
additive composition law (the *product* triangular norm). -/
def GradeFunction.mul (g k : GradeFunction X) : GradeFunction X :=
  ⟨fun μ => g μ * k μ,
   fun μ => mul_nonneg (g.nonneg μ) (k.nonneg μ),
   fun μ => (mul_le_of_le_one_right (g.nonneg μ) (k.le_one μ)).trans
     (g.le_one μ)⟩

@[simp] theorem GradeFunction.mul_apply (g k : GradeFunction X)
    (μ : FinPMF X) : (g.mul k) μ = g μ * k μ := rfl

/-- Pointwise minimum of grade functions: the grade-space costume of the
least-committal glue (the *minimum* triangular norm). -/
def GradeFunction.inf (g k : GradeFunction X) : GradeFunction X :=
  ⟨fun μ => min (g μ) (k μ),
   fun μ => le_min (g.nonneg μ) (k.nonneg μ),
   fun μ => (min_le_left _ _).trans (g.le_one μ)⟩

@[simp] theorem GradeFunction.inf_apply (g k : GradeFunction X)
    (μ : FinPMF X) : (g.inf k) μ = min (g μ) (k μ) := rfl

/-- **The pointwise containment**: on `[0,1]` grades the product is below
the minimum — the entire mathematical content of "the law is more
committal than the glue", one inequality per direction of the ray. -/
theorem GradeFunction.mul_le_inf (g k : GradeFunction X) :
    ∀ μ, (g.mul k) μ ≤ (g.inf k) μ := fun μ =>
  le_min (mul_le_of_le_one_right (g.nonneg μ) (k.le_one μ))
    (mul_le_of_le_one_left (k.nonneg μ) (g.le_one μ))

/-- The compile of the minimum is the intersection of the compiles —
distinct rays meet only at ⊥, so ray sections intersect segment-wise.
(No `Nonempty` hypothesis: membership itself supplies a direction.) -/
theorem GradeFunction.compile_inf (g k : GradeFunction X) :
    (g.inf k).compile = g.compile ∩ k.compile := by
  ext v
  constructor
  · rintro ⟨μ, γ, h0, hle, rfl⟩
    rw [GradeFunction.inf_apply] at hle
    exact ⟨g.smul_prob_mem_compile μ h0 (hle.trans (min_le_left _ _)),
      k.smul_prob_mem_compile μ h0 (hle.trans (min_le_right _ _))⟩
  · rintro ⟨⟨μ₁, γ₁, h10, h1le, rfl⟩, hk⟩
    rcases eq_or_lt_of_le h10 with hz | hpos
    · refine ⟨μ₁, γ₁, h10, ?_, rfl⟩
      rw [← hz]
      exact (g.inf k).nonneg μ₁
    · obtain ⟨μ₂, γ₂, h20, h2le, heq⟩ := hk
      have hmass : γ₁ = γ₂ := smul_prob_mass_eq heq
      rw [← hmass] at heq h2le
      have hdir : μ₁ = μ₂ := smul_prob_dir_eq hpos.ne' heq
      rw [← hdir] at h2le
      exact ⟨μ₁, γ₁, h10, le_min h1le h2le, rfl⟩

/-- Composite-below-glue at the compile level, same foot: monotonicity of
the compile applied to `mul_le_inf`. -/
theorem GradeFunction.compile_mul_subset_compile_inf
    (g k : GradeFunction X) :
    (g.mul k).compile ⊆ (g.inf k).compile :=
  (GradeFunction.compile_subset_iff _ _).mpr (g.mul_le_inf k)

/-! ## Admissibility of the glue

The minimum of two admissible grades is admissible. Proved on the credal
side, where it is transparent: the compile of the minimum is an
intersection of convex, ⊥-containing, scaling-closed sets, and the grade
of any credal denotation satisfies the harmonic-mean law
(`mulConvex_gradeFn`). The penalty-space reading:
$e^{\max(f_1,f_2)} = \max(e^{f_1}, e^{f_2})$ is convex when the
$e^{f_i}$ are. -/

/-- Pushforward commutes with mixture (`FinPMF.map` is affine) — the
transport fact behind pullback preserving admissibility. -/
theorem FinPMF.map_mix {Y : Type*} [Fintype Y] [DecidableEq Y] (g : X → Y)
    (μ₁ μ₂ : FinPMF X) (t : ℚ) (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
    (μ₁.mix μ₂ t h₀ h₁).map g = (μ₁.map g).mix (μ₂.map g) t h₀ h₁ := by
  apply FinPMF.ext
  intro y
  show ∑ x ∈ univ.filter (fun x => g x = y), (μ₁.mix μ₂ t h₀ h₁).prob x
      = t * (μ₁.map g).prob y + (1 - t) * (μ₂.map g).prob y
  simp only [FinPMF.mix_prob]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

/-- Pullback along a marginal map preserves the harmonic-mean law. -/
theorem MulConvex.pullback {Y : Type*} [Fintype Y] [DecidableEq Y]
    {g : GradeFunction Y} (hg : MulConvex g) (h : X → Y) :
    MulConvex (g.pullback h) := by
  intro μ₁ μ₂ t h₀ h₁
  simp only [GradeFunction.pullback_apply, FinPMF.map_mix]
  exact hg (μ₁.map h) (μ₂.map h) t h₀ h₁

/-- The glue of two admissible grades, packaged as a credal denotation:
carrier the compile of the minimum, grade the minimum. Convexity is
intersection-of-convex-sets through `compile_inf`. -/
def GradeFunction.infCredal [Nonempty X] (g k : GradeFunction X)
    (hg : MulConvex g) (hk : MulConvex k) : CredalDenotation X where
  carrier := (g.inf k).compile
  grade := (g.inf k).toFun
  subprob := (g.inf k).compile_subprob
  zero_mem := (g.inf k).zero_mem_compile
  convex := by
    intro v hv w hw s h0 h1
    rw [GradeFunction.compile_inf] at hv hw ⊢
    exact ⟨g.compile_convex hg v hv.1 w hw.1 s h0 h1,
      k.compile_convex hk v hv.2 w hw.2 s h0 h1⟩
  grade_mem := fun μ =>
    (g.inf k).smul_prob_mem_compile μ ((g.inf k).nonneg μ) le_rfl
  grade_max := fun μ γ h0 hmem =>
    ((g.inf k).mem_compile_smul_iff μ h0).mp hmem

/-- **Minimum preserves admissibility**: the glue of two admissible grades
is admissible. -/
theorem MulConvex.inf [Nonempty X] {g k : GradeFunction X}
    (hg : MulConvex g) (hk : MulConvex k) : MulConvex (g.inf k) := by
  intro μ₁ μ₂ t h₀ h₁
  exact (g.infCredal k hg hk).mulConvex_gradeFn μ₁ μ₂ t h₀ h₁

/-! ## The natural extension over the shared foot

Two components with wire spaces `Y₁, Y₂`, seen from the glued apex `X`
through marginal maps `h₁ : X → Y₁`, `h₂ : X → Y₂` (the finite-stratum
$(j_A)_\sharp, (j_B)_\sharp$). The glue is the greatest set of
subprobability joints whose marginals are admitted by the components. -/

section NaturalExtension

variable {Y₁ Y₂ : Type*} [Fintype Y₁] [DecidableEq Y₁]
  [Fintype Y₂] [DecidableEq Y₂]

/-- **The least-committal glue** $\mathrm{NE}(S_1, S_2)$ over the shared
foot: subprobability joints whose component marginals (linear pushforward
of vectors) lie in the components' credal sets. -/
def naturalExtension (h₁ : X → Y₁) (h₂ : X → Y₂)
    (S₁ : Set (Y₁ → ℚ)) (S₂ : Set (Y₂ → ℚ)) : Set (X → ℚ) :=
  {v | IsSubProb v ∧ vecMap h₁ v ∈ S₁ ∧ vecMap h₂ v ∈ S₂}

omit [Fintype Y₁] [Fintype Y₂] in
/-- "Least-committal", cashed out: any set of subprobability joints whose
marginals satisfy the component constraints is contained in the glue —
the glue is the greatest such set. -/
theorem subset_naturalExtension {h₁ : X → Y₁} {h₂ : X → Y₂}
    {S₁ : Set (Y₁ → ℚ)} {S₂ : Set (Y₂ → ℚ)} {A : Set (X → ℚ)}
    (hsub : ∀ v ∈ A, IsSubProb v)
    (hm₁ : ∀ v ∈ A, vecMap h₁ v ∈ S₁) (hm₂ : ∀ v ∈ A, vecMap h₂ v ∈ S₂) :
    A ⊆ naturalExtension h₁ h₂ S₁ S₂ :=
  fun v hv => ⟨hsub v hv, hm₁ v hv, hm₂ v hv⟩

/-- The glue of two compiles is the compile of the pointwise minimum of
the pulled-back grades: the least-committal glue *is* the minimum t-norm,
read through the credal isomorphism. -/
theorem naturalExtension_eq_compile [Nonempty X]
    (g₁ : GradeFunction Y₁) (g₂ : GradeFunction Y₂)
    (h₁ : X → Y₁) (h₂ : X → Y₂) :
    naturalExtension h₁ h₂ g₁.compile g₂.compile
      = ((g₁.pullback h₁).inf (g₂.pullback h₂)).compile := by
  rw [GradeFunction.compile_inf, GradeFunction.compile_pullback,
    GradeFunction.compile_pullback]
  ext v
  simp only [naturalExtension, Set.mem_setOf_eq, Set.mem_inter_iff]
  tauto

/-- The glue of two compiles as a plain intersection of the pulled-back
compiles (the form the crisp-locus corollary reads through). -/
theorem naturalExtension_eq_inter [Nonempty X]
    (g₁ : GradeFunction Y₁) (g₂ : GradeFunction Y₂)
    (h₁ : X → Y₁) (h₂ : X → Y₂) :
    naturalExtension h₁ h₂ g₁.compile g₂.compile
      = (g₁.pullback h₁).compile ∩ (g₂.pullback h₂).compile := by
  rw [naturalExtension_eq_compile, GradeFunction.compile_inf]

/-- The glue of admissible components is a credal denotation ("both sides
are already convex and scaling-closed — no closure operation rescues
equality"). -/
theorem naturalExtension_isCredal [Nonempty X]
    {g₁ : GradeFunction Y₁} {g₂ : GradeFunction Y₂}
    (hg₁ : MulConvex g₁) (hg₂ : MulConvex g₂)
    (h₁ : X → Y₁) (h₂ : X → Y₂) :
    ∃ S : CredalDenotation X,
      S.carrier = naturalExtension h₁ h₂ g₁.compile g₂.compile :=
  ⟨(g₁.pullback h₁).infCredal (g₂.pullback h₂)
      (hg₁.pullback h₁) (hg₂.pullback h₂),
    (naturalExtension_eq_compile g₁ g₂ h₁ h₂).symm⟩

/-! ### Containment -/

/-- **Containment, not identity — grade side**:
$S(g_1 \cdot g_2) \subseteq \mathrm{NE}(S_1, S_2)$ for arbitrary grade
functions (no admissibility consumed). -/
theorem compile_mul_pullback_subset_naturalExtension [Nonempty X]
    (g₁ : GradeFunction Y₁) (g₂ : GradeFunction Y₂)
    (h₁ : X → Y₁) (h₂ : X → Y₂) :
    ((g₁.pullback h₁).mul (g₂.pullback h₂)).compile
      ⊆ naturalExtension h₁ h₂ g₁.compile g₂.compile := by
  rw [naturalExtension_eq_compile]
  exact GradeFunction.compile_mul_subset_compile_inf _ _

/-- The `ENNRat` additive law read through an abstract exponential is the
product of the pulled-back grades (binary display of
`gradeOfPenalty_compositePenalty`). -/
theorem gradeOfPenalty_boxplus (E : ENNRat → ℚ)
    (e0 : ∀ a, 0 ≤ E a) (e1 : ∀ a, E a ≤ 1)
    (hmul : ∀ a b, E (a + b) = E a * E b)
    (F₁ : FinPMF Y₁ → ENNRat) (F₂ : FinPMF Y₂ → ENNRat)
    (h₁ : X → Y₁) (h₂ : X → Y₂) :
    gradeOfPenalty E e0 e1 (fun ν : FinPMF X => F₁ (ν.map h₁) + F₂ (ν.map h₂))
      = ((gradeOfPenalty E e0 e1 F₁).pullback h₁).mul
          ((gradeOfPenalty E e0 e1 F₂).pullback h₂) :=
  GradeFunction.ext fun _ => hmul _ _

/-- **The containment display, assembled**:
$S(f_1 \boxplus f_2) \subseteq \mathrm{NE}(S_1, S_2)$ — the compile of the
additive composite penalty (through any abstract exponential) is contained
in the natural extension of the components' compiled credal sets, always,
with no topological hypotheses. -/
theorem compile_boxplus_subset_naturalExtension [Nonempty X]
    (E : ENNRat → ℚ) (e0 : ∀ a, 0 ≤ E a) (e1 : ∀ a, E a ≤ 1)
    (hmul : ∀ a b, E (a + b) = E a * E b)
    (F₁ : FinPMF Y₁ → ENNRat) (F₂ : FinPMF Y₂ → ENNRat)
    (h₁ : X → Y₁) (h₂ : X → Y₂) :
    (gradeOfPenalty E e0 e1
        (fun ν : FinPMF X => F₁ (ν.map h₁) + F₂ (ν.map h₂))).compile
      ⊆ naturalExtension h₁ h₂ (gradeOfPenalty E e0 e1 F₁).compile
          (gradeOfPenalty E e0 e1 F₂).compile := by
  rw [gradeOfPenalty_boxplus E e0 e1 hmul]
  exact compile_mul_pullback_subset_naturalExtension _ _ _ _

end NaturalExtension

/-! ## The crisp locus

Equality holds precisely when every joint sees at least one side's grade
at `0` or `1` — one side's penalty at `∞` or `0`. On the crisp locus both
operations compute intersection of behaviors; off it they differ by the
lesser penalty, and deterministic intuition reads two operations as one
only because it lives on the locus. -/

/-- Scalar crisp-locus characterization: on `[0,1]`, `a·b = min a b` iff
one of the sides is `0` or `1`. -/
theorem mul_eq_min_iff_crisp {a b : ℚ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    a * b = min a b ↔ a = 0 ∨ a = 1 ∨ b = 0 ∨ b = 1 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨ha0', ha1', hb0', hb1'⟩ := hne
    have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha0')
    have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb0')
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab] at h
      have hblt : b < 1 := lt_of_le_of_ne hb1 hb1'
      nlinarith [mul_pos hapos (show (0:ℚ) < 1 - b by linarith)]
    · rw [min_eq_right hab] at h
      have halt : a < 1 := lt_of_le_of_ne ha1 ha1'
      nlinarith [mul_pos (show (0:ℚ) < 1 - a by linarith) hbpos]
  · rintro (h | h | h | h) <;> subst h
    · rw [zero_mul, min_eq_left hb0]
    · rw [one_mul, min_eq_right hb1]
    · rw [mul_zero, min_eq_right ha0]
    · rw [mul_one, min_eq_left ha1]

/-- Compile equality is pointwise grade equality (via injectivity of the
compile). -/
theorem GradeFunction.compile_mul_eq_compile_inf_iff
    (g k : GradeFunction X) :
    (g.mul k).compile = (g.inf k).compile
      ↔ ∀ μ, g μ * k μ = min (g μ) (k μ) := by
  constructor
  · intro h μ
    have heq : g.mul k = g.inf k := GradeFunction.compile_injective h
    exact congrArg (fun G : GradeFunction X => G μ) heq
  · intro h
    have heq : g.mul k = g.inf k := GradeFunction.ext fun μ => h μ
    rw [heq]

section CrispLocus

variable {Y₁ Y₂ : Type*} [Fintype Y₁] [DecidableEq Y₁]
  [Fintype Y₂] [DecidableEq Y₂]

/-- **The crisp-locus theorem, set level**: the composite's compile equals
the natural extension *iff* every joint sees at least one side's grade at
`0` or `1` (penalty at `∞` or `0`). Both directions — the containment is
an identity exactly on the crisp locus. -/
theorem crisp_locus_iff [Nonempty X]
    (g₁ : GradeFunction Y₁) (g₂ : GradeFunction Y₂)
    (h₁ : X → Y₁) (h₂ : X → Y₂) :
    ((g₁.pullback h₁).mul (g₂.pullback h₂)).compile
        = naturalExtension h₁ h₂ g₁.compile g₂.compile
      ↔ ∀ μ : FinPMF X,
          g₁ (μ.map h₁) = 0 ∨ g₁ (μ.map h₁) = 1
            ∨ g₂ (μ.map h₂) = 0 ∨ g₂ (μ.map h₂) = 1 := by
  rw [naturalExtension_eq_compile,
    GradeFunction.compile_mul_eq_compile_inf_iff]
  refine forall_congr' fun μ => ?_
  simpa only [GradeFunction.pullback_apply] using
    mul_eq_min_iff_crisp (g₁.nonneg (μ.map h₁)) (g₁.le_one (μ.map h₁))
      (g₂.nonneg (μ.map h₂)) (g₂.le_one (μ.map h₂))

/-- Indicator corollary ("on indicator penalties both compute intersection
of behaviors, exactly"): one crisp side suffices for equality, and the
common value is the intersection of the pulled-back compiles. -/
theorem compile_mul_eq_of_indicator [Nonempty X]
    {g₁ : GradeFunction Y₁} (g₂ : GradeFunction Y₂)
    (hg₁ : ∀ ν, g₁ ν = 0 ∨ g₁ ν = 1) (h₁ : X → Y₁) (h₂ : X → Y₂) :
    ((g₁.pullback h₁).mul (g₂.pullback h₂)).compile
      = (g₁.pullback h₁).compile ∩ (g₂.pullback h₂).compile := by
  rw [← naturalExtension_eq_inter,
    (crisp_locus_iff g₁ g₂ h₁ h₂).mpr fun μ =>
      (hg₁ (μ.map h₁)).elim Or.inl (fun h => Or.inr (Or.inl h))]

end CrispLocus

/-- Positive control for the mutants below: a crisp (everywhere-`1`) side
restores equality on the nose — `⊤ · k = k = min ⊤ k` at the compile
level. -/
theorem crisp_control_top (k : GradeFunction X) :
    ((GradeFunction.top X).mul k).compile
      = ((GradeFunction.top X).inf k).compile :=
  (GradeFunction.compile_mul_eq_compile_inf_iff _ _).mpr fun μ => by
    show 1 * k μ = min 1 (k μ)
    rw [one_mul, min_eq_right (k.le_one μ)]

/-! ## Strictness: the two-graph witness -/

/-- The square dictionary: for nonnegative rationals, `γ ≤ b ↔ γ² ≤ b²`.
This is the transport that lets the inclusion comparison against the
irrational glue grade $\tfrac{2\sqrt2}{3}$ be checked in grade-squared
space, where it is `729 ≤ 800`. -/
theorem witness_sq_dictionary {γ b : ℚ} (hγ : 0 ≤ γ) (hb : 0 ≤ b) :
    γ ≤ b ↔ γ ^ 2 ≤ b ^ 2 := by
  constructor
  · intro h
    nlinarith [mul_le_mul h h hγ hb]
  · intro h
    by_contra hlt
    push Not at hlt
    have hγpos : 0 < γ := lt_of_le_of_lt hb hlt
    nlinarith [mul_pos (sub_pos.mpr hlt) (add_pos_of_pos_of_nonneg hγpos hb)]

/-- The exclusion comparison of the two-graph witness: `8/9 < 9/10`,
i.e. `80 < 81` — the `9/10`-scaled uniform exceeds the composite's product
grade. -/
theorem witness_exclusion_81_gt_80 : (8 : ℚ) / 9 < 9 / 10 := by norm_num

/-- The inclusion comparison: `(9/10)² ≤ 8/9`, i.e. `729 ≤ 800` — through
the square dictionary, `9/10 ≤ 2√2/3`: the witness stays inside the
glue. -/
theorem witness_inclusion_729_le_800 : ((9 : ℚ) / 10) ^ 2 ≤ 8 / 9 := by
  norm_num

/-- The explicit separating point, general form: any scale strictly
between the product grade and the minimum grade of a direction yields a
joint inside the glue and outside the composite. -/
theorem witness_mem_glue_not_composite {g k : GradeFunction X}
    (μ : FinPMF X) {γ : ℚ} (h0 : 0 ≤ γ)
    (hgt : (g.mul k) μ < γ) (hle : γ ≤ (g.inf k) μ) :
    γ • μ.prob ∈ (g.inf k).compile ∧ γ • μ.prob ∉ (g.mul k).compile := by
  constructor
  · exact ((g.inf k).mem_compile_smul_iff μ h0).mpr hle
  · intro hmem
    exact absurd (((g.mul k).mem_compile_smul_iff μ h0).mp hmem)
      (not_le.mpr hgt)

/-- Strictness engine: a single non-crisp direction makes the containment
strict. -/
theorem compile_mul_ssubset_of_noncrisp {g k : GradeFunction X}
    (μ : FinPMF X) (hne : g μ * k μ ≠ min (g μ) (k μ)) :
    (g.mul k).compile ⊂ (g.inf k).compile := by
  rw [Set.ssubset_iff_subset_ne]
  refine ⟨GradeFunction.compile_mul_subset_compile_inf g k, fun heq => ?_⟩
  exact hne (((GradeFunction.compile_mul_eq_compile_inf_iff g k).mp heq) μ)

/-- Constant grade functions (admissible: the harmonic-mean law holds with
equality). -/
def constGrade (X : Type*) [Fintype X] (c : ℚ) (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    GradeFunction X :=
  ⟨fun _ => c, fun _ => h0, fun _ => h1⟩

@[simp] theorem constGrade_apply (c : ℚ) (h0 : 0 ≤ c) (h1 : c ≤ 1)
    (μ : FinPMF X) : constGrade X c h0 h1 μ = c := rfl

theorem constGrade_mulConvex (c : ℚ) (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    MulConvex (constGrade X c h0 h1) := by
  intro μ₁ μ₂ t ht0 ht1
  show c * c ≤ c * ((1 - t) * c + t * c)
  have h : (1 - t) * c + t * c = c := by ring
  rw [h]

/-- The rational witness grade `9/10` (the two-graph witness scale, recast
as a component grade — see the module header's fence note). -/
def witnessGradeA : GradeFunction (Fin 2) :=
  constGrade (Fin 2) (9 / 10) (by norm_num) (by norm_num)

/-- The rational witness grade `80/81 = (8/9)/(9/10)`: the rational split
of the two-graph witness's product-of-grades `8/9`. -/
def witnessGradeB : GradeFunction (Fin 2) :=
  constGrade (Fin 2) (80 / 81) (by norm_num) (by norm_num)

/-- The `9/10`-scaled uniform is **excluded from the composite**: its
scale exceeds the product grade `8/9` — the comparison is `81 > 80`. -/
theorem witness_excluded_from_composite :
    ((9 : ℚ) / 10) • (FinPMF.uniform (Fin 2)).prob
      ∉ (witnessGradeA.mul witnessGradeB).compile := by
  rw [GradeFunction.mem_compile_smul_iff _ _ (by norm_num : (0:ℚ) ≤ 9/10)]
  show ¬ (9 : ℚ) / 10 ≤ 9 / 10 * (80 / 81)
  norm_num

/-- The `9/10`-scaled uniform is **inside the glue**: `9/10 ≤ 9/10` on the
`A` side, and `9/10 ≤ 80/81` on the `B` side — the latter is `729 ≤ 800`,
the same integer comparison as the square-dictionary check against
`2√2/3`. -/
theorem witness_in_glue :
    ((9 : ℚ) / 10) • (FinPMF.uniform (Fin 2)).prob
      ∈ (witnessGradeA.inf witnessGradeB).compile := by
  rw [GradeFunction.mem_compile_smul_iff _ _ (by norm_num : (0:ℚ) ≤ 9/10)]
  show (9 : ℚ) / 10 ≤ min (9 / 10) (80 / 81)
  exact le_min le_rfl (by norm_num)

/-- **The containment is strict** (kernel-checked): at the finite-rational
stratum, with both components admissible constant grades, the composite's
credal set is properly contained in the glue — no closure operation
rescues equality. -/
theorem witness_containment_strict :
    (witnessGradeA.mul witnessGradeB).compile
      ⊂ (witnessGradeA.inf witnessGradeB).compile := by
  refine compile_mul_ssubset_of_noncrisp (FinPMF.uniform (Fin 2)) ?_
  show (9 : ℚ) / 10 * (80 / 81) ≠ min (9 / 10) (80 / 81)
  rw [min_eq_left (by norm_num : (9:ℚ)/10 ≤ 80/81)]
  norm_num

/-- Both witness components are admissible — the strict gap is not an
artifact of an inadmissible presentation. -/
theorem witnessGrades_mulConvex :
    MulConvex witnessGradeA ∧ MulConvex witnessGradeB :=
  ⟨constGrade_mulConvex _ _ _, constGrade_mulConvex _ _ _⟩

/-- Identity pushforward of vectors is the identity. -/
theorem vecMap_id [DecidableEq X] (v : X → ℚ) : vecMap id v = v := by
  funext y
  show ∑ x ∈ univ.filter (fun x => id x = y), v x = v y
  simp [Finset.filter_eq']

/-- Over the identity foot, the natural extension of two compiles is their
intersection. -/
theorem naturalExtension_id_id [DecidableEq X]
    (g k : GradeFunction X) :
    naturalExtension id id g.compile k.compile
      = g.compile ∩ k.compile := by
  ext v
  simp only [naturalExtension, Set.mem_setOf_eq, vecMap_id,
    Set.mem_inter_iff]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩,
    fun h => ⟨g.compile_subprob v h.1, h.1, h.2⟩⟩

/-- The strict witness in natural-extension costume:
$S(f_A \boxplus f_B) \subsetneq \mathrm{NE}(S_A, S_B)$ over the shared
binary variable (identity marginal maps — the witness's action happens
entirely on the shared foot). -/
theorem witness_containment_strict_naturalExtension :
    (witnessGradeA.mul witnessGradeB).compile
      ⊂ naturalExtension id id witnessGradeA.compile
          witnessGradeB.compile := by
  rw [naturalExtension_id_id, ← GradeFunction.compile_inf]
  exact witness_containment_strict

/-! ## Mutants (kernel-checked ¬-theorems) -/

/-- **Mutant: "the law is the glue" is refused.** The identity
`S(g·k) = S(g ⊓ k)` fails as a universal claim — the composition law is
strictly more committal off the crisp locus. -/
theorem mutant_identity_fails :
    ¬ ∀ g k : GradeFunction (Fin 2),
        (g.mul k).compile = (g.inf k).compile := by
  intro h
  exact witness_containment_strict.ne (h witnessGradeA witnessGradeB)

/-- **Mutant: the reverse containment is refused.** The glue does not
bound the composite from below — soundness flows one way only:
certificates on the glue bound every element of the composite, never
conversely. -/
theorem mutant_glue_not_subset_composite :
    ¬ ((witnessGradeA.inf witnessGradeB).compile
        ⊆ (witnessGradeA.mul witnessGradeB).compile) := fun h =>
  witness_excluded_from_composite (h witness_in_glue)

/-! ## Axiom receipts -/

#print axioms ENNRat.add_eq_max_add_min
#print axioms boxplus_eq_max_add_min
#print axioms mul_eq_min_mul_max
#print axioms GradeFunction.mul_le_inf
#print axioms GradeFunction.compile_inf
#print axioms GradeFunction.compile_mul_subset_compile_inf
#print axioms FinPMF.map_mix
#print axioms MulConvex.pullback
#print axioms MulConvex.inf
#print axioms subset_naturalExtension
#print axioms naturalExtension_eq_compile
#print axioms naturalExtension_eq_inter
#print axioms naturalExtension_isCredal
#print axioms compile_mul_pullback_subset_naturalExtension
#print axioms gradeOfPenalty_boxplus
#print axioms compile_boxplus_subset_naturalExtension
#print axioms mul_eq_min_iff_crisp
#print axioms GradeFunction.compile_mul_eq_compile_inf_iff
#print axioms crisp_locus_iff
#print axioms compile_mul_eq_of_indicator
#print axioms crisp_control_top
#print axioms witness_sq_dictionary
#print axioms witness_exclusion_81_gt_80
#print axioms witness_inclusion_729_le_800
#print axioms witness_mem_glue_not_composite
#print axioms compile_mul_ssubset_of_noncrisp
#print axioms witness_excluded_from_composite
#print axioms witness_in_glue
#print axioms witness_containment_strict
#print axioms witnessGrades_mulConvex
#print axioms witness_containment_strict_naturalExtension
#print axioms mutant_identity_fails
#print axioms mutant_glue_not_subset_composite

end Qtsl.Imprecise
