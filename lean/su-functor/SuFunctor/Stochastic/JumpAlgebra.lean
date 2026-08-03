import SuFunctor.Stochastic.JumpMeasure

/-! # The thinning-form composite algebra and the elaboration homomorphism

The measure-weighted tier composes as a graded conic module with
interleaving: superposition is the addition, majorant-declared
observables act by scaling, and independent components compose by
jumping in one coordinate while the other stays
(`SuFunctor.Stochastic.JumpMeasure`).  Sequential (Kleisli)
composition of jump kernels is deliberately absent at this tier —
successive jumps compose through time, and the discrete-time steps
that do want Kleisli composition live one tier down
(`SuFunctor.Stochastic.NoiseKleisli`).

This module equips the thinning normal forms themselves with that
composite algebra and proves that elaboration is a homomorphism onto
it, graded by the intensity majorants:

* **the normal-form composites** — `ThinningForm.superpose`,
  `ThinningForm.scale`, `ThinningForm.extendFst`/`extendSnd`,
  `ThinningForm.interleave`, `ThinningForm.zero`: the same formation
  shapes the term algebra has, now on arbitrary normal forms, with
  the rates composing by the grading arithmetic (`rate_superpose`,
  `rate_scale`, `rate_interleave`);
* **the composite algebra is sound** — `generator_superpose`
  (addition), `generator_scale` (the module action),
  `generator_extendFst`/`generator_extendSnd` (a coordinate extension
  acts on its own slot, with the killing channel transported
  unchanged), `generator_interleave` (the Leibniz rule at the
  normal-form level);
* **elaboration is the homomorphism** — on the module structure the
  commutation holds on the nose: `elaborate_superpose`,
  `elaborate_scale`, `elaborate_zero` are definitional (proved by
  `rfl`), elaboration being by construction the free extension of
  exactly this normal-form algebra.  For interleaving the
  commutation holds in the thinning quotient
  (`generator_elaborate_interleave`): elaborating the interleaved
  term and interleaving the elaborations denote the same generator
  functional — the equality the denotation factors through, normal
  forms being deliberately non-unique;
* **the tag bookkeeping is content** —
  `washKill_not_generator_invisible`: reclassifying killing mass as
  stay moves the generator, the mechanical complement of
  `ThinningForm.generator_absorbDiagonal` (self-jump mass may be so
  reclassified; killing mass may not).  This is why the coordinate
  extensions preserve the cemetery channel: the killing term of an
  extension is the killing term of its component, and washing it
  away would break the Leibniz rule.
-/

namespace SuFunctor.Stochastic

open SuFunctor.Universe
open scoped NNRat

universe u

/-! ## Tag-preserving relabelling on the one-step alphabet -/

namespace Step

variable {V : Type*} {W : Type*}

/-- Tag-preserving functorial map on the one-step alphabet: relabel
the next-states, fix the stay and cemetery tags. -/
def mapNext (θ : V → W) : Step V → Step W
  | .next v => .next (θ v)
  | .stay => .stay
  | .cemetery => .cemetery

@[simp] theorem mapNext_next (θ : V → W) (v : V) :
    mapNext θ (next v) = next (θ v) := rfl

@[simp] theorem mapNext_stay (θ : V → W) :
    mapNext θ (stay : Step V) = stay := rfl

@[simp] theorem mapNext_cemetery (θ : V → W) :
    mapNext θ (cemetery : Step V) = cemetery := rfl

theorem mapNext_injective {θ : V → W} (hθ : Function.Injective θ) :
    Function.Injective (mapNext θ) := by
  intro s s' h
  cases s with
  | next v =>
      cases s' with
      | next v' =>
          have h' : θ v = θ v' := by
            have hn : (next (θ v) : Step W) = next (θ v') := h
            injection hn
          exact congrArg next (hθ h')
      | stay => exact nomatch h
      | cemetery => exact nomatch h
  | stay =>
      cases s' with
      | next v' => exact nomatch h
      | stay => rfl
      | cemetery => exact nomatch h
  | cemetery =>
      cases s' with
      | next v' => exact nomatch h
      | stay => exact nomatch h
      | cemetery => rfl

theorem eq_stay_of_mapNext_eq_stay {θ : V → W} {s : Step V}
    (h : mapNext θ s = stay) : s = stay := by
  cases s with
  | next v => exact nomatch h
  | stay => rfl
  | cemetery => exact nomatch h

theorem eq_cemetery_of_mapNext_eq_cemetery {θ : V → W} {s : Step V}
    (h : mapNext θ s = cemetery) : s = cemetery := by
  cases s with
  | next v => exact nomatch h
  | stay => exact nomatch h
  | cemetery => rfl

/-- The kill-washing relabel: send the cemetery tag to stay, fix
everything else.  The move the thinning quotient refuses — see
`washKill_not_generator_invisible`. -/
def washKill : Step V → Step V
  | .next v => .next v
  | .stay => .stay
  | .cemetery => .stay

end Step

/-! ## Pushforward along a tag-preserving relabelling -/

section PushMapNext

variable {V : Type*} [Fintype V] {W : Type*}

/-- Pushing along a tag-preserving relabelling fixes the stay mass. -/
theorem pushFun_mapNext_stay (θ : V → W) (x : Step V → ℝ) :
    pushFun (Step.mapNext θ) x Step.stay = x Step.stay :=
  (Finset.sum_eq_single Step.stay
      (fun s _ hs => if_neg fun he => hs (Step.eq_stay_of_mapNext_eq_stay he))
      (fun h => absurd (Finset.mem_univ _) h)).trans (if_pos rfl)

/-- Pushing along a tag-preserving relabelling transports the killing
mass unchanged: the cemetery channel of an extension is the cemetery
channel of its component. -/
theorem pushFun_mapNext_cemetery (θ : V → W) (x : Step V → ℝ) :
    pushFun (Step.mapNext θ) x Step.cemetery = x Step.cemetery :=
  (Finset.sum_eq_single Step.cemetery
      (fun s _ hs => if_neg fun he =>
        hs (Step.eq_cemetery_of_mapNext_eq_cemetery he))
      (fun h => absurd (Finset.mem_univ _) h)).trans (if_pos rfl)

end PushMapNext

/-! ## The normal-form composite algebra -/

namespace ThinningForm

variable {V : Type u} [Fintype V]

/-- Superposition of thinning normal forms: rates add, kernels mix in
proportion to the rates (total division makes the all-zero case
harmless).  The same formation shape the term algebra's `superpose`
elaborates through, now as an operation on arbitrary normal forms. -/
noncomputable def superpose (T₁ T₂ : ThinningForm V) : ThinningForm V :=
  ⟨T₁.rate + T₂.rate, fun x =>
    ProbState.mix ((T₁.rate : ℝ) / ((T₁.rate : ℝ) + (T₂.rate : ℝ)))
      (div_add_mem_Icc (NNRat.cast_nonneg T₁.rate)
        (NNRat.cast_nonneg T₂.rate)).1
      (div_add_mem_Icc (NNRat.cast_nonneg T₁.rate)
        (NNRat.cast_nonneg T₂.rate)).2
      (T₁.kernel x) (T₂.kernel x)⟩

@[simp] theorem rate_superpose (T₁ T₂ : ThinningForm V) :
    (T₁.superpose T₂).rate = T₁.rate + T₂.rate := rfl

/-- **Superposition is generator addition**: the normal-form
superposition denotes the sum of the component generators — the
conic-module addition, sound at the level of arbitrary normal
forms. -/
theorem generator_superpose (T₁ T₂ : ThinningForm V) (f : V → ℝ) (x : V) :
    (T₁.superpose T₂).generator f x
      = T₁.generator f x + T₂.generator f x := by
  have hE₁ : T₁.generator f x
      = (T₁.rate : ℝ) *
          ((∑ y, (T₁.kernel x : Step V → ℝ) (Step.next y) * (f y - f x))
            - (T₁.kernel x : Step V → ℝ) Step.cemetery * f x) := rfl
  have hE₂ : T₂.generator f x
      = (T₂.rate : ℝ) *
          ((∑ y, (T₂.kernel x : Step V → ℝ) (Step.next y) * (f y - f x))
            - (T₂.kernel x : Step V → ℝ) Step.cemetery * f x) := rfl
  have ha0 : (0 : ℝ) ≤ (T₁.rate : ℝ) := NNRat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ (T₂.rate : ℝ) := NNRat.cast_nonneg _
  show ((T₁.rate + T₂.rate : ℚ≥0) : ℝ) *
      ((∑ y,
          ((T₁.rate : ℝ) / ((T₁.rate : ℝ) + (T₂.rate : ℝ))
              * (T₁.kernel x : Step V → ℝ) (Step.next y)
            + (1 - (T₁.rate : ℝ) / ((T₁.rate : ℝ) + (T₂.rate : ℝ)))
              * (T₂.kernel x : Step V → ℝ) (Step.next y))
            * (f y - f x))
        - ((T₁.rate : ℝ) / ((T₁.rate : ℝ) + (T₂.rate : ℝ))
              * (T₁.kernel x : Step V → ℝ) Step.cemetery
            + (1 - (T₁.rate : ℝ) / ((T₁.rate : ℝ) + (T₂.rate : ℝ)))
              * (T₂.kernel x : Step V → ℝ) Step.cemetery)
            * f x)
    = T₁.generator f x + T₂.generator f x
  rw [hE₁, hE₂, NNRat.cast_add]
  set a : ℝ := (T₁.rate : ℝ) with ha
  set c : ℝ := (T₂.rate : ℝ) with hc
  set A : ℝ := (∑ y, (T₁.kernel x : Step V → ℝ) (Step.next y)
      * (f y - f x)) with hA
  set C : ℝ := (∑ y, (T₂.kernel x : Step V → ℝ) (Step.next y)
      * (f y - f x)) with hC
  set dA : ℝ := (T₁.kernel x : Step V → ℝ) Step.cemetery with hdA
  set dC : ℝ := (T₂.kernel x : Step V → ℝ) Step.cemetery with hdC
  have hsplit :
      (∑ y,
          (a / (a + c) * (T₁.kernel x : Step V → ℝ) (Step.next y)
            + (1 - a / (a + c))
              * (T₂.kernel x : Step V → ℝ) (Step.next y))
            * (f y - f x))
        = a / (a + c) * A + (1 - a / (a + c)) * C := by
    rw [hA, hC, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hsplit]
  rcases eq_or_lt_of_le (add_nonneg ha0 hc0) with heq | hpos
  · have haz : a = 0 := by linarith
    have hcz : c = 0 := by linarith
    simp [haz, hcz]
  · have hne : a + c ≠ 0 := ne_of_gt hpos
    field_simp
    ring

section ScaleZero

variable [DecidableEq V]

/-- Scaling of a thinning normal form by a majorant-declared
observable: the majorant multiplies the rate and the kernel thins — a
convex gate between the kernel and an explicit stay branch, the gate
weight bounded by exactly the formation premise. -/
noncomputable def scale (p : V → ℝ) (bound : ℚ≥0)
    (hp : ∀ x, p x ∈ Set.Icc (0 : ℝ) (bound : ℝ)) (T : ThinningForm V) :
    ThinningForm V :=
  ⟨bound * T.rate, fun x =>
    ProbState.mix (p x / (bound : ℝ))
      (div_mem_Icc_of_Icc (NNRat.cast_nonneg bound) (hp x)).1
      (div_mem_Icc_of_Icc (NNRat.cast_nonneg bound) (hp x)).2
      (T.kernel x) (ProbState.dirac Step.stay)⟩

@[simp] theorem rate_scale (p : V → ℝ) (bound : ℚ≥0)
    (hp : ∀ x, p x ∈ Set.Icc (0 : ℝ) (bound : ℝ)) (T : ThinningForm V) :
    (T.scale p bound hp).rate = bound * T.rate := rfl

/-- **Scaling is the module action**: the normal-form thinning gate
denotes pointwise multiplication of the generator by the observable —
sound at the level of arbitrary normal forms; at the degenerate
majorant the formation premise forces the observable to vanish. -/
theorem generator_scale (p : V → ℝ) (bound : ℚ≥0)
    (hp : ∀ x, p x ∈ Set.Icc (0 : ℝ) (bound : ℝ)) (T : ThinningForm V)
    (f : V → ℝ) (x : V) :
    (T.scale p bound hp).generator f x = p x * T.generator f x := by
  have hE : T.generator f x
      = (T.rate : ℝ) *
          ((∑ y, (T.kernel x : Step V → ℝ) (Step.next y) * (f y - f x))
            - (T.kernel x : Step V → ℝ) Step.cemetery * f x) := rfl
  show ((bound * T.rate : ℚ≥0) : ℝ) *
      ((∑ y,
          (p x / (bound : ℝ) * (T.kernel x : Step V → ℝ) (Step.next y)
            + (1 - p x / (bound : ℝ))
              * ((ProbState.dirac (Step.stay : Step V)
                  : ProbState (Step V)) : Step V → ℝ) (Step.next y))
            * (f y - f x))
        - (p x / (bound : ℝ) * (T.kernel x : Step V → ℝ) Step.cemetery
            + (1 - p x / (bound : ℝ))
              * ((ProbState.dirac (Step.stay : Step V)
                  : ProbState (Step V)) : Step V → ℝ) Step.cemetery)
            * f x)
    = p x * T.generator f x
  simp only [dirac_stay_apply_next, dirac_stay_apply_cemetery, mul_zero,
    add_zero]
  rw [hE]
  rcases eq_or_ne bound 0 with rfl | hb
  · have hp0 : p x = 0 :=
      le_antisymm (by simpa using (hp x).2) (hp x).1
    simp [hp0]
  · have hbR : ((bound : ℚ≥0) : ℝ) ≠ 0 := by
      simpa using hb
    have hsum :
        (∑ y, p x / (bound : ℝ)
            * (T.kernel x : Step V → ℝ) (Step.next y)
            * (f y - f x))
          = p x / (bound : ℝ) *
              ∑ y, (T.kernel x : Step V → ℝ) (Step.next y)
                * (f y - f x) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hsum]
    push_cast
    field_simp

/-- The zero normal form: rate zero, idling at stay. -/
noncomputable def zero : ThinningForm V :=
  ⟨0, fun _ => ProbState.dirac Step.stay⟩

@[simp] theorem rate_zero : (zero : ThinningForm V).rate = 0 := rfl

end ScaleZero

/-! ## Coordinate extension and interleaving on normal forms -/

section Product

variable {V₁ V₂ : Type u} [Fintype V₁] [Fintype V₂]

private theorem sum_pushFun_mapNext_fst (κ : Step V₁ → ℝ) (x₂ : V₂)
    (g : V₁ × V₂ → ℝ) :
    (∑ y : V₁ × V₂,
        pushFun (Step.mapNext fun y₁ => (y₁, x₂)) κ (Step.next y) * g y)
      = ∑ y₁, κ (Step.next y₁) * g (y₁, x₂) := by
  classical
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y₁ _ => ?_
  have hstep : ∀ y₂ : V₂,
      pushFun (Step.mapNext fun z => (z, x₂)) κ (Step.next (y₁, y₂))
          * g (y₁, y₂)
        = if y₂ = x₂ then κ (Step.next y₁) * g (y₁, y₂) else 0 := by
    intro y₂
    by_cases hy : y₂ = x₂
    · rw [if_pos hy, hy]
      have himg : (Step.next (y₁, x₂) : Step (V₁ × V₂))
          = Step.mapNext (fun z => (z, x₂)) (Step.next y₁) := rfl
      rw [himg, pushFun_apply_of_injective
        (Step.mapNext_injective fun a b h => congrArg Prod.fst h) κ
        (Step.next y₁)]
    · have hne : ∀ s : Step V₁,
          Step.mapNext (fun z => (z, x₂)) s ≠ Step.next (y₁, y₂) := by
        intro s
        cases s with
        | next z =>
            intro h
            have h' : (Step.next (z, x₂) : Step (V₁ × V₂))
                = Step.next (y₁, y₂) := h
            exact hy ((congrArg Prod.snd (Step.next_injective h')).symm)
        | stay => exact fun h => nomatch h
        | cemetery => exact fun h => nomatch h
      rw [if_neg hy, pushFun_apply_of_forall_ne hne κ, zero_mul]
  rw [Finset.sum_congr rfl fun y₂ _ => hstep y₂,
    Finset.sum_ite_eq' Finset.univ x₂
      (fun y₂ => κ (Step.next y₁) * g (y₁, y₂))]
  simp

private theorem sum_pushFun_mapNext_snd (κ : Step V₂ → ℝ) (x₁ : V₁)
    (g : V₁ × V₂ → ℝ) :
    (∑ y : V₁ × V₂,
        pushFun (Step.mapNext fun y₂ => (x₁, y₂)) κ (Step.next y) * g y)
      = ∑ y₂, κ (Step.next y₂) * g (x₁, y₂) := by
  classical
  rw [Fintype.sum_prod_type]
  have hrow : ∀ y₁ : V₁, (∑ y₂ : V₂,
      pushFun (Step.mapNext fun z => (x₁, z)) κ (Step.next (y₁, y₂))
        * g (y₁, y₂))
      = if y₁ = x₁ then ∑ y₂, κ (Step.next y₂) * g (y₁, y₂) else 0 := by
    intro y₁
    by_cases hy : y₁ = x₁
    · rw [if_pos hy, hy]
      refine Finset.sum_congr rfl fun y₂ _ => ?_
      have himg : (Step.next (x₁, y₂) : Step (V₁ × V₂))
          = Step.mapNext (fun z => (x₁, z)) (Step.next y₂) := rfl
      rw [himg, pushFun_apply_of_injective
        (Step.mapNext_injective fun a b h => congrArg Prod.snd h) κ
        (Step.next y₂)]
    · rw [if_neg hy]
      refine Finset.sum_eq_zero fun y₂ _ => ?_
      have hne : ∀ s : Step V₂,
          Step.mapNext (fun z => (x₁, z)) s ≠ Step.next (y₁, y₂) := by
        intro s
        cases s with
        | next z =>
            intro h
            have h' : (Step.next (x₁, z) : Step (V₁ × V₂))
                = Step.next (y₁, y₂) := h
            exact hy ((congrArg Prod.fst (Step.next_injective h')).symm)
        | stay => exact fun h => nomatch h
        | cemetery => exact fun h => nomatch h
      rw [pushFun_apply_of_forall_ne hne κ, zero_mul]
  rw [Finset.sum_congr rfl fun y₁ _ => hrow y₁,
    Finset.sum_ite_eq' Finset.univ x₁
      (fun y₁ => ∑ y₂, κ (Step.next y₂) * g (y₁, y₂))]
  simp

/-- Extend a normal form to a product state space, acting on the
first coordinate: the kernel is pushed along the tag-preserving
relabelling — next-states move the first coordinate and hold the
second, stay stays, and the cemetery channel is transported
unchanged (that preservation is content:
`washKill_not_generator_invisible`). -/
noncomputable def extendFst (T : ThinningForm V₁) : ThinningForm (V₁ × V₂) :=
  ⟨T.rate, fun x =>
    ProbState.push (Step.mapNext fun y₁ => (y₁, x.2)) (T.kernel x.1)⟩

/-- Extend a normal form to a product state space, acting on the
second coordinate. -/
noncomputable def extendSnd (T : ThinningForm V₂) : ThinningForm (V₁ × V₂) :=
  ⟨T.rate, fun x =>
    ProbState.push (Step.mapNext fun y₂ => (x.1, y₂)) (T.kernel x.2)⟩

@[simp] theorem rate_extendFst (T : ThinningForm V₁) :
    (extendFst (V₂ := V₂) T).rate = T.rate := rfl

@[simp] theorem rate_extendSnd (T : ThinningForm V₂) :
    (extendSnd (V₁ := V₁) T).rate = T.rate := rfl

/-- The generator of a first-coordinate extension acts on the first
slot, the second held fixed — including the killing term, which the
tag-preserving pushforward transports unchanged. -/
theorem generator_extendFst (T : ThinningForm V₁) (f : V₁ × V₂ → ℝ)
    (x : V₁ × V₂) :
    (extendFst (V₂ := V₂) T).generator f x
      = T.generator (fun y₁ => f (y₁, x.2)) x.1 := by
  show (T.rate : ℝ) *
      ((∑ y : V₁ × V₂,
          (ProbState.push (Step.mapNext fun y₁ => (y₁, x.2)) (T.kernel x.1)
            : Step (V₁ × V₂) → ℝ) (Step.next y) * (f y - f x))
        - (ProbState.push (Step.mapNext fun y₁ => (y₁, x.2)) (T.kernel x.1)
            : Step (V₁ × V₂) → ℝ) Step.cemetery * f x)
    = T.generator (fun y₁ => f (y₁, x.2)) x.1
  rw [ProbState.push_coe,
    sum_pushFun_mapNext_fst ((T.kernel x.1) : Step V₁ → ℝ) x.2
      (fun y => f y - f x),
    pushFun_mapNext_cemetery]
  rfl

/-- The generator of a second-coordinate extension acts on the second
slot, the first held fixed. -/
theorem generator_extendSnd (T : ThinningForm V₂) (f : V₁ × V₂ → ℝ)
    (x : V₁ × V₂) :
    (extendSnd (V₁ := V₁) T).generator f x
      = T.generator (fun y₂ => f (x.1, y₂)) x.2 := by
  show (T.rate : ℝ) *
      ((∑ y : V₁ × V₂,
          (ProbState.push (Step.mapNext fun y₂ => (x.1, y₂)) (T.kernel x.2)
            : Step (V₁ × V₂) → ℝ) (Step.next y) * (f y - f x))
        - (ProbState.push (Step.mapNext fun y₂ => (x.1, y₂)) (T.kernel x.2)
            : Step (V₁ × V₂) → ℝ) Step.cemetery * f x)
    = T.generator (fun y₂ => f (x.1, y₂)) x.2
  rw [ProbState.push_coe,
    sum_pushFun_mapNext_snd ((T.kernel x.2) : Step V₂ → ℝ) x.1
      (fun y => f y - f x),
    pushFun_mapNext_cemetery]
  rfl

/-- Interleaving of thinning normal forms on independent components:
extend each to the product — the other coordinate stays — and
superpose. -/
noncomputable def interleave (T₁ : ThinningForm V₁) (T₂ : ThinningForm V₂) :
    ThinningForm (V₁ × V₂) :=
  (extendFst T₁).superpose (extendSnd T₂)

/-- Interleaved rates add: the grading of the normal-form product is
the sum of the gradings. -/
@[simp] theorem rate_interleave (T₁ : ThinningForm V₁)
    (T₂ : ThinningForm V₂) :
    (T₁.interleave T₂).rate = T₁.rate + T₂.rate := rfl

/-- **The Leibniz rule at the normal-form level**: the interleaved
generator is the sum of the componentwise generators, each acting on
its own slot. -/
theorem generator_interleave (T₁ : ThinningForm V₁) (T₂ : ThinningForm V₂)
    (f : V₁ × V₂ → ℝ) (x : V₁ × V₂) :
    (T₁.interleave T₂).generator f x
      = T₁.generator (fun y₁ => f (y₁, x.2)) x.1
        + T₂.generator (fun y₂ => f (x.1, y₂)) x.2 := by
  show ((extendFst T₁).superpose (extendSnd T₂)).generator f x = _
  rw [generator_superpose, generator_extendFst, generator_extendSnd]

end Product

/-! ## The separation: killing mass may not be reclassified as stay -/

/-- **Killing mass may not be reclassified as stay**: pushing a
normal-form kernel along the tag-collapsing map that sends the
cemetery to stay moves the generator — the mechanical complement of
`generator_absorbDiagonal` (self-jump mass may be so reclassified;
killing mass may not).  This is the reason the coordinate extensions
transport the cemetery channel unchanged: the tag bookkeeping is
content, not plumbing. -/
theorem washKill_not_generator_invisible :
    ∃ (T : ThinningForm PUnit) (f : PUnit → ℝ) (x : PUnit),
      (ThinningForm.mk T.rate
          (fun v => ProbState.push Step.washKill (T.kernel v))).generator f x
        ≠ T.generator f x := by
  classical
  refine ⟨⟨1, fun _ => ProbState.dirac Step.cemetery⟩, fun _ => 1,
    PUnit.unit, ?_⟩
  have hwash : ∀ s : Step PUnit, Step.washKill s ≠ Step.cemetery := by
    intro s
    cases s with
    | next v => exact fun h => nomatch h
    | stay => exact fun h => nomatch h
    | cemetery => exact fun h => nomatch h
  have hL : (ThinningForm.mk (1 : ℚ≥0)
      (fun _ : PUnit => ProbState.push Step.washKill
        (ProbState.dirac (Step.cemetery : Step PUnit)))).generator
      (fun _ => (1 : ℝ)) PUnit.unit = 0 := by
    rw [generator_def, ProbState.push_coe,
      pushFun_apply_of_forall_ne hwash]
    simp
  have hR : ((⟨1, fun _ => ProbState.dirac (Step.cemetery : Step PUnit)⟩
      : ThinningForm PUnit)).generator (fun _ => (1 : ℝ)) PUnit.unit
      = -1 := by
    rw [generator_def]
    simp
  show (ThinningForm.mk (1 : ℚ≥0)
      (fun _ : PUnit => ProbState.push Step.washKill
        (ProbState.dirac (Step.cemetery : Step PUnit)))).generator
      (fun _ => (1 : ℝ)) PUnit.unit
    ≠ ((⟨1, fun _ => ProbState.dirac (Step.cemetery : Step PUnit)⟩
      : ThinningForm PUnit)).generator (fun _ => (1 : ℝ)) PUnit.unit
  rw [hL, hR]
  norm_num

end ThinningForm

/-! ## Elaboration is the homomorphism -/

namespace JumpTerm

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Elaboration carries superposition to the normal-form
superposition on the nose**: elaboration is, by construction, the
homomorphic extension of the normal-form algebra along the six
generators, and on the module structure the commutation is
definitional — this proof is `rfl`. -/
theorem elaborate_superpose (J₁ J₂ : JumpTerm V) :
    (superpose J₁ J₂).elaborate
      = (J₁.elaborate).superpose (J₂.elaborate) := rfl

/-- Elaboration carries scaling to the normal-form thinning gate on
the nose. -/
theorem elaborate_scale (p : V → ℝ) (bound : ℚ≥0)
    (hp : ∀ x, p x ∈ Set.Icc (0 : ℝ) (bound : ℝ)) (J : JumpTerm V) :
    (scale p bound hp J).elaborate = (J.elaborate).scale p bound hp := rfl

/-- Elaboration carries the zero generator to the zero normal form on
the nose. -/
theorem elaborate_zero :
    (zero : JumpTerm V).elaborate = ThinningForm.zero := rfl

section Product

variable {V₁ V₂ : Type u} [Fintype V₁] [Fintype V₂]
variable [DecidableEq V₁] [DecidableEq V₂]

/-- **Elaboration commutes with interleaving, in the thinning
quotient**: elaborating the interleaved term and interleaving the
elaborations denote the same generator functional.  (Raw normal-form
equality is not the tier's equality — normal forms are deliberately
non-unique; the quotient is where composites live.)  The proof is the
equational chain through elaboration soundness and the two Leibniz
rules, term-level and normal-form-level. -/
theorem generator_elaborate_interleave (J₁ : JumpTerm V₁)
    (J₂ : JumpTerm V₂) :
    (interleave J₁ J₂).elaborate.generator
      = ((J₁.elaborate).interleave (J₂.elaborate)).generator := by
  funext f x
  rw [generator_elaborate, generator_interleave,
    ThinningForm.generator_interleave,
    generator_elaborate J₁, generator_elaborate J₂]

end Product

end JumpTerm

end SuFunctor.Stochastic

#print axioms SuFunctor.Stochastic.pushFun_mapNext_stay
#print axioms SuFunctor.Stochastic.pushFun_mapNext_cemetery
#print axioms SuFunctor.Stochastic.ThinningForm.generator_superpose
#print axioms SuFunctor.Stochastic.ThinningForm.generator_scale
#print axioms SuFunctor.Stochastic.ThinningForm.generator_extendFst
#print axioms SuFunctor.Stochastic.ThinningForm.generator_extendSnd
#print axioms SuFunctor.Stochastic.ThinningForm.generator_interleave
#print axioms SuFunctor.Stochastic.ThinningForm.washKill_not_generator_invisible
#print axioms SuFunctor.Stochastic.JumpTerm.elaborate_superpose
#print axioms SuFunctor.Stochastic.JumpTerm.elaborate_scale
#print axioms SuFunctor.Stochastic.JumpTerm.elaborate_zero
#print axioms SuFunctor.Stochastic.JumpTerm.generator_elaborate_interleave
