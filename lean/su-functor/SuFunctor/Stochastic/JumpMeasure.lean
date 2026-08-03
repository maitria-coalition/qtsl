import SuFunctor.Stochastic.NoiseSemantics
import SuFunctor.Universe.TotalCitizenship

/-! # Jump-measure hypernets: the measure-weighted tier at finite outcome

The probabilistic tier (`SuFunctor.Stochastic.NoiseSemantics`) is a
Markov-category tier: kernels of mass exactly one, by theorem.  The
measure-weighted tier above it adds what dynamics needs and mass-one
kernels cannot say — rates, killing, superposition — as **six
generators**

  `jump · stay · kill · scale · superpose · zero`

over a finite state space, with three deliberate distinctions:

* **discard ≠ kill ≠ stay.**  Discard (the probabilistic tier's
  marginalization) is mass-preserving plumbing.  Kill sends trajectory
  mass out of the state space — the `-κ·V` term of the extended
  generator; nothing at the probabilistic tier can express it
  (normalization is a theorem there).  Stay is the Dirac self-loop —
  generator-invisible, grading-visible.
* **Mass bookkeeping is a grading on the syntax.**  Every term carries
  a rational intensity majorant (`intensity`); `scale` cannot be
  written without declaring a majorant, and its side condition
  `0 ≤ p ≤ bound` is a formation premise.  Consequently
  **sub-stochastic deficit is unrepresentable**: the normal form's
  kernel is a mass-one state of the tagged alphabet, all mass is
  explicitly named next/stay/cemetery, and there is no syntax whose
  denotation silently loses mass.  (The finite-state rate stock makes
  the same move one storey down: a diagonal rate entry is
  unrepresentable rather than linted —
  `SuFunctor.Adequacy.CtmcJumpChain`.)
* **Bounded intensity is the composable class.**  The majorant is
  computed by the typing derivation (`scale` multiplies, `superpose`
  adds), so a declared rational bound is available syntactically —
  exactly the number non-explosion budgets consume — and unbounded
  intensities have no syntax at all.

**The thinning normal form.**  Every term elaborates (`elaborate`),
definitionally and by structural induction, to a scalar majorant
paired with a mass-one kernel into the tagged alphabet
`Step V = next V | stay | cemetery` (`ThinningForm`).  State-dependent
intensities thin: `scale` elaborates to a convex gate between the
scaled kernel and an *explicit* stay branch — forced by the type,
since the elaboration cannot emit sub-mass.  Soundness
(`generator_elaborate`): elaboration preserves the generator
functional.  Mass accounting (`elaborate_mass_partition`): the
declared intensity distributes exactly over the three named channels.

**The thinning quotient.**  The normal form is deliberately
non-unique; the semantics-preserving moves mechanized here are
dilation (`ThinningForm.generator_dilate` — inflate the majorant,
dilute with stay) and phantom-jump absorption
(`ThinningForm.generator_absorbDiagonal` — self-jump mass is
generator-invisible and may be reclassified as stay; killing mass may
**not**, which is the kill/stay separation made mechanical).

**Module structure and interleaving.**  `scale` acts as a module
action on terms (composition multiplies observables and majorants; it
distributes over `superpose`), and independent components compose by
interleaving: `interleave J₁ J₂` jumps in one coordinate while the
other *stays* — the second place `stay` earns its keep — with the
generator Leibniz rule `generator_interleave`.
-/

/-! ## Carrier plumbing: the convex combination on the flat carrier -/

namespace SuFunctor.Universe.ProbState

variable {V : Type*} [Fintype V]

/-- The convex combination of two probability states (the flat carrier
is convex, so the combination stays inside).  The mirror of
`BelState.mix`; unifying the two behind one generic definition is the
routine refactoring the carrier module already flags. -/
noncomputable def mix (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (μ ν : ProbState V) : ProbState V :=
  ⟨t • (μ : V → ℝ) + (1 - t) • (ν : V → ℝ),
    convex_probCarrier μ.2 ν.2 h0 (by linarith) (by ring)⟩

@[simp] theorem mix_apply (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (μ ν : ProbState V) (v : V) :
    ((mix t h0 h1 μ ν : ProbState V) : V → ℝ) v
      = t * (μ : V → ℝ) v + (1 - t) * (ν : V → ℝ) v := rfl

end SuFunctor.Universe.ProbState

namespace SuFunctor.Stochastic

open SuFunctor.Universe
open scoped NNRat

universe u

/-! ## The tagged one-step alphabet -/

/-- The one-step outcome alphabet over a state space: move to a next
state, stay put, or leave for the cemetery.  The cemetery tag is the
killing channel — trajectory death as an explicit *outcome*, never a
mass deficit. -/
inductive Step (V : Type u) : Type u where
  | next (v : V)
  | stay
  | cemetery
deriving DecidableEq

namespace Step

variable {V : Type*}

/-- The alphabet is the state space plus two tags. -/
def equivSumBool (V : Type*) : Step V ≃ V ⊕ Bool where
  toFun s := match s with
    | .next v => Sum.inl v
    | .stay => Sum.inr false
    | .cemetery => Sum.inr true
  invFun s := match s with
    | Sum.inl v => .next v
    | Sum.inr false => .stay
    | Sum.inr true => .cemetery
  left_inv s := by cases s <;> rfl
  right_inv s := by
    rcases s with v | b
    · rfl
    · cases b <;> rfl

instance [Fintype V] : Fintype (Step V) :=
  Fintype.ofEquiv (V ⊕ Bool) (equivSumBool V).symm

theorem next_injective : Function.Injective (next : V → Step V) :=
  fun _ _ h => by injection h

/-- Sums over the alphabet decompose into the next-block and the two
tags. -/
theorem sum_eq [Fintype V] (g : Step V → ℝ) :
    ∑ s, g s = (∑ v, g (next v)) + g stay + g cemetery := by
  rw [← Equiv.sum_comp (equivSumBool V).symm g]
  simp only [Fintype.sum_sum_type]
  have hbool : (∑ b : Bool, g ((equivSumBool V).symm (Sum.inr b)))
      = g cemetery + g stay := by
    rw [Fintype.sum_bool]
    rfl
  have hnext : (∑ v : V, g ((equivSumBool V).symm (Sum.inl v)))
      = ∑ v, g (next v) := rfl
  rw [hbool, hnext]
  ring

end Step

/-- A pushforward evaluates to zero off the range of the outcome
map. -/
theorem pushFun_apply_of_forall_ne {V W : Type*} [Fintype V]
    {ι : V → W} {w : W} (h : ∀ v, ι v ≠ w) (x : V → ℝ) :
    pushFun ι x w = 0 :=
  Finset.sum_eq_zero fun v _ => if_neg (h v)

/-- Tagging a kernel with `next` puts no mass on the cemetery. -/
@[simp] theorem pushFun_next_cemetery {V : Type*} [Fintype V] (x : V → ℝ) :
    pushFun (Step.next : V → Step V) x Step.cemetery = 0 :=
  pushFun_apply_of_forall_ne (ι := Step.next) (w := Step.cemetery)
    (fun _ h => nomatch h) x

section DiracSimp

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem dirac_stay_apply_next (y : V) :
    ((ProbState.dirac (Step.stay : Step V) : ProbState (Step V))
      : Step V → ℝ) (Step.next y) = 0 :=
  ProbState.dirac_apply_of_ne (fun h => nomatch h)

@[simp] theorem dirac_stay_apply_cemetery :
    ((ProbState.dirac (Step.stay : Step V) : ProbState (Step V))
      : Step V → ℝ) Step.cemetery = 0 :=
  ProbState.dirac_apply_of_ne (fun h => nomatch h)

@[simp] theorem dirac_cemetery_apply_next (y : V) :
    ((ProbState.dirac (Step.cemetery : Step V) : ProbState (Step V))
      : Step V → ℝ) (Step.next y) = 0 :=
  ProbState.dirac_apply_of_ne (fun h => nomatch h)

@[simp] theorem dirac_cemetery_apply_cemetery :
    ((ProbState.dirac (Step.cemetery : Step V) : ProbState (Step V))
      : Step V → ℝ) Step.cemetery = 1 :=
  ProbState.dirac_apply_same _

end DiracSimp

/-! ## Weight-bound helpers (the formation premises, consumed) -/

/-- A majorant-bounded nonnegative observable thins to a convex
weight.  Total division makes the degenerate majorant harmless: at
`b = 0` the premise forces `p = 0` and the weight is `0`. -/
theorem div_mem_Icc_of_Icc {p b : ℝ} (hb : 0 ≤ b)
    (hp : p ∈ Set.Icc 0 b) : p / b ∈ Set.Icc (0 : ℝ) 1 := by
  rcases eq_or_lt_of_le hb with heq | hpos
  · rw [← heq, div_zero]
    exact ⟨le_refl 0, zero_le_one⟩
  · exact ⟨div_nonneg hp.1 hpos.le, (div_le_one hpos).mpr hp.2⟩

/-- A superposition weight is convex.  Total division makes the
all-zero superposition harmless: `0 / 0 = 0`. -/
theorem div_add_mem_Icc {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a / (a + b) ∈ Set.Icc (0 : ℝ) 1 := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with heq | hpos
  · rw [← heq, div_zero]
    exact ⟨le_refl 0, zero_le_one⟩
  · exact ⟨div_nonneg ha hpos.le,
      (div_le_one hpos).mpr (le_add_of_nonneg_right hb)⟩

/-! ## The six generators -/

/-- A term of the measure-weighted tier over a finite state space: the
six generators.  `jump` consumes a mass-one kernel (a
probabilistic-tier object); `scale` is unwritable without a declared
rational majorant and the side condition `0 ≤ p ≤ bound` — mass
bookkeeping as formation premise, the move that makes sub-stochastic
deficit unrepresentable rather than linted. -/
inductive JumpTerm (V : Type u) [Fintype V] : Type u where
  | jump (K : V → ProbState V)
  | stay
  | kill
  | scale (p : V → ℝ) (bound : ℚ≥0)
      (hp : ∀ x, p x ∈ Set.Icc (0 : ℝ) (bound : ℝ)) (J : JumpTerm V)
  | superpose (J₁ J₂ : JumpTerm V)
  | zero

variable {V : Type u} [Fintype V]

namespace JumpTerm

/-- The declared intensity majorant: the grading arithmetic.  A
syntactic rational, computed by the typing derivation — `scale`
multiplies, `superpose` adds — and hence available to non-explosion
budgets without semantic evaluation. -/
def intensity : JumpTerm V → ℚ≥0
  | jump _ => 1
  | stay => 1
  | kill => 1
  | scale _ b _ J => b * intensity J
  | superpose J₁ J₂ => intensity J₁ + intensity J₂
  | zero => 0

@[simp] theorem intensity_jump (K : V → ProbState V) :
    (jump K).intensity = 1 := rfl
@[simp] theorem intensity_stay : (stay : JumpTerm V).intensity = 1 := rfl
@[simp] theorem intensity_kill : (kill : JumpTerm V).intensity = 1 := rfl
@[simp] theorem intensity_scale (p : V → ℝ) (b : ℚ≥0) (hp) (J : JumpTerm V) :
    (scale p b hp J).intensity = b * J.intensity := rfl
@[simp] theorem intensity_superpose (J₁ J₂ : JumpTerm V) :
    (superpose J₁ J₂).intensity = J₁.intensity + J₂.intensity := rfl
@[simp] theorem intensity_zero : (zero : JumpTerm V).intensity = 0 := rfl

/-- The generator functional of a term: the contribution to the
extended generator, acting on an observable.  Jump mass at the current
state contributes nothing (`f y - f x` vanishes at `y = x`) — the
phantom-jump quotient is built into the denotation. -/
noncomputable def generator : JumpTerm V → (V → ℝ) → V → ℝ
  | jump K => fun f x => ∑ y, (K x : V → ℝ) y * (f y - f x)
  | stay => fun _ _ => 0
  | kill => fun f x => -(f x)
  | scale p _ _ J => fun f x => p x * generator J f x
  | superpose J₁ J₂ => fun f x => generator J₁ f x + generator J₂ f x
  | zero => fun _ _ => 0

@[simp] theorem generator_jump (K : V → ProbState V) (f : V → ℝ) (x : V) :
    (jump K).generator f x = ∑ y, (K x : V → ℝ) y * (f y - f x) := rfl
@[simp] theorem generator_stay (f : V → ℝ) (x : V) :
    (stay : JumpTerm V).generator f x = 0 := rfl
@[simp] theorem generator_kill (f : V → ℝ) (x : V) :
    (kill : JumpTerm V).generator f x = -(f x) := rfl
@[simp] theorem generator_scale (p : V → ℝ) (b : ℚ≥0) (hp) (J : JumpTerm V)
    (f : V → ℝ) (x : V) :
    (scale p b hp J).generator f x = p x * J.generator f x := rfl
@[simp] theorem generator_superpose (J₁ J₂ : JumpTerm V) (f : V → ℝ) (x : V) :
    (superpose J₁ J₂).generator f x
      = J₁.generator f x + J₂.generator f x := rfl
@[simp] theorem generator_zero (f : V → ℝ) (x : V) :
    (zero : JumpTerm V).generator f x = 0 := rfl

/-- `stay` and `zero` denote the same (zero) generator — they differ
only in grading (`intensity_stay` vs `intensity_zero`), which is
certificate-relevant content: one point of the quotient, two points of
the syntax. -/
theorem generator_stay_eq_generator_zero :
    (stay : JumpTerm V).generator = (zero : JumpTerm V).generator := rfl

end JumpTerm

/-! ## The thinning normal form -/

/-- A thinning normal form: a scalar rational majorant paired with a
mass-one kernel into the tagged alphabet.  All mass is explicitly
named — next, stay, or cemetery — so a deficit has no representation.
This pair is the kernel presentation the schema stores: the majorant
is the grading, the kernel a probabilistic-tier citation. -/
structure ThinningForm (V : Type u) [Fintype V] : Type u where
  /-- The intensity majorant. -/
  rate : ℚ≥0
  /-- The mass-one one-step kernel. -/
  kernel : V → ProbState (Step V)

namespace ThinningForm

/-- The generator functional of a normal form: rate times the tagged
increment — next mass pairs state increments, cemetery mass pays the
killing term, stay mass is invisible. -/
noncomputable def generator (T : ThinningForm V) (f : V → ℝ) (x : V) : ℝ :=
  (T.rate : ℝ) *
    ((∑ y, (T.kernel x : Step V → ℝ) (Step.next y) * (f y - f x))
      - (T.kernel x : Step V → ℝ) Step.cemetery * f x)

theorem generator_def (T : ThinningForm V) (f : V → ℝ) (x : V) :
    T.generator f x
      = (T.rate : ℝ) *
          ((∑ y, (T.kernel x : Step V → ℝ) (Step.next y) * (f y - f x))
            - (T.kernel x : Step V → ℝ) Step.cemetery * f x) := rfl

end ThinningForm

namespace JumpTerm

variable [DecidableEq V]

/-- **Elaboration to the thinning normal form**, by structural
induction.  `jump` tags its kernel; `stay`/`kill` are Diracs at their
tags; `scale` thins — a convex gate between the scaled body and an
*explicit* stay branch, whose weight bound is exactly the formation
premise (drop the premise and this definition does not typecheck:
deficit-unrepresentability is the typing theorem); `superpose` mixes
in proportion to the majorants; `zero` idles at rate zero. -/
noncomputable def elaborate : JumpTerm V → ThinningForm V
  | jump K => ⟨1, fun x => ProbState.push Step.next (K x)⟩
  | stay => ⟨1, fun _ => ProbState.dirac Step.stay⟩
  | kill => ⟨1, fun _ => ProbState.dirac Step.cemetery⟩
  | scale p b hp J =>
      ⟨b * (elaborate J).rate, fun x =>
        ProbState.mix (p x / (b : ℝ))
          (div_mem_Icc_of_Icc (NNRat.cast_nonneg b) (hp x)).1
          (div_mem_Icc_of_Icc (NNRat.cast_nonneg b) (hp x)).2
          ((elaborate J).kernel x) (ProbState.dirac Step.stay)⟩
  | superpose J₁ J₂ =>
      ⟨(elaborate J₁).rate + (elaborate J₂).rate, fun x =>
        ProbState.mix
          (((elaborate J₁).rate : ℝ)
            / (((elaborate J₁).rate : ℝ) + ((elaborate J₂).rate : ℝ)))
          (div_add_mem_Icc (NNRat.cast_nonneg (elaborate J₁).rate)
            (NNRat.cast_nonneg (elaborate J₂).rate)).1
          (div_add_mem_Icc (NNRat.cast_nonneg (elaborate J₁).rate)
            (NNRat.cast_nonneg (elaborate J₂).rate)).2
          ((elaborate J₁).kernel x) ((elaborate J₂).kernel x)⟩
  | zero => ⟨0, fun _ => ProbState.dirac Step.stay⟩

/-- The normal form's rate is the declared intensity majorant: the
grading is preserved by elaboration, on the nose. -/
theorem elaborate_rate (J : JumpTerm V) :
    (elaborate J).rate = J.intensity := by
  induction J with
  | jump K => rfl
  | stay => rfl
  | kill => rfl
  | scale p b hp J ih =>
      show b * (elaborate J).rate = b * J.intensity
      rw [ih]
  | superpose J₁ J₂ ih₁ ih₂ =>
      show (elaborate J₁).rate + (elaborate J₂).rate
        = J₁.intensity + J₂.intensity
      rw [ih₁, ih₂]
  | zero => rfl

@[simp] theorem elaborate_stay_rate :
    (elaborate (stay : JumpTerm V)).rate = 1 := rfl

@[simp] theorem elaborate_zero_rate :
    (elaborate (zero : JumpTerm V)).rate = 0 := rfl

/-- **Elaboration soundness**: the thinning normal form denotes the
same generator functional as the term it elaborates.  The convex
re-association arithmetic of the gates is exactly what this induction
discharges, case by case. -/
theorem generator_elaborate (J : JumpTerm V) :
    (elaborate J).generator = J.generator := by
  induction J with
  | jump K =>
      funext f x
      show ((1 : ℚ≥0) : ℝ) *
          ((∑ y, pushFun Step.next ((K x : V → ℝ)) (Step.next y) * (f y - f x))
            - pushFun Step.next ((K x : V → ℝ)) Step.cemetery * f x)
        = ∑ y, (K x : V → ℝ) y * (f y - f x)
      rw [pushFun_next_cemetery]
      have hpt : ∀ y, pushFun Step.next ((K x : V → ℝ)) (Step.next y)
          = (K x : V → ℝ) y :=
        fun y => pushFun_apply_of_injective Step.next_injective _ y
      simp only [hpt, NNRat.cast_one, one_mul, zero_mul, sub_zero]
  | stay =>
      funext f x
      show ((1 : ℚ≥0) : ℝ) *
          ((∑ y,
              ((ProbState.dirac (Step.stay : Step V) : ProbState (Step V))
                : Step V → ℝ) (Step.next y) * (f y - f x))
            - ((ProbState.dirac (Step.stay : Step V) : ProbState (Step V))
                : Step V → ℝ) Step.cemetery * f x)
        = 0
      simp
  | kill =>
      funext f x
      show ((1 : ℚ≥0) : ℝ) *
          ((∑ y,
              ((ProbState.dirac (Step.cemetery : Step V) : ProbState (Step V))
                : Step V → ℝ) (Step.next y) * (f y - f x))
            - ((ProbState.dirac (Step.cemetery : Step V) : ProbState (Step V))
                : Step V → ℝ) Step.cemetery * f x)
        = -(f x)
      simp
  | scale p b hp J ih =>
      funext f x
      have hB := congrFun (congrFun ih f) x
      have hEJ : (elaborate J).generator f x
          = ((elaborate J).rate : ℝ) *
              ((∑ y, ((elaborate J).kernel x : Step V → ℝ) (Step.next y)
                  * (f y - f x))
                - ((elaborate J).kernel x : Step V → ℝ) Step.cemetery
                  * f x) := rfl
      show ((b * (elaborate J).rate : ℚ≥0) : ℝ) *
          ((∑ y,
              (p x / (b : ℝ)
                  * ((elaborate J).kernel x : Step V → ℝ) (Step.next y)
                + (1 - p x / (b : ℝ))
                  * ((ProbState.dirac (Step.stay : Step V)
                      : ProbState (Step V)) : Step V → ℝ) (Step.next y))
                * (f y - f x))
            - (p x / (b : ℝ)
                  * ((elaborate J).kernel x : Step V → ℝ) Step.cemetery
                + (1 - p x / (b : ℝ))
                  * ((ProbState.dirac (Step.stay : Step V)
                      : ProbState (Step V)) : Step V → ℝ) Step.cemetery)
                * f x)
        = p x * J.generator f x
      simp only [dirac_stay_apply_next, dirac_stay_apply_cemetery, mul_zero,
        add_zero]
      rw [← hB, hEJ]
      rcases eq_or_ne b 0 with rfl | hb
      · have hp0 : p x = 0 :=
          le_antisymm (by simpa using (hp x).2) (hp x).1
        simp [hp0]
      · have hbR : ((b : ℚ≥0) : ℝ) ≠ 0 := by
          simpa using hb
        have hsum :
            (∑ y, p x / (b : ℝ)
                * ((elaborate J).kernel x : Step V → ℝ) (Step.next y)
                * (f y - f x))
              = p x / (b : ℝ) *
                  ∑ y, ((elaborate J).kernel x : Step V → ℝ) (Step.next y)
                    * (f y - f x) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
        rw [hsum]
        push_cast
        field_simp
  | superpose J₁ J₂ ih₁ ih₂ =>
      funext f x
      have hB₁ := congrFun (congrFun ih₁ f) x
      have hB₂ := congrFun (congrFun ih₂ f) x
      have hE₁ : (elaborate J₁).generator f x
          = ((elaborate J₁).rate : ℝ) *
              ((∑ y, ((elaborate J₁).kernel x : Step V → ℝ) (Step.next y)
                  * (f y - f x))
                - ((elaborate J₁).kernel x : Step V → ℝ) Step.cemetery
                  * f x) := rfl
      have hE₂ : (elaborate J₂).generator f x
          = ((elaborate J₂).rate : ℝ) *
              ((∑ y, ((elaborate J₂).kernel x : Step V → ℝ) (Step.next y)
                  * (f y - f x))
                - ((elaborate J₂).kernel x : Step V → ℝ) Step.cemetery
                  * f x) := rfl
      have ha0 : (0 : ℝ) ≤ ((elaborate J₁).rate : ℝ) := NNRat.cast_nonneg _
      have hc0 : (0 : ℝ) ≤ ((elaborate J₂).rate : ℝ) := NNRat.cast_nonneg _
      show (((elaborate J₁).rate + (elaborate J₂).rate : ℚ≥0) : ℝ) *
          ((∑ y,
              (((elaborate J₁).rate : ℝ)
                    / (((elaborate J₁).rate : ℝ) + ((elaborate J₂).rate : ℝ))
                  * ((elaborate J₁).kernel x : Step V → ℝ) (Step.next y)
                + (1 - ((elaborate J₁).rate : ℝ)
                    / (((elaborate J₁).rate : ℝ) + ((elaborate J₂).rate : ℝ)))
                  * ((elaborate J₂).kernel x : Step V → ℝ) (Step.next y))
                * (f y - f x))
            - (((elaborate J₁).rate : ℝ)
                    / (((elaborate J₁).rate : ℝ) + ((elaborate J₂).rate : ℝ))
                  * ((elaborate J₁).kernel x : Step V → ℝ) Step.cemetery
                + (1 - ((elaborate J₁).rate : ℝ)
                    / (((elaborate J₁).rate : ℝ) + ((elaborate J₂).rate : ℝ)))
                  * ((elaborate J₂).kernel x : Step V → ℝ) Step.cemetery)
                * f x)
        = J₁.generator f x + J₂.generator f x
      rw [← hB₁, ← hB₂, hE₁, hE₂, NNRat.cast_add]
      set a : ℝ := ((elaborate J₁).rate : ℝ) with ha
      set c : ℝ := ((elaborate J₂).rate : ℝ) with hc
      set A : ℝ := (∑ y, ((elaborate J₁).kernel x : Step V → ℝ) (Step.next y)
          * (f y - f x)) with hA
      set C : ℝ := (∑ y, ((elaborate J₂).kernel x : Step V → ℝ) (Step.next y)
          * (f y - f x)) with hC
      set dA : ℝ := ((elaborate J₁).kernel x : Step V → ℝ) Step.cemetery
        with hdA
      set dC : ℝ := ((elaborate J₂).kernel x : Step V → ℝ) Step.cemetery
        with hdC
      have hsplit :
          (∑ y,
              (a / (a + c)
                  * ((elaborate J₁).kernel x : Step V → ℝ) (Step.next y)
                + (1 - a / (a + c))
                  * ((elaborate J₂).kernel x : Step V → ℝ) (Step.next y))
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
  | zero =>
      funext f x
      show ((0 : ℚ≥0) : ℝ) *
          ((∑ y,
              ((ProbState.dirac (Step.stay : Step V) : ProbState (Step V))
                : Step V → ℝ) (Step.next y) * (f y - f x))
            - ((ProbState.dirac (Step.stay : Step V) : ProbState (Step V))
                : Step V → ℝ) Step.cemetery * f x)
        = 0
      simp

/-! ## Mass accounting: deficit is unrepresentable -/

/-- **Mass accounting**: the declared intensity distributes exactly
over the three named channels — next, stay, cemetery.  There is no
fourth channel: a deficit has no representation, so the identity is an
equation, not an inequality with a slack term. -/
theorem elaborate_mass_partition (J : JumpTerm V) (x : V) :
    ((elaborate J).rate : ℝ) *
        ((∑ y, ((elaborate J).kernel x : Step V → ℝ) (Step.next y))
          + ((elaborate J).kernel x : Step V → ℝ) Step.stay
          + ((elaborate J).kernel x : Step V → ℝ) Step.cemetery)
      = (J.intensity : ℝ) := by
  have hmass : (∑ y, ((elaborate J).kernel x : Step V → ℝ) (Step.next y))
      + ((elaborate J).kernel x : Step V → ℝ) Step.stay
      + ((elaborate J).kernel x : Step V → ℝ) Step.cemetery = 1 := by
    rw [← Step.sum_eq]
    exact ((elaborate J).kernel x).2.2
  rw [hmass, mul_one, elaborate_rate]

/-- The jump-plus-killing outflow never exceeds the declared
intensity: the majorant the typing derivation computes is a sound
bound — the number non-explosion budgets consume. -/
theorem outflow_le_intensity (J : JumpTerm V) (x : V) :
    ((elaborate J).rate : ℝ) *
        ((∑ y, ((elaborate J).kernel x : Step V → ℝ) (Step.next y))
          + ((elaborate J).kernel x : Step V → ℝ) Step.cemetery)
      ≤ (J.intensity : ℝ) := by
  have hpart := elaborate_mass_partition J x
  have hstay : 0 ≤ ((elaborate J).rate : ℝ) *
      ((elaborate J).kernel x : Step V → ℝ) Step.stay :=
    mul_nonneg (NNRat.cast_nonneg _) (((elaborate J).kernel x).2.1 _)
  nlinarith [hpart, hstay]

end JumpTerm

/-! ## The thinning quotient: semantics-preserving moves -/

namespace ThinningForm

variable [DecidableEq V]

/-- Dilation: inflate the majorant by `c ≥ 1` and dilute the kernel
with stay mass in exact compensation. -/
noncomputable def dilate (c : ℚ≥0) (hc : 1 ≤ c) (T : ThinningForm V) :
    ThinningForm V :=
  ⟨c * T.rate, fun x =>
    ProbState.mix ((c : ℝ))⁻¹
      (inv_nonneg.mpr (NNRat.cast_nonneg c))
      (by
        have hpos : (0 : ℝ) < (c : ℝ) :=
          lt_of_lt_of_le zero_lt_one (by exact_mod_cast hc)
        rw [inv_le_one₀ hpos]
        exact_mod_cast hc)
      (T.kernel x) (ProbState.dirac Step.stay)⟩

/-- **Dilation is generator-invisible**: inflating the rate and
diluting with stay moves within the thinning class. -/
theorem generator_dilate (c : ℚ≥0) (hc : 1 ≤ c) (T : ThinningForm V) :
    (T.dilate c hc).generator = T.generator := by
  funext f x
  have hpos : (0 : ℝ) < (c : ℝ) :=
    lt_of_lt_of_le zero_lt_one (by exact_mod_cast hc)
  show ((c * T.rate : ℚ≥0) : ℝ) *
      ((∑ y,
          (((c : ℝ))⁻¹ * (T.kernel x : Step V → ℝ) (Step.next y)
            + (1 - ((c : ℝ))⁻¹) *
              ((ProbState.dirac (Step.stay : Step V) : ProbState (Step V))
                : Step V → ℝ) (Step.next y)) * (f y - f x))
        - (((c : ℝ))⁻¹ * (T.kernel x : Step V → ℝ) Step.cemetery
            + (1 - ((c : ℝ))⁻¹) *
              ((ProbState.dirac (Step.stay : Step V) : ProbState (Step V))
                : Step V → ℝ) Step.cemetery) * f x)
    = T.generator f x
  simp only [dirac_stay_apply_next, dirac_stay_apply_cemetery, mul_zero,
    add_zero]
  rw [generator_def]
  have hsum : (∑ y, ((c : ℝ))⁻¹ * (T.kernel x : Step V → ℝ) (Step.next y)
        * (f y - f x))
      = ((c : ℝ))⁻¹ *
          ∑ y, (T.kernel x : Step V → ℝ) (Step.next y) * (f y - f x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hsum]
  have hne : ((c : ℚ≥0) : ℝ) ≠ 0 := ne_of_gt hpos
  push_cast
  field_simp

/-- Phantom-jump absorption: reclassify self-jump mass as stay. -/
noncomputable def absorbDiagonal (T : ThinningForm V) : ThinningForm V where
  rate := T.rate
  kernel := fun x =>
    ⟨fun s => match s with
      | Step.next y =>
          if y = x then 0 else (T.kernel x : Step V → ℝ) (Step.next y)
      | Step.stay => (T.kernel x : Step V → ℝ) Step.stay
          + (T.kernel x : Step V → ℝ) (Step.next x)
      | Step.cemetery => (T.kernel x : Step V → ℝ) Step.cemetery,
    by
      constructor
      · intro s
        match s with
        | Step.next y =>
            by_cases hy : y = x
            · simp [hy]
            · simpa [hy] using (T.kernel x).2.1 (Step.next y)
        | Step.stay =>
            exact add_nonneg ((T.kernel x).2.1 _) ((T.kernel x).2.1 _)
        | Step.cemetery => exact (T.kernel x).2.1 _
      · have hT : (∑ y, (T.kernel x : Step V → ℝ) (Step.next y))
            + (T.kernel x : Step V → ℝ) Step.stay
            + (T.kernel x : Step V → ℝ) Step.cemetery = 1 := by
          rw [← Step.sum_eq]
          exact (T.kernel x).2.2
        rw [Step.sum_eq]
        have hsplit : (∑ y, (T.kernel x : Step V → ℝ) (Step.next y))
            = (T.kernel x : Step V → ℝ) (Step.next x)
              + ∑ y ∈ Finset.univ.erase x,
                  (T.kernel x : Step V → ℝ) (Step.next y) :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ x)).symm
        have hite : (∑ y,
              (fun s => match s with
                | Step.next y =>
                    if y = x then 0
                    else (T.kernel x : Step V → ℝ) (Step.next y)
                | Step.stay => (T.kernel x : Step V → ℝ) Step.stay
                    + (T.kernel x : Step V → ℝ) (Step.next x)
                | Step.cemetery =>
                    (T.kernel x : Step V → ℝ) Step.cemetery)
                (Step.next y))
            = ∑ y ∈ Finset.univ.erase x,
                (T.kernel x : Step V → ℝ) (Step.next y) := by
          rw [← Finset.sum_erase Finset.univ
            (a := x)
            (f := fun y => if y = x then (0 : ℝ)
              else (T.kernel x : Step V → ℝ) (Step.next y))
            (by simp)]
          exact Finset.sum_congr rfl fun y hy =>
            if_neg (Finset.ne_of_mem_erase hy)
        rw [hite]
        linarith [hT, hsplit]⟩

/-- **Phantom jumps are generator-invisible**: self-jump mass may be
reclassified as stay without moving the denotation.  (Killing mass may
not — the cemetery channel appears in the generator — which is the
kill/stay separation.)  The finite-state rate stock's
diagonal-blindness is this move one storey down. -/
theorem generator_absorbDiagonal (T : ThinningForm V) :
    T.absorbDiagonal.generator = T.generator := by
  funext f x
  rw [generator_def, generator_def]
  have hL : (∑ y, (T.absorbDiagonal.kernel x : Step V → ℝ) (Step.next y)
        * (f y - f x))
      = ∑ y ∈ Finset.univ.erase x,
          (T.kernel x : Step V → ℝ) (Step.next y) * (f y - f x) := by
    have hterm : ∀ y, (T.absorbDiagonal.kernel x : Step V → ℝ) (Step.next y)
        = if y = x then 0 else (T.kernel x : Step V → ℝ) (Step.next y) :=
      fun y => rfl
    rw [Finset.sum_congr rfl fun y _ => by rw [hterm y]]
    rw [← Finset.add_sum_erase _
      (fun y =>
        (if y = x then 0 else (T.kernel x : Step V → ℝ) (Step.next y))
          * (f y - f x))
      (Finset.mem_univ x)]
    simp only [sub_self, mul_zero, zero_add]
    exact Finset.sum_congr rfl fun y hy => by
      rw [if_neg (Finset.ne_of_mem_erase hy)]
  have hR : (∑ y, (T.kernel x : Step V → ℝ) (Step.next y) * (f y - f x))
      = ∑ y ∈ Finset.univ.erase x,
          (T.kernel x : Step V → ℝ) (Step.next y) * (f y - f x) := by
    rw [← Finset.add_sum_erase _
      (fun y => (T.kernel x : Step V → ℝ) (Step.next y) * (f y - f x))
      (Finset.mem_univ x)]
    simp only [sub_self, mul_zero, zero_add]
  have hcem : (T.absorbDiagonal.kernel x : Step V → ℝ) Step.cemetery
      = (T.kernel x : Step V → ℝ) Step.cemetery := rfl
  have hrate : ((T.absorbDiagonal.rate : ℚ≥0) : ℝ) = ((T.rate : ℚ≥0) : ℝ) :=
    rfl
  rw [hL, hR, hcem, hrate]

end ThinningForm

/-! ## Module laws: `scale` as a module action -/

namespace JumpTerm

/-- Products of majorant-bounded observables are bounded by the
product majorant: the derived formation premise for composite
scaling. -/
theorem Icc_mul_of_Icc {p q : ℝ} {b c : ℚ≥0}
    (hp : p ∈ Set.Icc (0 : ℝ) (b : ℝ)) (hq : q ∈ Set.Icc (0 : ℝ) (c : ℝ)) :
    p * q ∈ Set.Icc (0 : ℝ) (((b * c : ℚ≥0)) : ℝ) := by
  constructor
  · exact mul_nonneg hp.1 hq.1
  · push_cast
    exact mul_le_mul hp.2 hq.2 hq.1 (NNRat.cast_nonneg b)

/-- Sums of majorant-bounded observables are bounded by the sum
majorant. -/
theorem Icc_add_of_Icc {p q : ℝ} {b c : ℚ≥0}
    (hp : p ∈ Set.Icc (0 : ℝ) (b : ℝ)) (hq : q ∈ Set.Icc (0 : ℝ) (c : ℝ)) :
    p + q ∈ Set.Icc (0 : ℝ) (((b + c : ℚ≥0)) : ℝ) := by
  constructor
  · exact add_nonneg hp.1 hq.1
  · push_cast
    exact add_le_add hp.2 hq.2

/-- Scaling composes multiplicatively: the module action's
associativity law, at the generator. -/
theorem generator_scale_scale (p q : V → ℝ) (b c : ℚ≥0) (hp hq)
    (J : JumpTerm V) :
    (scale p b hp (scale q c hq J)).generator
      = (scale (fun x => p x * q x) (b * c)
          (fun x => Icc_mul_of_Icc (hp x) (hq x)) J).generator := by
  funext f x
  simp only [generator_scale]
  ring

/-- Scaling by the constant one observable at majorant one is the
identity, at the generator: the module action's unit law. -/
theorem generator_scale_one (J : JumpTerm V) :
    (scale (fun _ => 1) 1
      (fun _ => ⟨zero_le_one, by norm_num⟩) J).generator
      = J.generator := by
  funext f x
  simp only [generator_scale]
  ring

/-- Scaling distributes over superposition: bilinearity, kernel
side. -/
theorem generator_scale_superpose (p : V → ℝ) (b : ℚ≥0) (hp)
    (J₁ J₂ : JumpTerm V) :
    (scale p b hp (superpose J₁ J₂)).generator
      = (superpose (scale p b hp J₁) (scale p b hp J₂)).generator := by
  funext f x
  simp only [generator_scale, generator_superpose]
  ring

/-- Observable addition superposes: bilinearity, observable side. -/
theorem generator_scale_add (p q : V → ℝ) (b c : ℚ≥0) (hp hq)
    (J : JumpTerm V) :
    (scale (fun x => p x + q x) (b + c)
        (fun x => Icc_add_of_Icc (hp x) (hq x)) J).generator
      = (superpose (scale p b hp J) (scale q c hq J)).generator := by
  funext f x
  simp only [generator_scale, generator_superpose]
  ring

/-- Superposition is associative at the generator. -/
theorem generator_superpose_assoc (J₁ J₂ J₃ : JumpTerm V) :
    (superpose J₁ (superpose J₂ J₃)).generator
      = (superpose (superpose J₁ J₂) J₃).generator := by
  funext f x
  simp only [generator_superpose]
  ring

/-- Superposition is commutative at the generator. -/
theorem generator_superpose_comm (J₁ J₂ : JumpTerm V) :
    (superpose J₁ J₂).generator = (superpose J₂ J₁).generator := by
  funext f x
  simp only [generator_superpose]
  ring

end JumpTerm

/-! ## Interleaving: independent components jump one at a time -/

namespace JumpTerm

variable {V₁ V₂ : Type u} [Fintype V₁] [Fintype V₂]

/-- Extend a term to a product state space, acting on the first
coordinate: jumps move the first coordinate and hold the second — the
other component *stays*, which is the interleaving reading of the stay
generator. -/
noncomputable def extendFst : JumpTerm V₁ → JumpTerm (V₁ × V₂)
  | jump K => jump fun x => ProbState.push (fun y₁ => (y₁, x.2)) (K x.1)
  | stay => stay
  | kill => kill
  | scale p b hp J => scale (fun x => p x.1) b (fun x => hp x.1) (extendFst J)
  | superpose J₁ J₂ => superpose (extendFst J₁) (extendFst J₂)
  | zero => zero

/-- Extend a term to a product state space, acting on the second
coordinate. -/
noncomputable def extendSnd : JumpTerm V₂ → JumpTerm (V₁ × V₂)
  | jump K => jump fun x => ProbState.push (fun y₂ => (x.1, y₂)) (K x.2)
  | stay => stay
  | kill => kill
  | scale p b hp J => scale (fun x => p x.2) b (fun x => hp x.2) (extendSnd J)
  | superpose J₁ J₂ => superpose (extendSnd J₁) (extendSnd J₂)
  | zero => zero

theorem intensity_extendFst (J : JumpTerm V₁) :
    (extendFst (V₂ := V₂) J).intensity = J.intensity := by
  induction J with
  | jump K => rfl
  | stay => rfl
  | kill => rfl
  | scale p b hp J ih =>
      show b * (extendFst J).intensity = b * J.intensity
      rw [ih]
  | superpose J₁ J₂ ih₁ ih₂ =>
      show (extendFst J₁).intensity + (extendFst J₂).intensity = _
      rw [ih₁, ih₂]
      rfl
  | zero => rfl

theorem intensity_extendSnd (J : JumpTerm V₂) :
    (extendSnd (V₁ := V₁) J).intensity = J.intensity := by
  induction J with
  | jump K => rfl
  | stay => rfl
  | kill => rfl
  | scale p b hp J ih =>
      show b * (extendSnd J).intensity = b * J.intensity
      rw [ih]
  | superpose J₁ J₂ ih₁ ih₂ =>
      show (extendSnd J₁).intensity + (extendSnd J₂).intensity = _
      rw [ih₁, ih₂]
      rfl
  | zero => rfl

private theorem sum_push_slice₁ (μ : ProbState V₁) (x₂ : V₂)
    (g : V₁ × V₂ → ℝ) :
    (∑ y : V₁ × V₂,
        (ProbState.push (fun y₁ => (y₁, x₂)) μ : V₁ × V₂ → ℝ) y * g y)
      = ∑ y₁, (μ : V₁ → ℝ) y₁ * g (y₁, x₂) := by
  classical
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y₁ _ => ?_
  have hstep : ∀ y₂ : V₂,
      (ProbState.push (fun z => (z, x₂)) μ : V₁ × V₂ → ℝ) (y₁, y₂)
          * g (y₁, y₂)
        = if y₂ = x₂ then (μ : V₁ → ℝ) y₁ * g (y₁, y₂) else 0 := by
    intro y₂
    by_cases hy : y₂ = x₂
    · subst hy
      rw [if_pos rfl, ProbState.push_coe,
        pushFun_apply_of_injective
          (fun a b h => congrArg Prod.fst h) _ y₁]
    · rw [if_neg hy, ProbState.push_coe,
        pushFun_apply_of_forall_ne
          (fun v h => hy ((congrArg Prod.snd h).symm)) _,
        zero_mul]
  rw [Finset.sum_congr rfl fun y₂ _ => hstep y₂,
    Finset.sum_ite_eq' Finset.univ x₂
      (fun y₂ => (μ : V₁ → ℝ) y₁ * g (y₁, y₂))]
  all_goals simp

private theorem sum_push_slice₂ (μ : ProbState V₂) (x₁ : V₁)
    (g : V₁ × V₂ → ℝ) :
    (∑ y : V₁ × V₂,
        (ProbState.push (fun y₂ => (x₁, y₂)) μ : V₁ × V₂ → ℝ) y * g y)
      = ∑ y₂, (μ : V₂ → ℝ) y₂ * g (x₁, y₂) := by
  classical
  rw [Fintype.sum_prod_type]
  have hrow : ∀ y₁ : V₁, (∑ y₂ : V₂,
      (ProbState.push (fun z => (x₁, z)) μ : V₁ × V₂ → ℝ) (y₁, y₂)
        * g (y₁, y₂))
      = if y₁ = x₁ then ∑ y₂, (μ : V₂ → ℝ) y₂ * g (y₁, y₂) else 0 := by
    intro y₁
    by_cases hy : y₁ = x₁
    · subst hy
      rw [if_pos rfl]
      refine Finset.sum_congr rfl fun y₂ _ => ?_
      rw [ProbState.push_coe,
        pushFun_apply_of_injective
          (fun a b h => congrArg Prod.snd h) _ y₂]
    · rw [if_neg hy]
      refine Finset.sum_eq_zero fun y₂ _ => ?_
      rw [ProbState.push_coe,
        pushFun_apply_of_forall_ne
          (fun v h => hy ((congrArg Prod.fst h).symm)) _,
        zero_mul]
  rw [Finset.sum_congr rfl fun y₁ _ => hrow y₁,
    Finset.sum_ite_eq' Finset.univ x₁
      (fun y₁ => ∑ y₂, (μ : V₂ → ℝ) y₂ * g (y₁, y₂))]
  all_goals simp

/-- The generator of a first-coordinate extension acts on the first
slot, the second held fixed. -/
theorem generator_extendFst (J : JumpTerm V₁) (f : V₁ × V₂ → ℝ)
    (x : V₁ × V₂) :
    (extendFst (V₂ := V₂) J).generator f x
      = J.generator (fun y₁ => f (y₁, x.2)) x.1 := by
  induction J with
  | jump K =>
      show (∑ y : V₁ × V₂,
          (ProbState.push (fun y₁ => (y₁, x.2)) (K x.1) : V₁ × V₂ → ℝ) y
            * (f y - f x))
        = ∑ y₁, (K x.1 : V₁ → ℝ) y₁ * (f (y₁, x.2) - f (x.1, x.2))
      rw [sum_push_slice₁ (K x.1) x.2 (fun y => f y - f x)]
  | stay => rfl
  | kill =>
      show -(f x) = -(f (x.1, x.2))
      simp
  | scale p b hp J ih =>
      show p x.1 * (extendFst J).generator f x = p x.1 * _
      rw [ih]
  | superpose J₁ J₂ ih₁ ih₂ =>
      show (extendFst J₁).generator f x + (extendFst J₂).generator f x = _
      rw [ih₁, ih₂]
      rfl
  | zero => rfl

/-- The generator of a second-coordinate extension acts on the second
slot, the first held fixed. -/
theorem generator_extendSnd (J : JumpTerm V₂) (f : V₁ × V₂ → ℝ)
    (x : V₁ × V₂) :
    (extendSnd (V₁ := V₁) J).generator f x
      = J.generator (fun y₂ => f (x.1, y₂)) x.2 := by
  induction J with
  | jump K =>
      show (∑ y : V₁ × V₂,
          (ProbState.push (fun y₂ => (x.1, y₂)) (K x.2) : V₁ × V₂ → ℝ) y
            * (f y - f x))
        = ∑ y₂, (K x.2 : V₂ → ℝ) y₂ * (f (x.1, y₂) - f (x.1, x.2))
      rw [sum_push_slice₂ (K x.2) x.1 (fun y => f y - f x)]
  | stay => rfl
  | kill =>
      show -(f x) = -(f (x.1, x.2))
      simp
  | scale p b hp J ih =>
      show p x.2 * (extendSnd J).generator f x = p x.2 * _
      rw [ih]
  | superpose J₁ J₂ ih₁ ih₂ =>
      show (extendSnd J₁).generator f x + (extendSnd J₂).generator f x = _
      rw [ih₁, ih₂]
      rfl
  | zero => rfl

/-- Interleaving of independent components: jump in one coordinate
while the other stays. -/
noncomputable def interleave (J₁ : JumpTerm V₁) (J₂ : JumpTerm V₂) :
    JumpTerm (V₁ × V₂) :=
  superpose (extendFst J₁) (extendSnd J₂)

/-- **The generator Leibniz rule**: the interleaved generator is the
sum of the componentwise generators, each acting on its own slot. -/
theorem generator_interleave (J₁ : JumpTerm V₁) (J₂ : JumpTerm V₂)
    (f : V₁ × V₂ → ℝ) (x : V₁ × V₂) :
    (interleave J₁ J₂).generator f x
      = J₁.generator (fun y₁ => f (y₁, x.2)) x.1
        + J₂.generator (fun y₂ => f (x.1, y₂)) x.2 := by
  show (extendFst J₁).generator f x + (extendSnd J₂).generator f x = _
  rw [generator_extendFst, generator_extendSnd]

/-- Interleaved intensity adds: the grading of the product is the sum
of the gradings. -/
theorem intensity_interleave (J₁ : JumpTerm V₁) (J₂ : JumpTerm V₂) :
    (interleave J₁ J₂).intensity = J₁.intensity + J₂.intensity := by
  show (extendFst J₁).intensity + (extendSnd J₂).intensity = _
  rw [intensity_extendFst, intensity_extendSnd]

end JumpTerm

end SuFunctor.Stochastic

#print axioms SuFunctor.Stochastic.JumpTerm.generator_elaborate
#print axioms SuFunctor.Stochastic.JumpTerm.elaborate_rate
#print axioms SuFunctor.Stochastic.JumpTerm.elaborate_mass_partition
#print axioms SuFunctor.Stochastic.JumpTerm.outflow_le_intensity
#print axioms SuFunctor.Stochastic.ThinningForm.generator_dilate
#print axioms SuFunctor.Stochastic.ThinningForm.generator_absorbDiagonal
#print axioms SuFunctor.Stochastic.JumpTerm.generator_scale_scale
#print axioms SuFunctor.Stochastic.JumpTerm.generator_scale_add
#print axioms SuFunctor.Stochastic.JumpTerm.generator_interleave
#print axioms SuFunctor.Stochastic.JumpTerm.intensity_interleave
