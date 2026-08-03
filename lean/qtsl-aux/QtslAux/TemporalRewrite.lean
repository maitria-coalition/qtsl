import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Tauto

/-! # Sound rewriting for a deep-embedded linear temporal logic

This module defines a deep embedding of a discrete-time linear temporal logic
and proves that a small catalogue of rewrite rules preserves satisfaction, so
that formula normalization performed by an external tool can be replayed and
checked step by step.

Principal declarations:

* `Form A`: formulas over atoms `A` with Boolean connectives and the temporal
  operators next (`X`), eventually (`F`), always (`G`), until (`U`;
  non-strict: the target may hold immediately, the safety argument is
  required strictly before the hit), and their bounded-horizon forms
  (`F_le`/`G_le`/`U_le`, relative window `j ≤ i + T`).
* `sat V i φ`: satisfaction of `φ` at time `i` under the valuation
  `V : Nat → A → Prop`, defined by structural recursion.
* `Rewrites`: the root-rewrite catalogue — implication elimination,
  distribution of disjunction over conjunction, double-negation elimination,
  De Morgan laws, pushing negation through `X`/`F`/`G` (duality), and the
  polarity-absorption fusion family: over ω-words the ∃-over-time operators
  absorb `∨` and the ∀-over-time operators absorb `∧`, as denotation
  equalities — `GF φ ∨ GF ψ ↔ GF (φ ∨ ψ)`, `F φ ∨ F ψ ↔ F (φ ∨ ψ)`,
  `G φ ∧ G ψ ↔ G (φ ∧ ψ)`, `FG φ ∧ FG ψ ↔ FG (φ ∧ ψ)`,
  `(σ U τ₁) ∨ (σ U τ₂) ↔ σ U (τ₁ ∨ τ₂)` (target position is ∃),
  `(σ₁ U τ) ∧ (σ₂ U τ) ↔ (σ₁ ∧ σ₂) U τ` (safety position is ∀) — plus the
  bounded-horizon siblings of the four with a horizon (the `≤ T`
  decorations carry verbatim; `FG`'s settling time is unbounded by
  construction, so it has no bounded row) — each validated pointwise by
  `Rewrites.sound`.
* the residue fence: the four tempting fusions *outside* the absorption
  polarity are refuted by explicit ω-word counterexamples
  (`no_f_and_fusion`, `no_g_or_fusion`, `no_gf_and_fusion`,
  `no_fg_or_fusion`) — the boundary of the absorption law is exact.
* `RewritesAt`: closure of the root rules under all formula contexts
  (congruence), sound by `RewritesAt.sound`.
* `Chain`: finite sequences of context rewrites, sound by transitivity
  (`Chain.sound`), giving semantic equality between a formula and its normal
  form.
* `sat_GF_of_frequently`: a run satisfying a predicate at unboundedly many
  times satisfies `G (F γ)` for any formula `γ` implied by that predicate.
-/

namespace Qtsl.TemporalRewrite

inductive Form (A : Type*) where
  | atom : A → Form A
  | not : Form A → Form A
  | and : Form A → Form A → Form A
  | or : Form A → Form A → Form A
  | imp : Form A → Form A → Form A
  | X : Form A → Form A
  | F : Form A → Form A
  | G : Form A → Form A
  | U : Form A → Form A → Form A
  | F_le : Nat → Form A → Form A
  | G_le : Nat → Form A → Form A
  | U_le : Nat → Form A → Form A → Form A

variable {A : Type*}

def sat (V : Nat → A → Prop) : Nat → Form A → Prop
  | i, .atom a => V i a
  | i, .not φ => ¬ sat V i φ
  | i, .and φ ψ => sat V i φ ∧ sat V i ψ
  | i, .or φ ψ => sat V i φ ∨ sat V i ψ
  | i, .imp φ ψ => sat V i φ → sat V i ψ
  | i, .X φ => sat V (i + 1) φ
  | i, .F φ => ∃ j, i ≤ j ∧ sat V j φ
  | i, .G φ => ∀ j, i ≤ j → sat V j φ
  | i, .U σ τ => ∃ j, i ≤ j ∧ sat V j τ ∧ ∀ k, i ≤ k → k < j → sat V k σ
  | i, .F_le T φ => ∃ j, i ≤ j ∧ j ≤ i + T ∧ sat V j φ
  | i, .G_le T φ => ∀ j, i ≤ j → j ≤ i + T → sat V j φ
  | i, .U_le T σ τ =>
      ∃ j, i ≤ j ∧ j ≤ i + T ∧ sat V j τ ∧ ∀ k, i ≤ k → k < j → sat V k σ

theorem sat_imp_elim (V : Nat → A → Prop) (i : Nat) (φ ψ : Form A) :
    sat V i (.imp φ ψ) ↔ sat V i (.or (.not φ) ψ) := by
  simp only [sat]; tauto

theorem sat_or_and_r (V : Nat → A → Prop) (i : Nat) (φ ψ χ : Form A) :
    sat V i (.or φ (.and ψ χ)) ↔ sat V i (.and (.or φ ψ) (.or φ χ)) := by
  simp only [sat]; tauto

theorem sat_neg_neg (V : Nat → A → Prop) (i : Nat) (φ : Form A) :
    sat V i (.not (.not φ)) ↔ sat V i φ := by
  simp only [sat]; tauto

theorem sat_neg_and (V : Nat → A → Prop) (i : Nat) (φ ψ : Form A) :
    sat V i (.not (.and φ ψ)) ↔ sat V i (.or (.not φ) (.not ψ)) := by
  simp only [sat]; tauto

theorem sat_neg_or (V : Nat → A → Prop) (i : Nat) (φ ψ : Form A) :
    sat V i (.not (.or φ ψ)) ↔ sat V i (.and (.not φ) (.not ψ)) := by
  simp only [sat]; tauto

theorem sat_neg_F (V : Nat → A → Prop) (i : Nat) (φ : Form A) :
    sat V i (.not (.F φ)) ↔ sat V i (.G (.not φ)) := by
  simp only [sat]
  constructor
  · intro h j hj hs
    exact h ⟨j, hj, hs⟩
  · rintro h ⟨j, hj, hs⟩
    exact h j hj hs

theorem sat_neg_G (V : Nat → A → Prop) (i : Nat) (φ : Form A) :
    sat V i (.not (.G φ)) ↔ sat V i (.F (.not φ)) := by
  simp only [sat]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact h hc
  · rintro ⟨j, hj, hn⟩ hall
    exact hn (hall j hj)

theorem sat_neg_X (V : Nat → A → Prop) (i : Nat) (φ : Form A) :
    sat V i (.not (.X φ)) ↔ sat V i (.X (.not φ)) := by
  simp only [sat]

theorem sat_gf_or_fusion (V : Nat → A → Prop) (i : Nat) (φ ψ : Form A) :
    sat V i (.or (.G (.F φ)) (.G (.F ψ))) ↔
      sat V i (.G (.F (.or φ ψ))) := by
  simp only [sat]
  constructor
  · rintro (h | h) j hj
    · obtain ⟨k, hk, hs⟩ := h j hj
      exact ⟨k, hk, Or.inl hs⟩
    · obtain ⟨k, hk, hs⟩ := h j hj
      exact ⟨k, hk, Or.inr hs⟩
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨⟨a, ha, hna⟩, ⟨b, hb, hnb⟩⟩ := hc
    obtain ⟨k, hk, hs⟩ := h (max a b) (by omega)
    rcases hs with hs | hs
    · exact hna k (by omega) hs
    · exact hnb k (by omega) hs

/-! ### The fusion family (polarity absorption)

Over ω-words, the ∃-over-time positions (`F`, the target of `U`, the inner
`F` of `GF`) absorb `∨`, and the ∀-over-time positions (`G`, the safety of
`U`, the inner `G` of `FG`) absorb `∧` — each as a denotation *equality*,
so a satisfaction judgment transports verbatim in both directions.
`sat_gf_or_fusion` above is the ninth landed rule; these are its five
family members. -/

theorem sat_f_or_fusion (V : Nat → A → Prop) (i : Nat) (φ ψ : Form A) :
    sat V i (.or (.F φ) (.F ψ)) ↔ sat V i (.F (.or φ ψ)) := by
  simp only [sat]
  constructor
  · rintro (⟨j, hj, hs⟩ | ⟨j, hj, hs⟩)
    · exact ⟨j, hj, Or.inl hs⟩
    · exact ⟨j, hj, Or.inr hs⟩
  · rintro ⟨j, hj, hs | hs⟩
    · exact Or.inl ⟨j, hj, hs⟩
    · exact Or.inr ⟨j, hj, hs⟩

theorem sat_g_and_fusion (V : Nat → A → Prop) (i : Nat) (φ ψ : Form A) :
    sat V i (.and (.G φ) (.G ψ)) ↔ sat V i (.G (.and φ ψ)) := by
  simp only [sat]
  constructor
  · rintro ⟨h₁, h₂⟩ j hj
    exact ⟨h₁ j hj, h₂ j hj⟩
  · intro h
    exact ⟨fun j hj => (h j hj).1, fun j hj => (h j hj).2⟩

theorem sat_fg_and_fusion (V : Nat → A → Prop) (i : Nat) (φ ψ : Form A) :
    sat V i (.and (.F (.G φ)) (.F (.G ψ))) ↔ sat V i (.F (.G (.and φ ψ))) := by
  simp only [sat]
  constructor
  · rintro ⟨⟨a, ha, hga⟩, ⟨b, hb, hgb⟩⟩
    exact ⟨max a b, by omega,
      fun j hj => ⟨hga j (by omega), hgb j (by omega)⟩⟩
  · rintro ⟨a, ha, hg⟩
    exact ⟨⟨a, ha, fun j hj => (hg j hj).1⟩, ⟨a, ha, fun j hj => (hg j hj).2⟩⟩

theorem sat_until_target_or_fusion (V : Nat → A → Prop) (i : Nat)
    (σ τ₁ τ₂ : Form A) :
    sat V i (.or (.U σ τ₁) (.U σ τ₂)) ↔ sat V i (.U σ (.or τ₁ τ₂)) := by
  simp only [sat]
  constructor
  · rintro (⟨j, hj, ht, hs⟩ | ⟨j, hj, ht, hs⟩)
    · exact ⟨j, hj, Or.inl ht, hs⟩
    · exact ⟨j, hj, Or.inr ht, hs⟩
  · rintro ⟨j, hj, ht | ht, hs⟩
    · exact Or.inl ⟨j, hj, ht, hs⟩
    · exact Or.inr ⟨j, hj, ht, hs⟩

theorem sat_until_safe_and_fusion (V : Nat → A → Prop) (i : Nat)
    (σ₁ σ₂ τ : Form A) :
    sat V i (.and (.U σ₁ τ) (.U σ₂ τ)) ↔ sat V i (.U (.and σ₁ σ₂) τ) := by
  simp only [sat]
  constructor
  · rintro ⟨⟨a, ha, hta, hsa⟩, ⟨b, hb, htb, hsb⟩⟩
    rcases Nat.le_total a b with hab | hab
    · exact ⟨a, ha, hta,
        fun k hk hka => ⟨hsa k hk hka, hsb k hk (by omega)⟩⟩
    · exact ⟨b, hb, htb,
        fun k hk hkb => ⟨hsa k hk (by omega), hsb k hk hkb⟩⟩
  · rintro ⟨j, hj, ht, hs⟩
    exact ⟨⟨j, hj, ht, fun k hk hkj => (hs k hk hkj).1⟩,
           ⟨j, hj, ht, fun k hk hkj => (hs k hk hkj).2⟩⟩

/-! ### The bounded-horizon siblings

The fusion rows carry `≤ T` decorations verbatim: the same absorption
equalities hold for the bounded operators (relative window `j ≤ i + T`),
with the horizon riding the witness arithmetic unchanged (`FG` has no
bounded row: its settling time is unbounded by construction). -/

theorem sat_f_le_or_fusion (V : Nat → A → Prop) (i T : Nat) (φ ψ : Form A) :
    sat V i (.or (.F_le T φ) (.F_le T ψ)) ↔ sat V i (.F_le T (.or φ ψ)) := by
  simp only [sat]
  constructor
  · rintro (⟨j, hj, hT, hs⟩ | ⟨j, hj, hT, hs⟩)
    · exact ⟨j, hj, hT, Or.inl hs⟩
    · exact ⟨j, hj, hT, Or.inr hs⟩
  · rintro ⟨j, hj, hT, hs | hs⟩
    · exact Or.inl ⟨j, hj, hT, hs⟩
    · exact Or.inr ⟨j, hj, hT, hs⟩

theorem sat_g_le_and_fusion (V : Nat → A → Prop) (i T : Nat) (φ ψ : Form A) :
    sat V i (.and (.G_le T φ) (.G_le T ψ)) ↔ sat V i (.G_le T (.and φ ψ)) := by
  simp only [sat]
  constructor
  · rintro ⟨h₁, h₂⟩ j hj hT
    exact ⟨h₁ j hj hT, h₂ j hj hT⟩
  · intro h
    exact ⟨fun j hj hT => (h j hj hT).1, fun j hj hT => (h j hj hT).2⟩

theorem sat_until_le_target_or_fusion (V : Nat → A → Prop) (i T : Nat)
    (σ τ₁ τ₂ : Form A) :
    sat V i (.or (.U_le T σ τ₁) (.U_le T σ τ₂)) ↔
      sat V i (.U_le T σ (.or τ₁ τ₂)) := by
  simp only [sat]
  constructor
  · rintro (⟨j, hj, hT, ht, hs⟩ | ⟨j, hj, hT, ht, hs⟩)
    · exact ⟨j, hj, hT, Or.inl ht, hs⟩
    · exact ⟨j, hj, hT, Or.inr ht, hs⟩
  · rintro ⟨j, hj, hT, ht | ht, hs⟩
    · exact Or.inl ⟨j, hj, hT, ht, hs⟩
    · exact Or.inr ⟨j, hj, hT, ht, hs⟩

theorem sat_until_le_safe_and_fusion (V : Nat → A → Prop) (i T : Nat)
    (σ₁ σ₂ τ : Form A) :
    sat V i (.and (.U_le T σ₁ τ) (.U_le T σ₂ τ)) ↔
      sat V i (.U_le T (.and σ₁ σ₂) τ) := by
  simp only [sat]
  constructor
  · rintro ⟨⟨a, ha, haT, hta, hsa⟩, ⟨b, hb, hbT, htb, hsb⟩⟩
    rcases Nat.le_total a b with hab | hab
    · exact ⟨a, ha, haT, hta,
        fun k hk hka => ⟨hsa k hk hka, hsb k hk (by omega)⟩⟩
    · exact ⟨b, hb, hbT, htb,
        fun k hk hkb => ⟨hsa k hk (by omega), hsb k hk hkb⟩⟩
  · rintro ⟨j, hj, hT, ht, hs⟩
    exact ⟨⟨j, hj, hT, ht, fun k hk hkj => (hs k hk hkj).1⟩,
           ⟨j, hj, hT, ht, fun k hk hkj => (hs k hk hkj).2⟩⟩

/-! ### The residue fence (the four non-fusions)

The four positive Boolean/temporal combinations *outside* the absorption
polarity do not fuse: each has an explicit ω-word counterexample. Together
with the six fusion equalities these pin the absorption law's boundary
exactly: `∨` fuses at ∃-positions and only there; `∧` fuses at ∀-positions
and only there. (The counterexamples are also the mutant battery for the
fusion family: each refutes the tempting wrong-polarity rewrite.) -/

theorem no_f_and_fusion :
    ∃ V : Nat → Nat → Prop,
      sat V 0 (.and (.F (.atom 0)) (.F (.atom 1))) ∧
      ¬ sat V 0 (.F (.and (.atom 0) (.atom 1))) := by
  refine ⟨fun j n => j = n, ?_, ?_⟩
  · simp only [sat]
    exact ⟨⟨0, by omega, rfl⟩, ⟨1, by omega, rfl⟩⟩
  · simp only [sat]
    rintro ⟨j, -, h₀, h₁⟩
    omega

theorem no_g_or_fusion :
    ∃ V : Nat → Nat → Prop,
      sat V 0 (.G (.or (.atom 0) (.atom 1))) ∧
      ¬ sat V 0 (.or (.G (.atom 0)) (.G (.atom 1))) := by
  refine ⟨fun j n => j % 2 = n, ?_, ?_⟩
  · simp only [sat]
    intro j _
    omega
  · simp only [sat]
    rintro (h | h)
    · have := h 1 (by omega); omega
    · have := h 0 (by omega); omega

theorem no_gf_and_fusion :
    ∃ V : Nat → Nat → Prop,
      sat V 0 (.and (.G (.F (.atom 0))) (.G (.F (.atom 1)))) ∧
      ¬ sat V 0 (.G (.F (.and (.atom 0) (.atom 1)))) := by
  refine ⟨fun j n => j % 2 = n, ?_, ?_⟩
  · simp only [sat]
    exact ⟨fun j _ => ⟨2 * j, by omega, by omega⟩,
           fun j _ => ⟨2 * j + 1, by omega, by omega⟩⟩
  · simp only [sat]
    intro h
    obtain ⟨k, -, hk₀, hk₁⟩ := h 0 (by omega)
    omega

theorem no_fg_or_fusion :
    ∃ V : Nat → Nat → Prop,
      sat V 0 (.F (.G (.or (.atom 0) (.atom 1)))) ∧
      ¬ sat V 0 (.or (.F (.G (.atom 0))) (.F (.G (.atom 1)))) := by
  refine ⟨fun j n => j % 2 = n, ?_, ?_⟩
  · simp only [sat]
    exact ⟨0, by omega, fun j _ => by omega⟩
  · simp only [sat]
    rintro (⟨a, -, h⟩ | ⟨a, -, h⟩)
    · have := h (2 * a + 1) (by omega); omega
    · have := h (2 * a) (by omega); omega

inductive Rewrites : Form A → Form A → Prop where
  | imp_elim (φ ψ) : Rewrites (.imp φ ψ) (.or (.not φ) ψ)
  | or_and_r (φ ψ χ) :
      Rewrites (.or φ (.and ψ χ)) (.and (.or φ ψ) (.or φ χ))
  | neg_neg (φ) : Rewrites (.not (.not φ)) φ
  | neg_and (φ ψ) :
      Rewrites (.not (.and φ ψ)) (.or (.not φ) (.not ψ))
  | neg_or (φ ψ) :
      Rewrites (.not (.or φ ψ)) (.and (.not φ) (.not ψ))
  | neg_F (φ) : Rewrites (.not (.F φ)) (.G (.not φ))
  | neg_G (φ) : Rewrites (.not (.G φ)) (.F (.not φ))
  | neg_X (φ) : Rewrites (.not (.X φ)) (.X (.not φ))
  | gf_or_fusion (φ ψ) :
      Rewrites (.or (.G (.F φ)) (.G (.F ψ))) (.G (.F (.or φ ψ)))
  | f_or_fusion (φ ψ) :
      Rewrites (.or (.F φ) (.F ψ)) (.F (.or φ ψ))
  | g_and_fusion (φ ψ) :
      Rewrites (.and (.G φ) (.G ψ)) (.G (.and φ ψ))
  | fg_and_fusion (φ ψ) :
      Rewrites (.and (.F (.G φ)) (.F (.G ψ))) (.F (.G (.and φ ψ)))
  | until_target_or_fusion (σ τ₁ τ₂) :
      Rewrites (.or (.U σ τ₁) (.U σ τ₂)) (.U σ (.or τ₁ τ₂))
  | until_safe_and_fusion (σ₁ σ₂ τ) :
      Rewrites (.and (.U σ₁ τ) (.U σ₂ τ)) (.U (.and σ₁ σ₂) τ)
  | f_le_or_fusion (T φ ψ) :
      Rewrites (.or (.F_le T φ) (.F_le T ψ)) (.F_le T (.or φ ψ))
  | g_le_and_fusion (T φ ψ) :
      Rewrites (.and (.G_le T φ) (.G_le T ψ)) (.G_le T (.and φ ψ))
  | until_le_target_or_fusion (T σ τ₁ τ₂) :
      Rewrites (.or (.U_le T σ τ₁) (.U_le T σ τ₂)) (.U_le T σ (.or τ₁ τ₂))
  | until_le_safe_and_fusion (T σ₁ σ₂ τ) :
      Rewrites (.and (.U_le T σ₁ τ) (.U_le T σ₂ τ)) (.U_le T (.and σ₁ σ₂) τ)

theorem Rewrites.sound {φ ψ : Form A} (h : Rewrites φ ψ)
    (V : Nat → A → Prop) (i : Nat) : sat V i φ ↔ sat V i ψ := by
  cases h <;>
    first
      | exact sat_imp_elim ..
      | exact sat_or_and_r ..
      | exact sat_neg_neg ..
      | exact sat_neg_and ..
      | exact sat_neg_or ..
      | exact sat_neg_F ..
      | exact sat_neg_G ..
      | exact sat_neg_X ..
      | exact sat_gf_or_fusion ..
      | exact sat_f_or_fusion ..
      | exact sat_g_and_fusion ..
      | exact sat_fg_and_fusion ..
      | exact sat_until_target_or_fusion ..
      | exact sat_until_safe_and_fusion ..
      | exact sat_f_le_or_fusion ..
      | exact sat_g_le_and_fusion ..
      | exact sat_until_le_target_or_fusion ..
      | exact sat_until_le_safe_and_fusion ..

inductive RewritesAt : Form A → Form A → Prop where
  | root {φ ψ} : Rewrites φ ψ → RewritesAt φ ψ
  | not {φ ψ} : RewritesAt φ ψ → RewritesAt (.not φ) (.not ψ)
  | and_l {φ ψ χ} : RewritesAt φ ψ → RewritesAt (.and φ χ) (.and ψ χ)
  | and_r {φ ψ χ} : RewritesAt φ ψ → RewritesAt (.and χ φ) (.and χ ψ)
  | or_l {φ ψ χ} : RewritesAt φ ψ → RewritesAt (.or φ χ) (.or ψ χ)
  | or_r {φ ψ χ} : RewritesAt φ ψ → RewritesAt (.or χ φ) (.or χ ψ)
  | imp_l {φ ψ χ} : RewritesAt φ ψ → RewritesAt (.imp φ χ) (.imp ψ χ)
  | imp_r {φ ψ χ} : RewritesAt φ ψ → RewritesAt (.imp χ φ) (.imp χ ψ)
  | X {φ ψ} : RewritesAt φ ψ → RewritesAt (.X φ) (.X ψ)
  | F {φ ψ} : RewritesAt φ ψ → RewritesAt (.F φ) (.F ψ)
  | G {φ ψ} : RewritesAt φ ψ → RewritesAt (.G φ) (.G ψ)
  | U_l {φ ψ χ} : RewritesAt φ ψ → RewritesAt (.U φ χ) (.U ψ χ)
  | U_r {φ ψ χ} : RewritesAt φ ψ → RewritesAt (.U χ φ) (.U χ ψ)
  | F_le {T : Nat} {φ ψ} : RewritesAt φ ψ → RewritesAt (.F_le T φ) (.F_le T ψ)
  | G_le {T : Nat} {φ ψ} : RewritesAt φ ψ → RewritesAt (.G_le T φ) (.G_le T ψ)
  | U_le_l {T : Nat} {φ ψ χ} :
      RewritesAt φ ψ → RewritesAt (.U_le T φ χ) (.U_le T ψ χ)
  | U_le_r {T : Nat} {φ ψ χ} :
      RewritesAt φ ψ → RewritesAt (.U_le T χ φ) (.U_le T χ ψ)

theorem RewritesAt.sound {φ ψ : Form A} (h : RewritesAt φ ψ) :
    ∀ (V : Nat → A → Prop) (i : Nat), sat V i φ ↔ sat V i ψ := by
  induction h with
  | root h => exact h.sound
  | not _ ih => intro V i; simp only [sat]; exact not_congr (ih V i)
  | and_l _ ih => intro V i; simp only [sat]; exact and_congr_left' (ih V i)
  | and_r _ ih => intro V i; simp only [sat]; exact and_congr_right' (ih V i)
  | or_l _ ih => intro V i; simp only [sat]; exact or_congr_left (ih V i)
  | or_r _ ih => intro V i; simp only [sat]; exact or_congr_right (ih V i)
  | imp_l _ ih => intro V i; simp only [sat]; exact imp_congr (ih V i) Iff.rfl
  | imp_r _ ih => intro V i; simp only [sat]; exact imp_congr Iff.rfl (ih V i)
  | X _ ih => intro V i; simp only [sat]; exact ih V (i + 1)
  | F _ ih =>
      intro V i
      simp only [sat]
      exact exists_congr fun j => and_congr_right fun _ => ih V j
  | G _ ih =>
      intro V i
      simp only [sat]
      exact forall_congr' fun j => imp_congr Iff.rfl (ih V j)
  | U_l _ ih =>
      intro V i
      simp only [sat]
      exact exists_congr fun j => and_congr_right fun _ =>
        and_congr_right fun _ => forall_congr' fun k =>
          imp_congr Iff.rfl (imp_congr Iff.rfl (ih V k))
  | U_r _ ih =>
      intro V i
      simp only [sat]
      exact exists_congr fun j => and_congr_right fun _ =>
        and_congr_left' (ih V j)
  | F_le _ ih =>
      intro V i
      simp only [sat]
      exact exists_congr fun j => and_congr_right fun _ =>
        and_congr_right fun _ => ih V j
  | G_le _ ih =>
      intro V i
      simp only [sat]
      exact forall_congr' fun j =>
        imp_congr Iff.rfl (imp_congr Iff.rfl (ih V j))
  | U_le_l _ ih =>
      intro V i
      simp only [sat]
      exact exists_congr fun j => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ =>
          forall_congr' fun k =>
            imp_congr Iff.rfl (imp_congr Iff.rfl (ih V k))
  | U_le_r _ ih =>
      intro V i
      simp only [sat]
      exact exists_congr fun j => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_left' (ih V j)

inductive Chain : Form A → Form A → Prop where
  | refl (φ) : Chain φ φ
  | step {φ ψ χ} : RewritesAt φ ψ → Chain ψ χ → Chain φ χ

theorem Chain.sound {φ ψ : Form A} (h : Chain φ ψ)
    (V : Nat → A → Prop) (i : Nat) : sat V i φ ↔ sat V i ψ := by
  induction h with
  | refl φ => exact Iff.rfl
  | step hstep _ ih => exact (hstep.sound V i).trans ih

theorem sat_GF_of_frequently {V : Nat → A → Prop} {γ : Form A}
    {P : Nat → Prop}
    (himp : ∀ n, P n → sat V n γ)
    (hfreq : ∀ N, ∃ n, N ≤ n ∧ P n) :
    sat V 0 (.G (.F γ)) := by
  intro j _
  obtain ⟨n, hn, hP⟩ := hfreq j
  exact ⟨n, hn, himp n hP⟩

theorem sat_and_pairs (V : Nat → A → Prop) (i : Nat) (φ ψ : Form A) :
    sat V i (.and φ ψ) ↔ sat V i φ ∧ sat V i ψ := by
  simp only [sat]

end Qtsl.TemporalRewrite
