import SuFunctor.Site.TemporalTypeTheory
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-! # The wavy coverage of the interval base site, as a Grothendieck topology

Temporal type theory (Schultz–Spivak, *Temporal Type Theory: a
topos-theoretic approach to systems and behavior*, arXiv:1710.10258)
covers each duration `ℓ` of the interval base site by one family: the
*wavy* arrows `[r|s] : ℓ′ ⟶ ℓ` with `r, s > 0` — the strictly interior
placements (their `def:BaseSite`).  This module upgrades the landed
site-level leg (`SuFunctor.Site.TemporalTypeTheory`) to the coverage
stratum:

* `Shave.Wavy`, with the ideal lemmas `Wavy.comp_left`/`Wavy.comp_right`
  (composition only grows gaps) and the halving factorization
  `Wavy.factor` (gaps are divisible: every wavy arrow is a composite of
  two wavy arrows through the midpoint object);
* `wavyCoverage : Coverage IntervalBase` — Schultz–Spivak's coverage,
  verbatim: one covering family per object, automatically empty at
  duration zero;
* `wavyTopology : GrothendieckTopology IntervalBase` — the **closed
  form** of the generated topology: a sieve covers `ℓ` iff it contains
  every wavy arrow into `ℓ`.  `wavyCoverage_toGrothendieck` proves the
  closed form *is* the generated topology; the ideal lemmas discharge
  pullback-stability, the halving factorization discharges local
  character (transitivity);
* the zero-duration behavior, in two strengths.  `wavyTopology_zero`:
  every sieve covers `⟨0⟩`, the wavy condition being vacuous there
  (Schultz–Spivak's `rem:use_l>0`).  And the **forcing theorem**
  `bot_mem_of_le_wavy`: *any* Grothendieck topology in which the
  generated wavy sieves cover the positive durations already lets `⊥`
  cover `⟨0⟩` — pull the wavy sieve on `⟨1⟩` back along the flush
  placement `⟨0⟩ ⟶ ⟨1⟩` and nothing survives, because a flush placement
  never factors through a wavy arrow
  (`flush_not_mem_generate_wavyFam`).  Sheaf triviality at zero
  (`isSheaf_zero_unique`, their `X(0) ≅ {*}`) was therefore forced by
  the covers on the positive durations, not chosen at `0`;
* the window-side mirror: `Window.StrictlyInterior`, its absorption
  lemmas, its interpolation (midpoints), and `interiorTopology` — the
  same closed form on the window poset;
* **the morphism of sites**: the anchor quotient is cover-preserving
  (`coverPreserving_anchorQuot`, from the *existence* half of the
  downward lift), cocontinuous (`isCocontinuous_anchorQuot`), and
  compatible-preserving (`compatiblePreserving_anchorQuot`, from the
  *uniqueness* half — the discrete-fibration content), hence a
  continuous functor of sites (`isContinuous_anchorQuot`).  The landed
  cover correspondence `wavy_iff_strictlyInterior` thereby upgrades to
  the topology level: `mem_interiorTopology_iff` — a sieve covers `W`
  in the interior topology iff its pushforward along the anchor
  quotient covers `⟨W.len⟩` in the wavy topology.
-/

namespace SuFunctor

namespace Site

namespace TTT

noncomputable section

open CategoryTheory
open scoped NNReal

universe w

/-! ## Wavy arrows -/

/-- A shave-off is *wavy* when both gaps are strictly positive: the
strictly interior placements, Schultz–Spivak's covering arrows. -/
def Shave.Wavy {a b : IntervalBase} (e : Shave a b) : Prop :=
  0 < e.r ∧ 0 < e.s

/-- The bridge from the landed cover correspondence: the anchor image of
an inclusion is wavy iff both endpoint inequalities are strict. -/
theorem wavy_map_iff {W' W : Window} (h : W' ≤ W) :
    (anchorQuot.map (homOfLE h)).Wavy ↔ (W.d < W'.d ∧ W'.u < W.u) :=
  wavy_iff_strictlyInterior h

/-- Wavy arrows are a left ideal: post-composition preserves wavyness
(gaps only grow). -/
theorem Shave.Wavy.comp_left {a b c : IntervalBase} {e₁ : a ⟶ b}
    (h : Shave.Wavy e₁) (e₂ : b ⟶ c) : (e₁ ≫ e₂).Wavy :=
  ⟨h.1.trans_le le_add_self, h.2.trans_le le_self_add⟩

/-- Wavy arrows are a right ideal: pre-composition preserves wavyness. -/
theorem Shave.Wavy.comp_right {a b c : IntervalBase} (e₁ : a ⟶ b)
    {e₂ : b ⟶ c} (h : Shave.Wavy e₂) : (e₁ ≫ e₂).Wavy :=
  ⟨h.1.trans_le le_self_add, h.2.trans_le le_add_self⟩

/-- **The halving factorization**: every wavy arrow is a composite of two
wavy arrows through the midpoint object, with gaps `r/2`, `s/2` on each
leg.  This divisibility of the gap monoid is what drives the local
character of the wavy topology. -/
theorem Shave.Wavy.factor {a b : IntervalBase} {e : a ⟶ b}
    (he : Shave.Wavy e) :
    ∃ (c : IntervalBase) (f : c ⟶ b) (g : a ⟶ c),
      Shave.Wavy f ∧ Shave.Wavy g ∧ g ≫ f = e := by
  have heq : (e.r : ℝ) + a.len + e.s = b.len := by
    have h := congrArg NNReal.toReal e.eq
    push_cast at h
    simpa using h
  refine ⟨⟨e.r / 2 + a.len + e.s / 2⟩, ⟨e.r / 2, e.s / 2, ?_⟩,
    ⟨e.r / 2, e.s / 2, rfl⟩,
    ⟨half_pos he.1, half_pos he.2⟩, ⟨half_pos he.1, half_pos he.2⟩, ?_⟩
  · apply NNReal.coe_injective
    push_cast
    linarith
  · refine Shave.ext ?_ ?_
    · show e.r / 2 + e.r / 2 = e.r
      exact add_halves _
    · show e.s / 2 + e.s / 2 = e.s
      exact add_halves _

/-! ## Duration zero: placements into `⟨0⟩` -/

/-- A placement into the duration-zero interval has zero right gap. -/
theorem Shave.s_eq_zero {a : IntervalBase} (g : a ⟶ (⟨0⟩ : IntervalBase)) :
    g.s = 0 :=
  le_antisymm (le_add_self.trans_eq g.eq) zero_le

/-! ## The coverage and its generated topology -/

/-- The wavy covering family on `ℓ`: all wavy arrows into `ℓ`
(Schultz–Spivak `def:BaseSite`).  At `⟨0⟩` the family is automatically
empty: no wavy arrow can land in duration zero. -/
def wavyFam (ℓ : IntervalBase) : Presieve ℓ := fun _ e => Shave.Wavy e

@[simp]
theorem wavyFam_iff {ℓ ℓ' : IntervalBase} (e : ℓ' ⟶ ℓ) :
    wavyFam ℓ e ↔ Shave.Wavy e :=
  Iff.rfl

/-- **Schultz–Spivak `def:BaseSite`**: the coverage with exactly one
covering family per duration — its wavy family.  Pullback compatibility
is the left-ideal lemma. -/
def wavyCoverage : Coverage IntervalBase where
  coverings ℓ := {wavyFam ℓ}
  pullback := by
    rintro ℓ ℓ'' f S hS
    rw [Set.mem_singleton_iff] at hS
    subst hS
    refine ⟨wavyFam ℓ'', rfl, ?_⟩
    rintro w g hg
    exact ⟨w, 𝟙 w, g ≫ f, Shave.Wavy.comp_left hg f, Category.id_comp _⟩

/-- **The closed form of the generated topology**: a sieve covers `ℓ`
iff it contains every wavy arrow into `ℓ`.  At `⟨0⟩` the condition is
vacuous, so every sieve covers. -/
def wavyTopology : GrothendieckTopology IntervalBase where
  sieves ℓ := {S | ∀ ⦃ℓ' : IntervalBase⦄ (e : ℓ' ⟶ ℓ), Shave.Wavy e → S e}
  top_mem' _ := fun _ _ _ => trivial
  pullback_stable' := by
    intro ℓ ℓ'' S f hS w g hg
    exact hS (g ≫ f) (Shave.Wavy.comp_left hg f)
  transitive' := by
    intro ℓ S hS R hlocal ℓ' e he
    obtain ⟨c, f, g, hf, hg, rfl⟩ := he.factor
    exact hlocal (hS f hf) g hg

theorem mem_wavyTopology {ℓ : IntervalBase} {S : Sieve ℓ} :
    S ∈ wavyTopology ℓ ↔
      ∀ ⦃ℓ' : IntervalBase⦄ (e : ℓ' ⟶ ℓ), Shave.Wavy e → S e :=
  Iff.rfl

/-- **The closed form is the generated topology.** -/
theorem wavyCoverage_toGrothendieck :
    wavyCoverage.toGrothendieck = wavyTopology := by
  apply le_antisymm
  · refine ((Coverage.gi IntervalBase).gc wavyCoverage wavyTopology).mpr ?_
    intro ℓ S hS
    have hSeq : S = wavyFam ℓ := hS
    subst hSeq
    exact fun _ e he => ⟨_, 𝟙 _, e, he, Category.id_comp e⟩
  · intro ℓ S hS
    exact wavyCoverage.mem_toGrothendieck_sieves_of_superset
      (R := wavyFam ℓ) (fun _ e he => hS e he) rfl

/-- **Schultz–Spivak `rem:use_l>0`, mechanized**: every sieve covers the
zero duration — `⊥` included. -/
theorem wavyTopology_zero (S : Sieve (⟨0⟩ : IntervalBase)) :
    S ∈ wavyTopology ⟨0⟩ :=
  fun _ e he => absurd (Shave.s_eq_zero e) he.2.ne'

/-! ## The forcing theorem: triviality at zero was never a choice -/

/-- The flush placement `[ℓ.len|0] : ⟨0⟩ ⟶ ℓ` of the empty interval at
the right end of `ℓ`. -/
def flush (ℓ : IntervalBase) : (⟨0⟩ : IntervalBase) ⟶ ℓ :=
  ⟨ℓ.len, 0, by simp⟩

@[simp] theorem flush_r (ℓ : IntervalBase) : (flush ℓ).r = ℓ.len := rfl

@[simp] theorem flush_s (ℓ : IntervalBase) : (flush ℓ).s = 0 := rfl

/-- A flush placement never factors through a wavy arrow: any such
factorization would have strictly positive right gap. -/
theorem flush_not_mem_generate_wavyFam (ℓ : IntervalBase) :
    ¬ Sieve.generate (wavyFam ℓ) (flush ℓ) := by
  rintro ⟨c, h, w, hw, hcomp⟩
  have hcs := congrArg Shave.s hcomp
  rw [comp_s, flush_s] at hcs
  exact (hw.2.trans_le le_add_self).ne' hcs

/-- **The forcing theorem**: any Grothendieck topology in which the
generated wavy sieves cover every positive duration is forced to let
`⊥` cover `⟨0⟩` — pull the wavy sieve on `⟨1⟩` back along the flush
placement: nothing survives.  Schultz–Spivak's empty covering family at
`0` (and with it `X(0) ≅ {*}`) is a theorem of the positive-duration
covers, not a choice made at `0`. -/
theorem bot_mem_of_le_wavy (J' : GrothendieckTopology IntervalBase)
    (hJ' : ∀ ℓ : IntervalBase, 0 < ℓ.len →
      Sieve.generate (wavyFam ℓ) ∈ J' ℓ) :
    (⊥ : Sieve (⟨0⟩ : IntervalBase)) ∈ J' ⟨0⟩ := by
  have hbot :
      (Sieve.generate (wavyFam ⟨1⟩)).pullback (flush ⟨1⟩) = ⊥ := by
    ext c g
    simp only [Sieve.bot_apply, iff_false]
    rintro ⟨c', h, w, hw, hcomp⟩
    have hcs := congrArg Shave.s hcomp
    rw [comp_s, comp_s, flush_s, Shave.s_eq_zero g, add_zero] at hcs
    exact (hw.2.trans_le le_add_self).ne' hcs
  have hmem := J'.pullback_stable (flush ⟨1⟩) (hJ' ⟨1⟩ one_pos)
  rwa [hbot] at hmem

/-! ## The window-side mirror: strict interiority -/

namespace Window

/-- `W'` sits *strictly inside* `W`: both endpoint inequalities strict.
The window-side face of wavyness. -/
def StrictlyInterior (W' W : Window) : Prop :=
  W.d < W'.d ∧ W'.u < W.u

theorem StrictlyInterior.le {W' W : Window} (h : W'.StrictlyInterior W) :
    W' ≤ W :=
  ⟨h.1.le, h.2.le⟩

/-- Absorption: shrinking the inner window preserves strict interiority. -/
theorem StrictlyInterior.of_le {W₁ W₂ W₃ : Window}
    (h' : W₂.StrictlyInterior W₃) (h : W₁ ≤ W₂) :
    W₁.StrictlyInterior W₃ :=
  ⟨h'.1.trans_le h.1, h.2.trans_lt h'.2⟩

/-- Absorption: growing the outer window preserves strict interiority. -/
theorem StrictlyInterior.trans_le {W₁ W₂ W₃ : Window}
    (h : W₁.StrictlyInterior W₂) (h' : W₂ ≤ W₃) :
    W₁.StrictlyInterior W₃ :=
  ⟨h'.1.trans_lt h.1, h.2.trans_le h'.2⟩

/-- **Interpolation**: strict interiority is dense — the midpoint window
sits strictly between. -/
theorem StrictlyInterior.interpolate {W' W : Window}
    (h : W'.StrictlyInterior W) :
    ∃ W'' : Window, W'.StrictlyInterior W'' ∧ W''.StrictlyInterior W := by
  refine ⟨⟨(W.d + W'.d) / 2, (W'.u + W.u) / 2, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · have := W'.dle
    linarith [h.1, h.2]
  · show (W.d + W'.d) / 2 < W'.d
    linarith [h.1]
  · show W'.u < (W'.u + W.u) / 2
    linarith [h.2]
  · show W.d < (W.d + W'.d) / 2
    linarith [h.1]
  · show (W'.u + W.u) / 2 < W.u
    linarith [h.2]

end Window

/-- The landed cover correspondence, in `Wavy`/`StrictlyInterior` terms:
the anchor image of an inclusion is wavy iff the subwindow is strictly
interior. -/
theorem wavy_map_iff_strictlyInterior {W' W : Window} (h : W' ≤ W) :
    (anchorQuot.map (homOfLE h)).Wavy ↔ W'.StrictlyInterior W :=
  wavy_iff_strictlyInterior h

/-- **The interior topology on the window poset**: the same closed form —
a sieve covers `W` iff it contains every strictly interior inclusion. -/
def interiorTopology : GrothendieckTopology Window where
  sieves W := {S | ∀ ⦃W' : Window⦄ (h : W' ≤ W),
    W'.StrictlyInterior W → S (homOfLE h)}
  top_mem' _ := fun _ _ _ => trivial
  pullback_stable' := by
    intro W W₂ S f hS W' h hint
    show S (homOfLE h ≫ f)
    rw [Subsingleton.elim (homOfLE h ≫ f) (homOfLE (h.trans (leOfHom f)))]
    exact hS (h.trans (leOfHom f)) (hint.trans_le (leOfHom f))
  transitive' := by
    intro W S hS R hlocal W' hle hint
    obtain ⟨W'', h₁, h₂⟩ := hint.interpolate
    have hR : R (homOfLE h₁.le ≫ homOfLE h₂.le) :=
      hlocal (hS h₂.le h₂) h₁.le h₁
    rwa [Subsingleton.elim (homOfLE h₁.le ≫ homOfLE h₂.le : W' ⟶ W)
      (homOfLE hle)] at hR

theorem mem_interiorTopology {W : Window} {S : Sieve W} :
    S ∈ interiorTopology W ↔
      ∀ ⦃W' : Window⦄ (h : W' ≤ W),
        W'.StrictlyInterior W → S (homOfLE h) :=
  Iff.rfl

/-! ## The anchor quotient as a morphism of sites -/

/-- A shave's gap sum is bounded by its target duration. -/
theorem Shave.gaps_le {a b : IntervalBase} (e : a ⟶ b) :
    e.r + e.s ≤ b.len := by
  rw [← NNReal.coe_le_coe]
  push_cast
  have h := congrArg NNReal.toReal e.eq
  push_cast at h
  have := a.len.coe_nonneg
  linarith

/-- The gaps of an inclusion's anchor image always fit inside the outer
window. -/
theorem gaps_fit {W' W : Window} (h : W' ≤ W) :
    (anchorQuot.map (homOfLE h)).r + (anchorQuot.map (homOfLE h)).s
      ≤ W.len :=
  Shave.gaps_le _

/-- **The reshaped uniqueness corollary** — the consumer-facing form of
`existsUnique_lift_down`'s uniqueness clause: two subwindows of `W`
realizing the same gap pair coincide. -/
theorem eq_of_le_of_gaps_eq {W W₁ W₂ : Window} (h₁ : W₁ ≤ W) (h₂ : W₂ ≤ W)
    (hr : (anchorQuot.map (homOfLE h₁)).r = (anchorQuot.map (homOfLE h₂)).r)
    (hs : (anchorQuot.map (homOfLE h₁)).s = (anchorQuot.map (homOfLE h₂)).s) :
    W₁ = W₂ := by
  obtain ⟨W₀, -, huniq⟩ :=
    existsUnique_lift_down W (anchorQuot.map (homOfLE h₂)).r
      (anchorQuot.map (homOfLE h₂)).s (gaps_fit h₂)
  rw [huniq W₁ ⟨h₁, hr, hs⟩, huniq W₂ ⟨h₂, rfl, rfl⟩]

/-- **Cover preservation**: the anchor quotient sends interior covers to
wavy covers — the *existence* half of the downward lift, through the
bridge. -/
theorem coverPreserving_anchorQuot :
    CoverPreserving interiorTopology wavyTopology anchorQuot := by
  constructor
  intro W S hS ℓ' e he
  obtain ⟨W', ⟨hle, hr, hs⟩, -⟩ :=
    existsUnique_lift_down W e.r e.s (Shave.gaps_le e)
  have hrd : W'.d - W.d = (e.r : ℝ) := by
    have h := congrArg NNReal.toReal hr
    rwa [anchorQuot_map_r] at h
  have hsu : W.u - W'.u = (e.s : ℝ) := by
    have h := congrArg NNReal.toReal hs
    rwa [anchorQuot_map_s] at h
  have hlen : (e.r : ℝ) + ℓ'.len + e.s = W.u - W.d := by
    have h := congrArg NNReal.toReal e.eq
    push_cast at h
    simpa using h
  have hobj : anchorQuot.obj W' = ℓ' := by
    ext
    show W'.u - W'.d = (ℓ'.len : ℝ)
    linarith
  subst hobj
  have hmap : anchorQuot.map (homOfLE hle) = e := Shave.ext hr hs
  have hint : W'.StrictlyInterior W :=
    (wavy_map_iff_strictlyInterior hle).mp (by rw [hmap]; exact he)
  exact ⟨W', homOfLE hle, 𝟙 _, hS hle hint, by rw [Category.id_comp, hmap]⟩

/-- **Cover lifting (cocontinuity)**: wavy covers pull back to interior
covers along the anchor quotient — a one-liner from the bridge. -/
instance isCocontinuous_anchorQuot :
    anchorQuot.IsCocontinuous interiorTopology wavyTopology := by
  constructor
  intro W S hS W' hle hint
  exact hS (anchorQuot.map (homOfLE hle))
    ((wavy_map_iff_strictlyInterior hle).mpr hint)

/-- **Compatible preservation** — the discrete-fibration content of the
anchor quotient: two factorizations of one placement through two window
images down-lift, by the *uniqueness* half of the downward lift, to a
single subwindow, where the family's own compatibility applies (the
commuting square downstairs is free: window homs are subsingletons). -/
theorem compatiblePreserving_anchorQuot :
    CompatiblePreserving.{w} wavyTopology anchorQuot := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ heq
  obtain ⟨W₁, ⟨h₁, hr₁, hs₁⟩, -⟩ :=
    existsUnique_lift_down Y₁ f₁.r f₁.s (Shave.gaps_le f₁)
  obtain ⟨W₂, ⟨h₂, hr₂, hs₂⟩, -⟩ :=
    existsUnique_lift_down Y₂ f₂.r f₂.s (Shave.gaps_le f₂)
  -- endpoint forms of the four gap equations
  have hrd₁ : W₁.d - Y₁.d = (f₁.r : ℝ) := by
    have h := congrArg NNReal.toReal hr₁
    rwa [anchorQuot_map_r] at h
  have hsu₁ : Y₁.u - W₁.u = (f₁.s : ℝ) := by
    have h := congrArg NNReal.toReal hs₁
    rwa [anchorQuot_map_s] at h
  have hrd₂ : W₂.d - Y₂.d = (f₂.r : ℝ) := by
    have h := congrArg NNReal.toReal hr₂
    rwa [anchorQuot_map_r] at h
  have hsu₂ : Y₂.u - W₂.u = (f₂.s : ℝ) := by
    have h := congrArg NNReal.toReal hs₂
    rwa [anchorQuot_map_s] at h
  -- the commuting square upstairs, componentwise at ℝ
  have hcr₀ := congrArg Shave.r heq
  rw [comp_r, comp_r] at hcr₀
  have hcr := congrArg NNReal.toReal hcr₀
  push_cast at hcr
  rw [anchorQuot_map_r, anchorQuot_map_r] at hcr
  have hcs₀ := congrArg Shave.s heq
  rw [comp_s, comp_s] at hcs₀
  have hcs := congrArg NNReal.toReal hcs₀
  push_cast at hcs
  rw [anchorQuot_map_s, anchorQuot_map_s] at hcs
  -- the two down-lifts are one subwindow of Z
  have hW : W₁ = W₂ := by
    refine eq_of_le_of_gaps_eq (h₁.trans (leOfHom g₁))
      (h₂.trans (leOfHom g₂)) ?_ ?_
    · apply NNReal.coe_injective
      rw [anchorQuot_map_r, anchorQuot_map_r]
      linarith
    · apply NNReal.coe_injective
      rw [anchorQuot_map_s, anchorQuot_map_s]
      linarith
  -- identify the common source object
  have hlen₁ : (f₁.r : ℝ) + X.len + f₁.s = Y₁.u - Y₁.d := by
    have h := congrArg NNReal.toReal f₁.eq
    push_cast at h
    simpa using h
  have hobj₁ : anchorQuot.obj W₁ = X := by
    ext
    show W₁.u - W₁.d = (X.len : ℝ)
    linarith
  subst hW
  subst hobj₁
  have hmap₁ : anchorQuot.map (homOfLE h₁) = f₁ := Shave.ext hr₁ hs₁
  have hmap₂ : anchorQuot.map (homOfLE h₂) = f₂ := Shave.ext hr₂ hs₂
  rw [← hmap₁, ← hmap₂]
  exact hx (homOfLE h₁) (homOfLE h₂) hg₁ hg₂ (Subsingleton.elim _ _)

/-- **The anchor quotient is a morphism of sites** (interior → wavy):
continuous, by cover preservation and compatible preservation. -/
instance isContinuous_anchorQuot :
    anchorQuot.IsContinuous interiorTopology wavyTopology :=
  Functor.isContinuous_of_coverPreserving
    compatiblePreserving_anchorQuot coverPreserving_anchorQuot

/-- **The topology-level cover correspondence**: a sieve covers `W` in
the interior topology iff its pushforward along the anchor quotient
covers `⟨W.len⟩` in the wavy topology.  Forward is cover preservation;
backward is lift uniqueness plus downward closure. -/
theorem mem_interiorTopology_iff {W : Window} (S : Sieve W) :
    S ∈ interiorTopology W ↔
      S.functorPushforward anchorQuot ∈ wavyTopology ⟨W.len⟩ := by
  constructor
  · exact fun hS => coverPreserving_anchorQuot.cover_preserve hS
  · intro hS W'' hle hint
    obtain ⟨Y₁, g, h₁, hg, hfact⟩ :=
      hS (anchorQuot.map (homOfLE hle))
        ((wavy_map_iff_strictlyInterior hle).mpr hint)
    obtain ⟨W₃, ⟨h₃, hr₃, hs₃⟩, -⟩ :=
      existsUnique_lift_down Y₁ h₁.r h₁.s (Shave.gaps_le h₁)
    have hrd₃ : W₃.d - Y₁.d = (h₁.r : ℝ) := by
      have h := congrArg NNReal.toReal hr₃
      rwa [anchorQuot_map_r] at h
    have hsu₃ : Y₁.u - W₃.u = (h₁.s : ℝ) := by
      have h := congrArg NNReal.toReal hs₃
      rwa [anchorQuot_map_s] at h
    have hfr₀ := congrArg Shave.r hfact
    rw [comp_r] at hfr₀
    have hfr := congrArg NNReal.toReal hfr₀
    push_cast at hfr
    rw [anchorQuot_map_r, anchorQuot_map_r] at hfr
    have hfs₀ := congrArg Shave.s hfact
    rw [comp_s] at hfs₀
    have hfs := congrArg NNReal.toReal hfs₀
    push_cast at hfs
    rw [anchorQuot_map_s, anchorQuot_map_s] at hfs
    have hW : W'' = W₃ := by
      refine eq_of_le_of_gaps_eq hle (h₃.trans (leOfHom g)) ?_ ?_
      · apply NNReal.coe_injective
        rw [anchorQuot_map_r, anchorQuot_map_r]
        linarith
      · apply NNReal.coe_injective
        rw [anchorQuot_map_s, anchorQuot_map_s]
        linarith
    subst hW
    have hdc := S.downward_closed hg (homOfLE h₃)
    rwa [Subsingleton.elim (homOfLE h₃ ≫ g) (homOfLE hle)] at hdc

/-! ## Sheaf triviality at duration zero -/

/-- **Sections at zero are a point**: any type-valued sheaf for the wavy
topology has a unique section over `⟨0⟩` — the empty cover of `⟨0⟩`
(equivalently, `⊥` covering it) forces `X(0) ≅ {*}`. -/
theorem isSheaf_zero_unique {P : IntervalBaseᵒᵖ ⥤ Type w}
    (hP : Presieve.IsSheaf wavyTopology P) :
    Nonempty (Unique (P.obj (Opposite.op (⟨0⟩ : IntervalBase)))) := by
  obtain ⟨t, -, ht⟩ :=
    hP (⊥ : Sieve (⟨0⟩ : IntervalBase)) (wavyTopology_zero ⊥)
      (fun _ _ hf => False.elim hf)
      (fun _ _ _ _ _ _ _ h₁ _ _ => False.elim h₁)
  exact ⟨⟨⟨t⟩, fun y => ht y (fun _ _ hf => False.elim hf)⟩⟩

end

end TTT

end Site

end SuFunctor
