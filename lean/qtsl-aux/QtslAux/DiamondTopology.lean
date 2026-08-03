import QtslAux.DiamondSite
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Analysis.Normed.Module.Basic

/-! # The derived diamond topology, and the Minkowski chronology kit

The spacetime site, extracted from the causal order.  `QtslAux.DiamondSite`
packages the order-theoretic fragment of Martin–Panangaden bicontinuity
(`ChronologyKit`: a chronology `≪` beneath the causal order `≤`, absorbing
`≤` on both sides, interpolative) and proves the interior coverage
well-behaved — nonempty iff thick, pair-filtered.  This module takes the
remaining step to the site itself:

* `Diamond X` becomes a preorder (containment) and hence a category;
* `diamondTopology K : GrothendieckTopology (Diamond X)` — the **derived
  topology of the causal order**, in closed form: a sieve covers `D` iff
  it contains every chronologically interior subdiamond arrow.  Pullback
  stability is the two mixing laws; local character (transitivity) is
  interpolation, applied at both endpoints.  The construction consumes
  exactly four of `ChronologyKit`'s seven fields — `le_of_chron`, the two
  mixing laws, `interpolate` — and **not** `up_filtered`/`down_directed`:
  filteredness is the sheaf-descent stratum's consumption (the carrier's
  directed-limit arguments), never the topology's.  The site dimension's
  order-theoretic demands factor: *interpolative mixing buys the
  coverage-as-topology; bicontinuity's filtered/directed halves buy
  descent.*
* `mem_of_not_thick`: on the boundary family (degenerate and null-related
  diamonds) every sieve covers — the topology-grade form of the
  empty-cover decision, generalizing the classical duration-zero
  behaviour (`wavyTopology_zero` in the su-functor package is its
  (0+1)-dimensional shadow).
* `Mink E` / `minkowskiKit` — **the special-relativity witness**: the
  cone order on time × space for any real normed space `E`, with
  strict-cone chronology, is a `ChronologyKit`; hence `diamondTopology`
  instantiates at Minkowski space of any dimension.  The derived-site
  recipe is uniform in the causal order — the classical interval site is
  the value at `(ℝ, ≤, <)` (`linearOrderKit`), Minkowski is this kit,
  and a globally hyperbolic curved spacetime is Martin–Panangaden's
  theorem (chronology and causality of a GH spacetime satisfy exactly
  these axioms; arXiv:gr-qc/0407094).  Spacelike incomparability
  (`minkowski_spacelike_incomparable`) witnesses that the order is
  genuinely partial: this instance leaves the (0+1) column.
* `int_lt_no_chronologyKit` — the tick discriminator: no `ChronologyKit`
  on `ℤ` has the *strict* chronology `chron = (· < ·)` — interpolation
  fails between consecutive ticks — so the genuinely interior covers of
  the dense columns have no strict-setting tick counterpart.  That
  refusal is the whole kernel fact; it is **not** a uniqueness claim:
  nondegenerate kits on `ℤ` exist (e.g. `a ≪ b ↔ a ≤ 0 ∧ 0 ≤ b`
  satisfies every field, with `0` witnessing interpolation and both
  filtration laws), each with its own derived topology.

The kit deliberately does **not** exclude degenerate chronologies (e.g.
`chron := ≤` satisfies every field, and its derived topology is the
trivial one, every closed-form cover being `⊤`).  The excision content —
which diamonds are covered by nothing — is carried by the *strictness* of
the chronology, pinned per instance (`minkowski_not_thick_degenerate`).
-/

namespace Qtsl
namespace DiamondSite

open CategoryTheory

variable {X : Type*} [PartialOrder X]

/-! ## The diamond preorder -/

/-- Diamonds are preordered by containment: `E ≤ D` iff `E ⊆ D`
endpointwise (`Sub`).  This is the record-geometry direction — morphisms
are inclusions of subregions — matching the window poset of the classical
column. -/
instance : Preorder (Diamond X) where
  le E D := Sub E D
  le_refl _ := ⟨le_refl _, le_refl _⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₂.1.trans h₁.1, h₁.2.trans h₂.2⟩

theorem le_iff_sub {E D : Diamond X} : E ≤ D ↔ Sub E D := Iff.rfl

variable {K : ChronologyKit X}

/-! ## Absorption and interpolation for interiority -/

/-- Shrinking the inner diamond preserves interiority (mixing laws). -/
theorem InteriorMem.of_le {D E E' : Diamond X} (h : InteriorMem K D E)
    (h' : E' ≤ E) : InteriorMem K D E' :=
  ⟨K.chron_of_chron_le h.1 h'.1, K.chron_of_le_chron h'.2 h.2⟩

/-- Growing the outer diamond preserves interiority (mixing laws). -/
theorem InteriorMem.trans_le {D D' E : Diamond X} (h : InteriorMem K D E)
    (h' : D ≤ D') : InteriorMem K D' E :=
  ⟨K.chron_of_le_chron h'.1 h.1, K.chron_of_chron_le h.2 h'.2⟩

/-- **Interpolation for interiority**: a chronologically interior
subdiamond admits a diamond strictly between — interpolate at both
endpoints.  This divisibility is what drives the local character of the
derived topology. -/
theorem InteriorMem.interpolate {D E : Diamond X} (h : InteriorMem K D E) :
    ∃ F : Diamond X, InteriorMem K D F ∧ InteriorMem K F E := by
  obtain ⟨c, hDc, hcE⟩ := K.interpolate h.1
  obtain ⟨d, hEd, hdD⟩ := K.interpolate h.2
  exact ⟨⟨c, d, (K.le_of_chron hcE).trans (E.le.trans (K.le_of_chron hEd))⟩,
    ⟨hDc, hdD⟩, ⟨hcE, hEd⟩⟩

/-! ## The derived Grothendieck topology -/

/-- **The derived topology of a causal order**, in closed form: a sieve
covers `D` iff it contains every chronologically interior subdiamond
arrow.  Pullback stability is the mixing laws; transitivity is
two-endpoint interpolation.  Note the consumption: exactly
`le_of_chron`, `chron_of_le_chron`, `chron_of_chron_le`, `interpolate` —
the filtered/directed fields of bicontinuity are *not* used here (they
feed sheaf descent, not the topology). -/
def diamondTopology (K : ChronologyKit X) :
    GrothendieckTopology (Diamond X) where
  sieves D := {S | ∀ ⦃E : Diamond X⦄ (h : E ≤ D),
    InteriorMem K D E → S (homOfLE h)}
  top_mem' _ := fun _ _ _ => trivial
  pullback_stable' := by
    intro D D₂ S f hS E h hint
    show S (homOfLE h ≫ f)
    rw [Subsingleton.elim (homOfLE h ≫ f) (homOfLE (h.trans (leOfHom f)))]
    exact hS (h.trans (leOfHom f)) (hint.trans_le (leOfHom f))
  transitive' := by
    intro D S hS R hlocal E hle hint
    obtain ⟨F, hDF, hFE⟩ := hint.interpolate
    have hFD : F ≤ D := sub_of_interiorMem hDF
    have hEF : E ≤ F := sub_of_interiorMem hFE
    have hR : R (homOfLE hEF ≫ homOfLE hFD) :=
      hlocal (hS hFD hDF) hEF hFE
    rwa [Subsingleton.elim (homOfLE hEF ≫ homOfLE hFD) (homOfLE hle)] at hR

theorem mem_diamondTopology_iff {D : Diamond X} {S : Sieve D} :
    S ∈ diamondTopology K D ↔
      ∀ ⦃E : Diamond X⦄ (h : E ≤ D), InteriorMem K D E → S (homOfLE h) :=
  Iff.rfl

/-- On the boundary family — diamonds that are not chronologically thick —
every sieve covers, the interiority condition being vacuous there.  The
topology-grade form of the empty-cover decision; the classical
duration-zero behaviour is its (0+1)-dimensional shadow. -/
theorem mem_of_not_thick {D : Diamond X} (h : ¬ Thick K D)
    (S : Sieve D) : S ∈ diamondTopology K D :=
  fun _ _ hint => (h (thick_of_interior_nonempty ⟨_, hint⟩)).elim

/-- **The descent dial, trivial end**: under the degenerate chronology
(`chron = ≤` — which the kit admits; strictness is instance data, not a
kit axiom), the derived topology is the trivial one: only the maximal
sieve covers, so sheaves are exactly presheaves.  Together with
`int_lt_no_chronologyKit` below this places the tick column at
the dial's trivial end: on `ℤ` the *strict* setting is refused (so the
genuinely interior covers of the dense orders have no tick
counterpart) and the tick column runs on the degenerate setting —
though not because the degenerate kit is unique on `ℤ` (nondegenerate
kits exist, e.g. `a ≪ b ↔ a ≤ 0 ∧ 0 ≤ b`); dense orders also admit
the strict setting, whose covers are the genuinely interior ones.
The chronology is the descent dial. -/
theorem mem_diamondTopology_degenerate_iff
    (hK : ∀ a b : X, K.chron a b ↔ a ≤ b) {D : Diamond X} {S : Sieve D} :
    S ∈ diamondTopology K D ↔ S = ⊤ := by
  constructor
  · intro hS
    refine Sieve.ext fun E f => ?_
    simp only [Sieve.top_apply, iff_true]
    have hf : S (homOfLE (leOfHom f)) :=
      hS (leOfHom f)
        ⟨(hK _ _).mpr (leOfHom f).1, (hK _ _).mpr (leOfHom f).2⟩
    rwa [Subsingleton.elim (homOfLE (leOfHom f)) f] at hf
  · rintro rfl
    exact (diamondTopology K).top_mem D

/-! ## The Minkowski chronology kit: the special-relativity witness -/

section Minkowski

variable (E : Type*) [NormedAddCommGroup E]

/-- An event of Minkowski space over a real normed space `E`: a time
coordinate and a spatial coordinate.  (A structure rather than a product
type, so the cone order below cannot collide with the product order.) -/
@[ext]
structure Mink : Type _ where
  /-- The time coordinate. -/
  t : ℝ
  /-- The spatial coordinate. -/
  x : E

variable {E}

/-- The causal cone order: `p ≤ q` iff the spatial displacement fits
inside the elapsed time.  Transitivity is the triangle inequality. -/
instance : PartialOrder (Mink E) where
  le p q := ‖q.x - p.x‖ ≤ q.t - p.t
  le_refl p := by simp
  le_trans p q r h₁ h₂ := by
    have htri : ‖r.x - p.x‖ ≤ ‖r.x - q.x‖ + ‖q.x - p.x‖ := by
      simpa using norm_add_le (r.x - q.x) (q.x - p.x)
    show ‖r.x - p.x‖ ≤ r.t - p.t
    linarith [h₁, h₂]
  le_antisymm p q h₁ h₂ := by
    have h₁' : ‖q.x - p.x‖ ≤ q.t - p.t := h₁
    have h₂' : ‖p.x - q.x‖ ≤ p.t - q.t := h₂
    have ht : p.t = q.t := by
      have := (norm_nonneg (q.x - p.x)).trans h₁'
      have := (norm_nonneg (p.x - q.x)).trans h₂'
      linarith
    have hx : p.x = q.x := by
      have hle : ‖q.x - p.x‖ ≤ 0 := by rw [ht] at h₁'; simpa using h₁'
      have := le_antisymm hle (norm_nonneg _)
      exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm
    ext
    · exact ht
    · exact hx

theorem Mink.le_def {p q : Mink E} : p ≤ q ↔ ‖q.x - p.x‖ ≤ q.t - p.t :=
  Iff.rfl

/-- The chronological (strict-cone) relation. -/
def Mink.chron (p q : Mink E) : Prop := ‖q.x - p.x‖ < q.t - p.t

/-- **Spacelike incomparability**: distinct simultaneous events are
causally incomparable in both directions — the cone order is genuinely
partial, so the Minkowski instance leaves the (0+1)-dimensional column.
(The classical column's order is total; this is the kernel-checked
witness that the derived-site recipe covers orders no foliation
linearizes.) -/
theorem minkowski_spacelike_incomparable {x₀ : E} (hx : x₀ ≠ 0) :
    ¬ ((⟨0, 0⟩ : Mink E) ≤ ⟨0, x₀⟩) ∧ ¬ ((⟨0, x₀⟩ : Mink E) ≤ ⟨0, 0⟩) := by
  constructor
  · show ¬ ‖x₀ - 0‖ ≤ (0 : ℝ) - 0
    simpa using norm_pos_iff.mpr hx
  · show ¬ ‖(0 : E) - x₀‖ ≤ (0 : ℝ) - 0
    rw [zero_sub, norm_neg]
    simpa using norm_pos_iff.mpr hx

/-- **A thick diamond's stage space contains causally incomparable
pairs**: in the diamond from the origin to a pure time-step of `2`, the
events `(1, x₀)` and `(1, 0)` (any spatial displacement `0 < ‖x₀‖ ≤ 1`)
both lie between the endpoints, and neither causally precedes the
other.  Consequence for the record layer: a chain-supported record
cannot span a relativistic diamond's stages — the blank-slate record
over a spacetime site must admit spacelike-separated (causally
incomparable) stages, with regularity imposed per timeline; total
stage order is the foliated `(0+1)` shadow. -/
theorem minkowski_diamond_spacelike_pair {x₀ : E} (hx : x₀ ≠ 0)
    (hx1 : ‖x₀‖ ≤ 1) :
    ∃ p q : Mink E,
      ((⟨0, 0⟩ : Mink E) ≤ p ∧ p ≤ ⟨2, 0⟩) ∧
      ((⟨0, 0⟩ : Mink E) ≤ q ∧ q ≤ ⟨2, 0⟩) ∧
      ¬ p ≤ q ∧ ¬ q ≤ p := by
  refine ⟨⟨1, x₀⟩, ⟨1, 0⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · show ‖x₀ - 0‖ ≤ (1 : ℝ) - 0
    simpa using hx1
  · show ‖(0 : E) - x₀‖ ≤ (2 : ℝ) - 1
    rw [zero_sub, norm_neg]
    linarith
  · show ‖(0 : E) - 0‖ ≤ (1 : ℝ) - 0
    simp
  · show ‖(0 : E) - 0‖ ≤ (2 : ℝ) - 1
    simp
  · show ¬ ‖(0 : E) - x₀‖ ≤ (1 : ℝ) - 1
    rw [zero_sub, norm_neg]
    simpa using norm_pos_iff.mpr hx
  · show ¬ ‖x₀ - 0‖ ≤ (1 : ℝ) - 1
    simpa using norm_pos_iff.mpr hx

variable [NormedSpace ℝ E]

/-- Halving a displacement halves its norm (the midpoint step's norm
identity). -/
private theorem norm_half_smul (v : E) :
    ‖(2⁻¹ : ℝ) • v‖ = 2⁻¹ * ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2⁻¹)]

/-- **The Minkowski chronology kit**: the cone order with strict-cone
chronology satisfies the Martin–Panangaden bicontinuity fragment, over
any real normed space of any dimension.  Interpolation is the midpoint;
the filtered/directed fields take a pure-time step of size the smaller
chronological slack.  With `diamondTopology`, the derived spacetime site
of special relativity — thick diamonds, chronologically interior covers —
is a kernel-checked instance of the same construction whose value at
`(ℝ, <)` is the classical interval site. -/
def minkowskiKit : ChronologyKit (Mink E) where
  chron := Mink.chron
  le_of_chron h := h.le
  chron_of_le_chron {a b c} h h' := by
    have h₁ : ‖b.x - a.x‖ ≤ b.t - a.t := h
    have h₂ : ‖c.x - b.x‖ < c.t - b.t := h'
    have htri : ‖c.x - a.x‖ ≤ ‖c.x - b.x‖ + ‖b.x - a.x‖ := by
      simpa using norm_add_le (c.x - b.x) (b.x - a.x)
    show ‖c.x - a.x‖ < c.t - a.t
    linarith
  chron_of_chron_le {a b c} h h' := by
    have h₁ : ‖b.x - a.x‖ < b.t - a.t := h
    have h₂ : ‖c.x - b.x‖ ≤ c.t - b.t := h'
    have htri : ‖c.x - a.x‖ ≤ ‖c.x - b.x‖ + ‖b.x - a.x‖ := by
      simpa using norm_add_le (c.x - b.x) (b.x - a.x)
    show ‖c.x - a.x‖ < c.t - a.t
    linarith
  interpolate {a b} h := by
    have h' : ‖b.x - a.x‖ < b.t - a.t := h
    refine ⟨⟨a.t + (b.t - a.t) / 2, a.x + (2⁻¹ : ℝ) • (b.x - a.x)⟩, ?_, ?_⟩
    · show ‖(a.x + (2⁻¹ : ℝ) • (b.x - a.x)) - a.x‖
        < (a.t + (b.t - a.t) / 2) - a.t
      rw [add_sub_cancel_left, norm_half_smul, add_sub_cancel_left]
      linarith
    · show ‖b.x - (a.x + (2⁻¹ : ℝ) • (b.x - a.x))‖
        < b.t - (a.t + (b.t - a.t) / 2)
      have hbm : b.x - (a.x + (2⁻¹ : ℝ) • (b.x - a.x))
          = (2⁻¹ : ℝ) • (b.x - a.x) := by
        rw [sub_add_eq_sub_sub]
        nth_rewrite 1 [show b.x - a.x = (1 : ℝ) • (b.x - a.x) from
          (one_smul ℝ _).symm]
        rw [← sub_smul]
        norm_num
      rw [hbm, norm_half_smul]
      linarith
  up_filtered {a c c'} h h' := by
    have h₁ : ‖c.x - a.x‖ < c.t - a.t := h
    have h₂ : ‖c'.x - a.x‖ < c'.t - a.t := h'
    have hε₁ : (0 : ℝ) < c.t - a.t - ‖c.x - a.x‖ := by linarith
    have hε₂ : (0 : ℝ) < c'.t - a.t - ‖c'.x - a.x‖ := by linarith
    refine ⟨⟨a.t + min (c.t - a.t - ‖c.x - a.x‖)
      (c'.t - a.t - ‖c'.x - a.x‖), a.x⟩, ?_, ?_, ?_⟩
    · show ‖a.x - a.x‖ < (a.t + _) - a.t
      rw [sub_self, norm_zero, add_sub_cancel_left]
      exact lt_min hε₁ hε₂
    · show ‖c.x - a.x‖ ≤ c.t - (a.t + _)
      have := min_le_left (c.t - a.t - ‖c.x - a.x‖)
        (c'.t - a.t - ‖c'.x - a.x‖)
      linarith
    · show ‖c'.x - a.x‖ ≤ c'.t - (a.t + _)
      have := min_le_right (c.t - a.t - ‖c.x - a.x‖)
        (c'.t - a.t - ‖c'.x - a.x‖)
      linarith
  down_directed {b d d'} h h' := by
    have h₁ : ‖b.x - d.x‖ < b.t - d.t := h
    have h₂ : ‖b.x - d'.x‖ < b.t - d'.t := h'
    have hε₁ : (0 : ℝ) < b.t - d.t - ‖b.x - d.x‖ := by linarith
    have hε₂ : (0 : ℝ) < b.t - d'.t - ‖b.x - d'.x‖ := by linarith
    refine ⟨⟨b.t - min (b.t - d.t - ‖b.x - d.x‖)
      (b.t - d'.t - ‖b.x - d'.x‖), b.x⟩, ?_, ?_, ?_⟩
    · show ‖b.x - b.x‖ < b.t - (b.t - _)
      rw [sub_self, norm_zero, sub_sub_cancel]
      exact lt_min hε₁ hε₂
    · show ‖b.x - d.x‖ ≤ (b.t - _) - d.t
      have := min_le_left (b.t - d.t - ‖b.x - d.x‖)
        (b.t - d'.t - ‖b.x - d'.x‖)
      linarith
    · show ‖b.x - d'.x‖ ≤ (b.t - _) - d'.t
      have := min_le_right (b.t - d.t - ‖b.x - d.x‖)
        (b.t - d'.t - ‖b.x - d'.x‖)
      linarith

/-- Degenerate diamonds are not chronologically thick: the excision
content of the *strict* cone.  (This is the statement that separates the
strict chronology from the degenerate `chron := ≤`, under which every
kit field would still prove.) -/
theorem minkowski_not_thick_degenerate (p : Mink E) :
    ¬ Thick (minkowskiKit (E := E)) ⟨p, p, le_rfl⟩ := by
  show ¬ ‖p.x - p.x‖ < p.t - p.t
  simp

/-- A timelike pair: pure time-step diamonds are thick. -/
example : Thick (minkowskiKit (E := E))
    ⟨⟨0, 0⟩, ⟨1, 0⟩, by simp [Mink.le_def]⟩ := by
  show ‖(0 : E) - 0‖ < (1 : ℝ) - 0
  simp

end Minkowski

/-! ## The tick discriminator: no strict chronology on ℤ -/

/-- The discrete order refuses the *strict* chronology: no
`ChronologyKit` on `ℤ` has `chron = (· < ·)` — interpolation fails
between consecutive ticks.  Exactly this refusal, and no uniqueness
beyond it: nondegenerate kits on `ℤ` exist (e.g. `a ≪ b ↔ a ≤ 0 ∧
0 ≤ b` satisfies every field, `0` witnessing interpolation and both
filtration laws), so what ticks lack is specifically the strict
setting whose covers are the genuinely interior ones — the
classical/Minkowski/globally-hyperbolic instances all supply that
density as genuine structure. -/
theorem int_lt_no_chronologyKit :
    ¬ ∃ K : ChronologyKit ℤ, ∀ a b : ℤ, K.chron a b ↔ a < b := by
  rintro ⟨K, hK⟩
  obtain ⟨c, h₀c, hc₁⟩ := K.interpolate ((hK 0 1).mpr zero_lt_one)
  have h₀c' := (hK 0 c).mp h₀c
  have hc₁' := (hK c 1).mp hc₁
  omega

end DiamondSite
end Qtsl
