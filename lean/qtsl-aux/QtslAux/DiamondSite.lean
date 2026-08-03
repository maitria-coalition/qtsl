import Mathlib.Order.MinMax
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat

/-! # The causal-diamond site: interior coverage and clock maps

Order-theoretic well-behavedness of the interior coverage on causal
diamonds, at bicontinuous-poset generality; the empty-cover boundary
decision's witness; clock-map functoriality and cover-preservation; and
the algebraic homogenization core for time-inhomogeneous evolution
families.

**What this module proves.**

* For the exact order-theoretic fragment of Martin–Panangaden
  bicontinuity packaged in `ChronologyKit` (arXiv:gr-qc/0407094 —
  chronology `≪` a sub-relation of the causal order compatible with it on
  both sides, interpolative, with `↟a` filtered and `↡b` directed), the
  interior covers of a diamond are **nonempty iff the diamond is
  chronologically thick** (`a ≪ b`), and **pair-filtered** under
  containment (`interior_nonempty_iff_thick`, `interior_pairFiltered`).
  No manifold, no compactness — every bicontinuous poset qualifies, and
  the classical column is literally the instance `linearOrderKit` (any
  dense linear order, chronology = `<`): the interval domain is the
  (0+1)-dimensional case of the construction.

* **The empty-cover decision's mathematical content**
  (`no_interior_of_not_thick` + the degenerate-`ℚ`-diamond example):
  thickness is *exactly* the nonemptiness condition, definable in the
  site's own order vocabulary, so the thick-diamond subsite is the
  maximal domain on which the interior coverage has nonempty covers — and
  the classical excision of duration zero (Schultz–Spivak's `ℓ > 0`) is
  its one-dimensional shadow.

* **Clock-map functoriality and cover-preservation**, at the site grade:
  order theory only. A `ClockMap` is the abstract worldline clock —
  strictly chronology-preserving out of a linear time order, with the two
  approximation properties that openness of the chronological past/future
  supplies in a spacetime (`I⁻(x)` open ∋ γ(s) ⇒ γ(c) ∈ I⁻(x) for some
  c > s, and dually). Receipts: the induced diamond map is monotone for
  containment (`diamond_sub` — functoriality on the poset of diamonds),
  sends thick diamonds to thick diamonds (`diamond_thick`), interior-cover
  members to interior-cover members (`diamond_interiorMem`), and — the
  cover-preservation check proper — the image family is **cofinal** in the
  target's interior cover (`cover_cofinal`): every interior subdiamond of
  the image diamond is contained in the image of a source cover member, so
  the image generates a covering sieve. Density of the time order is the
  one hypothesis beyond the approximation fields.

* **The homogenization core for time-inhomogeneity** (algebraic face):
  the space-time-process trick — adjoin the process's own clock
  coordinate — turns a two-parameter evolution family into a one-parameter
  monoid action (`EvolutionFamily.spaceTime_zero`, `spaceTime_add`).

**What this module deliberately does NOT claim**:

* site-generic transport of extension theorems over an arbitrary site —
  this module supplies the coverage well-behavedness those arguments
  consume, not the arguments;
* the *manifold-level* instantiation facts: that a timelike worldline with
  proper time satisfies `ClockMap`'s approximation fields is supplied by
  openness of `I±` in a spacetime, cited here and not formalized;
* the probabilistic face of homogenization: jointly Borel two-parameter
  kernels, an inhomogeneous strong-Markov right-process realization,
  product-fine-topology care for moving regions, and the `∂ₛ`
  generator-domain question. The flow-level laws here name exactly the
  seam where those results dock.
-/

namespace Qtsl
namespace DiamondSite

/-- The order-theoretic fragment of Martin–Panangaden **bicontinuity** that
the diamond interior coverage consumes: a chronology relation `≪` beneath
the causal order `≤`, absorbing `≤` on both sides, interpolative, with
chronological up-sets filtered and down-sets directed. On a globally
hyperbolic spacetime, `≪` is chronology; on a dense linear order, `<`
(see `linearOrderKit`). -/
structure ChronologyKit (X : Type*) [PartialOrder X] where
  /-- chronology, `a ≪ b` -/
  chron : X → X → Prop
  le_of_chron : ∀ {a b : X}, chron a b → a ≤ b
  chron_of_le_chron : ∀ {a b c : X}, a ≤ b → chron b c → chron a c
  chron_of_chron_le : ∀ {a b c : X}, chron a b → b ≤ c → chron a c
  interpolate : ∀ {a b : X}, chron a b → ∃ c, chron a c ∧ chron c b
  up_filtered : ∀ {a c c' : X}, chron a c → chron a c' →
    ∃ c'', chron a c'' ∧ c'' ≤ c ∧ c'' ≤ c'
  down_directed : ∀ {b d d' : X}, chron d b → chron d' b →
    ∃ d'', chron d'' b ∧ d ≤ d'' ∧ d' ≤ d''

variable {X : Type*} [PartialOrder X]

/-- A causal diamond `[lo, hi]`, presented by its endpoints. -/
structure Diamond (X : Type*) [PartialOrder X] where
  lo : X
  hi : X
  le : lo ≤ hi

/-- Containment of diamonds, endpointwise: `E ⊆ D`. -/
def Sub (E D : Diamond X) : Prop := D.lo ≤ E.lo ∧ E.hi ≤ D.hi

/-- Chronological thickness `lo ≪ hi` — the subsite predicate of the
empty-cover decision. -/
def Thick (K : ChronologyKit X) (D : Diamond X) : Prop := K.chron D.lo D.hi

/-- Membership in the interior cover of `D`: a subdiamond both of whose
endpoints are chronologically interior. -/
def InteriorMem (K : ChronologyKit X) (D E : Diamond X) : Prop :=
  K.chron D.lo E.lo ∧ K.chron E.hi D.hi

variable {K : ChronologyKit X}

theorem sub_of_interiorMem {D E : Diamond X} (h : InteriorMem K D E) : Sub E D :=
  ⟨K.le_of_chron h.1, K.le_of_chron h.2⟩

/-- Nonemptiness half: a thick diamond has an interior cover member, by
interpolation (a degenerate one, `[c, c]`, suffices). -/
theorem interior_nonempty {D : Diamond X} (h : Thick K D) :
    ∃ E, InteriorMem K D E := by
  obtain ⟨c, hac, hcb⟩ := K.interpolate h
  exact ⟨⟨c, c, le_rfl⟩, hac, hcb⟩

/-- Converse: any interior member forces thickness — so the boundary family
(degenerate and null-related diamonds) has *empty* interior covers. -/
theorem thick_of_interior_nonempty {D : Diamond X}
    (h : ∃ E, InteriorMem K D E) : Thick K D := by
  obtain ⟨E, hlo, hhi⟩ := h
  exact K.chron_of_chron_le (K.chron_of_chron_le hlo E.le) (K.le_of_chron hhi)

/-- **Nonemptiness, iff form**: interior covers are nonempty exactly on the
chronologically thick diamonds. This is the mathematical content of the
empty-cover decision — the thick subsite is the maximal domain of the
coverage, and the classical `ℓ > 0` excision is its one-dimensional
shadow. -/
theorem interior_nonempty_iff_thick {D : Diamond X} :
    (∃ E, InteriorMem K D E) ↔ Thick K D :=
  ⟨thick_of_interior_nonempty, interior_nonempty⟩

/-- The boundary family has no interior covers (contrapositive form used by
the subsite decision). -/
theorem no_interior_of_not_thick {D : Diamond X} (h : ¬ Thick K D) :
    ¬ ∃ E, InteriorMem K D E :=
  fun hE => h (thick_of_interior_nonempty hE)

/-- **Filteredness**: two interior members are both contained in a third —
filteredness of `↟lo` meets directedness of `↡hi` in the middle. With
`interior_nonempty_iff_thick`, this is the coverage well-behavedness that
local-connectedness arguments consume, at full bicontinuous-poset
generality. -/
theorem interior_pairFiltered {D E₁ E₂ : Diamond X}
    (h₁ : InteriorMem K D E₁) (h₂ : InteriorMem K D E₂) :
    ∃ E, InteriorMem K D E ∧ Sub E₁ E ∧ Sub E₂ E := by
  obtain ⟨c, hc, hc₁, hc₂⟩ := K.up_filtered h₁.1 h₂.1
  obtain ⟨d, hd, hd₁, hd₂⟩ := K.down_directed h₁.2 h₂.2
  exact ⟨⟨c, d, ((hc₁.trans E₁.le).trans hd₁)⟩, ⟨hc, hd⟩, ⟨hc₁, hd₁⟩, ⟨hc₂, hd₂⟩⟩

section ClassicalColumn

/-- **The classical column as an instance**: any dense linear order (ℝ, ℚ —
the Schultz–Spivak interval-site base) carries the kit with chronology `<`.
The classical interval domain is the (0+1)-dimensional case of the diamond
construction, not a cousin of it. -/
def linearOrderKit (T : Type*) [LinearOrder T] [DenselyOrdered T] :
    ChronologyKit T where
  chron a b := a < b
  le_of_chron h := h.le
  chron_of_le_chron h h' := lt_of_le_of_lt h h'
  chron_of_chron_le h h' := lt_of_lt_of_le h h'
  interpolate h := exists_between h
  up_filtered h h' := ⟨_, lt_min h h', min_le_left _ _, min_le_right _ _⟩
  down_directed h h' := ⟨_, max_lt h h', le_max_left _ _, le_max_right _ _⟩

/-- Smoke: the thick rational diamond `[0, 1]` has an interior cover. -/
example : ∃ E, InteriorMem (linearOrderKit ℚ) ⟨0, 1, by norm_num⟩ E :=
  interior_nonempty (show (0 : ℚ) < 1 by norm_num)

/-- The boundary family concretely: the degenerate rational diamond `[0, 0]`
has no interior cover — the general form of the classical duration-zero
excision, witnessed. -/
example : ¬ ∃ E, InteriorMem (linearOrderKit ℚ) ⟨0, 0, le_rfl⟩ E :=
  no_interior_of_not_thick (lt_irrefl (0 : ℚ))

end ClassicalColumn

section ClockMaps

variable {T : Type*} [LinearOrder T]

/-- The abstract worldline clock: a map from a linear time order into a
chronology kit's carrier, strictly chronology-preserving, with the two
endpoint-approximation properties. In a spacetime these fields are exactly
what a *continuous timelike* curve supplies: `chron_of_lt` is
timelikeness, and the approximation fields hold because chronological
pasts/futures are open (`γ(s) ≪ x` puts `γ(s)` in the open set `I⁻(x)`,
so `γ(c) ∈ I⁻(x)` for some `c > s`; dually at the top). That instantiation
is cited, not formalized — this module works at the site grade the chapter
states the construction. -/
structure ClockMap (T : Type*) [LinearOrder T] {X : Type*} [PartialOrder X]
    (K : ChronologyKit X) where
  toFun : T → X
  chron_of_lt : ∀ {s t : T}, s < t → K.chron (toFun s) (toFun t)
  approx_above : ∀ {s : T} {x : X}, K.chron (toFun s) x →
    ∃ c, s < c ∧ K.chron (toFun c) x
  approx_below : ∀ {t : T} {y : X}, K.chron y (toFun t) →
    ∃ d, d < t ∧ K.chron y (toFun d)

theorem ClockMap.mono (γ : ClockMap T K) {s t : T} (h : s ≤ t) :
    γ.toFun s ≤ γ.toFun t := by
  rcases h.lt_or_eq with hlt | rfl
  · exact K.le_of_chron (γ.chron_of_lt hlt)
  · exact le_rfl

/-- The object map of the clock: proper-time intervals to causal hulls of
worldline segments. -/
def ClockMap.diamond (γ : ClockMap T K) (s t : T) (h : s ≤ t) : Diamond X :=
  ⟨γ.toFun s, γ.toFun t, γ.mono h⟩

/-- **Functoriality**: the object map is monotone for containment — interval
inclusions go to diamond containments, so the clock is a functor of the
diamond posets (site-map data at the poset stratum). -/
theorem ClockMap.diamond_sub (γ : ClockMap T K) {s t s' t' : T}
    (h : s ≤ t) (h' : s' ≤ t') (hs : s ≤ s') (ht : t' ≤ t) :
    Sub (γ.diamond s' t' h') (γ.diamond s t h) :=
  ⟨γ.mono hs, γ.mono ht⟩

/-- Thick intervals go to thick diamonds: the clock lands in the thick
subsite (composing with the empty-cover decision). -/
theorem ClockMap.diamond_thick (γ : ClockMap T K) {s t : T} (h : s < t) :
    Thick K (γ.diamond s t h.le) :=
  γ.chron_of_lt h

/-- Interior-cover members go to interior-cover members: `s < c ≤ d < t`
maps to a chronologically interior subdiamond. -/
theorem ClockMap.diamond_interiorMem (γ : ClockMap T K) {s t c d : T}
    (hst : s ≤ t) (hcd : c ≤ d) (h₁ : s < c) (h₂ : d < t) :
    InteriorMem K (γ.diamond s t hst) (γ.diamond c d hcd) :=
  ⟨γ.chron_of_lt h₁, γ.chron_of_lt h₂⟩

/-- **Cover-preservation**: the image of the source interior cover is
*cofinal* in the target's interior cover — every interior subdiamond `E` of
the image diamond is contained in the image of a source cover member. Hence
the image family generates a covering sieve: the clock is cover-preserving.
Density of the time order is the one hypothesis beyond the approximation
fields (it lets the lower witness be pulled below `t` before the upper
witness is pushed above it). -/
theorem ClockMap.cover_cofinal [DenselyOrdered T] (γ : ClockMap T K)
    {s t : T} (hst : s < t) {E : Diamond X}
    (hE : InteriorMem K (γ.diamond s t hst.le) E) :
    ∃ (c d : T) (hcd : c ≤ d), s < c ∧ d < t ∧
      InteriorMem K (γ.diamond s t hst.le) (γ.diamond c d hcd) ∧
      Sub E (γ.diamond c d hcd) := by
  obtain ⟨hlo, hhi⟩ := hE
  -- lower witness, pulled into (s, min c₀ t)
  obtain ⟨c₀, hsc₀, hc₀⟩ := γ.approx_above hlo
  obtain ⟨c, hsc, hcm⟩ := exists_between (lt_min hsc₀ hst)
  have hct : c < t := hcm.trans_le (min_le_right _ _)
  have hcx : K.chron (γ.toFun c) E.lo :=
    K.chron_of_le_chron (γ.mono (hcm.trans_le (min_le_left _ _)).le) hc₀
  -- upper witness, pushed above c
  obtain ⟨d₀, hd₀t, hd₀⟩ := γ.approx_below hhi
  refine ⟨c, max d₀ c, le_max_right _ _, hsc, max_lt hd₀t hct,
    ⟨γ.chron_of_lt hsc, γ.chron_of_lt (max_lt hd₀t hct)⟩,
    K.le_of_chron hcx,
    K.le_of_chron (K.chron_of_chron_le hd₀ (γ.mono (le_max_left _ _)))⟩

end ClockMaps

section Homogenization

/-- Two-parameter evolution family (the deterministic face of a
time-inhomogeneous dynamics along a worldline clock): `φ s t` evolves
state from clock-time `s` to clock-time `t`. -/
structure EvolutionFamily (T S : Type*) where
  φ : T → T → S → S
  idem : ∀ s x, φ s s x = x
  comp : ∀ s t u x, φ t u (φ s t x) = φ s u x

variable {T S : Type*} [AddMonoid T]

/-- The space-time process: adjoin the process's own clock coordinate to the
state, `(τ, x) ↦ (τ + h, φ τ (τ+h) x)`. -/
def EvolutionFamily.spaceTime (F : EvolutionFamily T S) (h : T) :
    T × S → T × S :=
  fun p => (p.1 + h, F.φ p.1 (p.1 + h) p.2)

@[simp] theorem EvolutionFamily.spaceTime_fst (F : EvolutionFamily T S)
    (h : T) (p : T × S) : (F.spaceTime h p).1 = p.1 + h := rfl

/-- **Homogenization, unit law**: the space-time process at duration zero is
the identity. -/
theorem EvolutionFamily.spaceTime_zero (F : EvolutionFamily T S) :
    F.spaceTime 0 = id := by
  funext p
  simp [spaceTime, F.idem]

/-- **Homogenization, composition law**: the space-time process is a
one-parameter monoid action — the algebraic content of "adjoining the
process's own time coordinate recovers homogeneity". The probabilistic
upgrades (jointly Borel kernels, right-process realization, fine-topology
care, the `∂ₛ` generator term) are deliberately not claimed here; see the
module docstring. -/
theorem EvolutionFamily.spaceTime_add (F : EvolutionFamily T S) (h h' : T) :
    F.spaceTime (h + h') = F.spaceTime h' ∘ F.spaceTime h := by
  funext p
  simp [spaceTime, F.comp, add_assoc]

end Homogenization

end DiamondSite
end Qtsl
