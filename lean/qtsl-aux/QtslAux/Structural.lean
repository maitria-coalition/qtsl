import Mathlib.Data.Set.Lattice
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith
import QtslAux.NNFDuality

/-! # Structural rules for region satisfaction

This module proves the soundness of the structural inference rules of
Bernstein Logic: rules that manipulate a region-satisfaction judgement
`RegionSat R den` (the region `R` is contained in the denotation `den` of a
specification) without reference to any particular dynamics. Each theorem
is the soundness statement of one checker-level rule, phrased so that a
certificate checker can discharge the rule by exhibiting the stated
hypotheses.

The rule families:

* monotonicity and weakening: `regionSat_mono`, `regionSat_weaken`;
* multiplier rules: `hypMultiplier_sound` — an S-procedure-style step
  absorbing a sign-definite hypothesis `0 ≤ g` into a combined residual via
  a nonnegative multiplier;
* domain rules: `fullDomainWeaken_sound`, `fullDomainWeaken_offScope`,
  `verifiedCover_sound`, `verifiedCover_components_sound` — restricting a
  full-domain fact to a scope, and covering a domain by a verified cell set
  plus excluded components;
* positive combinations: `positiveCombinationAnd_sound`,
  `positiveCombinationOr_sound`, `positiveCombinationInter_sound`,
  `positiveCombinationUnion_sound` — region satisfaction is preserved under
  binary and indexed intersections and unions;
* closure and rounding of polynomial inequality atoms:
  `closureExactLt_sound`, `closureExactGt_sound`,
  `closureExact_isClosed_ge`, `closureExact_isClosed_le`,
  `closureOutward_sound`, `closureOutwardGe_sound`, `compl_over_approx`,
  `closureInwardEpsLt_sound`, `closureInwardEpsGt_sound`,
  `closureInwardEps_isClosed` — relating strict and non-strict sublevel
  sets, their complements, and `ε`-strengthened (inward-rounded) versions;
* integer counter rounding: `countAtomRounding_sound`,
  `countAtomRounding_tighter`, `countAtomRounding_eq` — on reachable states
  where a counter takes integer values, failing `k ≤ j` is equivalent to
  `j + 1 ≤ k`;
* NNF rewrite warrants (T12): `nnfDoubleNeg_sound`, `nnfDeMorganAnd_sound`,
  `nnfDeMorganOr_sound`, `nnfAtomLe_sound`, `nnfAtomGe_sound`,
  `nnfAtomLt_sound`, `nnfAtomGt_sound`, `nnfRewrite_regionSat` — the
  per-duality region-denotation equalities warranting the QNnfRewrite alias
  batch, in the same bridge-hypothesis dress as the closure rules; the
  transform-level metatheory (NNF normalization and its semantic
  correctness) lives in `QtslAux.NNFDuality`, whose atom-swap equalities
  these delegate to.
-/

namespace Qtsl.Structural

variable {X : Type*}

/-- The region-satisfaction judgement: the region `R` satisfies a
specification with denotation `den` when `R ⊆ den`. -/
def RegionSat (R den : Set X) : Prop := R ⊆ den

theorem regionSat_iff {R den : Set X} : RegionSat R den ↔ ∀ x ∈ R, x ∈ den :=
  Iff.rfl

theorem regionSat_mono {R S den : Set X} (h : RegionSat R den) (hsub : S ⊆ R) :
    RegionSat S den :=
  hsub.trans h

theorem regionSat_weaken {R den den' : Set X} (h : RegionSat R den)
    (hden : den ⊆ den') : RegionSat R den' :=
  h.trans hden

/-- Soundness of the hypothesis-multiplier rule (an S-procedure step): if
the child atom is exactly `{x | 0 ≤ g x}`, the multiplier `lam` is
nonnegative on the cell, and the combined residual satisfies
`N + lam * g ≤ 0` on the cell, then `N ≤ 0` on the cell intersected with
the child atom. -/
theorem hypMultiplier_sound (cell childAtom : Set X) (N lam g : X → ℝ)
    (hbridge : childAtom = {x | 0 ≤ g x})
    (hlam : ∀ x ∈ cell, 0 ≤ lam x)
    (hcomb : ∀ x ∈ cell, N x + lam x * g x ≤ 0) :
    ∀ x ∈ cell ∩ childAtom, N x ≤ 0 := by
  rintro x ⟨hxc, hxa⟩
  rw [hbridge] at hxa
  have hg : (0 : ℝ) ≤ g x := hxa
  have hmul : (0 : ℝ) ≤ lam x * g x := mul_nonneg (hlam x hxc) hg
  linarith [hcomb x hxc]

/-- A property established on the full domain holds on any scope contained
in it. -/
theorem fullDomainWeaken_sound (Dm scope : Set X) (P : X → Prop)
    (hbridge : scope ⊆ Dm)
    (hrow : ∀ x ∈ Dm, P x) :
    ∀ x ∈ scope, P x :=
  fun x hx => hrow x (hbridge hx)

theorem fullDomainWeaken_offScope (Dm Off : Set X) (P : X → Prop)
    (hrow : ∀ x ∈ Dm, P x) :
    ∀ x ∈ Dm \ Off, P x :=
  fullDomainWeaken_sound Dm (Dm \ Off) P Set.diff_subset hrow

/-- Soundness of the verified-cover rule: if the property holds on the
verified cell set `C` and everything in the domain outside `C` is
off-scope, then the property holds on the scope `Dm \ Off`. -/
theorem verifiedCover_sound (Dm C Off scope : Set X) (P : X → Prop)
    (hbridge : scope = Dm \ Off)
    (hrowC : ∀ x ∈ C, P x)
    (hresidual : Dm \ C ⊆ Off) :
    ∀ x ∈ scope, P x := by
  intro x hx
  rw [hbridge] at hx
  by_cases hxC : x ∈ C
  · exact hrowC x hxC
  · exact absurd (hresidual ⟨hx.1, hxC⟩) hx.2

/-- Componentwise form of the verified-cover rule: the residual `Dm \ C`
may be decomposed into components `K i`, each individually contained in the
off-scope set. -/
theorem verifiedCover_components_sound {ι : Type*} (Dm C Off scope : Set X)
    (K : ι → Set X) (P : X → Prop)
    (hbridge : scope = Dm \ Off)
    (hrowC : ∀ x ∈ C, P x)
    (hdecomp : Dm \ C ⊆ ⋃ i, K i)
    (hcomp : ∀ i, K i ⊆ Off) :
    ∀ x ∈ scope, P x := by
  refine verifiedCover_sound Dm C Off scope P hbridge hrowC (fun x hx => ?_)
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hdecomp hx)
  exact hcomp i hxi

/-- Region satisfaction is preserved under conjunction: regions satisfying
two specifications intersect to a region satisfying their conjunction. -/
theorem positiveCombinationAnd_sound (R₁ R₂ den₁ den₂ denAnd : Set X)
    (hbridge : denAnd = den₁ ∩ den₂)
    (h₁ : RegionSat R₁ den₁) (h₂ : RegionSat R₂ den₂) :
    RegionSat (R₁ ∩ R₂) denAnd :=
  hbridge ▸ Set.inter_subset_inter h₁ h₂

theorem positiveCombinationOr_sound (R₁ R₂ den₁ den₂ denOr : Set X)
    (hbridge : denOr = den₁ ∪ den₂)
    (h₁ : RegionSat R₁ den₁) (h₂ : RegionSat R₂ den₂) :
    RegionSat (R₁ ∪ R₂) denOr :=
  hbridge ▸ Set.union_subset_union h₁ h₂

theorem positiveCombinationInter_sound {ι : Type*} (R den : ι → Set X)
    (denAll : Set X)
    (hbridge : denAll = ⋂ i, den i)
    (h : ∀ i, RegionSat (R i) (den i)) :
    RegionSat (⋂ i, R i) denAll :=
  hbridge ▸ Set.iInter_mono h

theorem positiveCombinationUnion_sound {ι : Type*} (R den : ι → Set X)
    (denAll : Set X)
    (hbridge : denAll = ⋃ i, den i)
    (h : ∀ i, RegionSat (R i) (den i)) :
    RegionSat (⋃ i, R i) denAll :=
  hbridge ▸ Set.iUnion_mono h

/-- Exact closure of a strict `<` atom: the complement of `{x | p x < c}`
is `{x | c ≤ p x}`. -/
theorem closureExactLt_sound (p : X → ℝ) (c : ℝ) (strictAtom : Set X)
    (hbridge : strictAtom = {x | p x < c}) :
    strictAtomᶜ = {x | c ≤ p x} := by
  subst hbridge
  ext x
  simp [not_lt]

theorem closureExactGt_sound (p : X → ℝ) (c : ℝ) (strictAtom : Set X)
    (hbridge : strictAtom = {x | c < p x}) :
    strictAtomᶜ = {x | p x ≤ c} := by
  subst hbridge
  ext x
  simp [not_lt]

theorem closureExact_isClosed_ge [TopologicalSpace X] {p : X → ℝ}
    (hp : Continuous p) (c : ℝ) : IsClosed {x | c ≤ p x} :=
  isClosed_le continuous_const hp

theorem closureExact_isClosed_le [TopologicalSpace X] {p : X → ℝ}
    (hp : Continuous p) (c : ℝ) : IsClosed {x | p x ≤ c} :=
  isClosed_le hp continuous_const

/-- Outward closure: the complement of the non-strict sublevel set
`{x | p x ≤ c}` is over-approximated by the closed superlevel set
`{x | c ≤ p x}`. -/
theorem closureOutward_sound (p : X → ℝ) (c : ℝ) (cmplAtom : Set X)
    (hbridge : cmplAtom = {x | c ≤ p x}) :
    {x | p x ≤ c}ᶜ ⊆ cmplAtom := by
  subst hbridge
  intro x hx
  have hx' : ¬ (p x ≤ c) := hx
  exact (not_le.mp hx').le

theorem closureOutwardGe_sound (p : X → ℝ) (c : ℝ) (cmplAtom : Set X)
    (hbridge : cmplAtom = {x | p x ≤ c}) :
    {x | c ≤ p x}ᶜ ⊆ cmplAtom := by
  subst hbridge
  intro x hx
  have hx' : ¬ (c ≤ p x) := hx
  exact (not_le.mp hx').le

/-- Complements reverse region satisfaction: `R ⊆ den` gives
`denᶜ ⊆ Rᶜ`, so an over-approximation of a denotation's complement
over-approximates the region's complement. -/
theorem compl_over_approx {R den : Set X} (h : RegionSat R den) :
    denᶜ ⊆ Rᶜ :=
  fun _ hx hxR => hx (h hxR)

/-- Inward `ε`-rounding of a strict `<` atom: the closed, `ε`-strengthened
set `{x | p x ≤ c - ε}` under-approximates the strict sublevel set
`{x | p x < c}` — so a certificate on the rounded set is sound for the
strict atom. -/
theorem closureInwardEpsLt_sound (p : X → ℝ) (c ε : ℝ) (hε : 0 < ε)
    (roundedAtom : Set X)
    (hbridge : roundedAtom = {x | p x ≤ c - ε}) :
    roundedAtom ⊆ {x | p x < c} := by
  subst hbridge
  intro x hx
  have hpx : p x ≤ c - ε := hx
  show p x < c
  linarith

theorem closureInwardEpsGt_sound (p : X → ℝ) (c ε : ℝ) (hε : 0 < ε)
    (roundedAtom : Set X)
    (hbridge : roundedAtom = {x | c + ε ≤ p x}) :
    roundedAtom ⊆ {x | c < p x} := by
  subst hbridge
  intro x hx
  have hpx : c + ε ≤ p x := hx
  show c < p x
  linarith

theorem closureInwardEps_isClosed [TopologicalSpace X] {p : X → ℝ}
    (hp : Continuous p) (c ε : ℝ) : IsClosed {x | p x ≤ c - ε} :=
  closureExact_isClosed_le hp (c - ε)

/-- Integer counter rounding: on reachable states where the counter `k`
takes integer values, failing the atom `k ≤ j` implies the strengthened
bound `j + 1 ≤ k`. -/
theorem countAtomRounding_sound (k : X → ℝ) (j : ℤ) (Reach : Set X)
    (hbridge : ∀ x ∈ Reach, ∃ n : ℤ, k x = (n : ℝ)) :
    ∀ x ∈ Reach, x ∈ {x | k x ≤ (j : ℝ)}ᶜ → (j : ℝ) + 1 ≤ k x := by
  intro x hxR hx
  obtain ⟨n, hn⟩ := hbridge x hxR
  have hx' : ¬ (k x ≤ (j : ℝ)) := hx
  have hlt : (j : ℝ) < (n : ℝ) := by
    rw [hn] at hx'
    exact not_le.mp hx'
  have hjn : j < n := by exact_mod_cast hlt
  have hj1 : j + 1 ≤ n := by omega
  rw [hn]
  exact_mod_cast hj1

theorem countAtomRounding_tighter (k : X → ℝ) (j : ℤ) :
    {x | (j : ℝ) + 1 ≤ k x} ⊆ {x | (j : ℝ) < k x} := by
  intro x hx
  have h1 : (j : ℝ) + 1 ≤ k x := hx
  show (j : ℝ) < k x
  linarith

/-- On reachable states with integer counter values, the failure of
`k ≤ j` and the strengthened bound `j + 1 ≤ k` cut out the same set. -/
theorem countAtomRounding_eq (k : X → ℝ) (j : ℤ) (Reach : Set X)
    (hbridge : ∀ x ∈ Reach, ∃ n : ℤ, k x = (n : ℝ)) :
    Reach ∩ {x | k x ≤ (j : ℝ)}ᶜ = Reach ∩ {x | (j : ℝ) + 1 ≤ k x} := by
  ext x
  constructor
  · rintro ⟨hxR, hx⟩
    exact ⟨hxR, countAtomRounding_sound k j Reach hbridge x hxR hx⟩
  · rintro ⟨hxR, hx⟩
    refine ⟨hxR, ?_⟩
    have h1 : (j : ℝ) + 1 ≤ k x := hx
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    linarith

/-! ## NNF rewrite warrants (T12, one lemma per duality)

Each `QNnfRewrite` alias is a judgement-level `1 → 1` rewrite whose
unpacking target is the region-denotation equality below — and nothing
else: these warrants are set-algebra identities on region denotations,
never a license for probability-layer complement rewrites (those are the
typing layer's rejection; the fault line is the measure boundary).

The lemmas are stated in the same bridge-hypothesis dress as the closure
rules above, so a checker discharges each rule by exhibiting the atom as
data plus the stated bridge. Where the underlying equality is already
proven elsewhere in this package, the warrant delegates rather than
re-derives: the four threshold-atom swaps are `Qtsl.NNF.compl_*_atom`
(`QtslAux.NNFDuality`, which also proves the transform-level metatheory),
and the strict-atom orientations coincide with the exact-closure rules
`closureExactLt_sound`/`closureExactGt_sound` — restated under the T12
kit's naming so the rule fixture consumes one scheme. -/

/-- T12 double negation: the complement of a negated region is the region
itself. -/
theorem nnfDoubleNeg_sound (A negAtom : Set X)
    (hbridge : negAtom = Aᶜ) :
    negAtomᶜ = A := by
  subst hbridge
  exact compl_compl A

/-- T12 De Morgan through `∧`: the complement of a conjunction denotation
is the disjunction of the complements. -/
theorem nnfDeMorganAnd_sound (A B andAtom : Set X)
    (hbridge : andAtom = A ∩ B) :
    andAtomᶜ = Aᶜ ∪ Bᶜ := by
  subst hbridge
  exact Set.compl_inter A B

/-- T12 De Morgan through `∨`: the complement of a disjunction denotation
is the conjunction of the complements. -/
theorem nnfDeMorganOr_sound (A B orAtom : Set X)
    (hbridge : orAtom = A ∪ B) :
    orAtomᶜ = Aᶜ ∩ Bᶜ := by
  subst hbridge
  exact Set.compl_union A B

/-- T12 atom swap, `≤` orientation: the complement of the non-strict
sublevel atom `{x | p x ≤ c}` is the strict superlevel set. -/
theorem nnfAtomLe_sound (p : X → ℝ) (c : ℝ) (closedAtom : Set X)
    (hbridge : closedAtom = {x | p x ≤ c}) :
    closedAtomᶜ = {x | c < p x} := by
  subst hbridge
  exact NNF.compl_le_atom p c

/-- T12 atom swap, `≥` orientation: the complement of the non-strict
superlevel atom `{x | c ≤ p x}` is the strict sublevel set. -/
theorem nnfAtomGe_sound (p : X → ℝ) (c : ℝ) (closedAtom : Set X)
    (hbridge : closedAtom = {x | c ≤ p x}) :
    closedAtomᶜ = {x | p x < c} := by
  subst hbridge
  exact NNF.compl_ge_atom p c

/-- T12 atom swap, `<` orientation — coincides with the exact-closure rule
`closureExactLt_sound`, restated under the T12 kit's naming. -/
theorem nnfAtomLt_sound (p : X → ℝ) (c : ℝ) (strictAtom : Set X)
    (hbridge : strictAtom = {x | p x < c}) :
    strictAtomᶜ = {x | c ≤ p x} :=
  closureExactLt_sound p c strictAtom hbridge

/-- T12 atom swap, `>` orientation — coincides with the exact-closure rule
`closureExactGt_sound`, restated under the T12 kit's naming. -/
theorem nnfAtomGt_sound (p : X → ℝ) (c : ℝ) (strictAtom : Set X)
    (hbridge : strictAtom = {x | c < p x}) :
    strictAtomᶜ = {x | p x ≤ c} :=
  closureExactGt_sound p c strictAtom hbridge

/-- Judgement-level face of the `1 → 1` rewrite: region satisfaction
transports along the region-denotation equality that warrants the
rewrite. -/
theorem nnfRewrite_regionSat {R den den' : Set X} (hden : den = den') :
    RegionSat R den ↔ RegionSat R den' := by
  subst hden
  exact Iff.rfl

/-- Boundary witness for the `≤` swap's strictness: the threshold point
lies in the closed atom and not in its complement-swap — pinning that the
swap direction is strict, not closed. -/
theorem nnfAtomLe_boundary (c : ℝ) :
    c ∈ {x : ℝ | x ≤ c} ∧ c ∉ {x : ℝ | c < x} :=
  ⟨le_refl c, lt_irrefl c⟩

/-- Boundary witness for the `≥` swap's strictness. -/
theorem nnfAtomGe_boundary (c : ℝ) :
    c ∈ {x : ℝ | c ≤ x} ∧ c ∉ {x : ℝ | x < c} :=
  ⟨le_refl c, lt_irrefl c⟩

end Qtsl.Structural

#print axioms Qtsl.Structural.regionSat_mono
#print axioms Qtsl.Structural.regionSat_weaken
#print axioms Qtsl.Structural.hypMultiplier_sound
#print axioms Qtsl.Structural.fullDomainWeaken_sound
#print axioms Qtsl.Structural.fullDomainWeaken_offScope
#print axioms Qtsl.Structural.verifiedCover_sound
#print axioms Qtsl.Structural.verifiedCover_components_sound
#print axioms Qtsl.Structural.positiveCombinationAnd_sound
#print axioms Qtsl.Structural.positiveCombinationOr_sound
#print axioms Qtsl.Structural.positiveCombinationInter_sound
#print axioms Qtsl.Structural.positiveCombinationUnion_sound
#print axioms Qtsl.Structural.closureExactLt_sound
#print axioms Qtsl.Structural.closureExactGt_sound
#print axioms Qtsl.Structural.closureExact_isClosed_ge
#print axioms Qtsl.Structural.closureExact_isClosed_le
#print axioms Qtsl.Structural.closureOutward_sound
#print axioms Qtsl.Structural.closureOutwardGe_sound
#print axioms Qtsl.Structural.compl_over_approx
#print axioms Qtsl.Structural.closureInwardEpsLt_sound
#print axioms Qtsl.Structural.closureInwardEpsGt_sound
#print axioms Qtsl.Structural.closureInwardEps_isClosed
#print axioms Qtsl.Structural.countAtomRounding_sound
#print axioms Qtsl.Structural.countAtomRounding_tighter
#print axioms Qtsl.Structural.countAtomRounding_eq
#print axioms Qtsl.Structural.nnfDoubleNeg_sound
#print axioms Qtsl.Structural.nnfDeMorganAnd_sound
#print axioms Qtsl.Structural.nnfDeMorganOr_sound
#print axioms Qtsl.Structural.nnfAtomLe_sound
#print axioms Qtsl.Structural.nnfAtomGe_sound
#print axioms Qtsl.Structural.nnfAtomLt_sound
#print axioms Qtsl.Structural.nnfAtomGt_sound
#print axioms Qtsl.Structural.nnfRewrite_regionSat
#print axioms Qtsl.Structural.nnfAtomLe_boundary
#print axioms Qtsl.Structural.nnfAtomGe_boundary
