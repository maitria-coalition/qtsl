import SuFunctor.Universe.ImageChar

/-! # Systems are ideal points: the singleton embedding is spec-shaped

A system's body is a *point* of the hyperspace, and the singleton
class of that point is closed there (the hyperspace of a metric
carrier is metric, so T1) — so a system embeds into the space of spec
classes as a closed singleton with no work.  This module proves the
sharper fact that makes the embedding *spec-shaped* rather than merely
topological (`eq_compile_of_subset_of_escapes`):

> among nonempty closed radial sets, the body of `σ` is pinned
> **exactly** by one miss-face demand (containment in `compile σ`)
> together with the escape demands of all citizens `σ` dips under.

Equivalently: `{compile σ}` is the intersection of the crescent
classes `(σ, {v})` over the dipped citizens `v` — a *directed
infinitary* crescent with a single miss-face.  Finitely many crescents
never suffice (`SuFunctor.Universe.Points.singletons_not_definable`,
the bump lemma), so the embedding lives precisely one level of
infinitude above judgment-definability: systems are the **ideal
points** of the spec lattice — principal filters, constructively
exhibited.  The proof runs on the image characterization: a strictly
smaller radial closed set is itself a compile (`compile_rayPenalty`),
and a scaled indicator on an open superlevel of its gauge penalty
separates it — a sector `σ` dips under but the smaller body cannot
escape. -/

namespace SuFunctor.Universe

open scoped ENNReal

variable {V : Type*} [Fintype V]

/-- **Systems are pinned by their spec-side shadow**: a nonempty
closed radial set inside the body of `σ` that escapes every citizen
`σ` dips under is the body of `σ` itself. -/
theorem eq_compile_of_subset_of_escapes [Nonempty V] {σ : ProbPenalty V}
    {K : Set (BelState V)} (hcl : IsClosed K) (hrad : IsRadial K)
    (hne : K.Nonempty) (hsub : K ⊆ compile σ)
    (hesc : ∀ v : ProbPenalty V, LowerSemicontinuous v → Dip σ v →
      ∃ x ∈ K, x ∉ compile v) :
    K = compile σ := by
  -- the smaller set is itself a compile, of its gauge penalty
  have hKτ : compile (rayPenalty K) = K := compile_rayPenalty hcl hrad hne
  have hτlsc : LowerSemicontinuous (rayPenalty K) := by
    have hcl' : IsClosed (compile (rayPenalty K)) := by
      rw [hKτ]
      exact hcl
    exact isClosed_compile_iff.mp hcl'
  -- containment reads as the pointwise order
  have hστ : σ ≤ rayPenalty K :=
    compile_subset_compile_iff.mp (by rw [hKτ]; exact hsub)
  -- if the orders differ somewhere, a sector separates
  by_contra hne'
  have hτσ : rayPenalty K ≠ σ := by
    intro he
    exact hne' (by rw [← hKτ, he])
  obtain ⟨μ₀, hμ₀⟩ := Function.ne_iff.mp hτσ
  have hlt : σ μ₀ < rayPenalty K μ₀ := lt_of_le_of_ne (hστ μ₀) (Ne.symm hμ₀)
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  -- the separating citizen: a plateau on an open superlevel of the gauge
  set v : ProbPenalty V := scaledIndicator c {μ | c < rayPenalty K μ} with hv
  have hvopen : IsOpen {μ : ProbState V | c < rayPenalty K μ} :=
    lowerSemicontinuous_iff_isOpen_preimage.mp hτlsc c
  have hvlsc : LowerSemicontinuous v :=
    lowerSemicontinuous_scaledIndicator hvopen
  have hvdip : Dip σ v :=
    ⟨μ₀, by rw [hv, scaledIndicator_apply_of_mem hc2]; exact hc1⟩
  -- but the smaller body cannot escape it: `v` sits below the gauge
  have hvτ : v ≤ rayPenalty K := by
    intro μ
    by_cases hμ : μ ∈ {μ : ProbState V | c < rayPenalty K μ}
    · rw [hv, scaledIndicator_apply_of_mem hμ]
      exact hμ.le
    · rw [hv, scaledIndicator_apply_of_not_mem hμ]
      exact zero_le
  obtain ⟨x, hxK, hxv⟩ := hesc v hvlsc hvdip
  exact hxv (compile_subset_compile_iff.mpr hvτ (by rw [hKτ]; exact hxK))
