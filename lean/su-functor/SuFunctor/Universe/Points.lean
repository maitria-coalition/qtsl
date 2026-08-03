import SuFunctor.Universe.CoupledJudgment

/-! # Systems are points, not citizens: two definability refutations

Two theorems bound what the coupled judgment can *define*, pinning the
sense in which systems are limit points of the spec logic rather than
objects it can name.

* **The bump lemma** (`exists_ne_model_of_proper`): every proper model
  of a spec atom with finitely many liveness demands has a companion
  model — distinct, still a citizen, still a model.  Hence no finite
  disjunction of atoms pins a single proper system
  (`singletons_not_definable`).

  The construction case-splits on where the system is finite.  If some
  point away from the (finitely many) dip witnesses carries finite
  penalty, a scaled-indicator **bump on a ball** there raises the
  system off itself while every dip survives at its untouched witness.
  Otherwise the system is `⊤` off a finite set, and a **raise at a
  single finite-penalty point** — strictly above the system, strictly
  below every liveness mark exceeding it there — stays lower
  semicontinuous because every punctured neighborhood is `⊤`
  (`lowerSemicontinuous_of_eq_top_off_finite`).  The ball-bump alone
  would not suffice: on a system that is `⊤` off its witnesses, adding
  a bump changes nothing.

  Both hypotheses are necessary.  Properness: under the reading that
  admits empty liveness slots, `Mod (⊤, ∅) = {⊤}` — the inconsistent
  system *is* pinned by the vacuous-safety atom.  Finiteness: the full
  liveness theory of a system pins it exactly (its directed family of
  finite approximants converges to it and never reaches it), so the
  theorem is false for infinite slots.

* **Upper opens are not spec classes**
  (`upper_open_not_definable`): the class `{σ | σ μ₀ ≠ 0}` — the trace
  on systems of the upper-Vietoris basic open `{K | μ₀ ∉ K}`, see
  `SuFunctor.Universe.VietorisStratum.toBel_mem_compile_iff` — is not
  the model class of any finite disjunction of atoms.  The constant
  systems `ε ↓ 0` all lie in the class, so some disjunct holds
  infinitely far down the chain; its safety floor is forced to `0` and
  its liveness demands are all dipped by the zero system — which the
  class excludes.  Spec classes cannot approach their infimum without
  containing it: safety is closed at every level of the tower.
-/

namespace SuFunctor.Universe

open scoped ENNReal

variable {V : Type*} [Fintype V]

/-- A penalty that is `⊤` off a finite set is a citizen, whatever its
finitely many finite values: every punctured neighborhood is `⊤`. -/
theorem lowerSemicontinuous_of_eq_top_off_finite {f : ProbPenalty V}
    {W : Finset (ProbState V)} (hW : ∀ μ ∉ W, f μ = ⊤) :
    LowerSemicontinuous f := by
  intro μ y hy
  have hcl : IsClosed ((W : Set (ProbState V)) \ {μ}) :=
    (W.finite_toSet.subset Set.sdiff_subset).isClosed
  have hμmem : μ ∈ ((W : Set (ProbState V)) \ {μ})ᶜ := by
    simp
  filter_upwards [hcl.isOpen_compl.mem_nhds hμmem] with ν hν
  rcases eq_or_ne ν μ with rfl | hne
  · exact hy
  · have hνW : ν ∉ W := fun hmem => hν ⟨hmem, by simpa using hne⟩
    rw [hW ν hνW]
    exact lt_of_lt_of_le hy le_top

/-- Finitely many liveness demands admit a common finite set of dip
witnesses. -/
theorem exists_finset_dip_witnesses {σ : ProbPenalty V}
    {𝒱 : Set (ProbPenalty V)} (h𝒱 : 𝒱.Finite)
    (hdip : ∀ v ∈ 𝒱, Dip σ v) :
    ∃ W : Finset (ProbState V), ∀ v ∈ 𝒱, ∃ μ ∈ W, σ μ < v μ := by
  classical
  have hdip' : ∀ v, v ∈ 𝒱 → ∃ μ, σ μ < v μ := hdip
  choose wit hwit using hdip'
  refine ⟨h𝒱.toFinset.attach.image fun p => wit p.1 (h𝒱.mem_toFinset.mp p.2),
    fun v hv => ?_⟩
  exact ⟨wit v hv,
    Finset.mem_image.mpr ⟨⟨v, h𝒱.mem_toFinset.mpr hv⟩, Finset.mem_attach _ _, rfl⟩,
    hwit v hv⟩

/-- **The bump lemma**: a proper model of an atom with finitely many
liveness demands is never the only model — some distinct citizen
models the same atom.  Ball-bump where a finite-penalty point exists
away from the witnesses; single-point raise (lsc by the
punctured-neighborhood-`⊤` argument) where the system is `⊤` off the
witness set. -/
theorem exists_ne_model_of_proper {σ u : ProbPenalty V}
    {𝒱 : Set (ProbPenalty V)} (hσ : LowerSemicontinuous σ)
    (hproper : ∃ μ, σ μ ≠ ⊤) (h𝒱 : 𝒱.Finite)
    (hsat : CoupledSat σ u 𝒱) :
    ∃ τ : ProbPenalty V, LowerSemicontinuous τ ∧ τ ≠ σ ∧ CoupledSat τ u 𝒱 := by
  classical
  obtain ⟨W, hW⟩ := exists_finset_dip_witnesses h𝒱 hsat.2
  by_cases hA : ∃ μs, μs ∉ W ∧ σ μs ≠ ⊤
  · -- ball-bump at a finite-penalty point away from the witnesses
    obtain ⟨μs, hμsW, hμstop⟩ := hA
    obtain ⟨r, hr0, hrW⟩ : ∃ r > 0, ∀ w ∈ W, w ∉ Metric.ball μs r := by
      by_cases hWne : W.Nonempty
      · refine ⟨W.inf' hWne fun w => dist μs w, ?_, fun w hw => ?_⟩
        · rw [gt_iff_lt, Finset.lt_inf'_iff]
          exact fun w hw => dist_pos.mpr fun he => hμsW (he ▸ hw)
        · rw [Metric.mem_ball, dist_comm]
          exact not_lt.mpr (Finset.inf'_le _ hw)
      · exact ⟨1, one_pos, fun w hw => absurd ⟨w, hw⟩ hWne⟩
    refine ⟨σ + scaledIndicator 1 (Metric.ball μs r),
      hσ.add (lowerSemicontinuous_scaledIndicator Metric.isOpen_ball),
      ?_, hsat.1.trans fun μ => le_self_add, fun v hv => ?_⟩
    · intro he
      have h1 : σ μs + scaledIndicator 1 (Metric.ball μs r) μs = σ μs := by
        conv_rhs => rw [← congrFun he μs]
        rfl
      rw [scaledIndicator_apply_of_mem (Metric.mem_ball_self hr0)] at h1
      exact absurd (h1 ▸ ENNReal.lt_add_right hμstop one_ne_zero) (lt_irrefl _)
    · obtain ⟨μw, hμwW, hμwlt⟩ := hW v hv
      refine ⟨μw, ?_⟩
      rw [Pi.add_apply, scaledIndicator_apply_of_not_mem (hrW μw hμwW), add_zero]
      exact hμwlt
  · -- the system is `⊤` off the witness set: raise at a proper point
    push Not at hA
    obtain ⟨μ₀, hμ₀⟩ := hproper
    have hμ₀W : μ₀ ∈ W := by
      by_contra h
      exact hμ₀ (hA μ₀ h)
    set F : Finset (ProbPenalty V) := h𝒱.toFinset.filter (fun v => σ μ₀ < v μ₀)
      with hF
    obtain ⟨rr, hr1, hr2⟩ : ∃ rr, σ μ₀ < rr ∧ ∀ v ∈ F, rr < v μ₀ := by
      by_cases hFne : F.Nonempty
      · obtain ⟨v₀, hv₀F, hv₀min⟩ := F.exists_min_image (fun v => v μ₀) hFne
        obtain ⟨rr, hrr1, hrr2⟩ :=
          exists_between ((Finset.mem_filter.mp hv₀F).2 : σ μ₀ < v₀ μ₀)
        exact ⟨rr, hrr1, fun v hv => lt_of_lt_of_le hrr2 (hv₀min v hv)⟩
      · exact ⟨σ μ₀ + 1, ENNReal.lt_add_right hμ₀ one_ne_zero,
          fun v hv => absurd ⟨v, hv⟩ hFne⟩
    have hupd_self : Function.update σ μ₀ rr μ₀ = rr := Function.update_self _ _ _
    have hupd_ne : ∀ μ, μ ≠ μ₀ → Function.update σ μ₀ rr μ = σ μ :=
      fun μ h => Function.update_of_ne h _ _
    refine ⟨Function.update σ μ₀ rr,
      lowerSemicontinuous_of_eq_top_off_finite (W := W) fun μ hμ => ?_,
      ?_, ?_, fun v hv => ?_⟩
    · rw [hupd_ne μ fun he => hμ (he ▸ hμ₀W)]
      exact hA μ hμ
    · intro he
      have : σ μ₀ = rr := by
        conv_lhs => rw [← he]
        exact hupd_self
      exact absurd (this ▸ hr1) (lt_irrefl _)
    · refine hsat.1.trans fun μ => ?_
      rcases eq_or_ne μ μ₀ with rfl | h
      · rw [hupd_self]
        exact hr1.le
      · rw [hupd_ne μ h]
    · obtain ⟨μw, hμwW, hμwlt⟩ := hW v hv
      rcases eq_or_ne μw μ₀ with rfl | h
      · have hvF : v ∈ F :=
          Finset.mem_filter.mpr ⟨h𝒱.mem_toFinset.mpr hv, hμwlt⟩
        exact ⟨μw, by rw [hupd_self]; exact hr2 v hvF⟩
      · exact ⟨μw, by rw [hupd_ne μw h]; exact hμwlt⟩

/-- **No finite disjunction of atoms pins a proper system**: the model
class of a finite coupled DNF (over citizens) is never the singleton
of a proper citizen. -/
theorem singletons_not_definable {σ : ProbPenalty V}
    (hσ : LowerSemicontinuous σ) (hproper : ∃ μ, σ μ ≠ ⊤)
    {n : ℕ} (u : Fin n → ProbPenalty V) (𝒱 : Fin n → Set (ProbPenalty V))
    (hfin : ∀ i, (𝒱 i).Finite) :
    ¬ ∀ τ : ProbPenalty V, LowerSemicontinuous τ →
        ((∃ i, CoupledSat τ (u i) (𝒱 i)) ↔ τ = σ) := by
  intro hiff
  obtain ⟨i₀, hi₀⟩ := (hiff σ hσ).mpr rfl
  obtain ⟨τ, hτlsc, hτne, hτsat⟩ :=
    exists_ne_model_of_proper hσ hproper (hfin i₀) hi₀
  exact hτne ((hiff τ hτlsc).mp ⟨i₀, hτsat⟩)

/-- **Upper opens are not spec classes.**  For any point `μ₀` of the
flat carrier, the class `{σ | σ μ₀ ≠ 0}` is not the model class of any
finite disjunction of atoms, over any class of systems containing the
constants: the constants `ε ↓ 0` pin some disjunct's safety floor to
`0` while its liveness demands are dipped by the zero system, which
the class excludes.  (Set-side this class is the trace of the
upper-Vietoris basic open `{K | μ₀ ∉ K}` on bodies — so the closed
miss-face of the crescent presentation is forced, not stylistic.) -/
theorem upper_open_not_definable {P : ProbPenalty V → Prop}
    (hP : ∀ c : ℝ≥0∞, P fun _ => c) (μ₀ : ProbState V) :
    ¬ ∃ (n : ℕ) (u : Fin n → ProbPenalty V) (𝒱 : Fin n → Set (ProbPenalty V)),
        ∀ σ, P σ → ((∃ i, CoupledSat σ (u i) (𝒱 i)) ↔ σ μ₀ ≠ 0) := by
  rintro ⟨n, u, 𝒱, hiff⟩
  classical
  have hmem : ∀ k : ℕ,
      ∃ i, CoupledSat (fun _ => ((k : ℝ≥0∞) + 1)⁻¹) (u i) (𝒱 i) := by
    intro k
    refine (hiff _ (hP _)).mpr ?_
    exact ENNReal.inv_ne_zero.mpr (by simp)
  choose g hg using hmem
  obtain ⟨i₀, hfib⟩ := Finite.exists_infinite_fiber g
  have hgi : ∀ k ∈ g ⁻¹' {i₀},
      CoupledSat (fun _ => ((k : ℝ≥0∞) + 1)⁻¹) (u i₀) (𝒱 i₀) := by
    intro k hk
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hk
    exact hk ▸ hg k
  -- the safety floor of the recurring disjunct vanishes
  have hu0 : ∀ μ, u i₀ μ = 0 := by
    intro μ
    by_contra h0
    obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt h0
    obtain ⟨k, hkfib, hk⟩ := (Set.infinite_coe_iff.mp hfib).exists_gt m
    have hle : u i₀ μ ≤ ((k : ℝ≥0∞) + 1)⁻¹ := (hgi k hkfib).1 μ
    have hmono : ((k : ℝ≥0∞) + 1)⁻¹ ≤ ((m : ℝ≥0∞))⁻¹ :=
      ENNReal.inv_le_inv.mpr ((Nat.cast_le.mpr hk.le).trans le_self_add)
    exact absurd (hm.trans_le (hle.trans hmono)) (lt_irrefl _)
  -- the zero system models the recurring disjunct
  obtain ⟨k₀, hk₀⟩ := (Set.infinite_coe_iff.mp hfib).nonempty
  have hzero : CoupledSat (0 : ProbPenalty V) (u i₀) (𝒱 i₀) := by
    refine ⟨(funext hu0 : u i₀ = 0).le, fun v hv => ?_⟩
    obtain ⟨μ, hμ⟩ := (hgi k₀ hk₀).2 v hv
    exact ⟨μ, lt_of_le_of_lt zero_le hμ⟩
  exact (hiff 0 (hP 0)).mp ⟨i₀, hzero⟩ rfl

/-- The refutation instantiated at the universe's citizens. -/
theorem upper_open_not_definable_lsc (μ₀ : ProbState V) :
    ¬ ∃ (n : ℕ) (u : Fin n → ProbPenalty V) (𝒱 : Fin n → Set (ProbPenalty V)),
        ∀ σ, LowerSemicontinuous σ →
          ((∃ i, CoupledSat σ (u i) (𝒱 i)) ↔ σ μ₀ ≠ 0) :=
  upper_open_not_definable (fun _ => lowerSemicontinuous_const) μ₀

end SuFunctor.Universe
