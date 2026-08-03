import SuFunctor.Universe.ConvexChart

/-! # Exact witnesses: what the chart cannot see

Two machine-checked exhibits pinning the gap between the universe and
its convex chart, each with the strongest form of its claim:

* **The independence witness** (`Bool × Bool`): the set of
  distributions making two booleans independent is the Segre variety
  `μ₁₁ μ₀₀ = μ₁₀ μ₀₁`.  Every point mass is a product law and the zero
  state is degenerate-independent, so the variety contains the Dirac
  skeleton — and therefore its biconjugate is the *zero penalty*
  (`biconj_wall_indSet`): convexification of an independence assertion
  retains no content whatsoever.  Not "some information is lost": all
  of it.  The even mixture of two independent point masses is perfectly
  correlated (`mixDiag_not_mem_indSet`), which also exhibits the wall
  as non-convex (`not_convexPenalty_wall_indSet`) — a citizen of the
  universe outside the chart.

* **The wall-coproduct witness** (`Bool`): disjunction of two point
  commitments.  In the universe the coproduct of walls is the union
  wall, exactly (`wall_inf_wall`, instantiated here); in the chart the
  same disjunction is seen through its biconjugate, which grants the
  hedged midpoint penalty `0` while the honest disjunction assigns it
  `⊤` (`modePair_chart_gap`).  Two convex walls whose exact coproduct
  exits the chart (`modePair_inf_not_convex`): mode-purity is
  expressible in the universe and invisible to the chart.

Both witnesses are exact rational computations on two- and
four-outcome carriers. -/

namespace SuFunctor.Universe

open scoped ENNReal

/-! ## The independence witness -/

/-- The independence variety: distributions on `Bool × Bool` under
which the two coordinates are independent (zero covariance;
determinant of the 2×2 mass table vanishes).  For full-mass states
this is exactly stochastic independence of the two projections; the
zero state and all subprobability scalings of point masses are
degenerate members. -/
def indSet : Set (BelState (Bool × Bool)) :=
  {μ | (μ : Bool × Bool → ℝ) (true, true) * (μ : Bool × Bool → ℝ) (false, false)
      = (μ : Bool × Bool → ℝ) (true, false) * (μ : Bool × Bool → ℝ) (false, true)}

theorem isClosed_indSet : IsClosed indSet := by
  have hc : ∀ w : Bool × Bool,
      Continuous fun μ : BelState (Bool × Bool) => (μ : Bool × Bool → ℝ) w :=
    fun w => (continuous_apply w).comp continuous_subtype_val
  exact isClosed_eq ((hc _).mul (hc _)) ((hc _).mul (hc _))

/-- The independence wall is a citizen of the universe. -/
theorem lowerSemicontinuous_wall_indSet :
    LowerSemicontinuous (wall indSet) :=
  lowerSemicontinuous_wall_iff.mpr isClosed_indSet

/-- Every point mass is a product law. -/
theorem dirac_mem_indSet (v : Bool × Bool) : BelState.dirac v ∈ indSet := by
  rcases v with ⟨b₁, b₂⟩
  rcases b₁ <;> rcases b₂ <;>
    simp [indSet, BelState.dirac]

/-- The zero state is (degenerately) independent. -/
theorem zero_mem_indSet : BelState.zero (Bool × Bool) ∈ indSet := by
  simp [indSet]

/-- The even mixture of the two perfectly-correlated point masses. -/
noncomputable def mixDiag : BelState (Bool × Bool) :=
  BelState.mix (1/2) (by norm_num) (by norm_num)
    (BelState.dirac (true, true)) (BelState.dirac (false, false))

/-- Mixing two independent laws destroys independence: the even
diagonal mixture is perfectly correlated. -/
theorem mixDiag_not_mem_indSet : mixDiag ∉ indSet := by
  intro h
  simp only [indSet, Set.mem_setOf_eq, mixDiag, BelState.mix_apply,
    BelState.dirac, Pi.single_apply] at h
  norm_num at h

/-- The independence wall is not convex: an epistemic assertion with no
chooser has no mixed-strategy reading, and mixing is the destruction of
the knowledge. -/
theorem not_convexPenalty_wall_indSet : ¬ ConvexPenalty (wall indSet) := by
  intro h
  have h2 := h (1/2) (by norm_num) (by norm_num)
    (BelState.dirac (true, true)) (BelState.dirac (false, false))
  rw [wall_apply_of_mem (dirac_mem_indSet _),
    wall_apply_of_mem (dirac_mem_indSet _)] at h2
  have h3 : wall indSet mixDiag = ⊤ :=
    wall_apply_of_not_mem mixDiag_not_mem_indSet
  rw [show BelState.mix (1/2) (by norm_num) (by norm_num)
      (BelState.dirac (true, true)) (BelState.dirac (false, false))
      = mixDiag from rfl, h3] at h2
  simp at h2

/-- **Total content loss under convexification, in general form.**  If
a wall's set contains the zero state and every point mass, its
biconjugate is the zero penalty: every affine minorant is bounded by
its values on the Dirac skeleton, which the affine-combination identity
propagates to the whole carrier. -/
theorem AffineGamble.eval_nonpos_of_isMinorant_wall {V : Type*} [Fintype V]
    [DecidableEq V] {C : Set (BelState V)}
    (hz : BelState.zero V ∈ C) (hd : ∀ v, BelState.dirac v ∈ C)
    {p : AffineGamble V} (hp : IsMinorant p (wall C)) (μ : BelState V) :
    p.eval μ ≤ 0 := by
  have hval : ∀ ν ∈ C, p.eval ν ≤ 0 := by
    intro ν hν
    have h := hp ν
    rw [wall_apply_of_mem hν] at h
    have h0 : p.evalPen ν = 0 := le_antisymm h zero_le
    exact ENNReal.ofReal_eq_zero.mp h0
  have hconst : p.const ≤ 0 := by
    have h := hval _ hz
    simpa [AffineGamble.eval] using h
  have hdir : ∀ v, p.eval (BelState.dirac v) ≤ 0 := fun v => hval _ (hd v)
  rw [p.eval_eq_sum_dirac]
  have h1 : ∑ v, (μ : V → ℝ) v * p.eval (BelState.dirac v) ≤ 0 :=
    Finset.sum_nonpos fun v _ =>
      mul_nonpos_iff.mpr (Or.inl ⟨μ.nonneg v, hdir v⟩)
  have h2 : (1 - μ.mass) * p.const ≤ 0 :=
    mul_nonpos_iff.mpr (Or.inl ⟨by linarith [μ.mass_le_one], hconst⟩)
  linarith

/-- A wall containing the Dirac skeleton has vacuous convex shadow. -/
theorem biconj_wall_eq_zero {V : Type*} [Fintype V] [DecidableEq V]
    {C : Set (BelState V)}
    (hz : BelState.zero V ∈ C) (hd : ∀ v, BelState.dirac v ∈ C) :
    biconj (wall C) = 0 := by
  refine le_antisymm ?_ (Pi.le_def.mpr fun _ => zero_le)
  intro μ
  refine iSup₂_le fun p hp => ?_
  rw [Pi.zero_apply, le_zero_iff]
  exact ENNReal.ofReal_eq_zero.mpr
    (AffineGamble.eval_nonpos_of_isMinorant_wall hz hd hp μ)

/-- **The independence witness, at full strength**: the convex chart's
shadow of the independence assertion is the vacuous penalty.  The
convex hull of the Segre variety is the entire carrier, so
convexification retains zero content. -/
theorem biconj_wall_indSet : biconj (wall indSet) = 0 :=
  biconj_wall_eq_zero zero_mem_indSet dirac_mem_indSet

/-! ## The wall-coproduct witness -/

/-- The two-mode commitment set: the system is (crisply) in mode
`true` or in mode `false` — point masses only, no hedging. -/
def modePair : Set (BelState Bool) :=
  {BelState.dirac true, BelState.dirac false}

/-- In the universe, the disjunction of the two mode walls is the union
wall, exactly. -/
theorem modePair_disj_exact :
    wall {BelState.dirac true} ⊓ wall {BelState.dirac false}
      = wall modePair := by
  rw [wall_inf_wall]
  rfl

/-- The hedged midpoint. -/
noncomputable def mixHalfBool : BelState Bool :=
  BelState.mix (1/2) (by norm_num) (by norm_num)
    (BelState.dirac true) (BelState.dirac false)

theorem mixHalfBool_not_mem : mixHalfBool ∉ modePair := by
  intro h
  rcases h with h | h
  · have h1 := congrArg (fun μ : BelState Bool => (μ : Bool → ℝ) true) h
    simp only [mixHalfBool, BelState.mix_apply, BelState.dirac,
      Pi.single_apply] at h1
    norm_num at h1
  · have h1 := congrArg (fun μ : BelState Bool => (μ : Bool → ℝ) true) h
    simp only [mixHalfBool, BelState.mix_apply, BelState.dirac,
      Pi.single_apply] at h1
    norm_num at h1

/-- Each mode wall is a chart citizen (singletons are convex)… -/
theorem convexPenalty_wall_singleton {V : Type*} [Fintype V]
    (μ₀ : BelState V) : ConvexPenalty (wall {μ₀}) := by
  rw [convexPenalty_wall_iff]
  intro t h0 h1 μ ν hμ hν
  rw [Set.mem_singleton_iff.mp hμ, Set.mem_singleton_iff.mp hν]
  rw [Set.mem_singleton_iff]
  exact BelState.mix_self h0 h1 μ₀

/-- …but their exact coproduct is not: pointwise minimum exits the
chart.  The disjunction of two chart citizens is a universe citizen
that no convex penalty can be. -/
theorem modePair_inf_not_convex :
    ¬ ConvexPenalty
      (wall {BelState.dirac true} ⊓ wall {BelState.dirac false}) := by
  rw [modePair_disj_exact]
  intro h
  have h2 := h (1/2) (by norm_num) (by norm_num)
    (BelState.dirac true) (BelState.dirac false)
  rw [wall_apply_of_mem
      (show BelState.dirac true ∈ modePair from Set.mem_insert _ _),
    wall_apply_of_mem
      (show BelState.dirac false ∈ modePair from
        Set.mem_insert_of_mem _ rfl)] at h2
  have h3 : wall modePair mixHalfBool = ⊤ :=
    wall_apply_of_not_mem mixHalfBool_not_mem
  rw [show BelState.mix (1/2) (by norm_num) (by norm_num)
      (BelState.dirac true) (BelState.dirac false) = mixHalfBool from rfl,
    h3] at h2
  simp at h2

/-- **The wall-coproduct witness**: at the hedged midpoint, the honest
disjunction charges `⊤` while its chart shadow charges `0`.  Exact
in the universe, hulled in the chart — the mode-purity content of a
disjunction is exactly what the biconjugate forgets. -/
theorem modePair_chart_gap :
    (wall {BelState.dirac true} ⊓ wall {BelState.dirac false}) mixHalfBool = ⊤
      ∧ biconj (wall {BelState.dirac true} ⊓ wall {BelState.dirac false})
          mixHalfBool = 0 := by
  constructor
  · rw [modePair_disj_exact]
    exact wall_apply_of_not_mem mixHalfBool_not_mem
  · rw [modePair_disj_exact]
    refine le_antisymm ?_ zero_le
    refine iSup₂_le fun p hp => ?_
    have ht : p.eval (BelState.dirac true) ≤ 0 := by
      have h := hp (BelState.dirac true)
      rw [wall_apply_of_mem
        (show BelState.dirac true ∈ modePair from Set.mem_insert _ _)] at h
      exact ENNReal.ofReal_eq_zero.mp (le_antisymm h zero_le)
    have hf : p.eval (BelState.dirac false) ≤ 0 := by
      have h := hp (BelState.dirac false)
      rw [wall_apply_of_mem
        (show BelState.dirac false ∈ modePair from
          Set.mem_insert_of_mem _ rfl)] at h
      exact ENNReal.ofReal_eq_zero.mp (le_antisymm h zero_le)
    have heval : p.eval mixHalfBool ≤ 0 := by
      rw [mixHalfBool, p.eval_mix]
      nlinarith
    rw [le_zero_iff]
    exact ENNReal.ofReal_eq_zero.mpr heval

end SuFunctor.Universe
