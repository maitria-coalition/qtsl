import SuFunctor.Universe.CredalPoset.Witnesses

/-! # Adjudicating the Richardson conjecture

The conjecture, due to David "davidad" Dalrymple: convexity of the
penalty
functional should be *sufficient* for convexity of the compiled body,
but perhaps **not necessary** — and perhaps **not even sufficient for
topological closedness**, since "boundary points need not be
lower-semicontinuous."  The trio:

* **A1 (sufficiency for convexity)** — `PenaltyConvex f →
  ConvexBody (compile f)`, all `V`: the inclusions leg's theorem (T2's
  engine); *not* proved in this file.
* **A2 (non-necessity)** — `exists_convexCredalBody_not_richardson`:
  the harmonic body `{x | x₀ + 2x₁ ≤ 1}` is a convex credal body
  (indeed ultra, HL, and MVS) compiled by **no** convex penalty.  The
  refutation is exp-free grade arithmetic
  (`not_isRichardsonBody_harmonicBody` in `Witnesses`): the body pins
  the grades `1, ½, ⅔` on `δa′, δb′, mid′`, and penalty convexity
  would square `⅔` past `½`, i.e. `½ ≤ 4/9`.  Richardson's class is
  **strictly stronger** than the convex class.
* **A3 (insufficiency for closedness — verdict: CONFIRMED)** —
  `exists_penaltyConvex_not_closed`: the boundary-jump penalty `f₇`
  (`log 2` on the face `μ₀ = 0`, else `0`) is convex yet its compile
  is not closed; by `isClosed_compile_iff` this is exactly its failure
  of lower semicontinuity, located at the simplex boundary — the
  conjecture's parenthetical is the mechanism.  Sharpening
  (`f₇_two_valued`/`f₇_ne_top`): `f₇` is bounded and finite-valued, so
  even *bounded* convex penalties fail closedness.  Corollary
  (`exists_penaltyConvex_compile_not_credalBody`): a Richardson-convex
  penalty whose body escapes the class CB altogether.

The A3 witness also settles the definitional question for the
Richardson node itself.  `IsRichardsonBody` reads the programme's
codomain as penalties both convex *and* lsc (see the provenance note on
the definition); the literal convexity-only reading would name a
strictly larger class of bodies, and `f₇` is the separating witness:
`exists_penaltyConvex_compile_not_richardson` — the compile of a convex
penalty that is no Richardson body, so the lsc conjunct is load-bearing
in the definition, not implied by convexity.

The trio's expected verdicts were preregistered before the proofs
were built.
-/

namespace SuFunctor.Universe

open scoped ENNReal

namespace CredalPoset

/-! ## A2: penalty convexity is not necessary for body convexity -/

/-- **A2 (non-necessity).**  A convex credal body that is not a
Richardson body: no convex penalty functional compiles to the harmonic
body, although it is ultra (hence closed, convex, radial), HL, and
MVS.  Penalty convexity is a strictly stronger condition than body
convexity. -/
theorem exists_convexCredalBody_not_richardson :
    ∃ S : Set (BelState (Fin 2)),
      IsConvexCredalBody S ∧ ¬ IsRichardsonBody S :=
  ⟨harmonicBody, isUltra_harmonicBody.isConvexCredalBody,
    not_isRichardsonBody_harmonicBody⟩

/-! ## A3: penalty convexity does not force a closed body -/

open Classical in
/-- The boundary-jump penalty: `log 2` on the simplex face `μ₀ = 0`
(a single point of the `Fin 2` simplex — the `b`-dirac), and `0` on
the interior-side complement.  Convex (the face is an extreme set:
a strict mixture lands on the face only if both endpoints do), yet
not lower semicontinuous — the penalty *jumps up* at the boundary
point, so its grade jumps down and the compiled body loses the limit
of its ray tips. -/
noncomputable def f₇ : ProbPenalty (Fin 2) :=
  fun μ => if (μ : Fin 2 → ℝ) 0 = 0 then ENNReal.ofReal (Real.log 2)
    else 0

theorem f₇_apply_of_eq {μ : ProbState (Fin 2)}
    (h : (μ : Fin 2 → ℝ) 0 = 0) :
    f₇ μ = ENNReal.ofReal (Real.log 2) := if_pos h

theorem f₇_apply_of_ne {μ : ProbState (Fin 2)}
    (h : (μ : Fin 2 → ℝ) 0 ≠ 0) : f₇ μ = 0 := if_neg h

/-- **A3, part (i): `f₇` is penalty-convex.**  On a strict mixture the
zeroth coordinate is a positively-weighted sum of nonnegatives, so it
vanishes iff both endpoints' do — the jump face is extreme. -/
theorem penaltyConvex_f₇ : PenaltyConvex f₇ := by
  intro μ ν s t hs ht hst
  by_cases hm : ((ProbState.mix s t hs.le ht.le hst μ ν
      : ProbState (Fin 2)) : Fin 2 → ℝ) 0 = 0
  · rw [ProbState.coe_mix] at hm
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hm
    have h₁ : 0 ≤ s * (μ : Fin 2 → ℝ) 0 :=
      mul_nonneg hs.le (μ.nonneg 0)
    have h₂ : 0 ≤ t * (ν : Fin 2 → ℝ) 0 :=
      mul_nonneg ht.le (ν.nonneg 0)
    have hμ0 : (μ : Fin 2 → ℝ) 0 = 0 := by
      have hs0 : s * (μ : Fin 2 → ℝ) 0 = 0 := by linarith
      rcases mul_eq_zero.mp hs0 with h | h
      · exact absurd h hs.ne'
      · exact h
    have hν0 : (ν : Fin 2 → ℝ) 0 = 0 := by
      have ht0 : t * (ν : Fin 2 → ℝ) 0 = 0 := by linarith
      rcases mul_eq_zero.mp ht0 with h | h
      · exact absurd h ht.ne'
      · exact h
    have hm' : ((ProbState.mix s t hs.le ht.le hst μ ν
        : ProbState (Fin 2)) : Fin 2 → ℝ) 0 = 0 := by
      rw [ProbState.coe_mix]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hμ0, hν0]
      ring
    rw [f₇_apply_of_eq hm', f₇_apply_of_eq hμ0, f₇_apply_of_eq hν0]
    refine le_of_eq ?_
    rw [← add_mul, ← ENNReal.ofReal_add hs.le ht.le, hst,
      ENNReal.ofReal_one, one_mul]
  · rw [f₇_apply_of_ne hm]
    exact zero_le

/-- **A3, part (ii): `f₇` is not lower semicontinuous.**  At the
`b`-dirac the penalty is `log 2 > 0`, but states with an arbitrarily
small positive zeroth coordinate — where the penalty is `0` — sit in
every neighborhood. -/
theorem not_lowerSemicontinuous_f₇ : ¬ LowerSemicontinuous f₇ := by
  intro h
  have hb0 : ((δb' : ProbState (Fin 2)) : Fin 2 → ℝ) 0 = 0 := δb'_zero
  have hpos : (0 : ℝ≥0∞) < f₇ δb' := by
    rw [f₇_apply_of_eq hb0]
    exact ENNReal.ofReal_pos.mpr (Real.log_pos one_lt_two)
  have hev := h δb' 0 hpos
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hd0 : (0:ℝ) < min (ε / 2) 1 := lt_min (by linarith) one_pos
  have hd1 : min (ε / 2) 1 ≤ 1 := min_le_right _ _
  set ν : ProbState (Fin 2) := ProbState.ofPair (min (ε / 2) 1)
    (1 - min (ε / 2) 1) hd0.le (by linarith) (by ring) with hν
  have hf : f₇ ν = 0 := f₇_apply_of_ne (by
    show ((ν : ProbState (Fin 2)) : Fin 2 → ℝ) 0 ≠ 0
    rw [hν]
    exact ne_of_gt hd0)
  have hlt : min (ε / 2) 1 < ε :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hdist : dist ν δb' < ε := by
    rw [Subtype.dist_eq, dist_pi_lt_iff hε, Fin.forall_fin_two]
    constructor
    · rw [Real.dist_eq]
      show |min (ε / 2) 1 - 0| < ε
      rw [sub_zero, abs_of_pos hd0]
      exact hlt
    · rw [Real.dist_eq]
      show |1 - min (ε / 2) 1 - 1| < ε
      rw [show (1:ℝ) - min (ε / 2) 1 - 1 = -(min (ε / 2) 1) by ring,
        abs_neg, abs_of_pos hd0]
      exact hlt
  have hcontra : (0 : ℝ≥0∞) < f₇ ν := hball hdist
  rw [hf] at hcontra
  exact lt_irrefl 0 hcontra

/-- **A3, part (iii): the compile of `f₇` is not closed** — one line
through the dictionary `isClosed_compile_iff`: closedness of the body
is exactly lower semicontinuity of the penalty. -/
theorem not_isClosed_compile_f₇ : ¬ IsClosed (compile f₇) := fun h =>
  not_lowerSemicontinuous_f₇ (isClosed_compile_iff.mp h)

/-- **A3 headline (the conjectured "maybe not even sufficient for
closedness" — CONFIRMED).**  A penalty-convex functional whose
compiled body is not topologically closed.  The failure is at the
simplex boundary, exactly as the conjecture's parenthetical
("boundary points need not be lower-semicontinuous") predicted. -/
theorem exists_penaltyConvex_not_closed :
    ∃ f : ProbPenalty (Fin 2),
      PenaltyConvex f ∧ ¬ IsClosed (compile f) :=
  ⟨f₇, penaltyConvex_f₇, not_isClosed_compile_f₇⟩

/-- **A3 escapee corollary**: a Richardson-*convex* penalty (without
the lsc leg) whose body leaves the house class CB altogether —
convexity alone does not buy citizenship. -/
theorem exists_penaltyConvex_compile_not_credalBody :
    ∃ f : ProbPenalty (Fin 2),
      PenaltyConvex f ∧ ¬ IsCredalBody (compile f) :=
  ⟨f₇, penaltyConvex_f₇, fun h => not_isClosed_compile_f₇ h.2.1⟩

/-- **The lsc conjunct is not redundant, body-level**: the compile of
`f₇` is no Richardson body — no penalty that is both convex and lower
semicontinuous compiles to it, because every Richardson body is closed
and `compile f₇` is not.  Since every Richardson body is trivially the
compile of a convex penalty, this is the strictness of the
literal-convexity reading over the Richardson class at the level of
*bodies*, not merely of penalties. -/
theorem not_isRichardsonBody_compile_f₇ :
    ¬ IsRichardsonBody (compile f₇) := by
  rintro ⟨g, -, hlsc, hEq⟩
  exact not_isClosed_compile_f₇ (hEq ▸ isClosed_compile hlsc)

/-- **The re-pinned Richardson class is strictly inside the
convexity-only reading**: a convex penalty functional whose compile is
no Richardson body.  Convexity of the penalty does not imply that the
body it compiles is compiled by any convex *lsc* penalty. -/
theorem exists_penaltyConvex_compile_not_richardson :
    ∃ f : ProbPenalty (Fin 2),
      PenaltyConvex f ∧ ¬ IsRichardsonBody (compile f) :=
  ⟨f₇, penaltyConvex_f₇, not_isRichardsonBody_compile_f₇⟩

/-- **A3 sharpening**: `f₇` takes only the two values `0` and `log 2`
— it is bounded, so even *bounded* convex penalties fail closedness. -/
theorem f₇_two_valued (μ : ProbState (Fin 2)) :
    f₇ μ = 0 ∨ f₇ μ = ENNReal.ofReal (Real.log 2) := by
  by_cases h : (μ : Fin 2 → ℝ) 0 = 0
  · exact Or.inr (f₇_apply_of_eq h)
  · exact Or.inl (f₇_apply_of_ne h)

/-- `f₇` never takes the hard-violation value: the closedness failure
of A3 is not a `⊤`-artifact. -/
theorem f₇_ne_top (μ : ProbState (Fin 2)) : f₇ μ ≠ ⊤ := by
  rcases f₇_two_valued μ with h | h <;> rw [h]
  · exact ENNReal.zero_ne_top
  · exact ENNReal.ofReal_ne_top

end CredalPoset

end SuFunctor.Universe
