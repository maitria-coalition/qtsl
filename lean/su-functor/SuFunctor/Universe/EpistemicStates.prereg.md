# Preregistration — SuFunctor.Universe.EpistemicStates

Statement ledger committed BEFORE proving (prereg-lite). Mechanizes the SU
chapter Example on conditional beliefs, independence beliefs, and what
composition does not assume (finite stratum). Expected statements and mutant
loci below; the module beside this file discharges them.

Setting: finite `A × B`, `ProbState (A × B)` (SuFunctor.Universe carrier),
`klq` the total ℝ≥0∞ relative entropy of `SuFunctor.Universe.HausdorffKL`.
Notation: μ_X = fst-marginal, μ_Y = snd-marginal. Penalties are ℝ≥0∞-valued,
so `f ≥ 0` holds by type; the substantive content of "≥ 0 with equality iff"
lives in the zero-set characterizations (strict Gibbs).

## Family 1 — independence penalty `f(μ) = β · klq μ (μ_X ⊗ μ_Y)`

- L1.1 (marginal domination): `AbsCont μ (prodState μ_X μ_Y)` always — the
  independence penalty has no wall (finite everywhere).
- L1.2 (zero-set): `klq μ (prodState μ_X μ_Y) = 0 ↔ μ = prodState μ_X μ_Y`,
  and product laws are exactly the fixed points: `(∃ p q, μ = prodState p q)
  ↔ μ = prodState μ_X μ_Y` (marginals of a product law are its factors).
- L1.3 (continuity, outright at the finite stratum):
  `Continuous (fun μ => klq μ (prodState μ_X μ_Y))` — entropy decomposition
  into `Real.negMulLog` sums, then `ENNReal.ofReal` continuity.
- L1.4 (non-convexity, exact-ℚ witness): on `Fin 2 × Fin 2`, δ₍₀,₀₎ and
  δ₍₁,₁₎ are product laws; their equal mixture χ has uniform marginals and
  differs from χ_X ⊗ χ_Y at coordinate (0,1) (0 vs 1/4). Hence
  (a) the set of product laws is not convex;
  (b) the crisp independence body — the radial set over the product laws —
      is non-convex (mass-1 members of the radial set are product laws);
  (c) the independence penalty is not convex as a functional:
      f(χ) > 0 = ½·f(δ₀₀) + ½·f(δ₁₁).

## Family 2 — conditional penalty `f(μ) = β · klq μ (μ_Y ⋉ k)`, kernel k : B → ProbState A

- L2.1 (bind): `bindState μY k : ProbState (A × B)`, `(a,b) ↦ μY b · k b a`;
  its snd-marginal is μY.
- L2.2 (affinity, proved not assumed): `T : μ ↦ bindState μ_Y k` is affine:
  `T (mix t μ ν) = mix t (T μ) (T ν)` for `t ∈ [0,1]`.
- L2.3 (zero-set = disintegration agreement):
  `klq μ (T μ) = 0 ↔ ∀ b, 0 < μ_Y b → ∀ a, μ (a,b) = μ_Y b · k b a`
  (the y of μ_Y-mass zero are automatic, since μ(a,b) ≤ μ_Y b).
- L2.4 (joint convexity of klq, the engine): for `t ∈ [0,1]`,
  `klq (mix t μ ν) (mix t ρ σ) ≤ ofReal t * klq μ ρ + ofReal (1−t) * klq ν σ`
  — pointwise two-term log-sum inequality + mixture AbsCont bookkeeping;
  every ⊤ case included.
- L2.5 (convexity of the conditional penalty): L2.4 at pairs ((μ,Tμ),(ν,Tν))
  through L2.2.
- L2.6 (lsc at the finite stratum):
  `LowerSemicontinuous (fun p : ProbState V × ProbState V => klq p.1 p.2)`
  by per-term decomposition (each Gibbs-shifted term ≥ 0 and lsc; finite
  ℝ≥0∞ sums of lsc are lsc); corollary — the conditional penalty is lsc.
  The wall is real when k has zeros, so lsc, not continuity, is the honest
  statement for this family.

## Family 3 — composition non-assumption (the Fréchet-class claim)

- L3.1 (marginal-reading penalties): for `fX = g ∘ fstMarg`, `fY = h ∘ sndMarg`:
  `(fX + fY) μ = 0 ↔ g (fstMarg μ) = 0 ∧ h (sndMarg μ) = 0` — the composite
  zero-set is the "Fréchet class" of the two zero-sets: marginal constraints
  only, jointly.
- L3.2 (crisp body form, if the finite compile is cheaply reachable): the
  compile of `wall M_X ∘ fstMarg + wall M_Y ∘ sndMarg` is the radial set over
  `{μ | μ_X ∈ M_X ∧ μ_Y ∈ M_Y}`. Downgrades to zero-set-only (L3.1) if the
  compile plumbing is heavy; the chapter's claim already lives at the zero-set.
- L3.3 (the exact witness): χ = ½δ₀₀ + ½δ₁₁ has both marginals uniform, so χ
  lies in the composite body of the two singleton-uniform walls, while χ is
  not a product law and the independence penalty is strictly positive at χ:
  sums of marginal-reading penalties cannot manufacture a correlation
  constraint, and do not imply independence.

## Mutants (one per family, preregistered)

- M1: replace δ₁₁ by δ₀₀ in the L1.4 witness (equal mixture of a product law
  with itself IS a product law) → the non-convexity proof must go red.
- M2: drop the `0 < μ_Y b` guard in L2.3 (demand agreement at all y) → the
  iff must go red (a kernel may differ arbitrarily at a null y).
- M3: strengthen L3.1's zero-set conclusion to "μ is a product law" → must go
  red at χ.

## Post-proof addendum (results; original prereg text above unedited)

- All statements landed as preregistered, with one honest spec delta found
  DURING mutant analysis, before proving: the **joint-coordinate** zero-set
  form (`klq_condTarget_eq_zero_iff'`) needs *no* null-`y` guard — the
  reconstruction `μ_Y ⋉ k` charges null columns nothing, so the coordinate
  equation is automatic there and the guarded/unguarded coordinate forms are
  equivalent.  The guard is load-bearing only in the **disintegration-ratio**
  form (`klq_condTarget_eq_zero_iff`), where the conceived conditional at a
  null `y` is the junk value `0/0 = 0`.  M2 was therefore aimed at the ratio
  form (as the chapter's "at μ_Y-a.e. y" phrasing intends), not the
  coordinate form (where it would NOT go red).
- Mutant results (throwaway branch, never landed; base 54547a2e4):
  - M1 (chi = mix of δ₀₀ with itself): RED — barn job su-functor-34e55a381;
    `chi_apply_11` becomes a false statement, and both load-bearing
    junctions break (`le_antisymm` bridge in
    `not_penaltyConvex_indepPenalty`; midpoint identification in
    `not_convexBody_indepBody`).
  - M2 (guard dropped from the ratio form): RED — barn job
    su-functor-e083a10cd; fails exactly at the `μ_Y b ≠ 0` consumption
    (`mul_div_cancel_left₀`).
  - M3 (composite zero-set strengthened to imply `IsProductLaw`): RED —
    barn job su-functor-a93c0b55d; the mpr constructor cannot manufacture
    independence.  `Witness.frechet_does_not_imply_independence` is the
    in-file semantic refutation (χ).
- Green receipts: standalone module su-functor-54547a2e4 (16.7 s warm);
  full su-functor default target su-functor-54547a2e4-195806 (382.7 s,
  exit 0).  Zero sorries.
