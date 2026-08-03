/-
RETIRED (archived).  This module belongs to the retired calculus-side
semantic tier, whose target is the thin double category of per-element
constraints on finitely supported subprobability mass functions
(`SuFunctor.Crd`).  That tier is superseded by the sheaf-fibred
construction: the locally closed Fell-hyperspace universe
(`SuFunctor.Universe`), the plain spec-class decoration functor
(`SuFunctor.Plain.SpecFunctor`), and the site-dimensional functor
(`SuFunctor.Site.SiteFunctor`).

This module: the polarity regression pins and the three-outcome reach-
avoid exhibit, over `SubPMF`.

New results must not import this module.  A result still needed
against the current semantics should be restated over the successor
carrier rather than proven here.
-/
import SuFunctorLegacy.Threshold
import SuFunctor.Adequacy.Inclusions
import Mathlib.Tactic.FinCases

/-! # Threshold polarity: regression pins and the three-outcome exhibit

Two batteries of build-checked facts, guarding the polarity table of
`SuFunctorLegacy.Threshold`.

**The pins.**  A satisfaction-form (lower-bound) reading of a
safety-shaped threshold conclusion is unsound over subprobability
mass, and the countermodel is minimal: one state, half the mass, and a
certificate with nothing left to certify.  On the carrier `Unit`, the
model `cmHalf` puts mass `1/2` on the sole state and loses the rest.
Take the safety claim "with probability at least `3/4`, always safe",
where the avoid event is *empty* — nothing bad can ever happen, and
the vacuous certificate is impeccable.  The violation half-space form
holds with room to spare (`cm1_violation_holds`); the satisfaction
form fails (`cm1_satisfaction_fails`); consequently no per-element
square can conclude the satisfaction form from the risk row
(`cm1_no_satisfaction_square`).  The satisfaction-form battery family
(`safetyBatteryFamily`) remains sound because its full-mass premise
excludes the countermodel (`cm1_fails_mass_premise`) — the total-mass
reading; the polarity-form family (`safetyBatteryWallFamily`) speaks
about the countermodel and speaks truly.  On the full-mass slice the
two readings coincide (`wall_polarity_slice`), which is why the fork
is invisible from the total-mass world.  The tilt reading charges the
lost mass finitely (`cm1_shortfall`) instead of refusing, with the
refusal recovered at `λ = ∞` (`livenessTilt_top`).

**The exhibit.**  The standard three-outcome reach–avoid scene:
carrier `Fin 3`, outcome `0` = the goal is reached, `1` = the safety
violation, `2` = inert (the run neither reaches nor violates).
Specification: safety wall `μ({1}) ≤ 1/4` in maximum with liveness
tilt `λ · (3/4 ∸ μ({0}))` — `reachAvoid` with budget `1/4` and
threshold `3/4`.  The worked models:

* `triRun = (7/10, 1/10, 1/5)`: passes the wall and pays a `λ/20`
  shortfall at every finite `λ` (`triRun_reachAvoid`,
  `triRun_shortfall`) — and *fails the hard wall* at threshold `3/4`
  (`triRun_livenessWall`): a finite tilt penalty is not a wall
  certificate, which is why hard liveness thresholds remain a separate
  (`λ = ∞`) member of the family; over this model the finite-`λ`
  composite penalties are cofinal, with the `λ = ∞` refusal as their
  least upper bound (`triRun_isLUB`).
* `triInert` (all mass inert): free behind the safety wall
  (`triInert_wall` — inertness violates nothing), fully charged by the
  liveness side (`triInert_shortfall`) — the polarity asymmetry in its
  purest form.
* `triBad = (7/10, 3/10, 0)`: refused by the wall at every `λ`
  (`triBad_reachAvoid`) — safety is not negotiable against reach
  mass.
-/

namespace SuFunctor

open Qtsl.Imprecise
open scoped NNRat

/-! ## The pins: the half-mass countermodel -/

/-- The half-mass model on one state: the minimal partiality
countermodel. -/
noncomputable def cmHalf : SubPMF Unit where
  wt := Finsupp.single () (1/2)
  nonneg := fun v => by
    rcases v
    rw [Finsupp.single_eq_same]
    norm_num
  mass_le_one := by
    rw [Finsupp.support_single_ne_zero _ (by norm_num : (1/2 : ℚ) ≠ 0)]
    rw [Finset.sum_singleton, Finsupp.single_eq_same]
    norm_num

theorem cmHalf_prob_univ : cmHalf.prob Set.univ = 1/2 := by
  classical
  unfold SubPMF.prob
  rw [show cmHalf.wt = Finsupp.single () (1/2) from rfl]
  rw [Finsupp.support_single_ne_zero _ (by norm_num : (1/2 : ℚ) ≠ 0)]
  rw [Finset.sum_singleton]
  simp

/-- Pin, positive half: the violation form holds on the half-mass
model, verbatim from the (vacuous) certificate — the avoid event is
empty. -/
theorem cm1_violation_holds : safetyWall (∅ : Set Unit) (1/4) cmHalf = 0 :=
  safetyWall_of_le (by rw [SubPMF.prob_empty]; norm_num)

/-- Pin, negative half: the satisfaction form fails on the same model.
The mass floor `3/4` is not met by a model that keeps only half its
mass — even though nothing bad ever happens. -/
theorem cm1_satisfaction_fails :
    livenessWall (Set.univ : Set Unit) (3/4) cmHalf = ⊤ :=
  livenessWall_of_not_le (by rw [cmHalf_prob_univ]; norm_num)

/-- The fence itself: no per-element square concludes a
satisfaction-form threshold from the risk row alone.  This is the
statement a satisfaction-form denotation of safety conclusions would
owe; `cmHalf` refutes it. -/
theorem cm1_no_satisfaction_square :
    ¬ ∀ μ : SubPMF Unit,
        μ.prob (∅ : Set Unit) ≤ 1/4 → (3/4 : ℚ) ≤ μ.prob Set.univ := by
  intro h
  have h2 := h cmHalf (by rw [SubPMF.prob_empty]; norm_num)
  rw [cmHalf_prob_univ] at h2
  norm_num at h2

/-- Why the satisfaction-form battery family is sound anyway: the
countermodel fails its full-mass premise.  The total-mass reading
holds exactly on the slice; the polarity reading holds everywhere. -/
theorem cm1_fails_mass_premise : ¬ ((1 : ℚ) ≤ cmHalf.prob Set.univ) := by
  rw [cmHalf_prob_univ]
  norm_num

/-- The tilt reading of the countermodel: the lost mass is charged as
a shortfall of `1/4` — finitely, at every finite `λ` — rather than
refused; the `λ = ∞` member recovers the refusal
(`cm1_satisfaction_fails` via `livenessTilt_top`). -/
theorem cm1_shortfall :
    (shortfall (Set.univ : Set Unit) (3/4) cmHalf : ℚ) = 1/4 := by
  rw [shortfall_coe, cmHalf_prob_univ]
  norm_num

/-! ## The exhibit: the three-outcome reach–avoid scene -/

/-- The goal event: outcome `0`. -/
def reachEvt : Set (Fin 3) := {0}

/-- The violation event: outcome `1`. -/
def avoidEvt : Set (Fin 3) := {1}

/-- The run: `7/10` reach, `1/10` violation, `1/5` inert. -/
noncomputable def triRun : SubPMF (Fin 3) where
  wt := Finsupp.single 0 (7/10) + Finsupp.single 1 (1/10) +
    Finsupp.single 2 (1/5)
  nonneg := fun v => by
    fin_cases v <;> simp [Finsupp.add_apply] <;> norm_num
  mass_le_one := by
    classical
    rw [Finset.sum_subset (Finset.subset_univ _)
      (fun _ _ hv => Finsupp.notMem_support_iff.mp hv)]
    rw [Fin.sum_univ_three]
    simp [Finsupp.add_apply]
    norm_num

/-- The inert model: all mass on the outcome that neither reaches nor
violates. -/
noncomputable def triInert : SubPMF (Fin 3) := SubPMF.dirac 2

/-- The violating model: `7/10` reach, `3/10` violation. -/
noncomputable def triBad : SubPMF (Fin 3) where
  wt := Finsupp.single 0 (7/10) + Finsupp.single 1 (3/10)
  nonneg := fun v => by
    fin_cases v <;> simp [Finsupp.add_apply] <;> norm_num
  mass_le_one := by
    classical
    rw [Finset.sum_subset (Finset.subset_univ _)
      (fun _ _ hv => Finsupp.notMem_support_iff.mp hv)]
    rw [Fin.sum_univ_three]
    simp [Finsupp.add_apply]
    norm_num

theorem triRun_prob_avoid : triRun.prob avoidEvt = 1/10 := by
  show triRun.prob {(1 : Fin 3)} = 1/10
  rw [SubPMF.prob_singleton]
  simp [triRun, Finsupp.add_apply]

theorem triRun_prob_reach : triRun.prob reachEvt = 7/10 := by
  show triRun.prob {(0 : Fin 3)} = 7/10
  rw [SubPMF.prob_singleton]
  simp [triRun, Finsupp.add_apply]

theorem triBad_prob_avoid : triBad.prob avoidEvt = 3/10 := by
  show triBad.prob {(1 : Fin 3)} = 3/10
  rw [SubPMF.prob_singleton]
  simp [triBad, Finsupp.add_apply]

/-- The run passes the safety wall: violation mass `1/10 ≤ 1/4`. -/
theorem triRun_wall : safetyWall avoidEvt (1/4) triRun = 0 :=
  safetyWall_of_le (by rw [triRun_prob_avoid]; norm_num)

/-- The run's liveness shortfall: `3/4 − 7/10 = 1/20`. -/
theorem triRun_shortfall :
    (shortfall reachEvt (3/4) triRun : ℚ) = 1/20 := by
  rw [shortfall_coe, triRun_prob_reach]
  norm_num

/-- A finite tilt penalty is not a wall certificate: the same run that
pays `λ/20` at every finite `λ` fails the hard threshold `3/4`. -/
theorem triRun_livenessWall : livenessWall reachEvt (3/4) triRun = ⊤ :=
  livenessWall_of_not_le (by rw [triRun_prob_reach]; norm_num)

/-- Behind the wall, the composite is the tilt: the run's reach–avoid
penalty is its (finite) liveness shortfall charge at every `λ`. -/
theorem triRun_reachAvoid (lam : ENNRat) :
    reachAvoid avoidEvt reachEvt (1/4) (3/4) lam triRun =
      livenessTilt reachEvt (3/4) lam triRun := by
  rw [reachAvoid_apply, triRun_wall, max_eq_right zero_le]

/-- At every finite tilt weight the run is admitted at finite
penalty. -/
theorem triRun_reachAvoid_lt_top (c : ℚ≥0) :
    reachAvoid avoidEvt reachEvt (1/4) (3/4) (c : ENNRat) triRun < ⊤ := by
  rw [triRun_reachAvoid]
  exact livenessTilt_coe_lt_top reachEvt (3/4) c triRun

/-- At `λ = ∞` the composite refuses the run: the hard-wall member of
the family is genuinely stronger than every finite relaxation. -/
theorem triRun_reachAvoid_top :
    reachAvoid avoidEvt reachEvt (1/4) (3/4) ⊤ triRun = ⊤ := by
  rw [triRun_reachAvoid, livenessTilt_top, triRun_livenessWall]

/-- The steepening hinge at work: over the run that passes the wall
but misses the hard threshold, the finite-`λ` composite penalties are
cofinal in the extended order — their least upper bound is the
`λ = ∞` refusal. -/
theorem triRun_isLUB :
    IsLUB (Set.range fun c : ℚ≥0 =>
      reachAvoid avoidEvt reachEvt (1/4) (3/4) (c : ENNRat) triRun) ⊤ := by
  have h := isLUB_livenessTilt reachEvt (3/4) triRun
  rw [triRun_livenessWall] at h
  simpa only [triRun_reachAvoid] using h

/-- Inertness violates no safety: the inert model is free behind the
wall. -/
theorem triInert_wall : safetyWall avoidEvt (1/4) triInert = 0 :=
  safetyWall_of_le (by
    show (SubPMF.dirac (2 : Fin 3)).prob avoidEvt ≤ 1/4
    rw [SubPMF.dirac_prob_of_not_mem (by simp [avoidEvt])]
    norm_num)

/-- Inertness is fully charged by the liveness side: the inert model's
shortfall is the whole threshold. -/
theorem triInert_shortfall :
    (shortfall reachEvt (3/4) triInert : ℚ) = 3/4 := by
  rw [shortfall_coe]
  show max (3/4 - (SubPMF.dirac (2 : Fin 3)).prob reachEvt) 0 = 3/4
  rw [SubPMF.dirac_prob_of_not_mem (by simp [reachEvt])]
  norm_num

/-- The inert model fails the hard liveness wall — which is what a
hard liveness threshold means. -/
theorem triInert_livenessWall :
    livenessWall reachEvt (3/4) triInert = ⊤ :=
  livenessWall_of_not_le (by
    show ¬ (3/4 : ℚ) ≤ (SubPMF.dirac (2 : Fin 3)).prob reachEvt
    rw [SubPMF.dirac_prob_of_not_mem (by simp [reachEvt])]
    norm_num)

/-- The violating model is refused by the wall. -/
theorem triBad_wall : safetyWall avoidEvt (1/4) triBad = ⊤ :=
  safetyWall_of_not_le (by rw [triBad_prob_avoid]; norm_num)

/-- Safety is not negotiable: at every tilt weight — however the
liveness side is relaxed — the composite refuses the violating
model. -/
theorem triBad_reachAvoid (lam : ENNRat) :
    reachAvoid avoidEvt reachEvt (1/4) (3/4) lam triBad = ⊤ := by
  rw [reachAvoid_apply, triBad_wall]
  exact max_eq_left le_top

end SuFunctor
