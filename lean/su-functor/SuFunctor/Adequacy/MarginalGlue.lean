import SuFunctor.Adequacy.Envelope
import Mathlib.Data.Fintype.BigOperators

/-! # Marginal gluing over a cyclic cover: the Vorob'ev obstruction

Pairwise-consistent marginal data need not glue: Vorob'ev exhibited
consistent families of finite marginals with no joint law, and proved
that such families exist over exactly the *non-regular* (cyclic)
covers [N. N. Vorob'ev, *Consistent families of measures and their
extensions*, Theory of Probability and its Applications **7** (1962),
147–163, doi:10.1137/1107014].  This module mechanizes the minimal
instance over the subprobability stock, together with its absorption
into the credal stratum — the obstruction is *carried* by the
semantics (the inconsistent family denotes the bottom credal object),
never suffered as a crash.

The instance: three boolean sites in a ring, adjacent pairs observed
by three pair laws —

* `pairCorr` on the first–second and second–third edges: perfect
  correlation, `wt (b, b) = 1/2`;
* `pairIndep` on the first–third edge: independent-uniform,
  `wt ≡ 1/4`.

Every shared one-variable marginal is uniform (`pairCorr_fst`,
`pairCorr_snd`, `pairIndep_fst`, `pairIndep_snd`), so the family is
pairwise consistent; yet the two correlation edges force any joint to
concentrate on the diagonal, which the independent edge forbids.

Headlines:

* `vorobev_no_joint` — **no subprobability joint has all three pair
  laws as marginals**.  Stated over `SubPMF`, so it is strictly
  stronger than the classical probability-law statement: not even a
  mass-losing joint exists.
* `vorobev_record_glue` — the tier separation: the *possibilistic*
  glue is untroubled (exactly the two global records `(b, b, b)` are
  compatible with every pair law's support).  Records glue where laws
  do not.
* `chain_glues` / `corrRing_glues` — the controls: dropping either the
  third edge (`chain_glues`) or replacing its law by the correlated
  one (`corrRing_glues`) restores gluability, with the diagonal joint
  `diagJoint` the witness for both.  The obstruction is the frustrated
  cyclic assignment, not the cyclic shape.
* `credalCompile_vorobevGlue` — **the absorption**: the least lawful
  credal constraint above the family's conjunction (`credalCompile`,
  the constraint-stratum form of the credal-denotation conventions:
  contains the bottom model, closed under admitted downward scalings)
  is exactly the bottom credal object `rayC 0`, extension `{0}`.
  Inconsistent marginal specifications denote honest inconsistency.
* `satCredal_lower_vorobevGlue` / `vorobev_unsatisfiable` — the two
  readings of the bottom object, kept deliberately side by side.  The
  lower-kind credal verdict at the absorbed family is vacuously
  affirmative for *every* constraint (the bottom object's maximal
  slice is empty — the degenerate case the semantic-universe chapter
  records for lower previsions at bottom), while satisfaction as
  consistency is false: no model exists (`vorobev_unsatisfiable`), so
  under a satisfaction judgment carrying an existence presupposition
  the same family satisfies nothing.  The two statements answer
  different questions — prevision arithmetic at bottom versus
  existence of a model — and any consumer that reads the vacuous
  verdict as satisfaction would conclude that an inconsistent family
  meets the absurd specification (`satCredal_lower_vorobevGlue`
  instantiated at `fun _ => False` makes the hazard explicit).
* `satisfiable_not_local` — the spatial moral: satisfiability of
  marginal constraint families is not local-to-global on cyclic
  covers.  Every proper sub-family of the ring is satisfiable; the
  ring is not.
-/

namespace SuFunctor

open CategoryTheory PseudoDoubleCategoryStruct

universe u v

variable {V : Type u} {W : Type v}

/-! ## Pushforward of subprobability mass functions

The marginal of a joint along a projection is its pushforward: image
weights.  Mass is preserved on the nose (a finite sum reindexed), so
subprobability is preserved; nonnegativity is preserved because every
image weight is a finite sum of source weights.  This mirrors the
penalty stratum's pushforward of joints, at the exact-rational
stock. -/

namespace SubPMF

/-- Pushforward of a subprobability mass function along a carrier map:
image weights.  For a projection out of a product carrier this is the
marginal. -/
noncomputable def push (f : V → W) (μ : SubPMF V) : SubPMF W where
  wt := μ.wt.mapDomain f
  nonneg w := by
    classical
    rw [Finsupp.mapDomain, Finsupp.sum, Finset.sum_apply']
    refine Finset.sum_nonneg fun v _ => ?_
    rw [Finsupp.single_apply]
    by_cases h : f v = w
    · simpa [h] using μ.nonneg v
    · simp [h]
  mass_le_one := by
    classical
    show ((μ.wt.mapDomain f).sum fun _ q => q) ≤ 1
    rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
    exact μ.mass_le_one

@[simp] theorem push_wt (f : V → W) (μ : SubPMF V) :
    (μ.push f).wt = μ.wt.mapDomain f := rfl

/-- The image weight at a point is the sum of the source weights over
its fibre, presented over the support. -/
theorem push_wt_apply [DecidableEq W] (f : V → W) (μ : SubPMF V) (w : W) :
    (μ.push f).wt w = ∑ v ∈ μ.wt.support, if f v = w then μ.wt v else 0 := by
  classical
  rw [push_wt, Finsupp.mapDomain, Finsupp.sum, Finset.sum_apply']
  exact Finset.sum_congr rfl fun v _ => Finsupp.single_apply

/-- The image weight at a point, as a whole-carrier sum (finite
carriers): the form in which marginals are computed pointwise. -/
theorem push_wt_sum [Fintype V] [DecidableEq W] (f : V → W) (μ : SubPMF V)
    (w : W) :
    (μ.push f).wt w = ∑ v : V, if f v = w then μ.wt v else 0 := by
  classical
  rw [push_wt_apply]
  refine Finset.sum_subset (Finset.subset_univ _) fun v _ hv => ?_
  have h0 : μ.wt v = 0 := by
    by_contra h
    exact hv (Finsupp.mem_support_iff.mpr h)
  rw [h0, ite_self]

/-! ## Finite-carrier constructor -/

/-- On a finite carrier, the support-sum of a finitely supported
function is its whole-carrier sum. -/
theorem sum_support_eq_sum_univ [Fintype V] (g : V →₀ ℚ) :
    ∑ v ∈ g.support, g v = ∑ v : V, g v := by
  refine Finset.sum_subset (Finset.subset_univ _) fun v _ hv => ?_
  by_contra h
  exact hv (Finsupp.mem_support_iff.mpr h)

/-- Build a subprobability mass function on a finite carrier from an
explicit weight function with nonnegative values of total mass at most
one. -/
noncomputable def ofFun [Fintype V] (f : V → ℚ) (h0 : ∀ v, 0 ≤ f v)
    (h1 : ∑ v : V, f v ≤ 1) : SubPMF V where
  wt := Finsupp.equivFunOnFinite.symm f
  nonneg v := by
    rw [Finsupp.equivFunOnFinite_symm_apply_apply]
    exact h0 v
  mass_le_one := by
    rw [sum_support_eq_sum_univ]
    calc ∑ v : V, (Finsupp.equivFunOnFinite.symm f) v
        = ∑ v : V, f v :=
          Finset.sum_congr rfl fun v _ =>
            Finsupp.equivFunOnFinite_symm_apply_apply f v
      _ ≤ 1 := h1

@[simp] theorem ofFun_wt [Fintype V] (f : V → ℚ) (h0 : ∀ v, 0 ≤ f v)
    (h1 : ∑ v : V, f v ≤ 1) (v : V) :
    (ofFun f h0 h1).wt v = f v :=
  Finsupp.equivFunOnFinite_symm_apply_apply f v

end SubPMF

/-! ## The three-site ring

Projections of a three-site carrier onto its adjacent pairs.  The
intersection pattern of the three pair carriers is cyclic — each pair
of projections shares one coordinate — which is exactly the cover
shape over which Vorob'ev's obstruction lives. -/

variable {V₁ : Type u} {V₂ : Type u} {V₃ : Type u}

/-- First–second projection of a three-site carrier. -/
def proj12 : V₁ × V₂ × V₃ → V₁ × V₂ := fun v => (v.1, v.2.1)

/-- Second–third projection of a three-site carrier. -/
def proj23 : V₁ × V₂ × V₃ → V₂ × V₃ := fun v => v.2

/-- First–third projection of a three-site carrier. -/
def proj13 : V₁ × V₂ × V₃ → V₁ × V₃ := fun v => (v.1, v.2.2)

/-! ## The cell laws -/

/-- The uniform law on one boolean site. -/
noncomputable def bitUniform : SubPMF Bool :=
  .ofFun (fun _ => 1 / 2) (fun _ => by norm_num)
    (by rw [Fintype.sum_bool]; norm_num)

/-- Perfect correlation on a pair of boolean sites: mass `1/2` on each
diagonal point. -/
noncomputable def pairCorr : SubPMF (Bool × Bool) :=
  .ofFun (fun p => if p.1 = p.2 then 1 / 2 else 0)
    (fun p => by split <;> norm_num)
    (by norm_num [Fintype.sum_prod_type, Fintype.sum_bool])

/-- Independent-uniform on a pair of boolean sites: mass `1/4`
everywhere. -/
noncomputable def pairIndep : SubPMF (Bool × Bool) :=
  .ofFun (fun _ => 1 / 4) (fun _ => by norm_num)
    (by norm_num [Fintype.sum_prod_type, Fintype.sum_bool])

/-! ## Pairwise consistency

Every shared one-variable marginal of the three cell laws is the
uniform law: the family is consistent on all overlaps of its cover. -/

theorem pairCorr_fst : pairCorr.push Prod.fst = bitUniform := by
  refine SubPMF.ext' (Finsupp.ext fun b => ?_)
  rw [SubPMF.push_wt_sum, Fintype.sum_prod_type]
  cases b <;> simp [pairCorr, bitUniform]

theorem pairCorr_snd : pairCorr.push Prod.snd = bitUniform := by
  refine SubPMF.ext' (Finsupp.ext fun b => ?_)
  rw [SubPMF.push_wt_sum, Fintype.sum_prod_type]
  cases b <;> simp [pairCorr, bitUniform]

theorem pairIndep_fst : pairIndep.push Prod.fst = bitUniform := by
  refine SubPMF.ext' (Finsupp.ext fun b => ?_)
  rw [SubPMF.push_wt_sum, Fintype.sum_prod_type]
  cases b <;> simp [pairIndep, bitUniform] <;> norm_num

theorem pairIndep_snd : pairIndep.push Prod.snd = bitUniform := by
  refine SubPMF.ext' (Finsupp.ext fun b => ?_)
  rw [SubPMF.push_wt_sum, Fintype.sum_prod_type]
  cases b <;> simp [pairIndep, bitUniform] <;> norm_num

/-! ## The obstruction -/

/-- **Vorob'ev non-gluability, minimal instance.**  No subprobability
joint on the three-site carrier has the two correlated pair laws and
the independent pair law as its three adjacent-pair marginals — even
though the family is pairwise consistent on every overlap.

The proof is the classical two-step elimination: the two correlation
edges force the off-diagonal atoms to vanish (nonnegativity squeezed
against a zero marginal weight), after which the first–third marginal
at `(false, true)` reads `0`, contradicting the independent law's
`1/4`.

Stated over `SubPMF`, the statement is strictly stronger than its
classical probability-law form: no mass-one hypothesis appears, so not
even a mass-losing joint reproduces the family. -/
theorem vorobev_no_joint (μ : SubPMF (Bool × Bool × Bool)) :
    ¬ (μ.push proj12 = pairCorr ∧ μ.push proj23 = pairCorr ∧
        μ.push proj13 = pairIndep) := by
  rintro ⟨h12, h23, h13⟩
  have e12 : (μ.push proj12).wt (false, true) = 0 := by
    rw [h12]; simp [pairCorr]
  have e23 : (μ.push proj23).wt (false, true) = 0 := by
    rw [h23]; simp [pairCorr]
  have e13 : (μ.push proj13).wt (false, true) = 1 / 4 := by
    rw [h13]; simp [pairIndep]
  rw [SubPMF.push_wt_sum, Fintype.sum_prod_type] at e12 e23 e13
  simp [proj12, proj23, proj13, Fintype.sum_prod_type,
    Prod.mk.injEq] at e12 e23 e13
  -- e12: the (false, true, ·) atoms sum to zero;
  -- e23: the (·, false, true) atoms sum to zero;
  -- e13: the (false, ·, true) atoms sum to 1/4.
  have n1 := μ.nonneg (false, true, false)
  have n2 := μ.nonneg (false, true, true)
  have n3 := μ.nonneg (false, false, true)
  have n4 := μ.nonneg (true, false, true)
  linarith

/-! ## The tier separation: records glue -/

/-- The possibilistic tier is untroubled by the obstruction: exactly
the two global records `(b, b, b)` are compatible with the support of
every pair law.  Records glue over the cyclic cover on which laws do
not — the obstruction is measure-tier, not record-tier. -/
theorem vorobev_record_glue (v : Bool × Bool × Bool) :
    (0 < pairCorr.wt (proj12 v) ∧ 0 < pairCorr.wt (proj23 v) ∧
        0 < pairIndep.wt (proj13 v)) ↔
      v = (false, false, false) ∨ v = (true, true, true) := by
  obtain ⟨x, y, z⟩ := v
  cases x <;> cases y <;> cases z <;>
    simp [pairCorr, pairIndep, proj12, proj23, proj13]

/-! ## The controls: gluability returns off the frustrated ring -/

/-- The diagonal joint: mass `1/2` on each constant global record.
The witness for both controls. -/
noncomputable def diagJoint : SubPMF (Bool × Bool × Bool) :=
  .ofFun
    (fun v => if v = (false, false, false) then 1 / 2
      else if v = (true, true, true) then 1 / 2 else 0)
    (fun v => by split_ifs <;> norm_num)
    (by
      norm_num [Fintype.sum_prod_type, Fintype.sum_bool, Prod.mk.injEq])

theorem diagJoint_proj12 : diagJoint.push proj12 = pairCorr := by
  refine SubPMF.ext' (Finsupp.ext fun p => ?_)
  obtain ⟨a, b⟩ := p
  rw [SubPMF.push_wt_sum, Fintype.sum_prod_type]
  cases a <;> cases b <;>
    simp [diagJoint, pairCorr, proj12, Fintype.sum_prod_type,
      Prod.mk.injEq]

theorem diagJoint_proj23 : diagJoint.push proj23 = pairCorr := by
  refine SubPMF.ext' (Finsupp.ext fun p => ?_)
  obtain ⟨a, b⟩ := p
  rw [SubPMF.push_wt_sum, Fintype.sum_prod_type]
  cases a <;> cases b <;>
    simp [diagJoint, pairCorr, proj23, Prod.mk.injEq]

theorem diagJoint_proj13 : diagJoint.push proj13 = pairCorr := by
  refine SubPMF.ext' (Finsupp.ext fun p => ?_)
  obtain ⟨a, b⟩ := p
  rw [SubPMF.push_wt_sum, Fintype.sum_prod_type]
  cases a <;> cases b <;>
    simp [diagJoint, pairCorr, proj13, Fintype.sum_prod_type,
      Prod.mk.injEq]

/-- **Control (the chain glues)**: dropping the first–third edge from
the ring leaves a decomposable (chain) cover, and the two correlation
edges glue — the diagonal joint reproduces both. -/
theorem chain_glues :
    ∃ μ : SubPMF (Bool × Bool × Bool),
      μ.push proj12 = pairCorr ∧ μ.push proj23 = pairCorr :=
  ⟨diagJoint, diagJoint_proj12, diagJoint_proj23⟩

/-- **Control (the consistent ring glues)**: replacing the third
edge's law by the correlated one makes the full cyclic family gluable
— the same diagonal joint reproduces all three.  The obstruction of
`vorobev_no_joint` is the frustrated assignment, not the cyclic cover
shape. -/
theorem corrRing_glues :
    ∃ μ : SubPMF (Bool × Bool × Bool),
      μ.push proj12 = pairCorr ∧ μ.push proj23 = pairCorr ∧
        μ.push proj13 = pairCorr :=
  ⟨diagJoint, diagJoint_proj12, diagJoint_proj23, diagJoint_proj13⟩

/-! ## The absorption: the inconsistent family denotes bottom

The natural-extension glue of a marginal constraint family is the
conjunction of its marginal constraints — a loose arrow of `Crd _`.
For the Vorob'ev family the conjunction has empty extension
(`vorobev_no_joint`); the credal stratum carries this as the *bottom
credal object* `{0}`, never as the empty set: a lawful credal
denotation contains the bottom model and is closed under admitted
downward scalings, and `credalCompile` adds exactly what lawfulness
demands. -/

/-- The ray relation composes: an admitted downward scaling of an
admitted downward scaling is one. -/
theorem rayC_trans {μ ν ξ : SubPMF V} (h₁ : rayC μ ν) (h₂ : rayC ν ξ) :
    rayC μ ξ := by
  obtain ⟨s, hs0, hs1, hsw⟩ := h₁
  obtain ⟨t, ht0, ht1, htw⟩ := h₂
  refine ⟨t * s, mul_nonneg ht0 hs0, ?_, ?_⟩
  · nlinarith
  · rw [htw, hsw, smul_smul]

/-- The constraint-stratum credal completion: the least constraint
above `C` that contains the bottom model and is closed under admitted
downward scalings.  This is the lawfulness closure of the credal
denotation stratum, stated per element. -/
def credalCompile (C : SubPMF V → Prop) : SubPMF V → Prop :=
  fun ν => ν = SubPMF.zero V ∨ ∃ μ, C μ ∧ rayC μ ν

theorem le_credalCompile (C : SubPMF V → Prop) :
    ∀ μ, C μ → credalCompile C μ :=
  fun μ h => Or.inr ⟨μ, h, rayC_self μ⟩

theorem credalCompile_zero (C : SubPMF V → Prop) :
    credalCompile C (SubPMF.zero V) :=
  Or.inl rfl

theorem downClosed_credalCompile (C : SubPMF V → Prop) :
    DownClosed (credalCompile C) := by
  rintro μ ν hray (rfl | ⟨ρ, hρ, hρμ⟩)
  · obtain ⟨t, _, _, hwt⟩ := hray
    exact Or.inl ((SubPMF.eq_zero_iff_wt ν).mpr
      (by rw [hwt, SubPMF.zero_wt, smul_zero]))
  · exact Or.inr ⟨ρ, hρ, rayC_trans hρμ hray⟩

/-- The completion is least: any bottom-containing, down-closed
constraint above `C` is above the completion. -/
theorem credalCompile_least {C D : SubPMF V → Prop}
    (h0 : D (SubPMF.zero V)) (hdc : DownClosed D)
    (hCD : ∀ μ, C μ → D μ) : ∀ ν, credalCompile C ν → D ν := by
  rintro ν (rfl | ⟨μ, hμ, hray⟩)
  · exact h0
  · exact hdc hray (hCD μ hμ)

/-- The natural-extension glue of the Vorob'ev family: the formal
conjunction of its three marginal constraints, as a loose arrow of
`Crd (Bool × Bool × Bool)`. -/
def vorobevGlue : SubPMF (Bool × Bool × Bool) → Prop :=
  looseConj
    [fun μ => μ.push proj12 = pairCorr,
      fun μ => μ.push proj23 = pairCorr,
      fun μ => μ.push proj13 = pairIndep]

theorem vorobevGlue_iff (μ : SubPMF (Bool × Bool × Bool)) :
    vorobevGlue μ ↔
      μ.push proj12 = pairCorr ∧ μ.push proj23 = pairCorr ∧
        μ.push proj13 = pairIndep := by
  simp [vorobevGlue, looseConj]

/-- The glue is unsatisfiable: no model at all, mass-losing models
included. -/
theorem vorobev_unsatisfiable : ¬ ∃ μ, vorobevGlue μ := by
  rintro ⟨μ, hμ⟩
  exact vorobev_no_joint μ ((vorobevGlue_iff μ).mp hμ)

/-- **The absorption**: the credal completion of the Vorob'ev glue is
exactly the bottom credal object — the ray at the zero model, with
extension `{0}`.  The inconsistent family is carried as honest
inconsistency: a lawful denotation, never the empty set, never a
crash. -/
theorem credalCompile_vorobevGlue :
    credalCompile vorobevGlue = rayC (SubPMF.zero (Bool × Bool × Bool)) := by
  funext ν
  refine propext ⟨?_, ?_⟩
  · rintro (rfl | ⟨μ, hμ, -⟩)
    · exact rayC_self _
    · exact absurd ⟨μ, hμ⟩ vorobev_unsatisfiable
  · rintro ⟨t, -, -, hwt⟩
    exact Or.inl ((SubPMF.eq_zero_iff_wt ν).mpr
      (by rw [hwt, SubPMF.zero_wt, smul_zero]))

/-- The absorption, packaged in the double category: the Vorob'ev
glue's credal completion and the bottom credal object are isomorphic
as loose arrows of `Crd (Bool × Bool × Bool)` (an invertible globular
cell). -/
theorem vorobev_absorption (a : Crd (Bool × Bool × Bool)) :
    ∃ α : Cell (credalCompile vorobevGlue)
        (rayC (SubPMF.zero (Bool × Bool × Bool))) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  Crd.looseIso_ofIff fun μ => by rw [credalCompile_vorobevGlue]

/-! ## The two readings of bottom, side by side

The bottom credal object has an empty radially maximal slice, so the
lower-kind credal verdict at the absorbed family is vacuously
affirmative for *every* constraint — the degenerate case the
semantic-universe chapter records for lower previsions at bottom.
Satisfaction as consistency of the same family is false
(`vorobev_unsatisfiable`): under a satisfaction judgment carrying an
existence presupposition, the inconsistent family satisfies nothing.
The two statements answer different questions — prevision arithmetic
at the bottom object versus existence of a model.  A consumer that
read the vacuous verdict as satisfaction would conclude that an
inconsistent specification family meets the absurd specification;
`satCredal_lower_vorobevGlue_false` states the hazard explicitly so
that no such conflation can pass silently. -/

/-- The lower-kind credal verdict at the absorbed Vorob'ev family is
vacuously affirmative for every constraint: the bottom credal object's
maximal slice is empty. -/
theorem satCredal_lower_vorobevGlue (c : SubPMF (Bool × Bool × Bool) → Prop) :
    SatCredal .lower (credalCompile vorobevGlue) c := by
  rw [credalCompile_vorobevGlue]
  intro ν hν
  exact absurd hν (maxSlice_rayC_zero ν)

/-- The hazard, explicit: the vacuous lower verdict affirms even the
absurd constraint.  Read alongside `vorobev_unsatisfiable`, this is
why the vacuous prevision reading at bottom must never be consumed as
satisfaction. -/
theorem satCredal_lower_vorobevGlue_false :
    SatCredal .lower (credalCompile vorobevGlue) (fun _ => False) :=
  satCredal_lower_vorobevGlue _

/-- Satisfiability of marginal constraint families is not
local-to-global over a cyclic cover: every adjacent pair of the ring's
constraints is satisfiable (the two-edge sub-families by `chain_glues`
and its rotations — here the two correlation edges), while the full
ring is not. -/
theorem satisfiable_not_local :
    (∃ μ : SubPMF (Bool × Bool × Bool),
        μ.push proj12 = pairCorr ∧ μ.push proj23 = pairCorr) ∧
      ¬ ∃ μ, vorobevGlue μ :=
  ⟨chain_glues, vorobev_unsatisfiable⟩

end SuFunctor
