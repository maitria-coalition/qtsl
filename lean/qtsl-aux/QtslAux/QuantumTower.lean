/-
Copyright (c) 2026 The maitria coalition. All rights reserved.
Released under Apache 2.0 / MIT dual license.
-/
import QtslAux.QuantumDiamondMeasure
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.OfSequence

/-! # The refinement tower: coarse-grainings as a functor, and Sorkin's
"coarser is more classical" as monotonicity

The coarse-graining module landed the single-merge calculus —
`pushforward_id`, `pushforward_comp`, `pushforward_isDiagonal`,
`pushforward_interference` — and the diamond toy exercised one merge on
a real site. What did not exist is the TOWER: the object Sorkin's
"coarser is more classical" slogan is actually about — a chain of
ever-coarser descriptions, with classicality a monotone property along
it. This module is that tower, kernel-checked at finite grade.

* **The D-form storey is a category** (`DFormStorey`): objects are
  finite-indexed quantum measures, morphisms are atom-merge maps
  intertwining the pushforward (`Hom.pushforward_val`). The category
  laws ARE the landed functoriality theorems — `pushforward_id` for
  identities, `pushforward_comp` for composition; no new mathematics
  enters the instance, which is the thesis: the coarse-graining
  calculus was already a category presentation, and this module only
  says so in the type.

* **A refinement tower is a functor from the thin index category**:
  stage types `X : ℕ → Type u` with step merges `step n : X n →
  X (n+1)` induce stage measures (`stageMeasure`, by recursion) and a
  literal functor `towerFunctor : ℕ ⥤ DFormStorey` (mathlib's
  `Functor.ofSequence` on the preorder category ℕ). Thinness of the
  index is why "functor" is property rather than data: all composites
  of steps agree. The composite leg `towerLeg (h : i ≤ j)` is
  EXTRACTED from the functor, its laws are the functor laws cashed out
  (`towerLeg_self`, `towerLeg_succ`, `towerLeg_trans`), and the
  workhorse is `towerLeg_pushforward`: every later stage is an honest
  single coarse-graining of every earlier stage.

* **Sorkin monotonicity, in the two honest forms the landed lemmas
  support** — and both land, because the summed form at ℓ¹ grade needs
  no new positivity work, only the triangle inequality:

  - *pairwise/spectral*: `interferenceSpectrum` — the set of grade-2
    additivity defects a measure exhibits on disjoint event pairs. One
    merge never mints interference values
    (`interferenceSpectrum_pushforward_subset`: coarse interference IS
    fine interference at preimage events, and preimages of disjoint
    events are disjoint), so along the tower the spectrum is
    ⊆-antitone (`interferenceSpectrum_stageMeasure_antitone`); a
    diagonal measure's spectrum is exactly `{0}`
    (`interferenceSpectrum_of_isDiagonal`).

  - *summed defect functional*: `offDiagMass` — the ℓ¹ off-diagonal
    mass, zero exactly at classical (`offDiagMass_eq_zero_iff`). One
    merge never increases it (`offDiagMass_pushforward_le`: triangle
    inequality per coarse block, fiber regroup, then dropping the
    within-fiber terms; NO positivity consumed), so along the tower it
    is antitone (`offDiagMass_stageMeasure_antitone`) — "coarser is
    more classical" as a real-valued Lyapunov-style statement.

  - *classicality is absorbing*: diagonal at stage `i` forces diagonal
    at every stage `j ≥ i` (`stageMeasure_isDiagonal_mono`), and every
    stage past a diagonal one is (equal to) a classical measure
    (`stageMeasure_classical_absorbing`).

* **The diamond tower** grows the toy into a 3-stage instance: stage 0
  = the landed `diamondMeasure` on the order events of the `Fin 2`
  site (interfering), stage 1 = `Bool` via the site-vocabulary
  `degeneracy` merge (diagonal, Born row 16/25 / 9/25), stage 2+ =
  `PUnit` via the total merge (eventually constant — exactly how a
  finite chain lives in an ℕ-indexed tower). The monotonicity is
  non-vacuous on the library's own site: the off-diagonal mass drops
  STRICTLY at the decohering rung (`towerMeasure_offDiagMass_lt`), and
  the interference value `6/5` — exhibited by an instantaneous event
  against the extended span
  (`diamondMeasure_interference_pointLo_span`) — is ERASED by the
  degeneracy merge (`towerMeasure_interferenceSpectrum_ssubset`).

Scope fences inherited from the record tier: finite index types at
every stage, matrix grade, toy grade at the witnesses; continuum
towers (Isham–Linden) are out of scope — finite chains embed in the
ℕ-indexed form by padding with identity-grade merges; the physical
reading is interpretation, not new claims. -/

namespace Qtsl

namespace QuantumTower

open Matrix CategoryTheory DiamondSite QuantumRecords QuantumDForm
  QuantumTransport QuantumCoarseGraining QuantumDiamondMeasure
open scoped ComplexOrder

universe u

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ## The summed defect functional: ℓ¹ off-diagonal mass -/

/-- Nonnegativity of the defect-functional term shape. -/
private theorem ite_norm_nonneg (P : Prop) [Decidable P] (x : ℂ) :
    0 ≤ if P then 0 else ‖x‖ := by
  split
  · exact le_rfl
  · exact norm_nonneg _

/-- **The ℓ¹ off-diagonal mass**: the summed magnitude of the Gram
data away from the diagonal — a real-valued classicality-defect
functional, zero exactly at diagonal measures
(`offDiagMass_eq_zero_iff`) and non-increasing under every
coarse-graining (`offDiagMass_pushforward_le`). -/
noncomputable def _root_.Qtsl.QuantumDForm.QuantumMeasure.offDiagMass
    [DecidableEq ι] (Q : QuantumMeasure ι) : ℝ :=
  ∑ α, ∑ β, if α = β then 0 else ‖Q.gram α β‖

theorem offDiagMass_nonneg [DecidableEq ι] (Q : QuantumMeasure ι) :
    0 ≤ Q.offDiagMass :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    ite_norm_nonneg _ _

/-- The defect functional vanishes exactly at classical: `offDiagMass`
is the real-valued face of `IsDiagonal`. -/
theorem offDiagMass_eq_zero_iff [DecidableEq ι] (Q : QuantumMeasure ι) :
    Q.offDiagMass = 0 ↔ Q.IsDiagonal := by
  constructor
  · intro h α β hαβ
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg fun α _ =>
      Finset.sum_nonneg fun β _ => ite_norm_nonneg _ _).mp h α
      (Finset.mem_univ α)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun β _ =>
      ite_norm_nonneg _ _).mp hrow β (Finset.mem_univ β)
    rw [if_neg hαβ] at hterm
    exact norm_eq_zero.mp hterm
  · intro hd
    refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun β _ => ?_
    by_cases hαβ : α = β
    · rw [if_pos hαβ]
    · rw [if_neg hαβ, hd hαβ, norm_zero]

omit [Fintype κ] in
/-- Preimages of disjoint coarse events are disjoint fine events. -/
theorem fiberEvent_disjoint [DecidableEq κ] (f : ι → κ)
    {A B : Finset κ} (h : Disjoint A B) :
    Disjoint (fiberEvent f A) (fiberEvent f B) := by
  rw [Finset.disjoint_left] at h ⊢
  intro a ha hb
  exact h ((mem_fiberEvent f).mp ha) ((mem_fiberEvent f).mp hb)

/-- **Coarse-graining never increases the off-diagonal mass**: the
summed-defect form of Sorkin's "coarser is more classical", at a
single merge. Each coarse off-diagonal block is a sum of fine entries
lying strictly off the diagonal (distinct coarse atoms have disjoint
fibers), so the triangle inequality per block, the fiber-partition
regroup, and dropping the within-fiber terms give the bound — NO
positivity is consumed. -/
theorem offDiagMass_pushforward_le [DecidableEq ι] [DecidableEq κ]
    (f : ι → κ) (Q : QuantumMeasure ι) :
    (Q.pushforward f).offDiagMass ≤ Q.offDiagMass := by
  have hregroup : ∀ g : ι → ι → ℝ,
      ∑ c, ∑ c', ∑ a ∈ fiber f c, ∑ b ∈ fiber f c', g a b
        = ∑ a, ∑ b, g a b := by
    intro g
    calc ∑ c, ∑ c', ∑ a ∈ fiber f c, ∑ b ∈ fiber f c', g a b
        = ∑ c, ∑ a ∈ fiber f c, ∑ c', ∑ b ∈ fiber f c', g a b :=
          Finset.sum_congr rfl fun c _ => Finset.sum_comm
      _ = ∑ c, ∑ a ∈ fiber f c, ∑ b, g a b :=
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
            sum_fiber f fun b => g a b
      _ = ∑ a, ∑ b, g a b := sum_fiber f fun a => ∑ b, g a b
  calc (Q.pushforward f).offDiagMass
      = ∑ c, ∑ c',
          if c = c' then 0
          else ‖Q.eventForm (fiber f c) (fiber f c')‖ := rfl
    _ ≤ ∑ c, ∑ c', ∑ a ∈ fiber f c, ∑ b ∈ fiber f c',
          if f a = f b then 0 else ‖Q.gram a b‖ := ?_
    _ = ∑ a, ∑ b, if f a = f b then 0 else ‖Q.gram a b‖ := hregroup _
    _ ≤ ∑ a, ∑ b, if a = b then 0 else ‖Q.gram a b‖ := ?_
    _ = Q.offDiagMass := rfl
  · refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun c' _ => ?_
    by_cases hcc : c = c'
    · rw [if_pos hcc]
      exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
        ite_norm_nonneg _ _
    · rw [if_neg hcc]
      calc ‖Q.eventForm (fiber f c) (fiber f c')‖
          ≤ ∑ a ∈ fiber f c, ‖∑ b ∈ fiber f c', Q.gram a b‖ :=
            norm_sum_le _ _
        _ ≤ ∑ a ∈ fiber f c, ∑ b ∈ fiber f c', ‖Q.gram a b‖ :=
            Finset.sum_le_sum fun a _ => norm_sum_le _ _
        _ = ∑ a ∈ fiber f c, ∑ b ∈ fiber f c',
              (if f a = f b then 0 else ‖Q.gram a b‖) :=
            Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl
              fun b hb => (if_neg fun hab => hcc
                (((mem_fiber f).mp ha).symm.trans
                  (hab.trans ((mem_fiber f).mp hb)))).symm
  · refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    by_cases hab : f a = f b
    · rw [if_pos hab]
      exact ite_norm_nonneg _ _
    · rw [if_neg hab, if_neg fun h => hab (congrArg f h)]

/-! ## The pairwise form: the interference spectrum -/

/-- **The interference spectrum**: the set of grade-2 additivity
defects a quantum measure exhibits on disjoint event pairs. Diagonal
measures have spectrum exactly `{0}`
(`interferenceSpectrum_of_isDiagonal`); coarse-graining never mints
new values (`interferenceSpectrum_pushforward_subset`). -/
def _root_.Qtsl.QuantumDForm.QuantumMeasure.interferenceSpectrum
    [DecidableEq ι] (Q : QuantumMeasure ι) : Set ℂ :=
  {z | ∃ A B : Finset ι, Disjoint A B ∧ Q.interference A B = z}

theorem zero_mem_interferenceSpectrum [DecidableEq ι]
    (Q : QuantumMeasure ι) : 0 ∈ Q.interferenceSpectrum :=
  ⟨∅, ∅, Finset.disjoint_empty_left _, by
    simp [QuantumMeasure.interference, QuantumMeasure.sorkinMeasure,
      QuantumMeasure.eventForm]⟩

/-- A diagonal measure's interference spectrum is exactly `{0}`:
grade 2 has degenerated to grade 1, and the only additivity defect on
disjoint pairs is the trivial one. -/
theorem interferenceSpectrum_of_isDiagonal [DecidableEq ι]
    {Q : QuantumMeasure ι} (hd : Q.IsDiagonal) :
    Q.interferenceSpectrum = {0} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨A, B, hAB, rfl⟩
    exact Set.mem_singleton_iff.mpr (Q.isDiagonal_interference hd hAB)
  · rintro z rfl
    exact zero_mem_interferenceSpectrum Q

/-- **Coarse-graining never mints interference values**: every
additivity defect of the merged measure was already exhibited by the
fine measure, at the preimage events. The pairwise form of "coarser is
more classical", at a single merge. -/
theorem interferenceSpectrum_pushforward_subset [DecidableEq ι]
    [DecidableEq κ] (f : ι → κ) (Q : QuantumMeasure ι) :
    (Q.pushforward f).interferenceSpectrum ⊆ Q.interferenceSpectrum := by
  rintro z ⟨A, B, hAB, rfl⟩
  exact ⟨fiberEvent f A, fiberEvent f B, fiberEvent_disjoint f hAB,
    (pushforward_interference f Q A B).symm⟩

/-! ## The D-form storey as a category

Objects: finite-indexed quantum measures. Morphisms: atom-merge maps
intertwining the pushforward. The category laws are the landed
functoriality theorems `pushforward_id` and `pushforward_comp` — no
new mathematics enters the instance. -/

/-- An object of the D-form storey: a finite index of alternatives
carrying a quantum measure. -/
structure DFormStorey : Type (u + 1) where
  /-- the index of alternatives -/
  idx : Type u
  [fintypeIdx : Fintype idx]
  [decEqIdx : DecidableEq idx]
  /-- the quantum measure on the index -/
  meas : QuantumMeasure idx

attribute [instance] DFormStorey.fintypeIdx DFormStorey.decEqIdx

/-- Smart constructor for D-form storey objects. -/
def DFormStorey.of (ι : Type u) [Fintype ι] [DecidableEq ι]
    (Q : QuantumMeasure ι) : DFormStorey :=
  ⟨ι, Q⟩

/-- Morphisms of the D-form storey: coarse-graining maps intertwining
the pushforward. -/
@[ext]
structure DFormStorey.Hom (S T : DFormStorey.{u}) where
  /-- the atom-merge map -/
  val : S.idx → T.idx
  pushforward_val : S.meas.pushforward val = T.meas

/-- The D-form storey is a category: identities by `pushforward_id`,
composition by `pushforward_comp` — the landed functoriality, worn as
a `Category` instance. -/
instance : Category DFormStorey.{u} where
  Hom := DFormStorey.Hom
  id S := ⟨_root_.id, pushforward_id S.meas⟩
  comp {S T U} f g := ⟨g.val ∘ f.val, by
    rw [pushforward_comp, f.pushforward_val, g.pushforward_val]⟩
  id_comp _ := DFormStorey.Hom.ext rfl
  comp_id _ := DFormStorey.Hom.ext rfl
  assoc _ _ _ := DFormStorey.Hom.ext rfl

@[simp] theorem DFormStorey.id_val (S : DFormStorey.{u}) :
    (𝟙 S : S ⟶ S).val = _root_.id := rfl

@[simp] theorem DFormStorey.comp_val {S T U : DFormStorey.{u}}
    (f : S ⟶ T) (g : T ⟶ U) : (f ≫ g).val = g.val ∘ f.val := rfl

/-! ## The refinement tower: a functor out of the thin index category -/

section Tower

variable {X : ℕ → Type u} [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]

/-- The stage measures of a refinement tower: stage `0` is the fine
measure, stage `n+1` merges stage `n` along the `n`-th step. (Bare
`Nat.rec`, so both equations hold by iota even at open `n`.) -/
noncomputable def stageMeasure (Q : QuantumMeasure (X 0))
    (step : ∀ n, X n → X (n + 1)) : ∀ n, QuantumMeasure (X n) :=
  Nat.rec Q fun n Qn => Qn.pushforward (step n)

variable (Q : QuantumMeasure (X 0)) (step : ∀ n, X n → X (n + 1))

@[simp] theorem stageMeasure_zero : stageMeasure Q step 0 = Q := rfl

@[simp] theorem stageMeasure_succ (n : ℕ) :
    stageMeasure Q step (n + 1)
      = (stageMeasure Q step n).pushforward (step n) := rfl

/-- The rung morphism of the tower: the `n`-th step merge, as a
D-form-storey morphism (its intertwining law is `stageMeasure_succ`'s
`rfl`). -/
noncomputable def towerHom (n : ℕ) :
    DFormStorey.of (X n) (stageMeasure Q step n) ⟶
      DFormStorey.of (X (n + 1)) (stageMeasure Q step (n + 1)) :=
  ⟨step n, rfl⟩

/-- **The refinement tower is a functor** from the thin index category
(ℕ with its preorder) into the D-form storey: mathlib's
`Functor.ofSequence` on the rungs. Thinness of the index is why
functoriality is property rather than data — all composites of steps
agree, and the composite legs with their laws are extracted below
(`towerLeg`, `towerLeg_pushforward`, `towerLeg_self`, `towerLeg_succ`,
`towerLeg_trans`). -/
noncomputable def towerFunctor : ℕ ⥤ DFormStorey.{u} :=
  Functor.ofSequence
    (X := fun n => DFormStorey.of (X n) (stageMeasure Q step n))
    fun n => towerHom Q step n

@[simp] theorem towerFunctor_obj (n : ℕ) :
    (towerFunctor Q step).obj n
      = DFormStorey.of (X n) (stageMeasure Q step n) := rfl

/-- The composite leg of the tower from stage `i` to stage `j`,
extracted from the functor. -/
noncomputable def towerLeg {i j : ℕ} (h : i ≤ j) : X i → X j :=
  ((towerFunctor Q step).map (homOfLE h)).val

/-- **Every later stage is an honest coarse-graining of every earlier
stage**: the functor identity, unbundled — the workhorse every
monotonicity theorem below consumes. -/
theorem towerLeg_pushforward {i j : ℕ} (h : i ≤ j) :
    (stageMeasure Q step i).pushforward (towerLeg Q step h)
      = stageMeasure Q step j :=
  ((towerFunctor Q step).map (homOfLE h)).pushforward_val

/-- The identity law of the functor, at leg grade. -/
theorem towerLeg_self (i : ℕ) :
    towerLeg Q step (le_refl i) = _root_.id :=
  congrArg DFormStorey.Hom.val ((towerFunctor Q step).map_id i)

/-- The single-rung leg is the step map (the `ofSequence` rung law). -/
theorem towerLeg_succ (n : ℕ) :
    towerLeg Q step (Nat.le_succ n) = step n := by
  have h := Functor.ofSequence_map_homOfLE_succ
    (fun k => towerHom Q step k) n
  exact congrArg DFormStorey.Hom.val h

/-- The composition law of the functor, at leg grade: legs compose,
and by thinness there is nothing else to check. -/
theorem towerLeg_trans {i j k : ℕ} (h : i ≤ j) (h' : j ≤ k) :
    towerLeg Q step (h.trans h')
      = towerLeg Q step h' ∘ towerLeg Q step h := by
  have hcomp : (homOfLE (h.trans h') : i ⟶ k)
      = homOfLE h ≫ homOfLE h' := rfl
  rw [towerLeg, hcomp, Functor.map_comp]
  rfl

/-! ## Sorkin monotonicity along the tower -/

/-- **Coarser is more classical**: diagonality — record-forcedness at
measure grade — is monotone along the tower. Once a stage is
classical, every coarser stage is. -/
theorem stageMeasure_isDiagonal_mono {i j : ℕ} (h : i ≤ j)
    (hd : (stageMeasure Q step i).IsDiagonal) :
    (stageMeasure Q step j).IsDiagonal := by
  rw [← towerLeg_pushforward Q step h]
  exact pushforward_isDiagonal _ _ hd

/-- **Classicality is absorbing**: every stage past a diagonal one is
(equal to) a classical measure. -/
theorem stageMeasure_classical_absorbing {i j : ℕ} (h : i ≤ j)
    (hd : (stageMeasure Q step i).IsDiagonal) :
    ∃ (p : X j → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1),
      stageMeasure Q step j = QuantumMeasure.classical p hp hs :=
  ⟨_, _, _, (stageMeasure Q step j).isDiagonal_eq_classical
    (stageMeasure_isDiagonal_mono Q step h hd)⟩

/-- **The off-diagonal mass is non-increasing along the tower**: the
summed-defect form of Sorkin monotonicity. -/
theorem offDiagMass_stageMeasure_antitone :
    Antitone fun n => (stageMeasure Q step n).offDiagMass := by
  intro i j h
  simp only
  rw [← towerLeg_pushforward Q step h]
  exact offDiagMass_pushforward_le _ _

/-- **The interference spectrum is ⊆-antitone along the tower**: the
pairwise form of Sorkin monotonicity — no stage exhibits an additivity
defect its finer stages did not already exhibit. -/
theorem interferenceSpectrum_stageMeasure_antitone :
    Antitone fun n => (stageMeasure Q step n).interferenceSpectrum := by
  intro i j h
  simp only
  rw [← towerLeg_pushforward Q step h]
  exact interferenceSpectrum_pushforward_subset _ _

end Tower

/-! ## The diamond tower: the toy grown to three stages

Stage 0: the order events of the `Fin 2` site, interfering. Stage 1:
"instantaneous or extended?", diagonal. Stage 2 and beyond: the total
merge, trivial — the tower is eventually constant, which is exactly
how a finite chain lives in an ℕ-indexed tower. -/

section DiamondTower

/-- The stage types of the diamond tower. -/
def towerX : ℕ → Type
  | 0 => Diamond (Fin 2)
  | 1 => Bool
  | _ + 2 => PUnit

noncomputable instance : ∀ n, Fintype (towerX n)
  | 0 => inferInstanceAs (Fintype (Diamond (Fin 2)))
  | 1 => inferInstanceAs (Fintype Bool)
  | _ + 2 => inferInstanceAs (Fintype PUnit)

instance : ∀ n, DecidableEq (towerX n)
  | 0 => inferInstanceAs (DecidableEq (Diamond (Fin 2)))
  | 1 => inferInstanceAs (DecidableEq Bool)
  | _ + 2 => inferInstanceAs (DecidableEq PUnit)

/-- The step merges: the site-vocabulary degeneracy classifier, then
total merges. -/
def towerStep : ∀ n, towerX n → towerX (n + 1)
  | 0 => degeneracy
  | 1 => fun _ => PUnit.unit
  | _ + 2 => fun _ => PUnit.unit

/-- The stage measures of the diamond tower. -/
noncomputable def towerMeasure : ∀ n, QuantumMeasure (towerX n) :=
  stageMeasure diamondMeasure towerStep

/-- The diamond tower's functor: the deliverable, concrete — stage 0
is the order-event site. -/
noncomputable def diamondTowerFunctor : ℕ ⥤ DFormStorey.{0} :=
  towerFunctor diamondMeasure towerStep

theorem towerMeasure_zero : towerMeasure 0 = diamondMeasure := rfl

theorem towerMeasure_one :
    towerMeasure 1 = diamondMeasure.pushforward degeneracy := rfl

/-- Stage 0 genuinely interferes (inherited from the toy). -/
theorem towerMeasure_zero_not_isDiagonal :
    ¬ (towerMeasure 0).IsDiagonal := by
  rw [towerMeasure_zero]
  exact diamondMeasure_not_isDiagonal

/-- Stage 1 is diagonal: the degeneracy merge decoheres (inherited
from the toy). -/
theorem towerMeasure_one_isDiagonal : (towerMeasure 1).IsDiagonal := by
  rw [towerMeasure_one]
  exact diamondMeasure_pushforward_isDiagonal

/-- **Monotonicity exercised**: every stage past the degeneracy merge
is diagonal — the `PUnit` tail included, with no further computation. -/
theorem towerMeasure_isDiagonal_of_pos {n : ℕ} (h : 1 ≤ n) :
    (towerMeasure n).IsDiagonal :=
  stageMeasure_isDiagonal_mono (X := towerX) diamondMeasure towerStep h
    towerMeasure_one_isDiagonal

/-- **Absorption exercised**: every stage past the degeneracy merge is
(equal to) a classical measure. -/
theorem towerMeasure_classical_of_pos {n : ℕ} (h : 1 ≤ n) :
    ∃ (p : towerX n → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1),
      towerMeasure n = QuantumMeasure.classical p hp hs :=
  stageMeasure_classical_absorbing (X := towerX) diamondMeasure towerStep h
    towerMeasure_one_isDiagonal

/-- The coarse stage carries zero defect. -/
theorem towerMeasure_offDiagMass_one : (towerMeasure 1).offDiagMass = 0 :=
  (offDiagMass_eq_zero_iff _).mpr towerMeasure_one_isDiagonal

/-- The fine stage carries positive defect — no norm arithmetic: the
positivity is the contrapositive of `offDiagMass_eq_zero_iff` at the
toy's landed non-diagonality. -/
theorem towerMeasure_offDiagMass_pos :
    0 < (towerMeasure 0).offDiagMass :=
  (offDiagMass_nonneg _).lt_of_ne fun h =>
    towerMeasure_zero_not_isDiagonal
      ((offDiagMass_eq_zero_iff _).mp h.symm)

/-- **The strict drop**: the off-diagonal mass falls strictly at the
decohering rung — the tower monotonicity is non-vacuous on the
house's own site. -/
theorem towerMeasure_offDiagMass_lt :
    (towerMeasure 1).offDiagMass < (towerMeasure 0).offDiagMass := by
  rw [towerMeasure_offDiagMass_one]
  exact towerMeasure_offDiagMass_pos

/-- The instantaneous event at `0` interferes with the extended span
at value `6/5`: the landed `3/5` Gram entry plus its conjugate — the
toy's one new value-level item, no matrix arithmetic re-done. -/
theorem diamondMeasure_interference_pointLo_span :
    diamondMeasure.interference {pointLo} {span} = 6 / 5 := by
  have hne : pointLo ≠ span := fun h =>
    absurd (congrArg Diamond.hi h) (by decide)
  have hd : Disjoint ({pointLo} : Finset (Diamond (Fin 2))) {span} :=
    Finset.disjoint_singleton.mpr hne
  have h1 : diamondMeasure.eventForm {pointLo} {span} = 3 / 5 := by
    simp only [QuantumMeasure.eventForm, Finset.sum_singleton]
    exact diamondMeasure_gram_pointLo_span
  have h2 : diamondMeasure.eventForm {span} {pointLo} = 3 / 5 := by
    rw [diamondMeasure.eventForm_conj, h1]
    norm_num [Complex.ext_iff]
  rw [diamondMeasure.interference_eq hd, h1, h2]
  norm_num

/-- **The spectrum shrinks strictly at the decohering rung**: the
interference value `6/5`, exhibited at the fine stage by an
instantaneous event against the extended span, is erased by the
degeneracy merge — whose spectrum is exactly `{0}`. -/
theorem towerMeasure_interferenceSpectrum_ssubset :
    (towerMeasure 1).interferenceSpectrum
      ⊂ (towerMeasure 0).interferenceSpectrum := by
  rw [interferenceSpectrum_of_isDiagonal towerMeasure_one_isDiagonal,
    Set.ssubset_def]
  refine ⟨Set.singleton_subset_iff.mpr
    (zero_mem_interferenceSpectrum _), fun hsub => ?_⟩
  have h65 : (6 / 5 : ℂ) ∈ (towerMeasure 0).interferenceSpectrum := by
    rw [towerMeasure_zero]
    have hne : pointLo ≠ span := fun h =>
      absurd (congrArg Diamond.hi h) (by decide)
    exact ⟨{pointLo}, {span}, Finset.disjoint_singleton.mpr hne,
      diamondMeasure_interference_pointLo_span⟩
  have h0 := hsub h65
  rw [Set.mem_singleton_iff] at h0
  norm_num at h0

end DiamondTower

end QuantumTower

end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumTower.offDiagMass_nonneg
#print axioms Qtsl.QuantumTower.offDiagMass_eq_zero_iff
#print axioms Qtsl.QuantumTower.fiberEvent_disjoint
#print axioms Qtsl.QuantumTower.offDiagMass_pushforward_le
#print axioms Qtsl.QuantumTower.zero_mem_interferenceSpectrum
#print axioms Qtsl.QuantumTower.interferenceSpectrum_of_isDiagonal
#print axioms Qtsl.QuantumTower.interferenceSpectrum_pushforward_subset
#print axioms Qtsl.QuantumTower.DFormStorey.id_val
#print axioms Qtsl.QuantumTower.DFormStorey.comp_val
#print axioms Qtsl.QuantumTower.towerFunctor_obj
#print axioms Qtsl.QuantumTower.towerLeg_pushforward
#print axioms Qtsl.QuantumTower.towerLeg_self
#print axioms Qtsl.QuantumTower.towerLeg_succ
#print axioms Qtsl.QuantumTower.towerLeg_trans
#print axioms Qtsl.QuantumTower.stageMeasure_isDiagonal_mono
#print axioms Qtsl.QuantumTower.stageMeasure_classical_absorbing
#print axioms Qtsl.QuantumTower.offDiagMass_stageMeasure_antitone
#print axioms Qtsl.QuantumTower.interferenceSpectrum_stageMeasure_antitone
#print axioms Qtsl.QuantumTower.towerMeasure_zero
#print axioms Qtsl.QuantumTower.towerMeasure_one
#print axioms Qtsl.QuantumTower.towerMeasure_zero_not_isDiagonal
#print axioms Qtsl.QuantumTower.towerMeasure_one_isDiagonal
#print axioms Qtsl.QuantumTower.towerMeasure_isDiagonal_of_pos
#print axioms Qtsl.QuantumTower.towerMeasure_classical_of_pos
#print axioms Qtsl.QuantumTower.towerMeasure_offDiagMass_one
#print axioms Qtsl.QuantumTower.towerMeasure_offDiagMass_pos
#print axioms Qtsl.QuantumTower.towerMeasure_offDiagMass_lt
#print axioms Qtsl.QuantumTower.diamondMeasure_interference_pointLo_span
#print axioms Qtsl.QuantumTower.towerMeasure_interferenceSpectrum_ssubset
