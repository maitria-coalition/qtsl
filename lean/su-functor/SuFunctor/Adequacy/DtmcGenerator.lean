import SuFunctor.Adequacy.SemanticUniverseWiring

/-! # The one-step generator form of the DTMC row grain

Battery-class certificate rules consume a system through its
*infinitesimal generator form*: given the system and a candidate
certificate — a nonnegative observable on the system's state space — a
signed observable saying how the certificate can change with duration.
At the discrete-kernel stratum the generator form is the one-step
drift: the transfer of the certificate along the stored outcome rows,
minus the certificate.  This module realizes that interface for the
compiled DTMC row grain and proves it adequate against the row set's
path law.

* `transferRow`, `genRow` — the recompute form: exact-rational
  contractions over the stored outcome rows, re-derivable by any
  checker from the subject's rows and the certificate's coefficients
  (derived data, never trusted storage; an absent row contributes the
  zero the sparse grain assigns it).
* `rowsLaw_expect_step` — the discrete segment-Dynkin identity: the
  expected change of the certificate across one step equals the
  expected generator value at the step's start.  Computed generator
  rows are thereby theorem-grade premises
  (`rowsLaw_expect_step_of_genForm`), and the drift-row consumption is
  the supermartingale corollary (`rowsLaw_expect_le_of_nonpos`).
* The **bottom fixtures**: infeasibility denotes the zero law — the
  bottom body `{0}`, never the empty set — which satisfies every
  down-closed safety floor (`bottom_sat_massLE_floor`) and refutes
  every positive-threshold liveness demand *provided the demand enters
  the judgment as the wall of its negation*, a mark
  (`bottom_refutes_liveMark`).  The polarity-control theorem
  (`bottom_sat_unNegated_mark`) proves the same demand written without
  the negation is *satisfied* by the zero law — the wrong verdict,
  derived on purpose: it is the reason a verdict schema carries
  safety and liveness atoms in separate, polarity-explicit positions,
  and the liveness face carries its existential content explicitly.
-/

namespace SuFunctor

universe u

/-! ## A dirac evaluation the fixtures need -/

theorem SubPMF.dirac_prob_of_not_mem {V : Type u}
    {v : V} {B : Set V} (h : v ∉ B) :
    (SubPMF.dirac v).prob B = 0 := by
  have hie := (SubPMF.dirac v).prob_union_add_inter B {v}
  have h1 : (SubPMF.dirac v).prob {v} = 1 :=
    SubPMF.dirac_prob_of_mem rfl
  have h2 : (SubPMF.dirac v).prob (B ∪ {v}) ≤ 1 :=
    SubPMF.prob_le_one _ _
  have h3 : (SubPMF.dirac v).prob (B ∩ {v}) ≤ 0 := by
    have hsub : B ∩ {v} ⊆ (∅ : Set V) := by
      rintro w ⟨hwB, hwv⟩
      rw [Set.mem_singleton_iff] at hwv
      subst hwv
      exact absurd hwB h
    simpa using (SubPMF.dirac v).prob_mono hsub
  have h4 : 0 ≤ (SubPMF.dirac v).prob B := SubPMF.prob_nonneg _ _
  linarith

namespace Adequacy

open Finset
open SuFunctor.Universe (CoupledSat)

/-! ## Expectation against a subprobability mass function -/

/-- The expectation of a rational observable against a subprobability
mass function over a finite carrier.  Exact arithmetic; submass means
the "expectation" is the mass-weighted sum, exactly as the verdict
stratum reads it. -/
def expectQ {V : Type u} [Fintype V] (μ : SubPMF V) (f : V → ℚ) : ℚ :=
  ∑ v, μ.wt v * f v

section Generator

variable {S : Type} [Fintype S] [DecidableEq S]

/-! ## The recompute form -/

/-- The one-step transfer of an observable along the stored outcome
rows: the contraction `(transferRow R V) s = ∑ s' , R.outcome (s, s') * V s'`
— the pullback of the observable along one step of the kernel, computed
from the rows.  On the sparse grain an absent row contributes zero, so
the stored support is the whole computation. -/
def transferRow (R : DtmcRows S) (V : S → ℚ) : S → ℚ :=
  fun s => ∑ s', R.outcome (s, s') * V s'

/-- The one-step generator form of the row grain against a candidate
certificate: how the certificate can change with one step of duration.
Derived from the subject's outcome rows and the certificate's
coefficients — a recompute obligation, never trusted storage. -/
def genRow (R : DtmcRows S) (V : S → ℚ) : S → ℚ :=
  fun s => transferRow R V s - V s

/-- On compiled rows the recompute form is the classical matrix form. -/
theorem transferRow_compile (M : FinDTMC S) (V : S → ℚ) (s : S) :
    transferRow (compile M) V s = ∑ s', M.step s s' * V s' := by
  unfold transferRow
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [compile_outcome]

/-- The compiled generator form, classically. -/
theorem genRow_compile (M : FinDTMC S) (V : S → ℚ) (s : S) :
    genRow (compile M) V s = (∑ s', M.step s s' * V s') - V s := by
  unfold genRow
  rw [transferRow_compile]

/-! ## The generator form against the path law -/

/-- The endpoint observable: read a state observable at a trajectory's
last coordinate. -/
def atLast {k : ℕ} (V : S → ℚ) : Traj S k → ℚ :=
  fun ω => V (ω (Fin.last k))

/-- Splitting a trajectory as front and last state. -/
private def snocEquivT (S : Type) (k : ℕ) : Traj S k × S ≃ Traj S (k + 1) where
  toFun p := Fin.snoc p.1 p.2
  invFun ω := (Fin.init ω, ω (Fin.last (k + 1)))
  left_inv p := by
    obtain ⟨ρ, s⟩ := p
    simp
  right_inv ω := by
    simp [Fin.snoc_init_self]

/-- One step of the path law moves the endpoint expectation through the
transfer: the expectation of `V` at the end of `k + 1` steps is the
expectation of the transferred observable at the end of `k` steps. -/
theorem rowsLaw_expect_succ (R : DtmcRows S) (hR : R.WF) (k : ℕ)
    (V : S → ℚ) :
    expectQ (rowsLaw R hR (k + 1)) (atLast V) =
      expectQ (rowsLaw R hR k) (atLast (transferRow R V)) := by
  have hterm : ∀ (ρ : Traj S k) (s : S),
      (rowsLaw R hR (k + 1)).wt (Fin.snoc ρ s) *
        V ((Fin.snoc ρ s : Traj S (k + 1)) (Fin.last (k + 1))) =
      (rowsLaw R hR k).wt ρ * (R.outcome (ρ (Fin.last k), s) * V s) := by
    intro ρ s
    rw [rowsLaw_wt, rowsLaw_wt, chainWt_snoc, Fin.snoc_last]
    ring
  unfold expectQ atLast
  rw [← Fintype.sum_equiv (snocEquivT S k)
      (fun p => (rowsLaw R hR (k + 1)).wt (Fin.snoc p.1 p.2) *
        V ((Fin.snoc p.1 p.2 : Traj S (k + 1)) (Fin.last (k + 1))))
      (fun ω' => (rowsLaw R hR (k + 1)).wt ω' * V (ω' (Fin.last (k + 1))))
      (fun p => rfl),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have h1 : (∑ s, (rowsLaw R hR (k + 1)).wt (Fin.snoc ρ s) *
        V ((Fin.snoc ρ s : Traj S (k + 1)) (Fin.last (k + 1)))) =
      ∑ s, (rowsLaw R hR k).wt ρ * (R.outcome (ρ (Fin.last k), s) * V s) :=
    Finset.sum_congr rfl fun s _ => hterm ρ s
  rw [h1, ← Finset.mul_sum]
  rfl

/-- **The discrete segment-Dynkin identity**: the expected change of
the certificate across one step is the expected value of its generator
form at the step's start.  The generator rows recomputed from the
subject's outcome rows are exactly the premise a drift rule consumes. -/
theorem rowsLaw_expect_step (R : DtmcRows S) (hR : R.WF) (k : ℕ)
    (V : S → ℚ) :
    expectQ (rowsLaw R hR (k + 1)) (atLast V) -
        expectQ (rowsLaw R hR k) (atLast V) =
      expectQ (rowsLaw R hR k) (atLast (genRow R V)) := by
  rw [rowsLaw_expect_succ R hR k V]
  unfold expectQ atLast genRow
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  ring

/-- Computed generator rows are theorem-grade premises: any observable
agreeing pointwise with the recompute form satisfies the segment-Dynkin
identity.  (The wire carries `g` as derived rows; the checker
re-derives the agreement hypothesis from the subject's rows.) -/
theorem rowsLaw_expect_step_of_genForm (R : DtmcRows S) (hR : R.WF)
    (k : ℕ) (V : S → ℚ) {g : S → ℚ} (hg : ∀ s, g s = genRow R V s) :
    expectQ (rowsLaw R hR (k + 1)) (atLast V) -
        expectQ (rowsLaw R hR k) (atLast V) =
      expectQ (rowsLaw R hR k) (atLast g) := by
  have hfun : g = genRow R V := funext hg
  rw [hfun]
  exact rowsLaw_expect_step R hR k V

/-- The drift-row consumption, one step: a nonpositive generator form
makes the endpoint expectation a supermartingale. -/
theorem rowsLaw_expect_succ_le_of_nonpos (R : DtmcRows S) (hR : R.WF)
    (k : ℕ) (V : S → ℚ) (hg : ∀ s, genRow R V s ≤ 0) :
    expectQ (rowsLaw R hR (k + 1)) (atLast V) ≤
      expectQ (rowsLaw R hR k) (atLast V) := by
  have hstep := rowsLaw_expect_step R hR k V
  have hle : expectQ (rowsLaw R hR k) (atLast (genRow R V)) ≤ 0 := by
    unfold expectQ atLast
    refine Finset.sum_nonpos fun ω _ => ?_
    have h1 := (rowsLaw R hR k).nonneg ω
    have h2 := hg (ω (Fin.last k))
    simpa using mul_le_mul_of_nonneg_left h2 h1
  linarith

/-- The drift-row consumption, telescoped to any horizon. -/
theorem rowsLaw_expect_le_of_nonpos (R : DtmcRows S) (hR : R.WF)
    (V : S → ℚ) (hg : ∀ s, genRow R V s ≤ 0) (k : ℕ) :
    expectQ (rowsLaw R hR k) (atLast V) ≤
      expectQ (rowsLaw R hR 0) (atLast V) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    exact le_trans (rowsLaw_expect_succ_le_of_nonpos R hR k V hg) ih

end Generator

/-! ## The bottom fixtures: the two faces at the zero law

Infeasibility denotes the *bottom body* `{0}` — the zero law stays in
the denotation — never the empty set.  The verdict consequences are
one-sided by polarity: every down-closed safety floor passes at the
zero law, and every positive-threshold liveness demand refuses there —
provided liveness enters as a mark (the wall of the demand's
negation).  The polarity-control theorem shows the un-negated spelling
would certify the zero law instead, which is why polarity is schema
data rather than a convention of reading. -/

section Fixtures

variable {V : Type u}

/-- The down-closed safety species: the mass on a bad event stays at or
below the threshold. -/
def massLE (E : Set V) (q : ℚ) : SubPMF V → Prop :=
  fun μ => μ.prob E ≤ q

/-- The liveness species: the mass on a good event reaches the
threshold. -/
def massGE (E : Set V) (q : ℚ) : SubPMF V → Prop :=
  fun μ => q ≤ μ.prob E

@[simp] theorem massLE_iff {E : Set V} {q : ℚ} {μ : SubPMF V} :
    massLE E q μ ↔ μ.prob E ≤ q := Iff.rfl

@[simp] theorem massGE_iff {E : Set V} {q : ℚ} {μ : SubPMF V} :
    massGE E q μ ↔ q ≤ μ.prob E := Iff.rfl

/-- A liveness demand enters the judgment as the wall of its
**negation** — a mark, strictly positive exactly where the demand
holds. -/
noncomputable def liveMark (E : Set V) (q : ℚ) : Plain.Pen V :=
  cwall (fun μ => ¬ massGE E q μ)

theorem liveMark_def (E : Set V) (q : ℚ) :
    liveMark E q = cwall (fun μ => ¬ massGE E q μ) := rfl

/-- Mark polarity at ideal points: a constraint's wall is strictly
positive at a law's ideal point exactly when the law violates the
constraint.  (This is why liveness rides negation walls: the mark of
`¬ demand` is positive exactly where the demand holds.) -/
theorem cwall_pos_at_idealPoint_iff {c : SubPMF V → Prop} {μ : SubPMF V} :
    0 < cwall c μ.toJoint ↔ ¬ c μ := by
  constructor
  · intro h hc
    rw [cwall_toJoint_eq_zero_iff.mpr hc] at h
    exact lt_irrefl 0 h
  · intro hc
    have hnm : μ.toJoint ∉ SubPMF.toJoint '' {μ' | c μ'} := by
      rintro ⟨μ', hμ', he⟩
      exact hc (by rwa [SubPMF.toJoint_injective he] at hμ')
    rw [cwall_def, wallPen_apply_of_not_mem hnm]
    exact lt_of_lt_of_le zero_lt_one le_top

/-- **All safety at the bottom**: the zero law satisfies every
down-closed floor.  Leaked mass can only lower the mass on a bad
event; the fully leaked law satisfies every safety constraint of the
species. -/
theorem bottom_sat_massLE_floor (E : Set V) {q : ℚ} (hq : 0 ≤ q) :
    CoupledSat (idealPoint (SubPMF.zero V)) (cwall (massLE E q))
      {(⊤ : Plain.Pen V)} := by
  rw [coupledSat_idealPoint_cwall_iff]
  show (SubPMF.zero V).prob E ≤ q
  rw [SubPMF.zero_prob]
  exact hq

/-- **No liveness at the bottom**: with the demand riding a mark, the
zero law refuses every positive threshold.  The zero measure stays in
the denotation and votes: it fails the demand, so the mark is not
positive at it, and the verdict refuses. -/
theorem bottom_refutes_liveMark (E : Set V) {q : ℚ} (hq : 0 < q) :
    ¬ CoupledSat (idealPoint (SubPMF.zero V)) 0 {liveMark E q} := by
  rw [coupledSat_idealPoint_iff]
  rintro ⟨-, hl⟩
  have h := hl (liveMark E q) (Set.mem_singleton _)
  rw [liveMark_def, cwall_pos_at_idealPoint_iff] at h
  apply h
  show ¬ q ≤ (SubPMF.zero V).prob E
  rw [SubPMF.zero_prob]
  exact not_le.mpr hq

/-- **Polarity control** (the wrong direction, derived on purpose):
were the liveness demand written as the wall *of itself* — the
negation dropped — the zero law would satisfy it, certifying a fully
leaked system as live.  Polarity is therefore schema data: the same
constraint species denotes differently as floor and as mark, and a
verdict schema must carry the two in separate positions. -/
theorem bottom_sat_unNegated_mark (E : Set V) {q : ℚ} (hq : 0 < q) :
    CoupledSat (idealPoint (SubPMF.zero V)) 0 {cwall (massGE E q)} := by
  rw [coupledSat_idealPoint_iff]
  refine ⟨rfl, ?_⟩
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  subst hv
  rw [cwall_pos_at_idealPoint_iff]
  show ¬ q ≤ (SubPMF.zero V).prob E
  rw [SubPMF.zero_prob]
  exact not_le.mpr hq

/-- The two faces on a live subject: a point mass at a good outcome
outside the bad set satisfies the zero-threshold safety floor and the
threshold-one liveness mark simultaneously. -/
theorem dirac_sat_two_faces {v : V} {E B : Set V}
    (hE : v ∈ E) (hB : v ∉ B) :
    CoupledSat (idealPoint (SubPMF.dirac v)) (cwall (massLE B 0))
      {liveMark E 1} := by
  rw [coupledSat_idealPoint_iff]
  constructor
  · apply cwall_toJoint_eq_zero_iff.mpr
    show (SubPMF.dirac v).prob B ≤ 0
    rw [SubPMF.dirac_prob_of_not_mem hB]
  · intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    rw [liveMark_def, cwall_pos_at_idealPoint_iff]
    intro hneg
    apply hneg
    show (1 : ℚ) ≤ (SubPMF.dirac v).prob E
    rw [SubPMF.dirac_prob_of_mem hE]

end Fixtures

/-! ## The carrier tie at the trajectory stratum -/

section RowsVerdict

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The carrier tie is free for the trajectory record space: a
compiled row set's path law satisfies a safety floor at the judgment
exactly when its path probability meets the bound — the judgment
bridge instantiated at `Traj S k`, with no transport machinery. -/
theorem rowsLaw_sat_floor_iff (R : DtmcRows S) (hR : R.WF) (k : ℕ)
    (E : Set (Traj S k)) (q : ℚ) :
    CoupledSat (idealPoint (rowsLaw R hR k)) (cwall (massLE E q))
        {(⊤ : Plain.Pen (Traj S k))} ↔
      (rowsLaw R hR k).prob E ≤ q :=
  coupledSat_idealPoint_cwall_iff

end RowsVerdict

end Adequacy
end SuFunctor
