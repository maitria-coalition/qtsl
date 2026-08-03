/-
Qtsl/ScmTwin.lean — twin-network counterfactuals for acyclic structural
causal models: substitution, box measure, union bound — machine-checked.

Chapter anchors: book, chapters/qtsl-mathematical-modelling.tex,
§"Structural Causal Models" (`sec:mt-scm`), whose Semantics paragraph
names exactly this bridge set — "Twin-world substitution in the
standard (Pearl) sense, with the lightest bridge set on the list:
substitution, box-measure monotonicity and additivity, and a union
bound — no stochastic analysis anywhere" — and
chapters/qtsl-composition-patterns.tex, §"The Twin-World Pattern"
(`sec:cp-twin`), whose semantic bridge this module machine-checks.

THE THREE BRIDGES.

1. **Twin-network substitution** (`Scm.twin`, `twin_solve_left/right`,
   `cfEvent_eq_twin`): the twin network — `2n` endogenous variables,
   the A-copy carrying one intervention's mechanisms and the B-copy the
   other's, both copies reading the SAME exogenous block — has solution
   map equal, copy by copy, to the pair of individual solution maps
   against the shared `ω`. Hence the counterfactual event (a shared-`ω`
   conjunction across two solved worlds) IS an ordinary single-network
   event of the twin SCM: Pearl ch. 7 at trivial abduction (the
   queries here condition on nothing, so the abduction step is the
   identity on the exogenous measure) — the license for composing both
   counterfactual worlds against one variable space.

2. **Box measure** (`volume_box`, `exclusion_upper`,
   `exclusion_upper_boxes`, `exclusion_zero`, `inner_lower`,
   `inner_lower_pair`, `decoupling_product`): boxes are `Set.Icc` in
   `Fin m → ℝ`; their volume is the product of side lengths
   (`Real.volume_Icc_pi`). The exclusion cover's either/or logic is
   pointwise: an `E`-point in an A-cell contradicts `HA + δ ≤ 0` (the
   AI does not harm `v` there), in a B-cell contradicts `δ − HB ≤ 0`
   (DoNothing harms `v` on all of it, so "would not have been harmed"
   fails) — so `E` lives in the charged family, and monotonicity +
   finite subadditivity give the upper bound. Inner boxes give the
   lower bound by monotonicity, disjoint pairs add by additivity, and
   `decoupling_product` is the Fubini face of the decoupling probe:
   under the independent-worlds PRODUCT the joint factors — the
   arithmetic the shared-`ω` coupling refuses (the certified probe of
   `sec:cp-twin` prices the difference: `0` coupled against `≥ 1/2048`
   decoupled for the same controller).

3. **Union bound over victims** (`victims_union_bound`, `p7_bound`,
   `p7_zero_lt`): the specification's `∃ v : V` step, composed with the
   two exclusion covers into the flagship counterfactual-harm sentence
   (the programme thesis's p. 7 bound, at its stated `10⁻⁴` threshold)
   — for the guard controller (both charged families empty) the
   counterfactual-harm probability is `0 < 10⁻⁴`, certified.

Every named obligation is proven outright — no quarantined fields, no
axioms beyond the standard classical base (receipts at the bottom).

THE WORKED INSTANCE. The bottom of the file pins the crossing example
certified in `sec:mt-scm` (pedestrian/cyclist bands, guard and flinch
controllers, DoNothing baseline): the five structural equations are
defined here and the certificate corpus's landmark values — composed
polynomials, the counterfactual-harm witness point, the box volumes —
are machine-checked, so any drift between this model and the values
the certificates cite fails elaboration.

WHAT REMAINS PROSE (the honest boundary): the identification of the
certificate checker's polynomial coefficient tables with `Scm.solve`'s
values is cross-checked on the executable side (per-coefficient
re-composition), and Lean-side by the instance pins here — cited, not
proven, as an identification between artifacts. The adequacy square
(profile ↦ SU semantics) is likewise not claimed by this module.
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

open scoped ENNReal
open MeasureTheory Set

namespace Qtsl

namespace ScmTwin

/-- The exogenous state space at arity `m` — plain coordinate tuples,
the exogenous table's `ω = (ω₁, …, ω_m)`. -/
abbrev State (m : ℕ) := Fin m → ℝ

/-- **An acyclic SCM** (the S-SCM row's shape: equations in topological
order over one exogenous table): `n` mechanisms over `m` exogenous
coordinates. `mech k` reads the whole endogenous tuple for typing
convenience; `lower` is acyclicity as data — mechanism `k` depends only
on strictly-earlier endogenous coordinates (`eq[k]` over
`(ω, endos[0..k-1])`, stated as invariance). -/
structure Scm (m n : ℕ) where
  /-- mechanism `k`: exogenous block + endogenous tuple ↦ value -/
  mech : Fin n → State m → (Fin n → ℝ) → ℝ
  /-- acyclicity: mechanism `k` reads only coordinates `j < k` -/
  lower : ∀ (k : Fin n) (ω : State m) (v w : Fin n → ℝ),
    (∀ j : Fin n, (j : ℕ) < (k : ℕ) → v j = w j) → mech k ω v = mech k ω w

namespace Scm

variable {m n : ℕ}

/-- Two SCMs with the same mechanisms are equal (the `lower` field is a
proposition). -/
theorem ext_mech {S T : Scm m n} (h : S.mech = T.mech) : S = T := by
  cases S; cases T; cases h; rfl

/-- **The solution map**: forward substitution in topological order.
Coordinates `≥ k` are passed as `0` junk; `lower` makes them
irrelevant. -/
noncomputable def solve (S : Scm m n) (ω : State m) (k : Fin n) : ℝ :=
  S.mech k ω fun j => if _h : (j : ℕ) < (k : ℕ) then S.solve ω j else 0
termination_by (k : ℕ)
decreasing_by exact _h

theorem solve_eq (S : Scm m n) (ω : State m) (k : Fin n) :
    S.solve ω k
      = S.mech k ω
          fun j => if _ : (j : ℕ) < (k : ℕ) then S.solve ω j else 0 := by
  rw [solve]

/-- The workhorse: any endogenous tuple that agrees with the solution on
the strict prefix evaluates mechanism `k` to the solution value. -/
theorem solve_eq_of_prefix (S : Scm m n) (ω : State m) (k : Fin n)
    (v : Fin n → ℝ)
    (hv : ∀ j : Fin n, (j : ℕ) < (k : ℕ) → v j = S.solve ω j) :
    S.mech k ω v = S.solve ω k := by
  rw [S.solve_eq ω k]
  exact S.lower k ω v _ fun j hj => by rw [hv j hj, dif_pos hj]

/-- **Mechanism surgery** — Pearl's `do`: replace the mechanisms in
`mask` by the donor `T`'s. -/
def surgery (S T : Scm m n) (mask : Fin n → Prop) [DecidablePred mask] :
    Scm m n where
  mech k := if mask k then T.mech k else S.mech k
  lower k ω v w h := by
    by_cases hk : mask k
    · rw [if_pos hk]; exact T.lower k ω v w h
    · rw [if_neg hk]; exact S.lower k ω v w h

/-- **Pearl consistency, trivial case**: intervening with a mechanism's
own equation changes nothing. -/
theorem surgery_self (S : Scm m n) (mask : Fin n → Prop)
    [DecidablePred mask] : S.surgery S mask = S :=
  ext_mech (funext fun _ => ite_self _)

theorem solve_surgery_self (S : Scm m n) (mask : Fin n → Prop)
    [DecidablePred mask] (ω : State m) :
    (S.surgery S mask).solve ω = S.solve ω := by
  rw [surgery_self]

/-- **The twin network** (Pearl ch. 7): `2n` endogenous variables — the
A-copy (indices `< n`) carrying `A`'s mechanisms, the B-copy (indices
`≥ n`) carrying `B`'s — BOTH copies reading the same exogenous block.
There is one `ω` and no second one to reference: the shared read is the
coupling (one variable space, two solution maps). -/
def twin (A B : Scm m n) : Scm m (n + n) where
  mech k ω v :=
    if h : (k : ℕ) < n then
      A.mech ⟨(k : ℕ), h⟩ ω fun j => v (Fin.castAdd n j)
    else
      B.mech ⟨(k : ℕ) - n, by omega⟩ ω fun j => v (Fin.natAdd n j)
  lower k ω v w h := by
    by_cases hk : (k : ℕ) < n
    · rw [dif_pos hk, dif_pos hk]
      exact A.lower _ ω _ _ fun j hj => h (Fin.castAdd n j) hj
    · rw [dif_neg hk, dif_neg hk]
      exact B.lower _ ω _ _ fun j hj => h (Fin.natAdd n j) (by
        show n + (j : ℕ) < (k : ℕ)
        have hj' : (j : ℕ) < (k : ℕ) - n := hj
        omega)

/-- **Twin-network substitution, A-copy**: the twin network's solution
restricted to the first copy is `A`'s own solution against the shared
`ω`. -/
theorem twin_solve_left (A B : Scm m n) (ω : State m) (k : Fin n) :
    (A.twin B).solve ω (Fin.castAdd n k) = A.solve ω k := by
  have H : ∀ N : ℕ, ∀ k : Fin n, (k : ℕ) < N →
      (A.twin B).solve ω (Fin.castAdd n k) = A.solve ω k := by
    intro N
    induction N with
    | zero => exact fun k hk => absurd hk (Nat.not_lt_zero _)
    | succ N ih =>
      intro k hk
      rw [(A.twin B).solve_eq ω (Fin.castAdd n k)]
      show (if h : ((Fin.castAdd n k : Fin (n + n)) : ℕ) < n then
          A.mech ⟨((Fin.castAdd n k : Fin (n + n)) : ℕ), h⟩ ω
            fun j => if _ : ((Fin.castAdd n j : Fin (n + n)) : ℕ)
                < ((Fin.castAdd n k : Fin (n + n)) : ℕ) then
              (A.twin B).solve ω (Fin.castAdd n j) else 0
        else _) = A.solve ω k
      rw [dif_pos (show ((Fin.castAdd n k : Fin (n + n)) : ℕ) < n
        from k.isLt)]
      exact A.solve_eq_of_prefix ω k _ fun j hj => by
        show (if _ : ((Fin.castAdd n j : Fin (n + n)) : ℕ)
            < ((Fin.castAdd n k : Fin (n + n)) : ℕ) then
          (A.twin B).solve ω (Fin.castAdd n j) else 0) = A.solve ω j
        rw [dif_pos (show ((Fin.castAdd n j : Fin (n + n)) : ℕ)
              < ((Fin.castAdd n k : Fin (n + n)) : ℕ) from hj)]
        exact ih j (by omega)
  exact H ((k : ℕ) + 1) k (Nat.lt_succ_self _)

/-- **Twin-network substitution, B-copy**: the twin network's solution
restricted to the second copy is `B`'s own solution against the SAME
`ω` — the two counterfactual worlds solved in one network, which is the
whole content of "shared resolution of unknowns". -/
theorem twin_solve_right (A B : Scm m n) (ω : State m) (k : Fin n) :
    (A.twin B).solve ω (Fin.natAdd n k) = B.solve ω k := by
  have H : ∀ N : ℕ, ∀ k : Fin n, (k : ℕ) < N →
      (A.twin B).solve ω (Fin.natAdd n k) = B.solve ω k := by
    intro N
    induction N with
    | zero => exact fun k hk => absurd hk (Nat.not_lt_zero _)
    | succ N ih =>
      intro k hk
      rw [(A.twin B).solve_eq ω (Fin.natAdd n k)]
      show (if h : ((Fin.natAdd n k : Fin (n + n)) : ℕ) < n then _
        else
          B.mech ⟨((Fin.natAdd n k : Fin (n + n)) : ℕ) - n, by omega⟩ ω
            fun j => if _ : ((Fin.natAdd n j : Fin (n + n)) : ℕ)
                < ((Fin.natAdd n k : Fin (n + n)) : ℕ) then
              (A.twin B).solve ω (Fin.natAdd n j) else 0)
        = B.solve ω k
      rw [dif_neg (show ¬ ((Fin.natAdd n k : Fin (n + n)) : ℕ) < n by
        show ¬ n + (k : ℕ) < n; omega)]
      have hidx : (⟨((Fin.natAdd n k : Fin (n + n)) : ℕ) - n,
          by omega⟩ : Fin n) = k := by
        apply Fin.ext
        show n + (k : ℕ) - n = (k : ℕ)
        omega
      rw [hidx]
      exact B.solve_eq_of_prefix ω k _ fun j hj => by
        show (if _ : ((Fin.natAdd n j : Fin (n + n)) : ℕ)
            < ((Fin.natAdd n k : Fin (n + n)) : ℕ) then
          (A.twin B).solve ω (Fin.natAdd n j) else 0) = B.solve ω j
        rw [dif_pos (show ((Fin.natAdd n j : Fin (n + n)) : ℕ)
              < ((Fin.natAdd n k : Fin (n + n)) : ℕ) by
            show n + (j : ℕ) < n + (k : ℕ); omega)]
        exact ih j (by omega)
  exact H ((k : ℕ) + 1) k (Nat.lt_succ_self _)

end Scm

/-- **The counterfactual event** for interventions `A` vs `B` (already
surgered SCMs), harm observables `HA`, `HB` on endogenous tuples, over
the working region `Ω`: harm under `A` AND no harm under `B`, both
worlds read at the same `ω` (`0 ≤ HA ∧ HB < 0`). This shared-`ω` set IS
the counterfactual query's denotation for a query conditioning on
nothing: the abduction step is the identity on the exogenous
measure. -/
def cfEvent {m n : ℕ} (A B : Scm m n) (HA HB : (Fin n → ℝ) → ℝ)
    (Ω : Set (State m)) : Set (State m) :=
  {ω ∈ Ω | 0 ≤ HA (A.solve ω) ∧ HB (B.solve ω) < 0}

/-- **Counterfactual query = single-network query on the twin network**
(Pearl ch. 7, trivial abduction): the counterfactual event is an
ordinary event of the twin SCM — the observables read the A-copy and
B-copy of ONE solved network. This is the license for composing both
worlds against one variable space. -/
theorem cfEvent_eq_twin {m n : ℕ} (A B : Scm m n)
    (HA HB : (Fin n → ℝ) → ℝ) (Ω : Set (State m)) :
    cfEvent A B HA HB Ω
      = {ω ∈ Ω |
          0 ≤ HA (fun j => (A.twin B).solve ω (Fin.castAdd n j)) ∧
          HB (fun j => (A.twin B).solve ω (Fin.natAdd n j)) < 0} := by
  ext ω
  simp only [cfEvent, Set.mem_setOf_eq,
    Scm.twin_solve_left, Scm.twin_solve_right]

/-! ## Bridge 2: the uniform product measure on boxes

Boxes are `Set.Icc` in `Fin m → ℝ` (`Set.pi_univ_Icc` identifies this
with the coordinatewise product of intervals); `volume` is the Lebesgue
product measure. Monotonicity and finite (sub)additivity are consumed
from mathlib (`measure_mono`, `measure_biUnion_finset_le`,
`measure_union`); this section states the certificate-facing forms. -/

variable {m : ℕ}

/-- Box volume = product of side lengths (`Real.volume_Icc_pi`). -/
theorem volume_box (a b : State m) :
    volume (Icc a b) = ∏ i, ENNReal.ofReal (b i - a i) :=
  Real.volume_Icc_pi

theorem measurableSet_box (a b : State m) : MeasurableSet (Icc a b) :=
  measurableSet_Icc

/-- **The exclusion cover's upper bound** (certificate class, upper):
if the working region is covered by A-cells (where the A-side sequent
family certifies `HA + δ ≤ 0`: the AI does not harm `v` there), B-cells
(where `δ − HB ≤ 0`: DoNothing harms `v` on all of the cell, so no
point of it satisfies "would not have been harmed"), and charged cells,
then the counterfactual event fits inside the charged family. The
B-side hypothesis is the causal content — dropping it collapses the
argument. -/
theorem exclusion_upper {Ω SA SB SC : Set (State m)}
    {HA HB : State m → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hcover : Ω ⊆ SA ∪ SB ∪ SC)
    (hA : ∀ ω ∈ SA, HA ω + δ ≤ 0)
    (hB : ∀ ω ∈ SB, δ - HB ω ≤ 0) :
    volume {ω ∈ Ω | 0 ≤ HA ω ∧ HB ω < 0} ≤ volume SC := by
  refine measure_mono fun ω hω => ?_
  obtain ⟨hΩ, hHA, hHB⟩ := hω
  rcases hcover hΩ with (hA' | hB') | hC'
  · exact absurd (hA ω hA') (by simp only [not_le]; linarith)
  · exact absurd (hB ω hB') (by simp only [not_le]; linarith)
  · exact hC'

/-- The exclusion bound with the charged family as boxes: monotonicity
+ finite subadditivity — `P[E_v] · vol(Ω) ≤ Σ charged-cell volumes` in
measure form. -/
theorem exclusion_upper_boxes {ι : Type*} {Ω SA SB : Set (State m)}
    {HA HB : State m → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (C : Finset ι) (a b : ι → State m)
    (hcover : Ω ⊆ SA ∪ SB ∪ ⋃ i ∈ C, Icc (a i) (b i))
    (hA : ∀ ω ∈ SA, HA ω + δ ≤ 0)
    (hB : ∀ ω ∈ SB, δ - HB ω ≤ 0) :
    volume {ω ∈ Ω | 0 ≤ HA ω ∧ HB ω < 0}
      ≤ ∑ i ∈ C, ∏ j, ENNReal.ofReal (b i j - a i j) := by
  refine (exclusion_upper hδ hcover hA hB).trans
    ((measure_biUnion_finset_le _ _).trans_eq ?_)
  exact Finset.sum_congr rfl fun i _ => volume_box _ _

/-- **The empty-charged case** — the guard controller's certificate
shape: every cell certified A-side or B-side means the
counterfactual-harm event is null (`P[E_v] = 0`, the flagship bound
holding with room to spare). -/
theorem exclusion_zero {Ω SA SB : Set (State m)}
    {HA HB : State m → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hcover : Ω ⊆ SA ∪ SB)
    (hA : ∀ ω ∈ SA, HA ω + δ ≤ 0)
    (hB : ∀ ω ∈ SB, δ - HB ω ≤ 0) :
    volume {ω ∈ Ω | 0 ≤ HA ω ∧ HB ω < 0} = 0 := by
  have h := exclusion_upper (SC := (∅ : Set (State m))) hδ
    (fun ω hω => by
      rcases hcover hω with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inl (Or.inr h')) hA hB
  simpa using h

/-- **The inner-box lower bound** (certificate class, lower): a box on
which the harm-side sequent (`δ − HA ≤ 0`, so harm under the AI) and
the safe-side sequent (`HB + δ ≤ 0`, so strictly no harm under
DoNothing) both certify lies inside the counterfactual event —
monotonicity gives `vol(box) ≤ P[E_v] · vol(Ω)` in measure form. This
is what makes violation *certifiable*, not merely non-certifiable. -/
theorem inner_lower {Ω : Set (State m)} {HA HB : State m → ℝ} {δ : ℝ}
    (hδ : 0 < δ) {a b : State m} (hsub : Icc a b ⊆ Ω)
    (hh : ∀ ω ∈ Icc a b, δ - HA ω ≤ 0)
    (hs : ∀ ω ∈ Icc a b, HB ω + δ ≤ 0) :
    ∏ j, ENNReal.ofReal (b j - a j)
      ≤ volume {ω ∈ Ω | 0 ≤ HA ω ∧ HB ω < 0} := by
  rw [← volume_box a b]
  exact measure_mono fun ω hω =>
    ⟨hsub hω, by linarith [hh ω hω], by linarith [hs ω hω]⟩

/-- Two disjoint inner boxes add — additivity of the box measure (the
two-box lower-bound shape of the violation bracket). -/
theorem inner_lower_pair {Ω : Set (State m)} {HA HB : State m → ℝ}
    {δ : ℝ} (hδ : 0 < δ) {a₁ b₁ a₂ b₂ : State m}
    (hd : Disjoint (Icc a₁ b₁) (Icc a₂ b₂))
    (hsub₁ : Icc a₁ b₁ ⊆ Ω) (hsub₂ : Icc a₂ b₂ ⊆ Ω)
    (hh₁ : ∀ ω ∈ Icc a₁ b₁, δ - HA ω ≤ 0)
    (hs₁ : ∀ ω ∈ Icc a₁ b₁, HB ω + δ ≤ 0)
    (hh₂ : ∀ ω ∈ Icc a₂ b₂, δ - HA ω ≤ 0)
    (hs₂ : ∀ ω ∈ Icc a₂ b₂, HB ω + δ ≤ 0) :
    (∏ j, ENNReal.ofReal (b₁ j - a₁ j))
        + ∏ j, ENNReal.ofReal (b₂ j - a₂ j)
      ≤ volume {ω ∈ Ω | 0 ≤ HA ω ∧ HB ω < 0} := by
  rw [← volume_box a₁ b₁, ← volume_box a₂ b₂,
    ← measure_union hd (measurableSet_box a₂ b₂)]
  refine measure_mono fun ω hω => ?_
  rcases hω with hω | hω
  · exact ⟨hsub₁ hω, by linarith [hh₁ ω hω], by linarith [hs₁ ω hω]⟩
  · exact ⟨hsub₂ hω, by linarith [hh₂ ω hω], by linarith [hs₂ ω hω]⟩

/-- **The decoupling probe's Fubini clause**: under the
independent-worlds PRODUCT measure the joint factors exactly — the
arithmetic that shared-`ω` counterfactual coupling refuses. (The
certified probe prices the difference: the guard controller's
counterfactual-harm probability is `0` under the coupling and certified
`≥ 1/2048` under this product misreading.) -/
theorem decoupling_product (s t : Set (State m)) :
    volume (s ×ˢ t) = volume s * volume t := by
  show (volume : Measure (State m)).prod volume (s ×ˢ t) = _
  exact Measure.prod_prod s t

/-! ## Bridge 3: the union bound over victims -/

/-- The specification's `∃ v : V` step: finitely many victims,
harm-anywhere bounded by the sum of per-victim bounds. -/
theorem victims_union_bound {V : Type*} [Fintype V]
    (E : V → Set (State m)) :
    volume (⋃ v, E v) ≤ ∑ v, volume (E v) :=
  (measure_iUnion_le E).trans (le_of_eq (tsum_fintype _))

/-- **The composed flagship shape** (two victims, as the crossing has):
the counterfactual-harm-to-anyone event, bounded by the two exclusion
covers' charged volumes via the union bound — the programme thesis's
counterfactual-harm bound (its p. 7) in certificate form. -/
theorem p7_bound {Ω SAP SBP SCP SAC SBC SCC : Set (State m)}
    {HPa HPb HCa HCb : State m → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hcoverP : Ω ⊆ SAP ∪ SBP ∪ SCP)
    (hAP : ∀ ω ∈ SAP, HPa ω + δ ≤ 0)
    (hBP : ∀ ω ∈ SBP, δ - HPb ω ≤ 0)
    (hcoverC : Ω ⊆ SAC ∪ SBC ∪ SCC)
    (hAC : ∀ ω ∈ SAC, HCa ω + δ ≤ 0)
    (hBC : ∀ ω ∈ SBC, δ - HCb ω ≤ 0) :
    volume {ω ∈ Ω | (0 ≤ HPa ω ∧ HPb ω < 0) ∨ (0 ≤ HCa ω ∧ HCb ω < 0)}
      ≤ volume SCP + volume SCC := by
  have hsplit :
      {ω ∈ Ω | (0 ≤ HPa ω ∧ HPb ω < 0) ∨ (0 ≤ HCa ω ∧ HCb ω < 0)}
        ⊆ {ω ∈ Ω | 0 ≤ HPa ω ∧ HPb ω < 0}
          ∪ {ω ∈ Ω | 0 ≤ HCa ω ∧ HCb ω < 0} := by
    rintro ω ⟨hΩ, hor⟩
    exact hor.imp (fun h => ⟨hΩ, h⟩) (fun h => ⟨hΩ, h⟩)
  refine ((measure_mono hsplit).trans (measure_union_le _ _)).trans ?_
  exact add_le_add (exclusion_upper hδ hcoverP hAP hBP)
    (exclusion_upper hδ hcoverC hAC hBC)

/-- **The flagship sentence for the guard verdict**: both victims'
covers certify with empty charged families ⟹ the counterfactual-harm
probability is `0 < 10⁻⁴` — the programme thesis's own threshold, met
with certificate. -/
theorem p7_zero_lt {Ω SAP SBP SAC SBC : Set (State m)}
    {HPa HPb HCa HCb : State m → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hcoverP : Ω ⊆ SAP ∪ SBP)
    (hAP : ∀ ω ∈ SAP, HPa ω + δ ≤ 0)
    (hBP : ∀ ω ∈ SBP, δ - HPb ω ≤ 0)
    (hcoverC : Ω ⊆ SAC ∪ SBC)
    (hAC : ∀ ω ∈ SAC, HCa ω + δ ≤ 0)
    (hBC : ∀ ω ∈ SBC, δ - HCb ω ≤ 0) :
    volume {ω ∈ Ω | (0 ≤ HPa ω ∧ HPb ω < 0) ∨ (0 ≤ HCa ω ∧ HCb ω < 0)}
      < ENNReal.ofReal (1 / 10000) := by
  have hP := exclusion_zero hδ hcoverP hAP hBP
  have hC := exclusion_zero hδ hcoverC hAC hBC
  have hsplit :
      {ω ∈ Ω | (0 ≤ HPa ω ∧ HPb ω < 0) ∨ (0 ≤ HCa ω ∧ HCb ω < 0)}
        ⊆ {ω ∈ Ω | 0 ≤ HPa ω ∧ HPb ω < 0}
          ∪ {ω ∈ Ω | 0 ≤ HCa ω ∧ HCb ω < 0} := by
    rintro ω ⟨hΩ, hor⟩
    exact hor.imp (fun h => ⟨hΩ, h⟩) (fun h => ⟨hΩ, h⟩)
  have h0 : volume {ω ∈ Ω |
      (0 ≤ HPa ω ∧ HPb ω < 0) ∨ (0 ≤ HCa ω ∧ HCb ω < 0)} = 0 := by
    have h : volume {ω ∈ Ω |
          (0 ≤ HPa ω ∧ HPb ω < 0) ∨ (0 ≤ HCa ω ∧ HCb ω < 0)}
        ≤ volume {ω ∈ Ω | 0 ≤ HPa ω ∧ HPb ω < 0}
          + volume {ω ∈ Ω | 0 ≤ HCa ω ∧ HCb ω < 0} :=
      (measure_mono hsplit).trans (measure_union_le _ _)
    rw [hP, hC, add_zero] at h
    simpa using h
  rw [h0]
  exact ENNReal.ofReal_pos.mpr (by norm_num)

/-! ## The worked instance (drift alarms)

The crossing example certified in the modelling chapter (`sec:mt-scm`):
five structural equations, with the certificate corpus's landmark
values machine-checked — any divergence between the composed
polynomials the certificates cite and `Scm.solve` fails elaboration
here. Variable order: `x0, u, x1, hp, hc` (topological); bands:
pedestrian `[1/2, 5/4]`, cyclist `[-2, -9/8]`. -/

/-- The crossing's mechanisms, by endogenous index (the `u` default is
the guard policy, as deployed; the queries only ever use `u` under
intervention). Index ≥ 5 is junk (never reached at `Fin 5`). -/
noncomputable def crossingMech : ℕ → State 2 → (Fin 5 → ℝ) → ℝ
  | 0, ω, _ => ω 0 / 2
  | 1, _, v => -(4 / 5) * v 0 + (1 / 10) * v 0 ^ 2 - 1 / 20
  | 2, ω, v => v 0 + v 1 + ω 1 / 2
  | 3, _, v => (v 2 - 1 / 2) * (5 / 4 - v 2)
  | 4, _, v => (v 2 + 2) * (-(9 / 8) - v 2)
  | _, _, _ => 0

/-- The crossing SCM (the worked instance). -/
noncomputable def crossing : Scm 2 5 where
  mech k := crossingMech (k : ℕ)
  lower k ω v w h := by
    rcases k with ⟨kv, hk⟩
    match kv, hk with
    | 0, hk => rfl
    | 1, hk =>
      show crossingMech 1 ω v = crossingMech 1 ω w
      simp only [crossingMech]
      rw [h 0 (show (0 : ℕ) < 1 by decide)]
    | 2, hk =>
      show crossingMech 2 ω v = crossingMech 2 ω w
      simp only [crossingMech]
      rw [h 0 (show (0 : ℕ) < 2 by decide),
        h 1 (show (1 : ℕ) < 2 by decide)]
    | 3, hk =>
      show crossingMech 3 ω v = crossingMech 3 ω w
      simp only [crossingMech]
      rw [h 2 (show (2 : ℕ) < 3 by decide)]
    | 4, hk =>
      show crossingMech 4 ω v = crossingMech 4 ω w
      simp only [crossingMech]
      rw [h 2 (show (2 : ℕ) < 4 by decide)]

/-- guard: `U = -(4/5)·x0 + (1/10)·x0² − 1/20`. -/
noncomputable def guardPolicy : State 2 → (Fin 5 → ℝ) → ℝ :=
  fun _ v => -(4 / 5) * v 0 + (1 / 10) * v 0 ^ 2 - 1 / 20

theorem guardPolicy_lower : ∀ (ω : State 2) (v w : Fin 5 → ℝ),
    v 0 = w 0 → guardPolicy ω v = guardPolicy ω w := by
  intro ω v w h
  simp only [guardPolicy, h]

/-- flinch: `U = -2·x0 − (1/2)·x0² − 1/4`. -/
noncomputable def flinchPolicy : State 2 → (Fin 5 → ℝ) → ℝ :=
  fun _ v => -2 * v 0 - (1 / 2) * v 0 ^ 2 - 1 / 4

theorem flinchPolicy_lower : ∀ (ω : State 2) (v w : Fin 5 → ℝ),
    v 0 = w 0 → flinchPolicy ω v = flinchPolicy ω w := by
  intro ω v w h
  simp only [flinchPolicy, h]

/-- DoNothing: `U = 0`. -/
def doNothingPolicy : State 2 → (Fin 5 → ℝ) → ℝ := fun _ _ => 0

theorem doNothingPolicy_lower : ∀ (ω : State 2) (v w : Fin 5 → ℝ),
    v 0 = w 0 → doNothingPolicy ω v = doNothingPolicy ω w := by
  intro _ _ _ _
  rfl

/-- `do U := π` on the crossing: replace mechanism 1 (the intervention
site). `hπ`: the policy reads only `x0` (coordinate 0). -/
noncomputable def doU (π : State 2 → (Fin 5 → ℝ) → ℝ)
    (hπ : ∀ ω v w, v 0 = w 0 → π ω v = π ω w) : Scm 2 5 where
  mech k := if (k : ℕ) = 1 then π else crossing.mech k
  lower k ω v w h := by
    by_cases hk : (k : ℕ) = 1
    · rw [if_pos hk]
      exact hπ ω v w (h 0 (show (0 : ℕ) < (k : ℕ) by omega))
    · rw [if_neg hk]
      exact crossing.lower k ω v w h

/-- Pearl consistency ON the instance: `do U := guard` is the identity
surgery, since guard IS the deployed default. -/
theorem doU_guard_eq : doU guardPolicy guardPolicy_lower = crossing := by
  refine Scm.ext_mech (funext fun k => ?_)
  by_cases hk : (k : ℕ) = 1
  · show (if (k : ℕ) = 1 then guardPolicy else crossing.mech k)
        = crossing.mech k
    rw [if_pos hk]
    show guardPolicy = crossingMech (k : ℕ)
    rw [hk]
    rfl
  · show (if (k : ℕ) = 1 then guardPolicy else crossing.mech k)
        = crossing.mech k
    rw [if_neg hk]

section SolvePins

variable (ω : State 2)

private theorem doU_solve_x0 (π : State 2 → (Fin 5 → ℝ) → ℝ)
    (hπ : ∀ ω v w, v 0 = w 0 → π ω v = π ω w) :
    (doU π hπ).solve ω 0 = ω 0 / 2 := by
  rw [Scm.solve_eq]
  rfl

private theorem doU_solve_u (π : State 2 → (Fin 5 → ℝ) → ℝ)
    (hπ : ∀ ω v w, v 0 = w 0 → π ω v = π ω w) :
    (doU π hπ).solve ω 1
      = π ω fun j => if (j : ℕ) = 0 then ω 0 / 2 else 0 := by
  have hv : ∀ j : Fin 5, (j : ℕ) < ((1 : Fin 5) : ℕ) →
      (fun j : Fin 5 => if (j : ℕ) = 0 then ω 0 / 2 else 0) j
        = (doU π hπ).solve ω j := by
    intro j hj
    have e1 : ((1 : Fin 5) : ℕ) = 1 := rfl
    have e0 : ((0 : Fin 5) : ℕ) = 0 := rfl
    have hj0 : j = 0 := Fin.ext (by omega)
    subst hj0
    show (if ((0 : Fin 5) : ℕ) = 0 then ω 0 / 2 else 0)
        = (doU π hπ).solve ω 0
    rw [if_pos e0]
    exact (doU_solve_x0 ω π hπ).symm
  rw [← Scm.solve_eq_of_prefix (doU π hπ) ω 1 _ hv]
  rfl

private theorem doU_solve_x1 (π : State 2 → (Fin 5 → ℝ) → ℝ)
    (hπ : ∀ ω v w, v 0 = w 0 → π ω v = π ω w) :
    (doU π hπ).solve ω 2
      = ω 0 / 2 + (π ω fun j => if (j : ℕ) = 0 then ω 0 / 2 else 0)
          + ω 1 / 2 := by
  have hv : ∀ j : Fin 5, (j : ℕ) < ((2 : Fin 5) : ℕ) →
      (fun j : Fin 5 => if (j : ℕ) = 0 then ω 0 / 2 else
        if (j : ℕ) = 1 then
          π ω fun j => if (j : ℕ) = 0 then ω 0 / 2 else 0
        else 0) j
        = (doU π hπ).solve ω j := by
    intro j hj
    have e2 : ((2 : Fin 5) : ℕ) = 2 := rfl
    have e1 : ((1 : Fin 5) : ℕ) = 1 := rfl
    have e0 : ((0 : Fin 5) : ℕ) = 0 := rfl
    have hj01 : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
    rcases hj01 with h0 | h1
    · have hj0 : j = 0 := Fin.ext (by omega)
      subst hj0
      show (if ((0 : Fin 5) : ℕ) = 0 then ω 0 / 2 else
          if ((0 : Fin 5) : ℕ) = 1 then
            π ω fun j => if (j : ℕ) = 0 then ω 0 / 2 else 0
          else 0)
          = (doU π hπ).solve ω 0
      rw [if_pos e0]
      exact (doU_solve_x0 ω π hπ).symm
    · have hj1 : j = 1 := Fin.ext (by omega)
      subst hj1
      show (if ((1 : Fin 5) : ℕ) = 0 then ω 0 / 2 else
          if ((1 : Fin 5) : ℕ) = 1 then
            π ω fun j => if (j : ℕ) = 0 then ω 0 / 2 else 0
          else 0)
          = (doU π hπ).solve ω 1
      rw [if_neg (show ¬ ((1 : Fin 5) : ℕ) = 0 by decide), if_pos e1]
      exact (doU_solve_u ω π hπ).symm
  rw [← Scm.solve_eq_of_prefix (doU π hπ) ω 2 _ hv]
  rfl

private theorem doU_solve_hp (π : State 2 → (Fin 5 → ℝ) → ℝ)
    (hπ : ∀ ω v w, v 0 = w 0 → π ω v = π ω w) :
    (doU π hπ).solve ω 3
      = ((doU π hπ).solve ω 2 - 1 / 2)
          * (5 / 4 - (doU π hπ).solve ω 2) := by
  rw [Scm.solve_eq]
  show ((if _ : ((2 : Fin 5) : ℕ) < ((3 : Fin 5) : ℕ) then
        (doU π hπ).solve ω 2 else 0) - 1 / 2)
      * (5 / 4 - (if _ : ((2 : Fin 5) : ℕ) < ((3 : Fin 5) : ℕ) then
        (doU π hπ).solve ω 2 else 0))
      = ((doU π hπ).solve ω 2 - 1 / 2)
          * (5 / 4 - (doU π hπ).solve ω 2)
  rw [dif_pos (by decide : ((2 : Fin 5) : ℕ) < ((3 : Fin 5) : ℕ))]

/-- landmark pin: guard `x1_A = ω₁/10 + ω₁²/40 − 1/20 + ω₂/2`. -/
theorem guard_x1 :
    (doU guardPolicy guardPolicy_lower).solve ω 2
      = ω 0 / 10 + (ω 0) ^ 2 / 40 - 1 / 20 + ω 1 / 2 := by
  rw [doU_solve_x1]
  show ω 0 / 2
      + (-(4 / 5) * (ω 0 / 2) + (1 / 10) * (ω 0 / 2) ^ 2 - 1 / 20)
      + ω 1 / 2
      = ω 0 / 10 + (ω 0) ^ 2 / 40 - 1 / 20 + ω 1 / 2
  ring

/-- landmark pin: DoNothing `x1_B = ω₁/2 + ω₂/2`. -/
theorem donothing_x1 :
    (doU doNothingPolicy doNothingPolicy_lower).solve ω 2
      = ω 0 / 2 + ω 1 / 2 := by
  rw [doU_solve_x1]
  show ω 0 / 2 + 0 + ω 1 / 2 = ω 0 / 2 + ω 1 / 2
  ring

/-- landmark pin: flinch `x1_A = −ω₁/2 − ω₁²/8 − 1/4 + ω₂/2`. -/
theorem flinch_x1 :
    (doU flinchPolicy flinchPolicy_lower).solve ω 2
      = -(ω 0) / 2 - (ω 0) ^ 2 / 8 - 1 / 4 + ω 1 / 2 := by
  rw [doU_solve_x1]
  show ω 0 / 2 + (-2 * (ω 0 / 2) - (1 / 2) * (ω 0 / 2) ^ 2 - 1 / 4)
      + ω 1 / 2
      = -(ω 0) / 2 - (ω 0) ^ 2 / 8 - 1 / 4 + ω 1 / 2
  ring

end SolvePins

/-- landmark pin, the counterfactual-harm witness point `ω* = (−1, 1)`:
the flinch controller HARMS the pedestrian there (`HP_A = 5/64 > 0`)… -/
theorem flinch_harmP_witness :
    (doU flinchPolicy flinchPolicy_lower).solve ![(-1 : ℝ), 1] 3
      = 5 / 64 := by
  rw [doU_solve_hp, flinch_x1]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- …while DoNothing was SAFE at the same `ω*` (`HP_B = −5/8 < 0`) —
the conjunction the counterfactual certificate is about, at one exact
point. -/
theorem donothing_harmP_witness :
    (doU doNothingPolicy doNothingPolicy_lower).solve ![(-1 : ℝ), 1] 3
      = -(5 / 8) := by
  rw [doU_solve_hp, donothing_x1]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-! Volume pins (the certificate corpus's box constants: `vol(Ω) = 4`,
the flinch inner boxes `1/64` and `1/32`, the decoupling harm box
`1/128`). -/

/-- `vol(Ω) = 4` for `Ω = [−1,1]²`. -/
theorem volume_omega_box :
    volume (Icc ![(-1 : ℝ), -1] ![(1 : ℝ), 1]) = 4 := by
  rw [volume_box, Fin.prod_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    ← ENNReal.ofReal_mul]

/-- The flinch pedestrian inner box `[−1,−7/8] × [7/8,1]`, volume
`1/64`. -/
theorem volume_flinch_inner_P :
    volume (Icc ![(-1 : ℝ), 7 / 8] ![(-(7 : ℝ) / 8), 1])
      = ENNReal.ofReal (1 / 64) := by
  rw [volume_box, Fin.prod_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    ← ENNReal.ofReal_mul]

/-- The flinch cyclist inner box `[7/8,1] × [−1,−3/4]`, volume
`1/32`. -/
theorem volume_flinch_inner_C :
    volume (Icc ![(7 : ℝ) / 8, -1] ![(1 : ℝ), -(3 / 4)])
      = ENNReal.ofReal (1 / 32) := by
  rw [volume_box, Fin.prod_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    ← ENNReal.ofReal_mul]

/-- The decoupling probe's harm box `[7/8,1] × [15/16,1]`, volume
`1/128` (priced through `decoupling_product`). -/
theorem volume_dec_inner_harm :
    volume (Icc ![(7 : ℝ) / 8, 15 / 16] ![(1 : ℝ), 1])
      = ENNReal.ofReal (1 / 128) := by
  rw [volume_box, Fin.prod_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    ← ENNReal.ofReal_mul]

end ScmTwin

end Qtsl

/-! axiom receipts: expected `[propext, Classical.choice, Quot.sound]`
or fewer, no sorryAx — every named bridge is proven outright. -/

#print axioms Qtsl.ScmTwin.Scm.surgery_self
#print axioms Qtsl.ScmTwin.Scm.solve_surgery_self
#print axioms Qtsl.ScmTwin.Scm.twin_solve_left
#print axioms Qtsl.ScmTwin.Scm.twin_solve_right
#print axioms Qtsl.ScmTwin.cfEvent_eq_twin
#print axioms Qtsl.ScmTwin.volume_box
#print axioms Qtsl.ScmTwin.exclusion_upper
#print axioms Qtsl.ScmTwin.exclusion_upper_boxes
#print axioms Qtsl.ScmTwin.exclusion_zero
#print axioms Qtsl.ScmTwin.inner_lower
#print axioms Qtsl.ScmTwin.inner_lower_pair
#print axioms Qtsl.ScmTwin.decoupling_product
#print axioms Qtsl.ScmTwin.victims_union_bound
#print axioms Qtsl.ScmTwin.p7_bound
#print axioms Qtsl.ScmTwin.p7_zero_lt
#print axioms Qtsl.ScmTwin.doU_guard_eq
#print axioms Qtsl.ScmTwin.guard_x1
#print axioms Qtsl.ScmTwin.donothing_x1
#print axioms Qtsl.ScmTwin.flinch_x1
#print axioms Qtsl.ScmTwin.flinch_harmP_witness
#print axioms Qtsl.ScmTwin.donothing_harmP_witness
#print axioms Qtsl.ScmTwin.volume_omega_box
#print axioms Qtsl.ScmTwin.volume_flinch_inner_P
#print axioms Qtsl.ScmTwin.volume_flinch_inner_C
#print axioms Qtsl.ScmTwin.volume_dec_inner_harm
