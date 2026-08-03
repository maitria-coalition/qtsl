import QtslAux.Imprecise.PenaltyEnvelope
import QtslAux.Imprecise.Compose
import Mathlib.Data.Fintype.BigOperators

/-! # Penalty kernels compose: the intertwining square, exact at finite support

An **imprecise (penalty) kernel** from `X` to `Y` at the finite stratum is,
per state, a family of laws with signed costs — the data of
`Imprecise.PenaltyEnvelope`, fibred over the source.  This module gives the
composition law and its keystone:

* `penCompCost` — the composite cost of a two-stage member `(i, σ)`: the
  first-stage cost **plus the first-stage expectation of the selected
  second-stage costs**.  Penalties integrate along the record: the
  per-consultation (fresh) reading of imprecision is the *definition* of
  composition here, and the mutants below show the aggregation shape is
  forced, not chosen.
* `penUpperE_compFam` / `penLowerE_compFam` — **the intertwining square**:
  the tilted envelope of the composite presentation equals the Kleisli
  (backward, value-level) composite of the tilted envelopes.  Law-level
  composition (infimal projection of chained penalties along
  disintegrations) and value-level composition agree *exactly*: at finite
  support the ε-optimal measurable selection of the general theory is exact
  selection (`Finset.exists_mem_eq_sup'` + `choose`).  The zero-cost shadow
  (`penUpperE_compFam_zero_recovers_tower`) is the credal tower law of
  `Imprecise.Compose`; the square is its strict generalisation to the convex
  tier.
* `penUpperE_le_of_subfamily` and the **once-drawn diagonal**: composing with
  a *shared* index (`diagFam` — one adversary choice read by both stages,
  the crystal) is dominated by the fresh composite
  (`penUpperE_diag_le_compFam`) and strictly below it in general
  (`Mutants.diag_lt_perFiring`): the filtration index of an imprecise wire
  is semantic content, and backward recursion prices only the fresh reading.
* Unit laws (`penUpperE_compFam_dirac_left/right`): the precise Dirac kernel
  is the identity of the composition at the prevision level.
* Acceptance skeletons: `precise_compFam_penUpperE` (+ the upper-equals-lower
  corollary) — all-singleton families with zero costs compose to the precise
  `compProd` expectation, the Everdij–Blom corner; `dirac_compFam_penUpperE`
  — Dirac families with zero costs compose to the nested max over reached
  states, the vanilla-net (reachability/envelope-union) corner.

Associativity note: both bracketings of a three-stage composite rewrite, by
this square applied twice, to the same nested value-level expression, so
composition is associative *at the prevision level*; presentation-level
index bookkeeping is deliberately not canonicalised.
-/

namespace Qtsl.Imprecise

open Finset

section PenCompose

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {κ : X → Type*} [∀ x, Fintype (κ x)] [∀ x, Nonempty (κ x)]

/-- The composite cost of a two-stage member: first-stage cost plus the
first-stage **expectation** of the selected second-stage costs.  The
expectation weighting is forced by the intertwining square (see the mutants
for the failure of the unweighted and sup-aggregated alternatives): an
unreachable state's penalty must not price the composite. -/
def penCompCost (M : ι → FinPMF X) (c : ι → ℚ) (d : (x : X) → κ x → ℚ) :
    ι × ((x : X) → κ x) → ℚ :=
  fun iσ => c iσ.1 + (M iσ.1).exp fun x => d x (iσ.2 x)

/-- **The intertwining square, upper face**: the tilted envelope of the
composite presentation is the Kleisli composite of the tilted envelopes.
Exact at finite support — the ε-optimal selection of the measurable theory
is exact selection here. -/
theorem penUpperE_compFam (M : ι → FinPMF X) (c : ι → ℚ)
    (K : (x : X) → κ x → FinPMF Y) (d : (x : X) → κ x → ℚ)
    (f : X × Y → ℚ) :
    penUpperE (compFam M K) (penCompCost M c d) f
      = penUpperE M c fun x => penUpperE (K x) (d x) fun y => f (x, y) := by
  apply le_antisymm
  · refine penUpperE_le ?_
    rintro ⟨i, σ⟩
    have hexp : (compFam M K (i, σ)).exp f
        = (M i).exp fun x => (K x (σ x)).exp fun y => f (x, y) := by
      rw [show compFam M K (i, σ) = (M i).compProd fun x => K x (σ x) from rfl,
        FinPMF.exp_compProd]
    have hcost : penCompCost M c d (i, σ)
        = c i + (M i).exp fun x => d x (σ x) := rfl
    rw [hexp, hcost]
    have hsub := (M i).exp_sub
      (fun x => (K x (σ x)).exp fun y => f (x, y)) (fun x => d x (σ x))
    have hmono : (M i).exp (fun x =>
          (K x (σ x)).exp (fun y => f (x, y)) - d x (σ x))
        ≤ (M i).exp fun x => penUpperE (K x) (d x) fun y => f (x, y) :=
      (M i).exp_mono fun x =>
        exp_sub_le_penUpperE (K x) (d x) (fun y => f (x, y)) (σ x)
    have houter := exp_sub_le_penUpperE M c
      (fun x => penUpperE (K x) (d x) fun y => f (x, y)) i
    linarith
  · obtain ⟨i₀, hi₀⟩ := exists_eq_penUpperE M c
      fun x => penUpperE (K x) (d x) fun y => f (x, y)
    choose σ hσ using fun x =>
      exists_eq_penUpperE (K x) (d x) fun y => f (x, y)
    have hcongr : (M i₀).exp
          (fun x => penUpperE (K x) (d x) fun y => f (x, y))
        = (M i₀).exp fun x =>
            (K x (σ x)).exp (fun y => f (x, y)) - d x (σ x) :=
      (M i₀).exp_congr fun x => hσ x
    have hsub := (M i₀).exp_sub
      (fun x => (K x (σ x)).exp fun y => f (x, y)) (fun x => d x (σ x))
    have hmem := exp_sub_le_penUpperE (compFam M K) (penCompCost M c d)
      f (i₀, σ)
    have hexp : (compFam M K (i₀, σ)).exp f
        = (M i₀).exp fun x => (K x (σ x)).exp fun y => f (x, y) := by
      rw [show compFam M K (i₀, σ) = (M i₀).compProd fun x => K x (σ x)
        from rfl, FinPMF.exp_compProd]
    have hcost : penCompCost M c d (i₀, σ)
        = c i₀ + (M i₀).exp fun x => d x (σ x) := rfl
    rw [hexp, hcost] at hmem
    rw [hi₀, hcongr, hsub]
    linarith

/-- **The intertwining square, lower face** (same cost aggregation; the
polarity lives in the envelope, not the record). -/
theorem penLowerE_compFam (M : ι → FinPMF X) (c : ι → ℚ)
    (K : (x : X) → κ x → FinPMF Y) (d : (x : X) → κ x → ℚ)
    (f : X × Y → ℚ) :
    penLowerE (compFam M K) (penCompCost M c d) f
      = penLowerE M c fun x => penLowerE (K x) (d x) fun y => f (x, y) := by
  apply le_antisymm
  · obtain ⟨i₀, hi₀⟩ := exists_eq_penLowerE M c
      fun x => penLowerE (K x) (d x) fun y => f (x, y)
    choose σ hσ using fun x =>
      exists_eq_penLowerE (K x) (d x) fun y => f (x, y)
    have hcongr : (M i₀).exp
          (fun x => penLowerE (K x) (d x) fun y => f (x, y))
        = (M i₀).exp fun x =>
            (K x (σ x)).exp (fun y => f (x, y)) + d x (σ x) :=
      (M i₀).exp_congr fun x => hσ x
    have hadd := (M i₀).exp_add
      (fun x => (K x (σ x)).exp fun y => f (x, y)) (fun x => d x (σ x))
    have hmem := penLowerE_le_exp_add (compFam M K) (penCompCost M c d)
      f (i₀, σ)
    have hexp : (compFam M K (i₀, σ)).exp f
        = (M i₀).exp fun x => (K x (σ x)).exp fun y => f (x, y) := by
      rw [show compFam M K (i₀, σ) = (M i₀).compProd fun x => K x (σ x)
        from rfl, FinPMF.exp_compProd]
    have hcost : penCompCost M c d (i₀, σ)
        = c i₀ + (M i₀).exp fun x => d x (σ x) := rfl
    rw [hexp, hcost] at hmem
    rw [hi₀, hcongr, hadd]
    linarith
  · refine le_penLowerE ?_
    rintro ⟨i, σ⟩
    have hexp : (compFam M K (i, σ)).exp f
        = (M i).exp fun x => (K x (σ x)).exp fun y => f (x, y) := by
      rw [show compFam M K (i, σ) = (M i).compProd fun x => K x (σ x) from rfl,
        FinPMF.exp_compProd]
    have hcost : penCompCost M c d (i, σ)
        = c i + (M i).exp fun x => d x (σ x) := rfl
    rw [hexp, hcost]
    have hadd := (M i).exp_add
      (fun x => (K x (σ x)).exp fun y => f (x, y)) (fun x => d x (σ x))
    have hmono : (M i).exp (fun x => penLowerE (K x) (d x) fun y => f (x, y))
        ≤ (M i).exp fun x =>
            (K x (σ x)).exp (fun y => f (x, y)) + d x (σ x) :=
      (M i).exp_mono fun x =>
        penLowerE_le_exp_add (K x) (d x) (fun y => f (x, y)) (σ x)
    have houter := penLowerE_le_exp_add M c
      (fun x => penLowerE (K x) (d x) fun y => f (x, y)) i
    linarith

omit [DecidableEq X] [Fintype ι] [Nonempty ι] [(x : X) → Fintype (κ x)]
  [∀ (x : X), Nonempty (κ x)] in
/-- Zero costs compose to zero costs. -/
theorem penCompCost_zero (M : ι → FinPMF X) :
    penCompCost M (0 : ι → ℚ) (fun (x : X) (_ : κ x) => (0 : ℚ)) = 0 := by
  funext iσ
  show (0 : ι → ℚ) iσ.1 + (M iσ.1).exp (fun _ => (0 : ℚ)) = 0
  rw [Pi.zero_apply, (M iσ.1).exp_const]
  ring

/-- **The tower law is the zero-cost shadow of the square**: specialising
both stages to walls recovers the credal iterated-envelope law. -/
theorem penUpperE_compFam_zero_recovers_tower (M : ι → FinPMF X)
    (K : (x : X) → κ x → FinPMF Y) (f : X × Y → ℚ) :
    penUpperE (compFam M K)
        (penCompCost M (0 : ι → ℚ) fun (x : X) (_ : κ x) => (0 : ℚ)) f
      = upperE M fun x => upperE (K x) fun y => f (x, y) := by
  rw [penCompCost_zero, penUpperE_zero_cost, upperE_compFam]

end PenCompose

section Subfamily

variable {X : Type*} [Fintype X]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Domination by presentation inclusion: a family whose every member appears
in another family at no greater cost is dominated by it.  (The engine behind
the once-drawn/fresh comparison below.) -/
theorem penUpperE_le_of_subfamily {ι' : Type*} [Fintype ι'] [Nonempty ι']
    {N : ι' → FinPMF X} {cN : ι' → ℚ} {M : ι → FinPMF X} {c : ι → ℚ}
    (h : ∀ i', ∃ i, N i' = M i ∧ c i ≤ cN i') (f : X → ℚ) :
    penUpperE N cN f ≤ penUpperE M c f := by
  refine penUpperE_le fun i' => ?_
  obtain ⟨i, hlaw, hcost⟩ := h i'
  rw [hlaw]
  have := exp_sub_le_penUpperE M c f i
  linarith

end Subfamily

section Diagonal

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {κ : X → Type*} [∀ x, Fintype (κ x)] [∀ x, Nonempty (κ x)]

/-- The **once-drawn** (crystal) composite: one index drawn at time zero and
read by both stages — a time-diagonal coupling, not a fresh product. -/
def diagFam (M : ι → FinPMF X) (L : ι → (x : X) → FinPMF Y) :
    ι → FinPMF (X × Y) :=
  fun i => (M i).compProd (L i)

/-- Costs along the once-drawn composite (same integrate-along-the-record
aggregation; only the index sharing differs). -/
def diagCost (M : ι → FinPMF X) (c : ι → ℚ) (e : ι → X → ℚ) : ι → ℚ :=
  fun i => c i + (M i).exp (e i)

/-- **The crystal is dominated by the fresh composite**: whenever each
once-drawn second stage is available to the fresh composite pointwise at no
greater cost, the once-drawn prevision is below the fresh one.  Strictness
in general is `Mutants.diag_lt_perFiring`. -/
theorem penUpperE_diag_le_compFam (M : ι → FinPMF X) (c : ι → ℚ)
    (L : ι → (x : X) → FinPMF Y) (e : ι → X → ℚ)
    (K : (x : X) → κ x → FinPMF Y) (d : (x : X) → κ x → ℚ)
    (hsel : ∀ i x, ∃ j : κ x, L i x = K x j ∧ d x j ≤ e i x)
    (f : X × Y → ℚ) :
    penUpperE (diagFam M L) (diagCost M c e) f
      ≤ penUpperE (compFam M K) (penCompCost M c d) f := by
  refine penUpperE_le_of_subfamily (fun i => ?_) f
  choose σ hlaw hcost using hsel i
  refine ⟨(i, σ), ?_, ?_⟩
  · show diagFam M L i = compFam M K (i, σ)
    unfold diagFam
    rw [show compFam M K (i, σ) = (M i).compProd fun x => K x (σ x) from rfl]
    congr 1
    funext x
    exact hlaw x
  · show c i + ((M i).exp fun x => d x (σ x)) ≤ c i + (M i).exp (e i)
    have := (M i).exp_mono fun x => hcost x
    linarith

end Diagonal

section Units

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {κ : X → Type*} [∀ x, Fintype (κ x)] [∀ x, Nonempty (κ x)]

/-- Left unit: composing the precise Dirac kernel at `x₀` with a penalty
kernel evaluates the kernel at `x₀` — at the prevision level. -/
theorem penUpperE_compFam_dirac_left (x₀ : X)
    (K : (x : X) → κ x → FinPMF Y) (d : (x : X) → κ x → ℚ)
    (f : X × Y → ℚ) :
    penUpperE (compFam (fun _ : Unit => FinPMF.dirac x₀) K)
        (penCompCost (fun _ : Unit => FinPMF.dirac x₀) 0 d) f
      = penUpperE (K x₀) (d x₀) fun y => f (x₀, y) := by
  rw [penUpperE_compFam, penUpperE_unique, FinPMF.exp_dirac]
  simp

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Right unit: post-composing with the Dirac graph kernel restricts the
gamble to the graph — at the prevision level. -/
theorem penUpperE_compFam_dirac_right (M : ι → FinPMF X) (c : ι → ℚ)
    (f : X × X → ℚ) :
    penUpperE (compFam M fun x => fun _ : Unit => FinPMF.dirac x)
        (penCompCost M c fun (_ : X) (_ : Unit) => (0 : ℚ)) f
      = penUpperE M c fun x => f (x, x) := by
  rw [penUpperE_compFam]
  refine penUpperE_congr fun x => ?_
  rw [penUpperE_unique, FinPMF.exp_dirac]
  simp

end Units

section Precise

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {ι' : Type*} [Fintype ι'] [Unique ι']
variable {κ' : X → Type*} [∀ x, Fintype (κ' x)] [∀ x, Unique (κ' x)]

/-- **The precise corner** (acceptance skeleton for the all-noise face):
singleton families with zero costs compose to the expectation of the
precise two-stage law. -/
theorem precise_compFam_penUpperE (M : ι' → FinPMF X)
    (K : (x : X) → κ' x → FinPMF Y) (f : X × Y → ℚ) :
    penUpperE (compFam M K)
        (penCompCost M (0 : ι' → ℚ) fun (x : X) (_ : κ' x) => (0 : ℚ)) f
      = ((M default).compProd fun x => K x default).exp f := by
  rw [penUpperE_compFam, FinPMF.exp_compProd]
  simp only [penUpperE_unique, Pi.zero_apply, sub_zero]

/-- On the precise corner the two envelopes coincide: imprecision is
genuinely absent, not merely hidden. -/
theorem precise_compFam_upper_eq_lower (M : ι' → FinPMF X)
    (K : (x : X) → κ' x → FinPMF Y) (f : X × Y → ℚ) :
    penUpperE (compFam M K)
        (penCompCost M (0 : ι' → ℚ) fun (x : X) (_ : κ' x) => (0 : ℚ)) f
      = penLowerE (compFam M K)
          (penCompCost M (0 : ι' → ℚ) fun (x : X) (_ : κ' x) => (0 : ℚ)) f := by
  rw [precise_compFam_penUpperE, penLowerE_compFam, FinPMF.exp_compProd]
  simp only [penLowerE_unique, Pi.zero_apply, add_zero]

end Precise

section Reachability

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {κ : X → Type*} [∀ x, Fintype (κ x)] [∀ x, Nonempty (κ x)]

/-- **The possibilistic corner** (acceptance skeleton for the vanilla-net
face): Dirac families with zero costs compose to the nested max over reached
states — jumps are firings, and the composite prevision is classical
reachability of the two-step unrolling. -/
theorem dirac_compFam_penUpperE (a : ι → X) (b : (x : X) → κ x → Y)
    (f : X × Y → ℚ) :
    penUpperE (compFam (fun i => FinPMF.dirac (a i))
        fun x j => FinPMF.dirac (b x j))
        (penCompCost (fun i => FinPMF.dirac (a i)) (0 : ι → ℚ)
          fun (x : X) (_ : κ x) => (0 : ℚ)) f
      = univ.sup' univ_nonempty fun i =>
          univ.sup' univ_nonempty fun j : κ (a i) => f (a i, b (a i) j) := by
  rw [penUpperE_compFam]
  unfold penUpperE
  refine Finset.sup'_congr _ rfl fun i _ => ?_
  simp only [Pi.zero_apply, sub_zero, FinPMF.exp_dirac]

end Reachability

namespace Mutants

open FinPMF

/-- The composite index of the one-member witnesses is a point (provided
locally; the general product instance is not in this import closure). -/
private instance : Unique (Unit × (Bool → Unit)) where
  default := ((), fun _ => ())
  uniq := fun _ => rfl

/-! ### The aggregation shape of `penCompCost` is forced

Two rival cost aggregations, each refuted on a two-point witness, plus the
once-drawn/fresh strict gap.  Shared cast: `Bool` as the mid carrier,
`Unit` as the outcome carrier, the zero gamble, and the cost
`d x = bif x then 0 else 1` charging only the state `false`. -/

/-- Rival aggregation: unweighted sum of selected second-stage costs. -/
def unweightedCost {X : Type*} [Fintype X] {ι : Type*}
    {κ : X → Type*} (c : ι → ℚ) (d : (x : X) → κ x → ℚ) :
    ι × ((x : X) → κ x) → ℚ :=
  fun iσ => c iσ.1 + ∑ x, d x (iσ.2 x)

/-- Rival aggregation: worst selected second-stage cost. -/
def supCost {X : Type*} [Fintype X] [Nonempty X] {ι : Type*}
    {κ : X → Type*} (c : ι → ℚ) (d : (x : X) → κ x → ℚ) :
    ι × ((x : X) → κ x) → ℚ :=
  fun iσ => c iσ.1 + univ.sup' univ_nonempty fun x => d x (iσ.2 x)

/-- The one-member first stage concentrated on `true`. -/
private def Mw : Unit → FinPMF Bool := fun _ => dirac true

/-- The one-member second stage (outcome carrier `Unit`). -/
private def Kw : Bool → Unit → FinPMF Unit := fun _ _ => dirac ()

/-- Second-stage cost charging only the unreached state `false`. -/
private def dw : Bool → Unit → ℚ := fun x _ => bif x then 0 else 1

private def fw : Bool × Unit → ℚ := fun _ => 0

private theorem true_value :
    penUpperE Mw 0 (fun x => penUpperE (Kw x) (dw x) fun y => fw (x, y))
      = 0 := by
  rw [penUpperE_unique]
  simp only [Mw, FinPMF.exp_dirac, Pi.zero_apply, sub_zero]
  rw [penUpperE_unique]
  simp [Kw, dw, fw, FinPMF.exp_dirac]

/-- **M1 (cost-aggregation locus)**: with the unweighted sum, the composite
charges the unreachable state's penalty (`-1`), while the Kleisli composite
prices `0` — the square fails, so the expectation weighting in
`penCompCost` is load-bearing. -/
theorem mutant_unweighted_cost_breaks_square :
    penUpperE (compFam Mw Kw) (unweightedCost 0 dw) fw
      ≠ penUpperE Mw 0 (fun x => penUpperE (Kw x) (dw x) fun y => fw (x, y)) := by
  rw [true_value, penUpperE_unique]
  have hexp : (compFam Mw Kw default).exp fw = 0 := by
    have : ∀ p : Bool × Unit, fw p = 0 := fun _ => rfl
    rw [(compFam Mw Kw default).exp_congr this,
      (compFam Mw Kw default).exp_const]
  rw [hexp]
  have hcost : unweightedCost (0 : Unit → ℚ) dw default = 1 := by
    show (0 : Unit → ℚ) default + ∑ x : Bool, dw x () = 1
    rw [Pi.zero_apply, Fintype.sum_bool]
    norm_num [dw]
  rw [hcost]
  norm_num

/-- The fair-coin first stage (for the sup-aggregation refutation: the
weighting must see the *probabilities*, not just the support). -/
private def coin : FinPMF Bool where
  prob := fun _ => 1 / 2
  nonneg := fun _ => by norm_num
  total := by rw [Fintype.sum_bool]; norm_num

private def Mc : Unit → FinPMF Bool := fun _ => coin

private theorem coin_true_value :
    penUpperE Mc 0 (fun x => penUpperE (Kw x) (dw x) fun y => fw (x, y))
      = -(1 / 2) := by
  rw [penUpperE_unique]
  have hinner : ∀ x : Bool,
      penUpperE (Kw x) (dw x) (fun y => fw (x, y)) = -(dw x ()) := fun x => by
    rw [penUpperE_unique]
    simp [Kw, fw, FinPMF.exp_dirac]
  rw [(Mc default).exp_congr hinner]
  show coin.exp (fun x => -(dw x ())) - (0 : Unit → ℚ) default = -(1/2)
  unfold FinPMF.exp
  rw [Fintype.sum_bool, Pi.zero_apply]
  simp [coin, dw]

/-- **M2 (weighting-shape locus)**: with the worst-case aggregation, a fair
coin over a cheap and a costly state prices the composite at the worst cost
(`-1`) instead of the expected cost (`-1/2`) — the square fails again: the
record integrates, it does not max. -/
theorem mutant_sup_cost_breaks_square :
    penUpperE (compFam Mc Kw) (supCost 0 dw) fw
      ≠ penUpperE Mc 0 (fun x => penUpperE (Kw x) (dw x) fun y => fw (x, y)) := by
  rw [coin_true_value, penUpperE_unique]
  have hexp : (compFam Mc Kw default).exp fw = 0 := by
    have : ∀ p : Bool × Unit, fw p = 0 := fun _ => rfl
    rw [(compFam Mc Kw default).exp_congr this,
      (compFam Mc Kw default).exp_const]
  rw [hexp]
  have hsup : univ.sup' univ_nonempty (fun x : Bool => dw x ()) = 1 := by
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun b _ => ?_
      cases b <;> norm_num [dw]
    · have h := Finset.le_sup' (fun x : Bool => dw x ()) (mem_univ false)
      simp only [dw, Bool.cond_false] at h
      exact h
  have hcost : supCost (0 : Unit → ℚ) dw default = 1 := by
    show (0 : Unit → ℚ) default
        + univ.sup' univ_nonempty (fun x : Bool => dw x ()) = 1
    rw [Pi.zero_apply, hsup]
    ring
  rw [hcost]
  norm_num

/-! ### M3 (freshness locus): the once-drawn/fresh strict gap

The crystal game: the first stage reveals the drawn index, the second stage
either re-chooses freshly (per-firing) or replays the same draw (once-drawn).
The miss gamble scores the discrepancy. -/

private def missGamble : Bool × Bool → ℚ := fun p => if p.1 = p.2 then 0 else 1

private def crystalM : Bool → FinPMF Bool := fun b => dirac b

private def freshK : Bool → Bool → FinPMF Bool := fun _ j => dirac j

private def crystalL : Bool → Bool → FinPMF Bool := fun b _ => dirac b

private theorem missGamble_le_one : ∀ p : Bool × Bool, missGamble p ≤ 1 := by
  intro p
  unfold missGamble
  by_cases h : p.1 = p.2 <;> norm_num [h]

private theorem perFiring_value :
    penUpperE (compFam crystalM freshK)
        (penCompCost crystalM 0 fun (_ : Bool) (_ : Bool) => (0 : ℚ))
        missGamble = 1 := by
  rw [penCompCost_zero, penUpperE_zero_cost]
  apply le_antisymm
  · refine upperE_le fun iσ => ?_
    calc (compFam crystalM freshK iσ).exp missGamble
        ≤ (compFam crystalM freshK iσ).exp fun _ => 1 :=
          (compFam crystalM freshK iσ).exp_mono missGamble_le_one
      _ = 1 := (compFam crystalM freshK iσ).exp_const 1
  · have hmem := exp_le_upperE (compFam crystalM freshK) missGamble
      (true, fun _ => false)
    have hval : (compFam crystalM freshK (true, fun _ => false)).exp missGamble
        = 1 := by
      rw [show compFam crystalM freshK (true, fun _ => false)
          = (crystalM true).compProd fun _ => dirac false from rfl,
        FinPMF.exp_compProd]
      show (dirac true).exp (fun x => (dirac false).exp fun y => missGamble (x, y)) = 1
      rw [FinPMF.exp_dirac, FinPMF.exp_dirac]
      simp [missGamble]
    rw [hval] at hmem
    exact hmem

private theorem onceDrawn_value :
    penUpperE (diagFam crystalM crystalL)
        (diagCost crystalM 0 fun (_ : Bool) (_ : Bool) => (0 : ℚ))
        missGamble = 0 := by
  have hval : ∀ b : Bool,
      (diagFam crystalM crystalL b).exp missGamble = 0 := fun b => by
    show ((crystalM b).compProd (crystalL b)).exp missGamble = 0
    rw [FinPMF.exp_compProd]
    show (dirac b).exp (fun x => (dirac b).exp fun y => missGamble (x, y)) = 0
    rw [FinPMF.exp_dirac, FinPMF.exp_dirac]
    simp [missGamble]
  have hcost : ∀ b : Bool,
      diagCost crystalM 0 (fun (_ : Bool) (_ : Bool) => (0 : ℚ)) b = 0 := by
    intro b
    show (0 : Bool → ℚ) b + (crystalM b).exp (fun _ => (0 : ℚ)) = 0
    rw [Pi.zero_apply, (crystalM b).exp_const]
    ring
  apply le_antisymm
  · refine penUpperE_le fun b => ?_
    rw [hval b, hcost b]
    norm_num
  · have := exp_sub_le_penUpperE (diagFam crystalM crystalL)
      (diagCost crystalM 0 fun (_ : Bool) (_ : Bool) => (0 : ℚ)) missGamble true
    rw [hval true, hcost true] at this
    simpa using this

/-- **M3: the once-drawn (crystal) prevision sits strictly below the fresh
composite** — the filtration index of an imprecise wire is semantic content:
`0 < 1` on the crystal game.  (Kernel-level sibling of the robust-MDP
once-drawn counterexample.) -/
theorem diag_lt_perFiring :
    penUpperE (diagFam crystalM crystalL)
        (diagCost crystalM 0 fun (_ : Bool) (_ : Bool) => (0 : ℚ))
        missGamble
      < penUpperE (compFam crystalM freshK)
          (penCompCost crystalM 0 fun (_ : Bool) (_ : Bool) => (0 : ℚ))
          missGamble := by
  rw [onceDrawn_value, perFiring_value]
  norm_num

end Mutants

end Qtsl.Imprecise
