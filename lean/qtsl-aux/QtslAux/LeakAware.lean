import QtslAux.Ville

/-! # The leak-aware safe-side bound

For submass (sub-Markov / leaky) models, the safe-side accounting of a
supermartingale certificate subtracts the certificate budget from the
*surviving* mass, not from `1`:
$\underline{P}(\mathrm{safe}) \ge \underline{E}(1) - V(x_0)$ — the
subtraction is not decoration, and the naive full-mass floor is refuted
below by a kernel-checked counterexample.

**Reading.** A submass model is represented here by a finite measure `μ`
on trajectory space whose total mass `μ Set.univ` is the surviving
mass — $E(1)$; nothing below *requires* `μ Set.univ ≤ 1`, the bounds hold
for every finite measure. The safe event is `{ω | ∀ n, X n ω ∉ B}` —
survive-and-never-bad: leaked trajectories are *not* counted safe, which
is why the subtraction lands on the surviving mass and not on `1`:

* per element (`safe_mass_lower_bound`):
  `μ(univ) − (∫ V 0)/a ≤ μ(safe)` — total mass splits into safe + reach by
  the union bound, and Ville–Doob (`reach_avoid_div`, consumed from
  `Ville.lean`) caps the reach term;
* envelope form (`envelope_safe_mass_lower_bound`): for a family
  `𝔐 : ι → Measure Ω` of compatible precise elements sharing one
  certificate `V` (pointwise rows hold per element, the inf is taken
  **last**),
  `(⨅ i, 𝔐 i univ) − v₀/a ≤ ⨅ i, 𝔐 i (safe)` — with barrier `a = 1`
  this is the signature display, `⨅ 𝔐(univ)` being $\underline{E}(1)$
  and `v₀` the certificate's initial value `V x₀` (deterministic starts
  make `∫ V 0 = V x₀` under every element, kept here as the hypothesis
  `∀ i, ∫ V 0 ∂𝔐 i ≤ v₀`);
* precise recovery (`envelope_safe_mass_lower_bound_isProbability`): when
  every element is a probability measure, $\underline{E}(1) = 1$ and the
  familiar display `P(safe) ≥ 1 − V(x₀)` returns;
* **the subtraction is not decoration** (`naive_bound_fails`): a total-leak
  model (zero measure — every trajectory leaks at time 0, no bad states at
  all) satisfies every certificate hypothesis while `μ(safe) = 0 < 1`,
  refuting the naive `1 − V(x₀)` floor for submass models. The leak-aware
  bound holds with equality there (`0 − 0 ≤ 0`).

The credal family enters as a bare index `ι → Measure Ω`, not through the
finite credal machinery of `Imprecise.Credal` — a kernel-stratum version
of the envelope vocabulary needs only sub-Markov kernels. Everything here
is measure theory and naturally noncomputable. -/

open scoped NNReal ENNReal MeasureTheory

namespace Qtsl.LeakAware

open MeasureTheory

variable {Ω S : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}
  {V : ℕ → Ω → ℝ} {X : ℕ → Ω → S} {B : Set S}

/-- **Mass split** (union bound; no measurability needed of `X` or `B`): the total
mass is at most the safe mass plus the reach mass — `univ` is covered by
`{∀ n, X n ∉ B} ∪ {∃ n, X n ∈ B}` and outer regularity of measures gives
subadditivity on arbitrary sets. This is the leak-aware replacement for
"P(safe) = 1 − P(bad)": under submass models the two events need not exhaust
mass `1`, but they always exhaust `μ univ`. -/
theorem measure_univ_le_safe_add_reach (μ : Measure Ω) (X : ℕ → Ω → S) (B : Set S) :
    μ Set.univ ≤ μ {ω | ∀ n, X n ω ∉ B} + μ {ω | ∃ n, X n ω ∈ B} := by
  have hcover : (Set.univ : Set Ω) ⊆ {ω | ∀ n, X n ω ∉ B} ∪ {ω | ∃ n, X n ω ∈ B} := by
    intro ω _
    by_cases h : ∃ n, X n ω ∈ B
    · exact Or.inr h
    · exact Or.inl fun n hn => h ⟨n, hn⟩
  exact (measure_mono hcover).trans (measure_union_le _ _)

/-- **Leak-aware safe-side bound, per precise element** (single-measure
stratum): a nonnegative supermartingale `V` with barrier `a > 0` on the bad set `B`
lower-bounds the *safe* mass by the *surviving* mass minus the Ville–Doob budget:
`μ(univ) − (∫ V 0)/a ≤ μ {∀ n, X n ∉ B}`. For a probability measure this is the
familiar `1 − V(x₀)/a` floor; for a submass model the subtraction correctly starts
from the surviving mass `μ univ = E(1)`. Consumes
`Qtsl.Ville.reach_avoid_div` for the reach term. -/
theorem safe_mass_lower_bound [IsFiniteMeasure μ] (hV : Supermartingale V 𝒢 μ)
    (hnonneg : 0 ≤ V) {a : ℝ} (ha : 0 < a)
    (hbarrier : ∀ n ω, X n ω ∈ B → a ≤ V n ω) :
    μ Set.univ - ENNReal.ofReal (∫ ω, V 0 ω ∂μ) / ENNReal.ofReal a ≤
      μ {ω | ∀ n, X n ω ∉ B} := by
  refine tsub_le_iff_right.2 ?_
  calc
    μ Set.univ ≤ μ {ω | ∀ n, X n ω ∉ B} + μ {ω | ∃ n, X n ω ∈ B} :=
      measure_univ_le_safe_add_reach μ X B
    _ ≤ μ {ω | ∀ n, X n ω ∉ B} +
          ENNReal.ofReal (∫ ω, V 0 ω ∂μ) / ENNReal.ofReal a :=
      add_le_add le_rfl (Ville.reach_avoid_div hV hnonneg ha hbarrier)

/-- `safe_mass_lower_bound` with the initial integral replaced by any upper bound
`v₀` (the certificate's initial value: under a deterministic start `x₀`, every
compatible element has `∫ V 0 = V x₀ ≤ v₀`). The form the envelope theorem
consumes per element. -/
theorem safe_mass_lower_bound_of_initial [IsFiniteMeasure μ]
    (hV : Supermartingale V 𝒢 μ) (hnonneg : 0 ≤ V) {a : ℝ} (ha : 0 < a)
    (hbarrier : ∀ n ω, X n ω ∈ B → a ≤ V n ω) {v₀ : ℝ}
    (hinit : (∫ ω, V 0 ω ∂μ) ≤ v₀) :
    μ Set.univ - ENNReal.ofReal v₀ / ENNReal.ofReal a ≤ μ {ω | ∀ n, X n ω ∉ B} :=
  le_trans
    (tsub_le_tsub_left
      (ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hinit) _) _)
    (safe_mass_lower_bound hV hnonneg ha hbarrier)

/-- **Leak-aware safe-side bound, envelope form**: for a credal family of
compatible precise elements `𝔐 : ι → Measure Ω` sharing one certificate
(`V` is a nonnegative supermartingale with barrier `a` under *every*
element — pointwise rows hold per element, and the inf over elements is
taken last, one quantifier, one direction, no interchange),
`(⨅ i, 𝔐 i univ) − v₀/a ≤ ⨅ i, 𝔐 i {∀ n, X n ∉ B}` — the lower envelope of the
safe mass is floored by the *guaranteed surviving mass* $\underline{E}(1)$ minus
the certificate budget, not by `1 − v₀/a`. -/
theorem envelope_safe_mass_lower_bound {ι : Type*} (𝔐 : ι → Measure Ω)
    [∀ i, IsFiniteMeasure (𝔐 i)] (hV : ∀ i, Supermartingale V 𝒢 (𝔐 i))
    (hnonneg : 0 ≤ V) {a : ℝ} (ha : 0 < a)
    (hbarrier : ∀ n ω, X n ω ∈ B → a ≤ V n ω) {v₀ : ℝ}
    (hinit : ∀ i, (∫ ω, V 0 ω ∂𝔐 i) ≤ v₀) :
    (⨅ i, 𝔐 i Set.univ) - ENNReal.ofReal v₀ / ENNReal.ofReal a ≤
      ⨅ i, 𝔐 i {ω | ∀ n, X n ω ∉ B} := by
  refine le_iInf fun i => ?_
  refine le_trans (tsub_le_tsub_right (iInf_le (fun j => 𝔐 j Set.univ) i) _) ?_
  exact safe_mass_lower_bound_of_initial (hV i) hnonneg ha hbarrier (hinit i)

/-- **The signature display** (barrier at `1`):
$\underline{P}(\mathrm{safe}) \ge \underline{E}(1) - V(x_0)$. The barrier-`1`
specialization of `envelope_safe_mass_lower_bound`: with `V ≥ 1` on the bad set,
`(⨅ i, 𝔐 i univ) − v₀ ≤ ⨅ i, 𝔐 i {∀ n, X n ∉ B}`. -/
theorem envelope_safe_mass_lower_bound_barrier_one {ι : Type*} (𝔐 : ι → Measure Ω)
    [∀ i, IsFiniteMeasure (𝔐 i)] (hV : ∀ i, Supermartingale V 𝒢 (𝔐 i))
    (hnonneg : 0 ≤ V) (hbarrier : ∀ n ω, X n ω ∈ B → (1 : ℝ) ≤ V n ω) {v₀ : ℝ}
    (hinit : ∀ i, (∫ ω, V 0 ω ∂𝔐 i) ≤ v₀) :
    (⨅ i, 𝔐 i Set.univ) - ENNReal.ofReal v₀ ≤
      ⨅ i, 𝔐 i {ω | ∀ n, X n ω ∉ B} := by
  have h := envelope_safe_mass_lower_bound 𝔐 hV hnonneg one_pos hbarrier hinit
  simpa [ENNReal.ofReal_one] using h

/-- **Precise recovery**: when every element of the family is a probability
measure (no leak anywhere in the credal set), $\underline{E}(1) = 1$ and
the familiar display `P̲(safe) ≥ 1 − V(x₀)` returns as a special case —
witnessing that the leak-aware form strictly generalizes rather than replaces
the full-mass bound. -/
theorem envelope_safe_mass_lower_bound_isProbability {ι : Type*} [Nonempty ι]
    (𝔐 : ι → Measure Ω) [∀ i, IsProbabilityMeasure (𝔐 i)]
    (hV : ∀ i, Supermartingale V 𝒢 (𝔐 i)) (hnonneg : 0 ≤ V)
    (hbarrier : ∀ n ω, X n ω ∈ B → (1 : ℝ) ≤ V n ω) {v₀ : ℝ}
    (hinit : ∀ i, (∫ ω, V 0 ω ∂𝔐 i) ≤ v₀) :
    1 - ENNReal.ofReal v₀ ≤ ⨅ i, 𝔐 i {ω | ∀ n, X n ω ∉ B} := by
  have h := envelope_safe_mass_lower_bound_barrier_one 𝔐 hV hnonneg hbarrier hinit
  simpa [measure_univ] using h

/-- **The subtraction is not decoration**, as a theorem: the naive full-mass
floor `1 − V(x₀)` is *unsound* for submass models.
Witness: the total-leak model — zero measure (all mass leaks at time 0), zero
certificate, *no bad states at all* (`B = ∅`). Every hypothesis of the
reach-avoid machinery holds (zero is a martingale under any measure, the barrier
is vacuous), the naive floor claims safe mass `≥ 1 − 0 = 1`, and the actual safe
mass is `0`. The leak-aware bound `safe_mass_lower_bound` is satisfied with
equality there: `μ univ − 0 = 0 ≤ 0`. -/
theorem naive_bound_fails :
    ∃ (Ω' S' : Type) (m0' : MeasurableSpace Ω') (μ' : Measure Ω')
      (𝒢' : Filtration ℕ m0') (V' : ℕ → Ω' → ℝ) (X' : ℕ → Ω' → S') (B' : Set S'),
      IsFiniteMeasure μ' ∧ Supermartingale V' 𝒢' μ' ∧ 0 ≤ V' ∧
        (∀ n ω, X' n ω ∈ B' → (1 : ℝ) ≤ V' n ω) ∧
        μ' {ω | ∀ n, X' n ω ∉ B'} <
          1 - ENNReal.ofReal (∫ ω, V' 0 ω ∂μ') := by
  refine ⟨Unit, Unit, ⊤, 0, ⊥, 0, fun _ _ => (), ∅, inferInstance,
    (martingale_zero _ _ _).supermartingale, le_rfl, fun n ω h => absurd h (by simp),
    ?_⟩
  simp

end Qtsl.LeakAware
