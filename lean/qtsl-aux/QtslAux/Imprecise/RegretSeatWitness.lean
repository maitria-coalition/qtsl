import QtslAux.Imprecise.InclusionWitness

/-! # Seat regret is not a reading of the closed subject's credal body

Witness for the `SRegretLE` design (the statement was preregistered —
committed before the proofs were attempted): the regret of a
policy against its comparison seat quantifies over the *fillers of a hole*,
and no truth-function of the closed subject's credal body expresses it.

Two combs (composition patterns with one hole), modelled semantically by
their closure maps — filler to credal body of the closed composite — over the
`Bool` outcome carrier with the goal-indicator gamble:

* **Comb A** (control matters, no weather): `bodyA f = {δ_{r f}}` — the
  filler's choice is the whole outcome.
* **Comb B** (weather matters, control doesn't): `bodyB f = {δ₁, δ₀}` for
  both fillers — a residual demonic wing the filler cannot touch.

The two combs have **the same demonic envelope** (`env_range_eq`,
`subFam_env_A_B`/`subFam_env_B_A`): closed demonically, they present the same
credal body, so every judgment that reads the closed subject's body assigns
them equal truth (`envelope_reading_blind`). Yet the seat-regret judgment at
`ε = 0` for the filler `false` differs: comb A refuses it (`regJA_not` —
`true` beats `false` by `1`) while comb B accepts it (`regJB` — when only
weather varies, the trivial filler is exactly optimal). Hence no
envelope-reading former expresses seat regret
(`regret_not_envelope_function`) — the formal core of the design memo's
inexpressibility section, in the style of
`QtslAux.Imprecise.InclusionWitness`.

The module also pins the **implicit reading's double failure** — the reading
that infers the comparison class from the closed composite's own residual
demonic freedom (envelope spread ≤ ε):

* `implicit_false_positive`: on comb A closed with the strictly suboptimal
  filler, the spread is `0` — the implicit reading certifies it as 0-regret
  (closing the loop forgot the unchosen action);
* `implicit_false_negative`: on comb B closed with the genuinely optimal
  filler, the spread is `1` — the implicit reading charges the filler for
  the weather's malice.

This is the kernel-checked form of the design resolution: there can be
nondeterminism in the System that is *not* resolvable by policy, so the
comparison class cannot be left implicit.
-/

namespace Qtsl.Imprecise
namespace RegretSeatWitness

open InclusionWitness (ind pone pzero exp_pone exp_pzero)

/-- The one-shot outcome law a filler buys in comb A: `δ₁` for `true`,
`δ₀` for `false`. -/
def rA : Bool → FinPMF Bool := fun f => cond f pone pzero

/-- Comb A's closure map: the filler's choice is the whole outcome — a
singleton body per filler, no residual freedom. -/
def bodyA : Bool → (Fin 1 → FinPMF Bool) := fun f => ![rA f]

/-- Comb B's closure map: an untouchable demonic weather wing — the same
two-law body for every filler. -/
def bodyB : Bool → (Fin 2 → FinPMF Bool) := fun _ => ![pone, pzero]

/-- Achieved value of a filler in comb A: lower expectation of the goal
indicator over the closed composite's body (residual nondeterminism
demonic). -/
def JA (f : Bool) : ℚ := lowerE (bodyA f) ind

/-- Achieved value of a filler in comb B, same demonic-uniform reading. -/
def JB (f : Bool) : ℚ := lowerE (bodyB f) ind

theorem exp_rA (f : Bool) : (rA f).exp ind = cond f 1 0 := by
  cases f <;> simp [rA, exp_pone, exp_pzero]

theorem JA_true : JA true = 1 := by
  unfold JA
  exact le_antisymm
    (by simpa [bodyA, exp_rA] using lowerE_le_exp (bodyA true) ind 0)
    (le_lowerE fun i => by fin_cases i; simp [bodyA, exp_rA])

theorem JA_false : JA false = 0 := by
  unfold JA
  exact le_antisymm
    (by simpa [bodyA, exp_rA] using lowerE_le_exp (bodyA false) ind 0)
    (le_lowerE fun i => by fin_cases i; simp [bodyA, exp_rA])

theorem JB_eq (f : Bool) : JB f = 0 := by
  unfold JB
  exact le_antisymm
    (by simpa [bodyB, exp_pzero] using lowerE_le_exp (bodyB f) ind 1)
    (le_lowerE fun i => by
      fin_cases i <;> simp [bodyB, exp_pone, exp_pzero])

/-- Comb A's demonic envelope: the union of the closed bodies over all
fillers, as a sigma-family. -/
def envA : Bool × Fin 1 → FinPMF Bool := fun p => bodyA p.1 p.2

/-- Comb B's demonic envelope. -/
def envB : Bool × Fin 2 → FinPMF Bool := fun p => bodyB p.1 p.2

theorem subFam_env_A_B : SubFam envA envB := by
  rintro ⟨f, i⟩
  fin_cases i
  cases f
  · exact ⟨(true, 1), rfl⟩
  · exact ⟨(true, 0), rfl⟩

theorem subFam_env_B_A : SubFam envB envA := by
  rintro ⟨f, i⟩
  fin_cases i
  · exact ⟨(true, 0), rfl⟩
  · exact ⟨(false, 0), rfl⟩

/-- The two combs present **the same** demonic envelope: any former whose
denotation reads the closed subject's credal body cannot tell them apart. -/
theorem env_range_eq : Set.range envA = Set.range envB := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, rfl⟩
    obtain ⟨q, hq⟩ := subFam_env_A_B p
    exact ⟨q, hq⟩
  · rintro _ ⟨p, rfl⟩
    obtain ⟨q, hq⟩ := subFam_env_B_A p
    exact ⟨q, hq⟩

/-- Seat-regret judgment at `ε = 0` for the filler `false` in comb A:
every rival filler's achieved value is bounded by `false`'s. -/
def RegJA : Prop := ∀ f' : Bool, JA f' ≤ JA false + 0

/-- The same judgment in comb B. -/
def RegJB : Prop := ∀ f' : Bool, JB f' ≤ JB false + 0

/-- Comb A refuses `SRegretLE(false, ·, 0)`: the rival `true` achieves `1`
against `false`'s `0`. -/
theorem regJA_not : ¬ RegJA := fun h => by
  have h1 := h true
  rw [JA_true, JA_false] at h1
  norm_num at h1

/-- Comb B accepts `SRegretLE(false, ·, 0)`: when only weather varies, the
trivial filler is exactly optimal — the weather's spread is charged to no
one. -/
theorem regJB : RegJB := fun f' => by
  rw [JB_eq, JB_eq]; norm_num

/-- Every reading of the closed subject's credal body is blind to the
difference between the combs. -/
theorem envelope_reading_blind (P : Set (FinPMF Bool) → Prop) :
    P (Set.range envA) ↔ P (Set.range envB) := by
  rw [env_range_eq]

/-- **Inexpressibility, quantifier-explicit**: no truth-function of the
closed subject's credal body decides the seat-regret judgment on both
combs — the comparison seat is structure the envelope has already
forgotten. -/
theorem regret_not_envelope_function :
    ¬ ∃ P : Set (FinPMF Bool) → Prop,
      (P (Set.range envA) ↔ RegJA) ∧ (P (Set.range envB) ↔ RegJB) := by
  rintro ⟨P, hA, hB⟩
  exact regJA_not (hA.mp ((envelope_reading_blind P).mpr (hB.mpr regJB)))

/-- The implicit reading: comparison class inferred from the *closed*
composite's own residual demonic freedom — the envelope spread at `ε = 0`. -/
def ImplicitJ {ι : Type*} [Fintype ι] [Nonempty ι]
    (M : ι → FinPMF Bool) : Prop :=
  upperE M ind ≤ lowerE M ind + 0

theorem upperE_bodyA_false : upperE (bodyA false) ind = 0 :=
  le_antisymm
    (upperE_le fun i => by fin_cases i; simp [bodyA, exp_rA])
    (by simpa [bodyA, exp_rA] using exp_le_upperE (bodyA false) ind 0)

theorem upperE_bodyB_false : upperE (bodyB false) ind = 1 :=
  le_antisymm
    (upperE_le fun i => by
      fin_cases i <;> simp [bodyB, exp_pone, exp_pzero])
    (by simpa [bodyB, exp_pone] using exp_le_upperE (bodyB false) ind 0)

/-- **False positive**: on comb A closed with the strictly suboptimal filler
`false`, the implicit reading holds — closing the loop forgot the unchosen
action, and a filler that loses the whole gamble gets certified 0-regret. -/
theorem implicit_false_positive : ImplicitJ (bodyA false) := by
  unfold ImplicitJ
  rw [upperE_bodyA_false,
    show lowerE (bodyA false) ind = 0 from by rw [← JA_false]; rfl]
  norm_num

/-- **False negative**: on comb B closed with the genuinely optimal filler
`false` (see `regJB`), the implicit reading fails — it charges the filler
for the weather's malice. -/
theorem implicit_false_negative : ¬ ImplicitJ (bodyB false) := by
  unfold ImplicitJ
  rw [upperE_bodyB_false,
    show lowerE (bodyB false) ind = 0 from by rw [← JB_eq false]; rfl]
  norm_num

end RegretSeatWitness
end Qtsl.Imprecise
