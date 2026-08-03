import SuFunctor.Universe.Marginalization

/-! # Frobenius reciprocity for hiding, through the lsc-envelope reflector

Hiding a coordinate is the reflected existential `hide p σ = lscEnv
(infProj p σ)`: against every lower semicontinuous specification it is
left adjoint to penalty pullback in the entailment order (`le_hide_iff`).
Frobenius reciprocity asks whether that existential commutes with
conjoining a visible-carrier penalty, for either conjunction the penalty
storey speaks — pointwise join, or additive composition:

    hide p (σ ⊔ g ∘ p)  =  hide p σ ⊔ g        (join)
    hide p (σ + g ∘ p)  =  hide p σ + g        (additive)

This file adjudicates the question in three strata.

* **Propositional stratum — holds on the nose, no topology**
  (`infProj_sup_comp`, `infProj_add_comp`): for the raw inf-projection
  both identities are pointwise computations in `ℝ≥0∞` (`⨅` commutes
  with `⊔ c` in a coframe and with `+ c` by order-continuity of
  addition), empty fibers included.

* **Through the reflector — the lax law survives, equality does not.**
  The canonical comparison holds for every penalty and every lower
  semicontinuous `g` (`hide_sup_le`, `hide_add_le`):

      hide p σ ⊔ g ≤ hide p (σ ⊔ g ∘ p),
      hide p σ + g ≤ hide p (σ + g ∘ p)

  — read in the entailment order, `∃_p (σ ⊛ p^*g) ⊑ ∃_p σ ⊛ g`, exactly
  the direction every adjunction with a `⊛`-preserving right adjoint
  supplies formally: the fibred existential is *lax*, never oplax.  The
  reverse inequality **fails**
  (`exists_lowerSemicontinuous_hide_sup_ne`,
  `exists_lowerSemicontinuous_hide_add_ne`), witnessed on the escaping-
  mass family of `Marginalization`: the wall of that family marginalizes
  to a wall whose envelope adds the unattained boundary value of the
  visible coordinate, and a penalty vanishing exactly at the added point
  detects the addition — conjoining *before* hiding sees only attained
  fibers, where the penalty never vanishes.  The envelope of a wall is
  the wall of the closure (`lscEnv_charFn`); Frobenius fails because the
  reflector and the conjunction see different boundaries.  Moreover the
  failure is *judgment-visible* (`exists_judgment_separating_hide_sup`,
  `exists_judgment_separating_hide_add`): a constant specification is
  dominated by one side and not the other, so the gap is not an
  intensional artifact below judgment resolution — unlike the reflector
  itself, which changes no judgment (`le_lscEnv_iff`).

* **Under the inf-compactness certificate — equality is restored**
  (`hide_sup_comp`, `hide_add_comp`): a certified penalty conjoined with
  a pulled-back citizen is again certified (`{σ ⊛ g∘p ≤ c} ⊆ {σ ≤ c}`,
  closed inside compact), so the inf-projections on both sides are
  already lower semicontinuous (`lowerSemicontinuous_infProj`), the
  reflector idles (`hide_eq_infProj`), and the propositional identities
  carry the day.  Where marginalization is exact, Frobenius costs
  nothing; off the certificate the existential is honestly lax.
-/

namespace SuFunctor.Universe

open MeasureTheory Filter Set
open scoped ENNReal Topology

/-! ## Propositional stratum: the raw inf-projection satisfies Frobenius -/

section Propositional

variable {Z W : Type*}

/-- Frobenius for the raw inf-projection, join form: hiding after
conjoining a pulled-back penalty is conjoining after hiding.  A pointwise
computation in the coframe `ℝ≥0∞`; no topology, arbitrary fibers (empty
ones give `⊤ ⊔ g w = ⊤`). -/
theorem infProj_sup_comp (p : Z → W) (σ : Z → ℝ≥0∞) (g : W → ℝ≥0∞) :
    infProj p (σ ⊔ g ∘ p) = infProj p σ ⊔ g := by
  funext w
  simp only [infProj, Pi.sup_apply, Function.comp_apply, iInf_sup_eq]
  exact iInf_congr fun z => iInf_congr fun hz => by rw [hz]

/-- Frobenius for the raw inf-projection, additive form: a pointwise
computation by order-continuity of addition in `ℝ≥0∞`; no topology,
arbitrary fibers (empty ones give `⊤ + g w = ⊤`). -/
theorem infProj_add_comp (p : Z → W) (σ : Z → ℝ≥0∞) (g : W → ℝ≥0∞) :
    infProj p (σ + g ∘ p) = infProj p σ + g := by
  funext w
  simp only [infProj, Pi.add_apply, Function.comp_apply, ENNReal.iInf_add]
  exact iInf_congr fun z => iInf_congr fun hz => by rw [hz]

end Propositional

/-! ## The envelope of a wall is the wall of the closure -/

section WallEnvelope

variable {Z : Type*} [TopologicalSpace Z]

omit [TopologicalSpace Z] in
/-- Walls are antitone in the set: a larger set imposes a smaller
penalty. -/
theorem charFn_anti {C D : Set Z} (h : C ⊆ D) : charFn D ≤ charFn C := by
  intro z
  by_cases hz : z ∈ C
  · exact (charFn_of_mem (h hz)).trans_le zero_le
  · rw [charFn_of_notMem hz]
    exact le_top

/-- **The lsc envelope of a wall is the wall of the closure.**  Every lsc
minorant of `charFn C` must vanish on the closure of `C` (a positive
value would propagate to a neighborhood, which meets `C`), and the wall
of the closure is itself an lsc minorant. -/
theorem lscEnv_charFn (C : Set Z) : lscEnv (charFn C) = charFn (closure C) := by
  refine le_antisymm (fun z => ?_)
    (le_lscEnv (lowerSemicontinuous_charFn_iff.mpr isClosed_closure)
      (charFn_anti subset_closure))
  by_cases hz : z ∈ closure C
  · rw [charFn_of_mem hz, lscEnv, iSup_apply]
    refine iSup_le fun φ => ?_
    by_contra hpos
    rw [not_le] at hpos
    have hev : ∀ᶠ x in 𝓝 z, 0 < (φ : Z → ℝ≥0∞) x := φ.2.1 z 0 hpos
    have hfreq : ∃ᶠ x in 𝓝 z, x ∈ C := mem_closure_iff_frequently.mp hz
    obtain ⟨x, hxC, hx0⟩ := (hfreq.and_eventually hev).exists
    have hle := φ.2.2 x
    rw [charFn_of_mem hxC] at hle
    exact absurd hle (not_le.mpr hx0)
  · rw [charFn_of_notMem hz]
    exact le_top

/-- Relaxing before a join is conservative: the join of the envelopes is
an lsc minorant of the join.  (The `⊔` sibling of
`lscEnv_add_lscEnv_le`.) -/
theorem lscEnv_sup_lscEnv_le (g₁ g₂ : Z → ℝ≥0∞) :
    lscEnv g₁ ⊔ lscEnv g₂ ≤ lscEnv (g₁ ⊔ g₂) :=
  le_lscEnv ((lowerSemicontinuous_lscEnv g₁).sup (lowerSemicontinuous_lscEnv g₂))
    (sup_le_sup (lscEnv_le g₁) (lscEnv_le g₂))

end WallEnvelope

/-! ## The lax law: the canonical Frobenius comparison always holds -/

section LaxFrobenius

variable {Z W : Type*} [TopologicalSpace W]

/-- Where the raw inf-projection is already lower semicontinuous, the
reflector idles and the repaired marginalization is the naive one. -/
theorem hide_eq_infProj {p : Z → W} {σ : Z → ℝ≥0∞}
    (h : LowerSemicontinuous (infProj p σ)) : hide p σ = infProj p σ := by
  rw [hide]
  exact lscEnv_eq_self h

/-- **Lax Frobenius, join form.**  The canonical comparison of the hiding
adjunction: in the entailment order, `∃_p (σ ⊔ p^*g) ⊑ ∃_p σ ⊔ g` for
every citizen `g`.  Equality fails in general
(`exists_lowerSemicontinuous_hide_sup_ne`). -/
theorem hide_sup_le (p : Z → W) (σ : Z → ℝ≥0∞) {g : W → ℝ≥0∞}
    (hg : LowerSemicontinuous g) :
    hide p σ ⊔ g ≤ hide p (σ ⊔ g ∘ p) := by
  rw [hide, hide, infProj_sup_comp]
  calc lscEnv (infProj p σ) ⊔ g
      = lscEnv (infProj p σ) ⊔ lscEnv g := by rw [lscEnv_eq_self hg]
    _ ≤ lscEnv (infProj p σ ⊔ g) := lscEnv_sup_lscEnv_le _ _

/-- **Lax Frobenius, additive form.**  The canonical comparison of the
hiding adjunction: in the entailment order, `∃_p (σ + p^*g) ⊑ ∃_p σ + g`
for every citizen `g`.  Equality fails in general
(`exists_lowerSemicontinuous_hide_add_ne`). -/
theorem hide_add_le (p : Z → W) (σ : Z → ℝ≥0∞) {g : W → ℝ≥0∞}
    (hg : LowerSemicontinuous g) :
    hide p σ + g ≤ hide p (σ + g ∘ p) := by
  rw [hide, hide, infProj_add_comp]
  calc lscEnv (infProj p σ) + g
      = lscEnv (infProj p σ) + lscEnv g := by rw [lscEnv_eq_self hg]
    _ ≤ lscEnv (infProj p σ + g) := lscEnv_add_lscEnv_le _ _

end LaxFrobenius

/-! ## Equality under the inf-compactness certificate -/

section CertificateFrobenius

variable {Z W : Type*} [TopologicalSpace Z] [TopologicalSpace W]

/-- **Frobenius reciprocity under the certificate, join form.**  For an
inf-compact lsc penalty and a citizen `g`, hiding commutes with the join
on the nose: the conjoined penalty inherits the certificate, both
inf-projections are lsc, the reflector idles, and the propositional
identity finishes. -/
theorem hide_sup_comp [T2Space W] {p : Z → W} (hp : Continuous p)
    {σ : Z → ℝ≥0∞} (hσ : LowerSemicontinuous σ)
    (hcpt : ∀ c : ℝ≥0∞, c ≠ ⊤ → IsCompact {z | σ z ≤ c})
    {g : W → ℝ≥0∞} (hg : LowerSemicontinuous g) :
    hide p (σ ⊔ g ∘ p) = hide p σ ⊔ g := by
  have hgp : LowerSemicontinuous (g ∘ p) := hg.comp hp
  have hσ' : LowerSemicontinuous (σ ⊔ g ∘ p) := hσ.sup hgp
  have hcpt' : ∀ c : ℝ≥0∞, c ≠ ⊤ → IsCompact {z | (σ ⊔ g ∘ p) z ≤ c} := by
    intro c hc
    refine (hcpt c hc).of_isClosed_subset (hσ'.isClosed_preimage c) ?_
    intro z hz
    have hz' : σ z ⊔ (g ∘ p) z ≤ c := hz
    show σ z ≤ c
    exact le_sup_left.trans hz'
  rw [hide_eq_infProj (lowerSemicontinuous_infProj hp hσ' hcpt'),
    hide_eq_infProj (lowerSemicontinuous_infProj hp hσ hcpt), infProj_sup_comp]

/-- **Frobenius reciprocity under the certificate, additive form.**  For
an inf-compact lsc penalty and a citizen `g`, hiding commutes with
additive composition on the nose. -/
theorem hide_add_comp [T2Space W] {p : Z → W} (hp : Continuous p)
    {σ : Z → ℝ≥0∞} (hσ : LowerSemicontinuous σ)
    (hcpt : ∀ c : ℝ≥0∞, c ≠ ⊤ → IsCompact {z | σ z ≤ c})
    {g : W → ℝ≥0∞} (hg : LowerSemicontinuous g) :
    hide p (σ + g ∘ p) = hide p σ + g := by
  have hgp : LowerSemicontinuous (g ∘ p) := hg.comp hp
  have hσ' : LowerSemicontinuous (σ + g ∘ p) := hσ.add hgp
  have hcpt' : ∀ c : ℝ≥0∞, c ≠ ⊤ → IsCompact {z | (σ + g ∘ p) z ≤ c} := by
    intro c hc
    refine (hcpt c hc).of_isClosed_subset (hσ'.isClosed_preimage c) ?_
    intro z hz
    have hz' : σ z + (g ∘ p) z ≤ c := hz
    show σ z ≤ c
    exact le_self_add.trans hz'
  rw [hide_eq_infProj (lowerSemicontinuous_infProj hp hσ' hcpt'),
    hide_eq_infProj (lowerSemicontinuous_infProj hp hσ hcpt), infProj_add_comp]

end CertificateFrobenius

/-! ## The witness: Frobenius equality fails through the reflector

On the escaping-mass family of `Marginalization`: the wall of the family
marginalizes along the live-mass coordinate to the wall of a
*non-closed* image, whose envelope silently adds the boundary value `1`.
The fee vanishing exactly at `1` — free precisely at the value the
family approaches but never attains — detects the added point. -/

section FrobeniusWitness

open Classical in
/-- The fee that is free exactly at visible value `1`: penalty `1`
elsewhere.  Lower semicontinuous, because the positive value sits on the
open set `{w ≠ 1}`. -/
noncomputable def offOneFee : ℝ≥0∞ → ℝ≥0∞ :=
  fun w => if w = 1 then 0 else 1

@[simp] theorem offOneFee_one : offOneFee 1 = 0 := by
  simp [offOneFee]

theorem offOneFee_of_ne {w : ℝ≥0∞} (h : w ≠ 1) : offOneFee w = 1 := by
  simp [offOneFee, h]

theorem lowerSemicontinuous_offOneFee : LowerSemicontinuous offOneFee := by
  intro w y hy
  rcases eq_or_ne w 1 with rfl | hw
  · rw [offOneFee_one] at hy
    exact absurd hy (not_lt.mpr zero_le)
  · rw [offOneFee_of_ne hw] at hy
    filter_upwards [isOpen_ne.mem_nhds hw] with x hx
    rw [offOneFee_of_ne hx]
    exact hy

/-- The escaping family's visible values all pay the fee. -/
theorem offOneFee_liveMass_escapeMix (n : ℕ) :
    offOneFee (liveMass (escapeMix n)) = 1 :=
  offOneFee_of_ne (liveMass_escapeMix_lt_one n).ne

/-- The boundary value `1` lies in the closure of the visible image of
the escaping family. -/
theorem one_mem_closure_image_liveMass :
    (1 : ℝ≥0∞) ∈ closure (liveMass '' Set.range escapeMix) :=
  mem_closure_of_tendsto tendsto_liveMass_escapeMix
    (Eventually.of_forall fun n => Set.mem_image_of_mem _ (Set.mem_range_self n))

/-- The repaired marginalization of the escaping wall is free at the
boundary value: the envelope has added the unattained point. -/
theorem hide_charFn_escapeMix_one :
    hide liveMass (charFn (Set.range escapeMix)) 1 = 0 := by
  rw [hide, infProj_charFn, lscEnv_charFn]
  exact charFn_of_mem one_mem_closure_image_liveMass

/-- Conjoined before hiding, wall-plus-fee is at least `1` everywhere:
on the family the wall is free but the fee is not (no member attains the
visible value `1`); off the family the wall is `⊤`. -/
theorem one_le_wall_add_fee (ρ : ProbabilityMeasure ℕ) :
    1 ≤ charFn (Set.range escapeMix) ρ + offOneFee (liveMass ρ) := by
  by_cases hρ : ρ ∈ Set.range escapeMix
  · obtain ⟨n, rfl⟩ := hρ
    rw [charFn_of_mem (Set.mem_range_self n), offOneFee_liveMass_escapeMix]
    exact le_of_eq (zero_add 1).symm
  · rw [charFn_of_notMem hρ]
    exact le_top.trans le_self_add

/-- Join sibling of `one_le_wall_add_fee`. -/
theorem one_le_wall_sup_fee (ρ : ProbabilityMeasure ℕ) :
    1 ≤ charFn (Set.range escapeMix) ρ ⊔ offOneFee (liveMass ρ) := by
  by_cases hρ : ρ ∈ Set.range escapeMix
  · obtain ⟨n, rfl⟩ := hρ
    rw [offOneFee_liveMass_escapeMix]
    exact le_sup_right
  · rw [charFn_of_notMem hρ]
    exact le_top.trans le_sup_left

/-- **Frobenius reciprocity fails through the reflector, additive
form.**  There are lower semicontinuous penalties for which hiding does
not commute with additive composition: the escaping wall and the
off-one fee.  At the boundary value the conjoined-then-hidden penalty
is at least `1` (the fee is paid on every attained fiber), while the
hidden-then-conjoined penalty vanishes (the envelope added the boundary
point, where the fee is free). -/
theorem exists_lowerSemicontinuous_hide_add_ne :
    ∃ (σ : ProbabilityMeasure ℕ → ℝ≥0∞) (g : ℝ≥0∞ → ℝ≥0∞),
      LowerSemicontinuous σ ∧ LowerSemicontinuous g ∧
      hide liveMass (σ + g ∘ liveMass) ≠ hide liveMass σ + g := by
  refine ⟨charFn (Set.range escapeMix), offOneFee,
    lowerSemicontinuous_charFn_iff.mpr isClosed_range_escapeMix,
    lowerSemicontinuous_offOneFee, fun hEq => ?_⟩
  have h1 : (1 : ℝ≥0∞) ≤
      hide liveMass (charFn (Set.range escapeMix) + offOneFee ∘ liveMass) 1 :=
    ((le_hide_iff lowerSemicontinuous_const).mpr
      fun ρ => one_le_wall_add_fee ρ) 1
  rw [hEq, Pi.add_apply, hide_charFn_escapeMix_one, offOneFee_one,
    add_zero] at h1
  exact absurd h1 (not_le.mpr zero_lt_one)

/-- **Frobenius reciprocity fails through the reflector, join form.**
The same witness refutes the join form. -/
theorem exists_lowerSemicontinuous_hide_sup_ne :
    ∃ (σ : ProbabilityMeasure ℕ → ℝ≥0∞) (g : ℝ≥0∞ → ℝ≥0∞),
      LowerSemicontinuous σ ∧ LowerSemicontinuous g ∧
      hide liveMass (σ ⊔ g ∘ liveMass) ≠ hide liveMass σ ⊔ g := by
  refine ⟨charFn (Set.range escapeMix), offOneFee,
    lowerSemicontinuous_charFn_iff.mpr isClosed_range_escapeMix,
    lowerSemicontinuous_offOneFee, fun hEq => ?_⟩
  have h1 : (1 : ℝ≥0∞) ≤
      hide liveMass (charFn (Set.range escapeMix) ⊔ offOneFee ∘ liveMass) 1 :=
    ((le_hide_iff lowerSemicontinuous_const).mpr
      fun ρ => one_le_wall_sup_fee ρ) 1
  rw [hEq, Pi.sup_apply, hide_charFn_escapeMix_one, offOneFee_one,
    sup_idem] at h1
  exact absurd h1 (not_le.mpr zero_lt_one)

/-- **The Frobenius gap is judgment-visible, additive form.**  Unlike
the reflector itself — which changes no domination judgment
(`le_lscEnv_iff`) — the Frobenius failure separates the two sides by an
honest judgment: the constant specification `1` is dominated by the
conjoined-then-hidden penalty and not by the hidden-then-conjoined
one. -/
theorem exists_judgment_separating_hide_add :
    ∃ (σ : ProbabilityMeasure ℕ → ℝ≥0∞) (g φ : ℝ≥0∞ → ℝ≥0∞),
      LowerSemicontinuous σ ∧ LowerSemicontinuous g ∧
      LowerSemicontinuous φ ∧
      φ ≤ hide liveMass (σ + g ∘ liveMass) ∧
      ¬ φ ≤ hide liveMass σ + g := by
  refine ⟨charFn (Set.range escapeMix), offOneFee, fun _ => 1,
    lowerSemicontinuous_charFn_iff.mpr isClosed_range_escapeMix,
    lowerSemicontinuous_offOneFee, lowerSemicontinuous_const,
    (le_hide_iff lowerSemicontinuous_const).mpr fun ρ => one_le_wall_add_fee ρ,
    fun hle => ?_⟩
  have h1 := hle 1
  rw [Pi.add_apply, hide_charFn_escapeMix_one, offOneFee_one, add_zero] at h1
  exact absurd h1 (not_le.mpr zero_lt_one)

/-- **The Frobenius gap is judgment-visible, join form.** -/
theorem exists_judgment_separating_hide_sup :
    ∃ (σ : ProbabilityMeasure ℕ → ℝ≥0∞) (g φ : ℝ≥0∞ → ℝ≥0∞),
      LowerSemicontinuous σ ∧ LowerSemicontinuous g ∧
      LowerSemicontinuous φ ∧
      φ ≤ hide liveMass (σ ⊔ g ∘ liveMass) ∧
      ¬ φ ≤ hide liveMass σ ⊔ g := by
  refine ⟨charFn (Set.range escapeMix), offOneFee, fun _ => 1,
    lowerSemicontinuous_charFn_iff.mpr isClosed_range_escapeMix,
    lowerSemicontinuous_offOneFee, lowerSemicontinuous_const,
    (le_hide_iff lowerSemicontinuous_const).mpr fun ρ => one_le_wall_sup_fee ρ,
    fun hle => ?_⟩
  have h1 := hle 1
  rw [Pi.sup_apply, hide_charFn_escapeMix_one, offOneFee_one, sup_idem] at h1
  exact absurd h1 (not_le.mpr zero_lt_one)

end FrobeniusWitness

end SuFunctor.Universe
