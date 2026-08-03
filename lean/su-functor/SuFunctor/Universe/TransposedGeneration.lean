import SuFunctor.Universe.VietorisStratum

/-! # The transposed generation theorem: two atom families see the
whole hyperspace universe

`SuFunctor.Universe.Generation` proves every lsc citizen of the flat
carrier is a countable sup of finite mins of rational threshold rows.
This module transposes the statement one level up, per the dictionary:
every Vietoris-lsc functional on the hyperspace of a second-countable
space is a countable sup of finite mins of **graded atoms** —
miss-graded atoms `infAtom` and hit-graded atoms `supAtom` with
scaled-indicator parameters (`iSup_hyperRows_eq_self`).

* **Atoms of indicators are indicators of sub-basics**
  (`infAtom_indicator`, `supAtom_indicator`): the miss-graded atom of
  `c·𝟙_U` is `c` exactly on the containment class `{K ⊆ U}`, the
  hit-graded atom is `c` exactly on the hit class — the two faces of
  the Vietoris sub-base, priced.
* **Rows are basic-open indicators** (`hyperRow`): one containment
  atom min finitely many hit atoms — `c` on a Vietoris basic, `0`
  elsewhere.
* **The engine is the same layer-cake**: below any rational height
  under `Φ` at `K₀`, semicontinuity opens the superlevel, the
  hyperspace basis of a countable base (the library's
  `IsTopologicalBasis.nonemptyCompacts`) fits a basic between `K₀`
  and the superlevel, and the row of that basic is a minorant
  attaining the height.  The index data is countable
  (`hyperRow_index_countable`): rational heights, finite families
  drawn from a countable base.

Together with the polarity facts of the topological stratum
(`lowerSemicontinuous_supAtom`, `lowerSemicontinuous_infAtom`: for lsc
parameters both atoms are Vietoris-lsc, through opposite faces), this
is the graded spec universe over the hyperspace exhibited as the
connective closure of two polarity-pure atom families. -/

namespace SuFunctor.Universe

open scoped ENNReal
open TopologicalSpace

section TransposedGeneration

variable {X : Type*} [TopologicalSpace X]

/-! ## Atoms of scaled indicators price the two faces -/

open Classical in
theorem infAtom_indicator (c : ℝ≥0∞) (U : Set X) (K : NonemptyCompacts X) :
    infAtom (U.indicator fun _ => c) K
      = if (K : Set X) ⊆ U then c else 0 := by
  by_cases hsub : (K : Set X) ⊆ U
  · rw [if_pos hsub]
    refine le_antisymm ?_ (le_iInf₂ fun x hx => ?_)
    · obtain ⟨x₀, hx₀⟩ := K.nonempty
      exact iInf₂_le_of_le x₀ hx₀
        (by rw [Set.indicator_of_mem (hsub hx₀)])
    · rw [Set.indicator_of_mem (hsub hx)]
  · rw [if_neg hsub]
    obtain ⟨x₀, hx₀K, hx₀U⟩ := Set.not_subset.mp hsub
    refine le_antisymm ?_ zero_le
    exact iInf₂_le_of_le x₀ hx₀K (by rw [Set.indicator_of_notMem hx₀U])

open Classical in
theorem supAtom_indicator (c : ℝ≥0∞) (U : Set X) (K : NonemptyCompacts X) :
    supAtom (U.indicator fun _ => c) K
      = if ((K : Set X) ∩ U).Nonempty then c else 0 := by
  by_cases hhit : ((K : Set X) ∩ U).Nonempty
  · rw [if_pos hhit]
    obtain ⟨x₀, hx₀K, hx₀U⟩ := hhit
    refine le_antisymm (iSup₂_le fun x hx => ?_) ?_
    · by_cases hxU : x ∈ U
      · rw [Set.indicator_of_mem hxU]
      · rw [Set.indicator_of_notMem hxU]
        exact zero_le
    · exact le_iSup₂_of_le x₀ hx₀K (by rw [Set.indicator_of_mem hx₀U])
  · rw [if_neg hhit]
    refine le_antisymm (iSup₂_le fun x hx => ?_) zero_le
    have hxU : x ∉ U := fun hc => hhit ⟨x, hx, hc⟩
    rw [Set.indicator_of_notMem hxU]

/-! ## Rows: one containment atom, finitely many hit atoms -/

/-- The hyperspace row: the min of a miss-graded atom on `U` and
hit-graded atoms on the members of `F` — the graded indicator of the
Vietoris basic `⟨U; F⟩`. -/
noncomputable def hyperRow (c : ℝ≥0∞) (U : Set X) (F : Finset (Set X)) :
    NonemptyCompacts X → ℝ≥0∞ :=
  fun K => infAtom (U.indicator fun _ => c) K
    ⊓ F.inf fun W => supAtom (W.indicator fun _ => c) K

theorem hyperRow_apply_of_mem {c : ℝ≥0∞} {U : Set X} {F : Finset (Set X)}
    {K : NonemptyCompacts X} (h1 : (K : Set X) ⊆ U)
    (h2 : ∀ W ∈ F, ((K : Set X) ∩ W).Nonempty) :
    hyperRow c U F K = c := by
  rw [hyperRow, infAtom_indicator, if_pos h1]
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · simp
  · have hterm : ∀ W ∈ F, supAtom (W.indicator fun _ => c) K = c :=
      fun W hW => by rw [supAtom_indicator, if_pos (h2 W hW)]
    rw [Finset.inf_congr rfl hterm, Finset.inf_const hFne, inf_idem]

theorem hyperRow_apply_of_not_mem {c : ℝ≥0∞} {U : Set X}
    {F : Finset (Set X)} {K : NonemptyCompacts X}
    (h : ¬((K : Set X) ⊆ U ∧ ∀ W ∈ F, ((K : Set X) ∩ W).Nonempty)) :
    hyperRow c U F K = 0 := by
  rw [not_and_or] at h
  rcases h with h | h
  · rw [hyperRow, infAtom_indicator, if_neg h]
    simp
  · push Not at h
    obtain ⟨W, hWF, hWmiss⟩ := h
    refine le_antisymm ?_ zero_le
    refine inf_le_right.trans ((Finset.inf_le hWF).trans ?_)
    rw [supAtom_indicator,
      if_neg (Set.not_nonempty_iff_eq_empty.mpr hWmiss)]

/-- The row index over a countable base is countable: rational
heights, finite families from the base. -/
theorem hyperRow_index_countable {B : Set (Set X)} (hB : B.Countable) :
    {p : ℚ × Finset (Set X) | ↑p.2 ⊆ B}.Countable := by
  have h1 : {p : ℚ × Finset (Set X) | ↑p.2 ⊆ B}
      ⊆ Set.univ ×ˢ {u : Finset (Set X) | ↑u ⊆ B} := by
    rintro ⟨q, u⟩ hu
    exact ⟨Set.mem_univ _, hu⟩
  refine Set.Countable.mono h1 (Set.Countable.prod Set.countable_univ ?_)
  have h2 : {u : Finset (Set X) | ↑u ⊆ B}
      = (fun u : Finset (Set X) => (u : Set (Set X))) ⁻¹'
          {t | Set.Finite t ∧ t ⊆ B} := by
    ext u
    simp [Finset.finite_toSet]
  rw [h2]
  exact (Set.countable_setOf_finite_subset hB).preimage Finset.coe_injective

/-! ## The transposed generation theorem -/

/-- **The transposed generation theorem.**  On the hyperspace of a
second-countable space, every Vietoris-lsc functional is the pointwise
supremum of its hyperspace-row minorants over a countable base —
hence a countable sup (`hyperRow_index_countable`) of finite mins of
miss-graded and hit-graded atoms with scaled-indicator parameters. -/
theorem iSup_hyperRows_eq_self [SecondCountableTopology X]
    {Φ : NonemptyCompacts X → ℝ≥0∞} (hΦ : LowerSemicontinuous Φ) :
    ∃ B : Set (Set X), B.Countable ∧ (∀ U ∈ B, IsOpen U)
      ∧ (⨆ (q : ℚ) (u : Finset (Set X)) (_ : ↑u ⊆ B) (_ : 0 < q)
          (_ : ∀ K, hyperRow (ENNReal.ofReal q) (⋃₀ ↑u) u K ≤ Φ K),
          hyperRow (ENNReal.ofReal q) (⋃₀ ↑u) u) = Φ := by
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis X
  refine ⟨B, hBc, fun U hU => hB.isOpen hU, ?_⟩
  apply le_antisymm
  · exact iSup_le fun q => iSup_le fun u => iSup_le fun _ => iSup_le fun _ =>
      iSup_le fun hmin => fun K => hmin K
  · intro K₀
    by_contra hlt'
    rw [not_le] at hlt'
    obtain ⟨q, -, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hlt'
    have hcoe : ((Real.toNNReal (q : ℝ)) : ℝ≥0∞) = ENNReal.ofReal (q : ℝ) := rfl
    rw [hcoe] at h1 h2
    have hq0 : 0 < q := by
      have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal q := zero_le.trans_lt h1
      exact_mod_cast ENNReal.ofReal_pos.mp hpos
    -- the superlevel is Vietoris-open; a basic of the countable base
    -- fits between `K₀` and it
    obtain ⟨A, hA, hK₀A, hAsub⟩ :=
      (hB.nonemptyCompacts).exists_subset_of_mem_open
        (show K₀ ∈ Φ ⁻¹' Set.Ioi (ENNReal.ofReal (q : ℝ)) from h2)
        (lowerSemicontinuous_iff_isOpen_preimage.mp hΦ _)
    obtain ⟨u, ⟨hufin, -, huB⟩, rfl⟩ := hA
    have hFu : (hufin.toFinset : Set (Set X)) = u := hufin.coe_toFinset
    -- the row of that basic is a minorant of `Φ`
    have hmin : ∀ K, hyperRow (ENNReal.ofReal q) (⋃₀ ↑hufin.toFinset)
        hufin.toFinset K ≤ Φ K := by
      intro K
      by_cases hK : (K : Set X) ⊆ ⋃₀ (hufin.toFinset : Set (Set X))
          ∧ ∀ W ∈ hufin.toFinset, ((K : Set X) ∩ W).Nonempty
      · rw [hyperRow_apply_of_mem hK.1 hK.2]
        have hKA : K ∈ {K : NonemptyCompacts X |
            ↑K ⊆ ⋃₀ u ∧ ∀ U ∈ u, (↑K ∩ U).Nonempty} := by
          constructor
          · rw [← hFu]
            exact hK.1
          · intro U hU
            exact hK.2 U (hufin.mem_toFinset.mpr hU)
        exact (hAsub hKA).le
      · rw [hyperRow_apply_of_not_mem hK]
        exact zero_le
    -- the row attains the height at `K₀`, beating the supremum
    have happ : hyperRow (ENNReal.ofReal q) (⋃₀ ↑hufin.toFinset)
        hufin.toFinset K₀ = ENNReal.ofReal q := by
      refine hyperRow_apply_of_mem ?_ ?_
      · rw [hFu]
        exact hK₀A.1
      · intro W hW
        exact hK₀A.2 W (hufin.mem_toFinset.mp hW)
    have hle : hyperRow (ENNReal.ofReal q) (⋃₀ ↑hufin.toFinset) hufin.toFinset
        ≤ ⨆ (q : ℚ) (u : Finset (Set X)) (_ : ↑u ⊆ B) (_ : 0 < q)
            (_ : ∀ K, hyperRow (ENNReal.ofReal q) (⋃₀ ↑u) u K ≤ Φ K),
            hyperRow (ENNReal.ofReal q) (⋃₀ ↑u) u := by
      refine le_iSup_of_le q ?_
      refine le_iSup_of_le hufin.toFinset ?_
      refine le_iSup_of_le (by rw [hFu]; exact huB) ?_
      refine le_iSup_of_le hq0 ?_
      exact le_iSup_of_le hmin le_rfl
    have hcontra : ENNReal.ofReal q
        ≤ (⨆ (q : ℚ) (u : Finset (Set X)) (_ : ↑u ⊆ B) (_ : 0 < q)
            (_ : ∀ K, hyperRow (ENNReal.ofReal q) (⋃₀ ↑u) u K ≤ Φ K),
            hyperRow (ENNReal.ofReal q) (⋃₀ ↑u) u) K₀ := by
      calc ENNReal.ofReal q
          = hyperRow (ENNReal.ofReal q) (⋃₀ ↑hufin.toFinset)
              hufin.toFinset K₀ := happ.symm
        _ ≤ _ := hle K₀
    exact absurd (lt_of_le_of_lt hcontra h1) (lt_irrefl _)

end TransposedGeneration

end SuFunctor.Universe
