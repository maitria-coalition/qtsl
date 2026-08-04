import QtslAux.QuantumStackVonNeumann
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # The bottom of the von Neumann lattice, and two-valued nets

`QtslAux.QuantumStackVonNeumann` proved the descent comparison for a
net of von Neumann algebras fully faithful under generation and
connectivity, and built the missing upstream vocabulary (`generate`, a
`⊤` instance, the bicommutant lemma).  This module adds the *other end
of the lattice* and its descent-theoretic consumer:

* **The scalars are the bottom.**  `⊥ := generate ∅` is a von Neumann
  algebra by construction, and `bot_le` is immediate from `generate_le`.
  The content is the identification of the carrier: the double
  centralizer of the empty set is the centralizer of *everything* — the
  center of `B(H)` — and the **operator Schur lemma**
  (`centralizer_univ_eq_range_algebraMap`, proved here by a rank-one
  argument: an operator commuting with `z ↦ ⟪y, z⟫ • x` for every `x`
  scales every vector by the same ratio `⟪y, T y⟫ / ⟪y, y⟫`) identifies
  that center with the scalar operators.  So "⊥ is the scalars" is a
  theorem (`coe_bot`), not a definition, and the lattice's two ends
  come with order instances (`OrderBot`, `OrderTop`, `BoundedOrder`)
  and the polar pair `commutant_top = ⊥`, `commutant_bot = ⊤`.  No
  operator topology appears anywhere in this file.

* **Two-valued nets.**  `twoValuedWNet` assigns `⊤` on an upward-closed
  predicate of diamonds and `⊥` off it — observable nets valued in the
  scalars-vs-full dichotomy, the Boolean fragment of the von Neumann
  lattice made into net data.  Three witnesses on the landed Minkowski
  site:

  - the constant-`⊥` net is fully faithful at the canonical interior
    cover (`scalarWNet_full_interior`) — full faithfulness holds at the
    lattice's bottom exactly as at its top, each by attainment;
  - the **step net** (`⊤` precisely on diamonds containing the apex
    `Dstar`) satisfies isotony but *fails the generation hypothesis* at
    the canonical interior cover (`stepNet_not_generated`): interiority
    is chronologically strict, so no interior-sieve member contains the
    apex (`not_le_of_interiorSieve_arrow`), every member algebra is the
    scalars, and the generated algebra stays at `⊥` while the apex
    carries `⊤`;
  - **fullness itself fails there** (`stepNet_not_full`): the
    everywhere-`T` endomorphism of the unit descent datum
    (`stepConstEndo`) is lawful for an arbitrary operator `T` — scalars
    commute with everything, so the commutant condition over each
    member is free — but a preimage under the comparison would place
    `T` in the commutant of `⊤`, which is the center, which is the
    scalars.  Taking `T` non-scalar (the rank-one witness
    `smulRight_innerSL_notMem_range_algebraMap`, e.g. on the qubit
    space `EuclideanSpace ℂ (Fin 2)`) refutes fullness.  The generation
    hypothesis of `descentComparisonW_full` is thereby load-bearing at
    operator grade: a kernel-checked bottom-vs-top contrast on one
    cover.

Descent for categories fibered over sites is Benini–Grant-Stuart–Schenkel
(arXiv:2404.14510); nets of operator algebras on causal diamonds are
Haag–Kastler (J. Math. Phys. 5, 848 (1964)); interiority as order-grade
relative compactness is Martin–Panangaden (arXiv:gr-qc/0407094); the
rank-one characterization of the center of `B(H)` is the operator form
of Schur's lemma for the standard representation.
-/

noncomputable section

open scoped ComplexInnerProductSpace

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ## The operator Schur lemma -/

omit [CompleteSpace H] in
/-- **The operator Schur lemma**: the center of the bounded operators
on a complex Hilbert space consists of the scalar operators.  The
nontrivial inclusion is by rank-one operators: if `T` commutes with
`z ↦ ⟪y, z⟫ • x` for a fixed nonzero `y` and every `x`, then evaluating
the commutation identity at `y` gives `⟪y, T y⟫ • x = ⟪y, y⟫ • T x`, so
`T` is the scalar `⟪y, y⟫⁻¹ * ⟪y, T y⟫`.  No operator topology — and no
completeness — is consumed. -/
theorem centralizer_univ_eq_range_algebraMap :
    Set.centralizer (Set.univ : Set (H →L[ℂ] H))
      = Set.range (algebraMap ℂ (H →L[ℂ] H)) := by
  apply Set.eq_of_subset_of_subset
  · intro T hT
    by_cases hH : ∃ y : H, y ≠ 0
    · obtain ⟨y, hy⟩ := hH
      have hyy : (⟪y, y⟫ : ℂ) ≠ 0 := inner_self_ne_zero.mpr hy
      refine ⟨(⟪y, y⟫ : ℂ)⁻¹ * ⟪y, T y⟫, ?_⟩
      ext x
      have hcomm := hT ((innerSL ℂ y).smulRight x) (Set.mem_univ _)
      have h1 := congrArg (fun f : H →L[ℂ] H => f y) hcomm
      simp only [mul_apply_eq_comp, ContinuousLinearMap.smulRight_apply,
        innerSL_apply_apply, map_smul] at h1
      -- h1 : ⟪y, T y⟫ • x = ⟪y, y⟫ • T x
      show ((⟪y, y⟫ : ℂ)⁻¹ * ⟪y, T y⟫) • x = T x
      rw [mul_smul, h1, inv_smul_smul₀ hyy]
    · refine ⟨0, ?_⟩
      ext x
      have hx : T x = 0 := not_not.mp fun h => hH ⟨T x, h⟩
      simp [hx]
  · rintro _ ⟨c, rfl⟩
    intro m _
    exact (Algebra.commutes c m).symm

/-! ## The bottom of the lattice -/

/-- The scalars, as the von Neumann algebra generated by the empty
set: the bottom of the lattice of von Neumann algebras on `H`. -/
instance : Bot (VonNeumannAlgebra H) :=
  ⟨generate ∅⟩

theorem generate_empty : generate (∅ : Set (H →L[ℂ] H)) = ⊥ := rfl

/-- Pre-Schur characterization of the bottom: the carrier of `⊥` is
the centralizer of everything — the center of `B(H)`. -/
theorem coe_bot_eq_centralizer_univ :
    ((⊥ : VonNeumannAlgebra H) : Set (H →L[ℂ] H))
      = Set.centralizer Set.univ := by
  show (generate (∅ : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) = _
  rw [coe_generate, Set.star_empty, Set.union_self, Set.centralizer_empty,
    Set.top_eq_univ]

/-- **The bottom of the von Neumann lattice is the scalars.** -/
theorem coe_bot :
    ((⊥ : VonNeumannAlgebra H) : Set (H →L[ℂ] H))
      = Set.range (algebraMap ℂ (H →L[ℂ] H)) := by
  rw [coe_bot_eq_centralizer_univ, centralizer_univ_eq_range_algebraMap]

theorem mem_bot_iff {x : H →L[ℂ] H} :
    x ∈ (⊥ : VonNeumannAlgebra H)
      ↔ ∃ c : ℂ, algebraMap ℂ (H →L[ℂ] H) c = x := by
  rw [← SetLike.mem_coe, coe_bot]
  exact Set.mem_range

theorem coe_top :
    ((⊤ : VonNeumannAlgebra H) : Set (H →L[ℂ] H)) = Set.univ :=
  Set.eq_univ_of_forall mem_top

/-- The generated von Neumann algebra of the empty set is below every
von Neumann algebra: the lattice has a bottom in the order sense. -/
instance : OrderBot (VonNeumannAlgebra H) where
  bot_le _ := generate_le (Set.empty_subset _)

instance : OrderTop (VonNeumannAlgebra H) where
  le_top _ x _ := mem_top x

instance : BoundedOrder (VonNeumannAlgebra H) where

/-- The commutant of everything is the scalars: one half of the polar
pair at the ends of the lattice. -/
theorem commutant_top :
    (⊤ : VonNeumannAlgebra H).commutant = ⊥ := by
  apply SetLike.coe_injective
  rw [coe_commutant, coe_top, coe_bot_eq_centralizer_univ]

/-- The commutant of the scalars is everything: the other half of the
polar pair.  Only the pre-Schur direction is consumed — central
elements commute with everything. -/
theorem commutant_bot :
    (⊥ : VonNeumannAlgebra H).commutant = ⊤ := by
  apply SetLike.coe_injective
  rw [coe_commutant, coe_top, coe_bot_eq_centralizer_univ]
  refine Set.eq_univ_of_forall fun T => ?_
  intro m hm
  exact (hm T (Set.mem_univ T)).symm

/-! ## A non-scalar operator from an orthogonal pair -/

omit [CompleteSpace H] in
/-- The rank-one operator `z ↦ ⟪y₀, z⟫ • y₀` built from a nonzero
vector with a nonzero orthogonal companion is not a scalar operator:
it kills `y₁` but not `y₀`. -/
theorem smulRight_innerSL_notMem_range_algebraMap {y₀ y₁ : H}
    (h₀ : y₀ ≠ 0) (h₁ : y₁ ≠ 0) (horth : (⟪y₀, y₁⟫ : ℂ) = 0) :
    ((innerSL ℂ y₀).smulRight y₀ : H →L[ℂ] H)
      ∉ Set.range (algebraMap ℂ (H →L[ℂ] H)) := by
  rintro ⟨c, hc⟩
  have e₁ := congrArg (fun f : H →L[ℂ] H => f y₁) hc
  simp only [ContinuousLinearMap.algebraMap_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, horth,
    zero_smul] at e₁
  -- e₁ : c • y₁ = 0
  have hc0 : c = 0 := by
    rcases smul_eq_zero.mp e₁ with h | h
    · exact h
    · exact absurd h h₁
  have e₀ := congrArg (fun f : H →L[ℂ] H => f y₀) hc
  simp only [ContinuousLinearMap.algebraMap_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hc0,
    zero_smul] at e₀
  -- e₀ : 0 = ⟪y₀, y₀⟫ • y₀
  exact smul_ne_zero (inner_self_ne_zero.mpr h₀) h₀ e₀.symm

/-- The lattice's two ends are distinct as soon as a non-scalar
operator exists. -/
theorem bot_ne_top
    (hex : ∃ T : H →L[ℂ] H, T ∉ Set.range (algebraMap ℂ (H →L[ℂ] H))) :
    (⊥ : VonNeumannAlgebra H) ≠ ⊤ := by
  obtain ⟨T, hT⟩ := hex
  intro h
  apply hT
  have hTbot : T ∈ (⊥ : VonNeumannAlgebra H) := by
    rw [h]; exact mem_top T
  rwa [← SetLike.mem_coe, coe_bot] at hTbot

theorem bot_lt_top
    (hex : ∃ T : H →L[ℂ] H, T ∉ Set.range (algebraMap ℂ (H →L[ℂ] H))) :
    (⊥ : VonNeumannAlgebra H) < ⊤ :=
  lt_of_le_of_ne bot_le (bot_ne_top hex)

/-- Non-vacuity anchor: on the qubit space the bottom and the top are
distinct — the rank-one witness at the standard orthogonal pair. -/
theorem bot_ne_top_qubit :
    (⊥ : VonNeumannAlgebra (EuclideanSpace ℂ (Fin 2))) ≠ ⊤ := by
  refine bot_ne_top ⟨(innerSL ℂ (EuclideanSpace.single 0 1)).smulRight
    (EuclideanSpace.single 0 1),
    smulRight_innerSL_notMem_range_algebraMap
      (y₁ := EuclideanSpace.single 1 1) ?_ ?_ ?_⟩
  · simp [PiLp.single_eq_zero_iff]
  · simp [PiLp.single_eq_zero_iff]
  · rw [EuclideanSpace.inner_single_left]
    simp

end VonNeumannAlgebra

namespace Qtsl
namespace QuantumStack

open CategoryTheory DiamondSite QuantumDescent

variable {X : Type*} [PartialOrder X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ## Two-valued nets -/

/-- A two-valued net: all bounded operators on the diamonds satisfying
an upward-closed predicate, the scalars elsewhere.  Observable nets
valued in the scalars-vs-full dichotomy — the Boolean fragment of the
von Neumann lattice as net data. -/
@[reducible] def twoValuedWNet (P : Diamond X → Prop) [DecidablePred P]
    (hP : ∀ ⦃E D : Diamond X⦄, E ≤ D → P E → P D) : WNet X H where
  alg D := if P D then ⊤ else ⊥
  isotone {E D} hED := by
    by_cases hE : P E
    · rw [if_pos hE, if_pos (hP hED hE)]
    · rw [if_neg hE]
      exact bot_le

@[simp] theorem twoValuedWNet_alg_pos (P : Diamond X → Prop)
    [DecidablePred P] (hP : ∀ ⦃E D : Diamond X⦄, E ≤ D → P E → P D)
    {D : Diamond X} (hD : P D) :
    (twoValuedWNet (H := H) P hP).alg D = ⊤ :=
  if_pos hD

@[simp] theorem twoValuedWNet_alg_neg (P : Diamond X → Prop)
    [DecidablePred P] (hP : ∀ ⦃E D : Diamond X⦄, E ≤ D → P E → P D)
    {D : Diamond X} (hD : ¬ P D) :
    (twoValuedWNet (H := H) P hP).alg D = ⊥ :=
  if_neg hD

/-- The constant net at the bottom: every diamond carries exactly the
scalars. -/
def scalarWNet (X : Type*) [PartialOrder X] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    WNet X H where
  alg _ := ⊥
  isotone _ := le_rfl

/-- Full faithfulness at the canonical interior cover holds at the
lattice's bottom exactly as at its top: the constant scalar net is
interior-attained, so the landed fullness theorem applies verbatim. -/
theorem scalarWNet_full_interior :
    (descentComparisonW (scalarWNet (Mink ℝ) H) Dstar
      (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit) Dstar)).Full :=
  descentComparisonW_full_interior _ _ E₃_interior
    ((minkowskiKit (E := ℝ)).interior_directed Dstar)
    (le_generate_of_attained
      (MixingKit.sub_of_interiorMem E₃_interior)
      ⟨E₃, E₃_interior, le_rfl⟩ le_rfl)

/-- Faithfulness half of the bottom witness. -/
theorem scalarWNet_faithful_interior :
    (descentComparisonW (scalarWNet (Mink ℝ) H) Dstar
      (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit) Dstar)).Faithful :=
  descentComparisonW_faithful_interior _ _ E₃_interior

/-! ## Interior members never contain the apex -/

/-- At any mixing kit whose chronology is irreflexive at the base's
lower endpoint, no member of the canonical interior sieve contains the
base diamond: interiority is strict containment. -/
theorem not_le_of_interiorSieve_arrow {M : MixingKit X}
    {D E : Diamond X} (hirr : ¬ M.chron D.lo D.lo) (hE : E ≤ D)
    (hS : (interiorSieve M D).arrows (homOfLE hE)) : ¬ D ≤ E := by
  intro hDE
  obtain ⟨F, hDF, hEF⟩ := hS
  exact hirr (M.chron_of_chron_le hDF.1 (le_iff_sub.mp (hDE.trans hEF)).1)

/-- The Minkowski chronology is irreflexive: no event chronologically
precedes itself.  This strictness is what localizes the two-valued
dichotomy below. -/
theorem mink_chron_irrefl {E' : Type*} [NormedAddCommGroup E']
    (a : Mink E') : ¬ Mink.chron a a := by
  intro h
  have h' : ‖a.x - a.x‖ < a.t - a.t := h
  rw [sub_self, norm_zero, sub_self] at h'
  exact lt_irrefl 0 h'

/-! ## The step net: the bottom-vs-top contrast on one cover -/

/-- Classical decidability for the step predicate: the step net is a
noncomputable witness, and pinning one named instance makes every
consumer of `twoValuedWNet`'s conditional agree definitionally. -/
noncomputable instance stepDec :
    DecidablePred (fun D : Diamond (Mink ℝ) => Dstar ≤ D) :=
  fun _ => Classical.propDecidable _

/-- The step net on the Minkowski site: all bounded operators exactly
on the diamonds containing the apex `Dstar`, the scalars on every
smaller region.  Isotone by transitivity of containment. -/
@[reducible] def stepNet (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : WNet (Mink ℝ) H :=
  twoValuedWNet (fun D => Dstar ≤ D)
    (fun _ _ hED hE => hE.trans hED)

/-- The apex carries everything. -/
theorem stepNet_alg_apex : (stepNet H).alg Dstar = ⊤ :=
  twoValuedWNet_alg_pos _ _ le_rfl

/-- Every member of the canonical interior sieve carries only the
scalars: interiority is chronologically strict, so no member contains
the apex. -/
theorem stepNet_alg_member ⦃E : Diamond (Mink ℝ)⦄ (hE : E ≤ Dstar)
    (hS : (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit)
      Dstar).arrows (homOfLE hE)) :
    (stepNet H).alg E = ⊥ :=
  twoValuedWNet_alg_neg _ _
    (not_le_of_interiorSieve_arrow (mink_chron_irrefl Dstar.lo) hE hS)

/-- The union of the member algebras of the canonical interior cover
lies inside the scalars. -/
theorem stepNet_netUnion_subset_bot :
    netUnion (stepNet H) Dstar
        (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit) Dstar)
      ⊆ ((⊥ : VonNeumannAlgebra H) : Set (H →L[ℂ] H)) := by
  intro x hx
  simp only [netUnion, Set.mem_iUnion] at hx
  obtain ⟨E, hE, hS, hxE⟩ := hx
  have hxE' : x ∈ (stepNet H).alg E := hxE
  rw [stepNet_alg_member hE hS] at hxE'
  exact hxE'

/-- **Generation fails at the canonical interior cover for the step
net**: the generated algebra of the member union stays at the scalars
while the apex carries all bounded operators.  The generation
hypothesis of the fullness theorem is not implied by isotony. -/
theorem stepNet_not_generated
    (hex : ∃ T : H →L[ℂ] H, T ∉ Set.range (algebraMap ℂ (H →L[ℂ] H))) :
    ¬ ((stepNet H).alg Dstar ≤ VonNeumannAlgebra.generate
        (netUnion (stepNet H) Dstar
          (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit) Dstar))) := by
  obtain ⟨T, hT⟩ := hex
  intro hle
  have hbot : VonNeumannAlgebra.generate
      (netUnion (stepNet H) Dstar
        (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit) Dstar))
      ≤ (⊥ : VonNeumannAlgebra H) :=
    VonNeumannAlgebra.generate_le stepNet_netUnion_subset_bot
  have hTmem : T ∈ (stepNet H).alg Dstar := by
    rw [stepNet_alg_apex]
    exact VonNeumannAlgebra.mem_top T
  have hTbot := hbot (hle hTmem)
  rw [← SetLike.mem_coe, VonNeumannAlgebra.coe_bot] at hTbot
  exact hT hTbot

/-- The everywhere-`T` endomorphism of the step net's unit descent
datum at the canonical interior cover: lawful for an *arbitrary*
operator `T`, because every member algebra is the scalars and scalars
commute with everything (the pre-Schur direction only). -/
def stepConstEndo (T : H →L[ℂ] H) :
    (descentComparisonW (stepNet H) Dstar
        (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit) Dstar)).obj
          (unitSubRep ((stepNet H).alg Dstar)) ⟶
      (descentComparisonW (stepNet H) Dstar
        (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit) Dstar)).obj
          (unitSubRep ((stepNet H).alg Dstar)) where
  app E hE hS :=
    { val := T
      mem_commutant := by
        rw [VonNeumannAlgebra.mem_commutant_iff]
        intro g hg
        have hg' : g ∈ (⊥ : VonNeumannAlgebra H) := by
          rw [← stepNet_alg_member hE hS]
          exact hg
        rw [← SetLike.mem_coe,
          VonNeumannAlgebra.coe_bot_eq_centralizer_univ] at hg'
        exact (hg' T (Set.mem_univ T)).symm
      compress := by
        show (1 : H →L[ℂ] H) * T * 1 = T
        rw [one_mul, mul_one] }
  compat E F hEF hFD hSF hSE := by
    simp only [Iso.refl_hom, SubRep.id_val]
    show (1 : H →L[ℂ] H) * T = T * 1
    rw [one_mul, mul_one]

@[simp] theorem stepConstEndo_app_val (T : H →L[ℂ] H)
    ⦃E : Diamond (Mink ℝ)⦄ (hE : E ≤ Dstar)
    (hS : (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit)
      Dstar).arrows (homOfLE hE)) :
    ((stepConstEndo T).app hE hS).val = T := rfl

/-- **The fullness fence.**  At the canonical interior cover of the
apex, the descent comparison for the step net is not full: the
everywhere-`T` endomorphism of the unit descent datum is lawful for an
arbitrary operator `T`, but a preimage under the comparison would
place `T` in the commutant of `⊤`, i.e. the center of `B(H)`, i.e. the
scalars.  With `T` non-scalar this is absurd: the generation
hypothesis of `descentComparisonW_full` is load-bearing. -/
theorem stepNet_not_full
    (hex : ∃ T : H →L[ℂ] H, T ∉ Set.range (algebraMap ℂ (H →L[ℂ] H))) :
    ¬ (descentComparisonW (stepNet H) Dstar
        (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit) Dstar)).Full := by
  obtain ⟨T, hT⟩ := hex
  intro hFull
  obtain ⟨S, hSu⟩ := hFull.map_surjective (stepConstEndo T)
  have hval : S.val = T := by
    have happ := congrArg
      (fun w : (descentComparisonW (stepNet H) Dstar
          (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit) Dstar)).obj
            (unitSubRep ((stepNet H).alg Dstar)) ⟶
        (descentComparisonW (stepNet H) Dstar
          (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit) Dstar)).obj
            (unitSubRep ((stepNet H).alg Dstar)) =>
        (w.app E₃_le_Dstar ⟨E₃, E₃_interior, le_rfl⟩).val) hSu
    simpa using happ
  have hcen : T ∈ Set.centralizer (Set.univ : Set (H →L[ℂ] H)) := by
    intro m _
    have hmem := S.mem_commutant
    rw [VonNeumannAlgebra.mem_commutant_iff] at hmem
    have hm : m ∈ (stepNet H).alg Dstar := by
      rw [stepNet_alg_apex]
      exact VonNeumannAlgebra.mem_top m
    have hcomm := hmem m hm
    rwa [hval] at hcomm
  rw [VonNeumannAlgebra.centralizer_univ_eq_range_algebraMap] at hcen
  exact hT hcen

/-- The fence is non-vacuous: on the qubit space, the step net's
comparison at the canonical interior cover is not full. -/
theorem stepNet_qubit_not_full :
    ¬ (descentComparisonW (stepNet (EuclideanSpace ℂ (Fin 2))) Dstar
        (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit) Dstar)).Full :=
  stepNet_not_full
    ⟨(innerSL ℂ (EuclideanSpace.single 0 1)).smulRight
        (EuclideanSpace.single 0 1),
      VonNeumannAlgebra.smulRight_innerSL_notMem_range_algebraMap
        (y₁ := EuclideanSpace.single 1 1)
        (by simp [PiLp.single_eq_zero_iff])
        (by simp [PiLp.single_eq_zero_iff])
        (by rw [EuclideanSpace.inner_single_left]
            simp)⟩

end QuantumStack
end Qtsl
