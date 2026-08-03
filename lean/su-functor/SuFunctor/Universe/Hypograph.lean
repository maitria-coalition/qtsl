import SuFunctor.Universe.Sector
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Homeomorph.Lemmas

/-! # The hypograph homeomorphism: radial bodies are hypographs

The Vietoris topology on the radial locus is the hypo-topology on
grade functions: the radial map `(μ, γ) ↦ γ·μ` from the slab
`Δ(V) × [0, 1]` to the subprobability carrier induces a homeomorphism
(`hypoHomeo`) between the **hypograph locus** of the slab's hyperspace
— nonempty compact sets containing the whole zero section and closed
downward in the scale coordinate, i.e. the closed hypographs of usc
grade functions — and the radial locus.

* **The hypograph locus is closed, hence compact**
  (`isClosed_hypoSet`, `isCompact_hypoSet`): the zero section is an
  intersection of point-membership demands (each closed on the
  hyperspace of a T1 base), and downward closure survives Vietoris
  limits by the hit-and-miss transport of `isClosed_setOf_isRadial`,
  with the scale truncation in place of scaling.
* **The zero-section collapse is harmless** — and load-bearing: the
  radial map crushes `Δ(V) × {0}` to the single point `0`, so it is
  far from injective on the slab; but every hypograph contains the
  whole zero section, so the crushed fibers never separate two
  hypographs (`polarLift_map`, the injectivity leg), which is exactly
  where the zero-section axiom earns its place.
* **The polar lift** (`polarLift`) — the preimage of a radial body
  under the radial map — is the two-sided inverse
  (`map_polarLift`, `polarLift_map`), the set-level face of
  `ImageChar`'s gauge reconstruction.
* **The homeomorphism** (`hypoHomeo`): a continuous bijection from a
  compact space to a T2 space; continuity of the image map is the
  hyperspace functoriality of the library, and no metric estimate
  appears anywhere — the memo's uniform-continuity modulus is
  subsumed by Vietoris functoriality.
-/

namespace SuFunctor.Universe

open scoped ENNReal unitInterval
open TopologicalSpace

variable {V : Type*} [Fintype V]

/-! ## The radial map on the slab -/

/-- The radial map: a direction and a scale, sent to the scaled point
of the subprobability carrier. -/
def radialMap (p : ProbState V × I) : BelState V :=
  scalePoint (p.2 : ℝ) p.2.2.1 p.2.2.2 p.1

@[simp] theorem radialMap_coe (p : ProbState V × I) :
    ((radialMap p : BelState V) : V → ℝ) = (p.2 : ℝ) • ((p.1 : ProbState V) : V → ℝ) :=
  rfl

theorem continuous_radialMap : Continuous (radialMap (V := V)) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_subtype_val.comp continuous_snd).smul
    (continuous_subtype_val.comp continuous_fst)

theorem radialMap_zero_scale (μ : ProbState V) :
    radialMap (μ, (0 : I)) = BelState.zero V := by
  refine Subtype.ext (funext fun v => ?_)
  simp [radialMap]

/-- Every distribution lies on some ray: the radial map is onto. -/
theorem surjective_radialMap [Nonempty V] :
    Function.Surjective (radialMap (V := V)) := by
  intro x
  rcases BelState.exists_polar x with h0 | ⟨μ, m, hm0, hm1, he⟩
  · obtain ⟨μ⟩ := (inferInstance : Nonempty (ProbState V))
    refine ⟨(μ, 0), Subtype.ext ?_⟩
    rw [h0]
    funext v
    simp [radialMap]
  · exact ⟨(μ, ⟨m, hm0.le, hm1⟩), Subtype.ext he.symm⟩

/-! ## The hypograph locus of the slab's hyperspace -/

variable (V) in
/-- The hypograph locus: nonempty compact subsets of the slab that
contain the whole zero section and are closed downward in scale —
exactly the closed hypographs of usc grade functions `Δ(V) → [0, 1]`. -/
def hypoSet : Set (NonemptyCompacts (ProbState V × I)) :=
  {H | (∀ μ : ProbState V, ((μ, 0) : ProbState V × I) ∈ H)
    ∧ ∀ p ∈ (H : Set (ProbState V × I)), ∀ t : I, t ≤ p.2 → (p.1, t) ∈ H}

theorem mem_hypoSet_iff {H : NonemptyCompacts (ProbState V × I)} :
    H ∈ hypoSet V
      ↔ (∀ μ : ProbState V, ((μ, 0) : ProbState V × I) ∈ H)
        ∧ ∀ p ∈ (H : Set (ProbState V × I)), ∀ t : I, t ≤ p.2 → (p.1, t) ∈ H :=
  Iff.rfl

/-- Point membership is a closed demand on the hyperspace of any T1
base — the general form of the record lens's discrete graph-face
lemma. -/
theorem isClosed_setOf_mem_nonemptyCompacts {α : Type*} [TopologicalSpace α]
    [T1Space α] (x : α) : IsClosed {K : NonemptyCompacts α | x ∈ K} := by
  rw [← isOpen_compl_iff]
  have heq : {K : NonemptyCompacts α | x ∈ K}ᶜ
      = {K : NonemptyCompacts α | (K : Set α) ⊆ {x}ᶜ} := by
    ext K
    simp [Set.subset_compl_singleton_iff]
  rw [heq]
  exact NonemptyCompacts.isOpen_subsets_of_isOpen isOpen_compl_singleton

/-- Downward scale-closure survives hyperspace limits: the
hit-and-miss transport of the radial locus's closedness, with scale
truncation in place of scaling. -/
theorem isClosed_setOf_downClosed :
    IsClosed {H : NonemptyCompacts (ProbState V × I) |
      ∀ p ∈ (H : Set (ProbState V × I)), ∀ t : I, t ≤ p.2 → (p.1, t) ∈ H} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  rintro H hH
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hH
  push Not at hH
  obtain ⟨p, hpH, t, hle, hout⟩ := hH
  have hpos : 0 < Metric.infDist ((p.1, t) : ProbState V × I)
      (H : Set (ProbState V × I)) :=
    (IsClosed.notMem_iff_infDist_pos H.isCompact.isClosed H.nonempty).mp hout
  set ε := Metric.infDist ((p.1, t) : ProbState V × I)
    (H : Set (ProbState V × I)) with hε
  refine ⟨{H' : NonemptyCompacts (ProbState V × I) |
        ((H' : Set (ProbState V × I)) ∩ Metric.ball p (ε / 2)).Nonempty}
      ∩ {H' : NonemptyCompacts (ProbState V × I) |
        (H' : Set (ProbState V × I))
          ⊆ (Metric.closedBall ((p.1, t) : ProbState V × I) (ε / 2))ᶜ},
    ?_, ?_, ?_⟩
  · -- every hyperspace point in the neighborhood fails downward closure
    rintro H' ⟨⟨p', hp'H, hp'ball⟩, hmiss⟩
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    push Not
    have hfst : dist p'.1 p.1 ≤ dist p' p := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    have hsnd : dist p'.2 p.2 ≤ dist p' p := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    have hp'p : dist p' p < ε / 2 := Metric.mem_ball.mp hp'ball
    rcases le_total t p'.2 with hcase | hcase
    · -- the truncated point is trapped inside the miss-ball
      refine ⟨p', hp'H, t, hcase, fun hmem => hmiss hmem ?_⟩
      rw [Metric.mem_closedBall]
      have hd : dist ((p'.1, t) : ProbState V × I) (p.1, t)
          = dist p'.1 p.1 := by
        rw [Prod.dist_eq, dist_self]
        exact max_eq_left dist_nonneg
      rw [hd]
      exact (hfst.trans_lt hp'p).le
    · -- the member itself would sit inside the miss-ball: contradiction
      exfalso
      refine hmiss hp'H ?_
      rw [Metric.mem_closedBall]
      have hd2 : dist p'.2 t ≤ dist p'.2 p.2 := by
        rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
        have h1 : (p'.2 : ℝ) ≤ (t : ℝ) := hcase
        have h2 : (t : ℝ) ≤ (p.2 : ℝ) := hle
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h1),
          abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (h1.trans h2))]
        linarith
      have hd : dist p' ((p.1, t) : ProbState V × I) ≤ dist p' p := by
        rw [Prod.dist_eq]
        exact max_le hfst (hd2.trans hsnd)
      exact (hd.trans_lt hp'p).le
  · exact (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen
      Metric.isOpen_ball).inter
      (NonemptyCompacts.isOpen_subsets_of_isOpen
        Metric.isClosed_closedBall.isOpen_compl)
  · constructor
    · exact ⟨p, hpH, Metric.mem_ball_self (by positivity)⟩
    · intro y hyH
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le]
      calc ε / 2 < ε := by linarith
        _ ≤ dist ((p.1, t) : ProbState V × I) y :=
            Metric.infDist_le_dist_of_mem hyH
        _ = dist y ((p.1, t) : ProbState V × I) := dist_comm _ _

theorem isClosed_hypoSet : IsClosed (hypoSet V) := by
  have heq : hypoSet V
      = (⋂ μ : ProbState V,
          {H : NonemptyCompacts (ProbState V × I) |
            ((μ, 0) : ProbState V × I) ∈ H})
        ∩ {H : NonemptyCompacts (ProbState V × I) |
            ∀ p ∈ (H : Set (ProbState V × I)), ∀ t : I, t ≤ p.2 →
              (p.1, t) ∈ H} := by
    ext H
    simp only [hypoSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [heq]
  exact (isClosed_iInter fun μ =>
    isClosed_setOf_mem_nonemptyCompacts _).inter isClosed_setOf_downClosed

theorem isCompact_hypoSet : IsCompact (hypoSet V) :=
  isClosed_hypoSet.isCompact

/-! ## The image of a hypograph is radial -/

theorem isRadial_map_radialMap {H : NonemptyCompacts (ProbState V × I)}
    (hH : H ∈ hypoSet V) :
    IsRadial ((H.map radialMap continuous_radialMap :
      NonemptyCompacts (BelState V)) : Set (BelState V)) := by
  rintro x hx s hs0 hs1
  rw [NonemptyCompacts.coe_map] at hx ⊢
  obtain ⟨p, hpH, rfl⟩ := hx
  have hmem : s * (p.2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hs0 p.2.2.1, by
      calc s * (p.2 : ℝ) ≤ 1 * 1 :=
            mul_le_mul hs1 p.2.2.2 p.2.2.1 zero_le_one
        _ = 1 := one_mul 1⟩
  refine ⟨(p.1, ⟨s * (p.2 : ℝ), hmem⟩), hH.2 p hpH _ ?_, ?_⟩
  · exact Subtype.coe_le_coe.mp (mul_le_of_le_one_left p.2.2.1 hs1)
  · refine Subtype.ext ?_
    rw [BelState.coe_scale, radialMap_coe, radialMap_coe, smul_smul]

/-! ## The polar lift -/

/-- The polar lift of a radial body: its preimage under the radial
map — the hypograph of its ray gauge. -/
noncomputable def polarLift [Nonempty V] (K : RadialCompacts V) :
    NonemptyCompacts (ProbState V × I) :=
  ⟨⟨radialMap ⁻¹' (K.1 : Set (BelState V)),
    (IsClosed.preimage continuous_radialMap
      K.1.isCompact.isClosed).isCompact⟩,
    ⟨(Classical.arbitrary (ProbState V), 0), by
      show radialMap _ ∈ (K.1 : Set (BelState V))
      rw [radialMap_zero_scale]
      exact zero_mem_of_isRadial K.2 K.1.nonempty⟩⟩

@[simp] theorem coe_polarLift [Nonempty V] (K : RadialCompacts V) :
    (polarLift K : Set (ProbState V × I))
      = radialMap ⁻¹' (K.1 : Set (BelState V)) :=
  rfl

theorem polarLift_mem_hypoSet [Nonempty V] (K : RadialCompacts V) :
    polarLift K ∈ hypoSet V := by
  constructor
  · intro μ
    show radialMap _ ∈ (K.1 : Set (BelState V))
    rw [radialMap_zero_scale]
    exact zero_mem_of_isRadial K.2 K.1.nonempty
  · rintro ⟨μ, γ⟩ hp t ht
    have hp' : radialMap (μ, γ) ∈ (K.1 : Set (BelState V)) := hp
    show radialMap (μ, t) ∈ (K.1 : Set (BelState V))
    rcases (γ.2.1 : (0 : ℝ) ≤ γ).lt_or_eq with hγ | hγ
    · -- descend the ray inside the body
      have ht0 : 0 ≤ (t : ℝ) / (γ : ℝ) := div_nonneg t.2.1 hγ.le
      have ht1 : (t : ℝ) / (γ : ℝ) ≤ 1 := (div_le_one hγ).mpr ht
      have he : radialMap ((μ, t) : ProbState V × I)
          = BelState.scale ((t : ℝ) / (γ : ℝ)) ht0 ht1 (radialMap (μ, γ)) := by
        refine Subtype.ext ?_
        rw [BelState.coe_scale, radialMap_coe, radialMap_coe, smul_smul,
          div_mul_cancel₀ _ hγ.ne']
      rw [he]
      exact K.2 _ hp' _ ht0 ht1
    · -- the ray is degenerate: the scale was already zero
      have htγ : t = γ := by
        refine Subtype.ext (le_antisymm (Subtype.coe_le_coe.mpr ht) ?_)
        rw [← hγ]
        exact t.2.1
      rwa [htγ]

/-! ## The round trips -/

/-- Image after lift: the radial map is onto each radial body, so the
lift reconstructs it exactly. -/
theorem map_polarLift [Nonempty V] (K : RadialCompacts V) :
    (polarLift K).map radialMap continuous_radialMap = K.1 := by
  refine NonemptyCompacts.ext ?_
  rw [NonemptyCompacts.coe_map, coe_polarLift]
  exact Set.image_preimage_eq _ surjective_radialMap

/-- Lift after image: the zero section absorbs the collapsed fibers,
and polar uniqueness separates the rest — injectivity of the compile,
set-side. -/
theorem polarLift_map [Nonempty V] {H : NonemptyCompacts (ProbState V × I)}
    (hH : H ∈ hypoSet V) :
    polarLift ⟨H.map radialMap continuous_radialMap,
      isRadial_map_radialMap hH⟩ = H := by
  refine NonemptyCompacts.ext ?_
  rw [coe_polarLift]
  show radialMap ⁻¹' ((H.map radialMap continuous_radialMap :
    NonemptyCompacts (BelState V)) : Set (BelState V)) = _
  rw [NonemptyCompacts.coe_map]
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro ⟨μ, γ⟩ hp
  obtain ⟨⟨μ', γ'⟩, hq, heq⟩ := hp
  have hval : (γ' : ℝ) • ((μ' : ProbState V) : V → ℝ)
      = (γ : ℝ) • ((μ : ProbState V) : V → ℝ) := by
    have := congrArg (fun x : BelState V => (x : V → ℝ)) heq
    simpa using this
  rcases (γ.2.1 : (0 : ℝ) ≤ γ).lt_or_eq with hγ | hγ
  · -- positive scale: polar uniqueness identifies the fibers
    have hscale : (γ' : ℝ) = (γ : ℝ) := polar_scale_eq hval
    have hstate : μ' = μ := by
      refine polar_state_eq hγ.ne' ?_
      rw [← hscale] at hval ⊢
      exact hval
    have : ((μ', γ') : ProbState V × I) = (μ, γ) := by
      rw [hstate]
      exact Prod.ext rfl (Subtype.ext hscale)
    rwa [← this]
  · -- zero scale: the zero section owns the point outright
    have hγ0 : γ = (0 : I) := Subtype.ext hγ.symm
    rw [hγ0]
    exact hH.1 μ

/-! ## The homeomorphism -/

/-- The underlying equivalence: hypographs to radial bodies by the
radial image, back by the polar lift. -/
noncomputable def hypoEquiv [Nonempty V] : ↥(hypoSet V) ≃ RadialCompacts V where
  toFun H := ⟨H.1.map radialMap continuous_radialMap,
    isRadial_map_radialMap H.2⟩
  invFun K := ⟨polarLift K, polarLift_mem_hypoSet K⟩
  left_inv H := Subtype.ext (polarLift_map H.2)
  right_inv K := Subtype.ext (map_polarLift K)

/-- **The hypograph homeomorphism**: the Vietoris topology on the
radial locus is the hypo-topology — the hyperspace topology on closed
hypographs of grade functions.  A continuous bijection from a compact
space onto a T2 space; hyperspace functoriality carries the
continuity, no metric modulus needed. -/
noncomputable def hypoHomeo [Nonempty V] : ↥(hypoSet V) ≃ₜ RadialCompacts V :=
  haveI : CompactSpace ↥(hypoSet V) :=
    isCompact_iff_compactSpace.mp isCompact_hypoSet
  Continuous.homeoOfEquivCompactToT2 (f := hypoEquiv)
    (Continuous.subtype_mk
      ((continuous_radialMap.nonemptyCompacts_map).comp
        continuous_subtype_val) _)

@[simp] theorem hypoHomeo_apply [Nonempty V] (H : ↥(hypoSet V)) :
    (hypoHomeo H).1 = H.1.map radialMap continuous_radialMap :=
  rfl

@[simp] theorem hypoHomeo_symm_apply [Nonempty V] (K : RadialCompacts V) :
    ((hypoHomeo.symm K : ↥(hypoSet V)) : NonemptyCompacts (ProbState V × I))
      = polarLift K :=
  rfl

end SuFunctor.Universe
