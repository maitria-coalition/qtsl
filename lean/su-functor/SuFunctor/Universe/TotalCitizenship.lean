import SuFunctor.Universe.TopologicalCitizenship

/-! # Total citizenship: transport preserves constructibility along every outcome map

`SuFunctor.Universe.TransportCitizenship` proved the structure theorem of
the surjective stratum and exhibited the non-surjective seam;
`SuFunctor.Universe.TopologicalCitizenship` laid the topological brick and
proved constructibility preservation along surjective outcome maps.  This
module removes the surjectivity hypothesis: image-transport citizenship is
**total**.

* **Transport factors contravariantly** (`transportClass_comp`): the
  hyperspace class transport of a composite outcome map is the composite
  of the transports, in reversed order — with no hypotheses at all.  In
  particular every transport factors through the surjection onto the range
  followed by the subtype inclusion.
* **The biting case split** (`Biting`): a liveness demand *bites* through
  an outcome map when its escape region inside the safety body lies
  wholly on the range of the pushforward.  Biting demands transfer to the
  transported class; non-biting demands are dischargeable by supplement
  points off the range, and vanish.  Along a surjective map every demand
  bites (`biting_of_surjective`); the non-surjective seam of
  `exists_transport_not_subset_pulled_crescent` is a non-biting demand
  being dropped (`exists_not_biting_transportClass_ne`).
* **The total structure theorem** (`transportClass_crescentClass_total`):
  along ANY outcome map, the transported class of a crescent is the
  crescent of the transported atom restricted to its biting demands,
  intersected with the saturated classes.  The two landed strata are its
  faces: surjective maps make every demand bite (recovering
  `transportClass_crescentClass`), and injective maps make every class
  saturated (`saturated_of_injective`), so there the transported crescent
  is *exactly* a crescent
  (`transportClass_crescentClass_of_injective`).
* **Saturation is closed along every outcome map**
  (`isClosed_satClass_total`): saturation is invariant under the range
  factorization (`saturated_rangeFactorization_iff`, via injectivity of
  the inclusion's pushforward), and the factorization's surjective leg
  carries the landed brick.  No new topological arguments are consumed.
* **Citizenship, total**
  (`isLocallyClosed_transportClass_crescentClass_total`,
  `isConstructibleUnion_transportClass_dnfClass_total`): the transported
  class of a crescent is locally closed, and the transported class of a
  citizen DNF class is constructible, along EVERY outcome map — the
  fibre typing of the composition tier needs no surjectivity anywhere.
-/

namespace SuFunctor.Universe

open scoped ENNReal
open TopologicalSpace

/-! ## Functoriality of the pushforward, and contravariant transport -/

section Comp

variable {V U W : Type*} [Fintype V] [Fintype U] [Fintype W]

omit [Fintype W] in
/-- Pushforward along a composite is the composite of the pushforwards:
a finite sum reindexed along the intermediate fibres. -/
theorem pushFun_comp (f : V → U) (g : U → W) (x : V → ℝ) :
    pushFun (g ∘ f) x = pushFun g (pushFun f x) := by
  classical
  funext w
  simp only [pushFun, Function.comp_apply]
  have hstep : ∀ u : U,
      (if g u = w then (∑ v, if f v = u then x v else 0) else 0)
        = ∑ v, if f v = u then (if g (f v) = w then x v else 0) else 0 := by
    intro u
    by_cases hgu : g u = w
    · rw [if_pos hgu]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hfv : f v = u
      · rw [if_pos hfv, if_pos hfv, if_pos (by rw [hfv]; exact hgu)]
      · rw [if_neg hfv, if_neg hfv]
    · rw [if_neg hgu]
      symm
      refine Finset.sum_eq_zero fun v _ => ?_
      by_cases hfv : f v = u
      · rw [if_pos hfv, if_neg (by rw [hfv]; exact hgu)]
      · rw [if_neg hfv]
  rw [Finset.sum_congr rfl fun u _ => hstep u, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_ite_eq Finset.univ (f v)
    (fun _ => if g (f v) = w then x v else 0)]
  simp

/-- Functoriality of the distribution pushforward. -/
theorem BelState.push_comp (f : V → U) (g : U → W) (x : BelState V) :
    BelState.push (g ∘ f) x = BelState.push g (BelState.push f x) :=
  Subtype.ext (by
    rw [BelState.push_coe, BelState.push_coe, BelState.push_coe,
      pushFun_comp])

/-- **Class transport factors contravariantly**, with no hypotheses:
the transport of a composite outcome map is the composite of the
transports in reversed order.  The intermediate member is the body
preimage under the second leg — compact because the carrier is compact,
nonempty because the outer member is. -/
theorem transportClass_comp (f : V → U) (g : U → W)
    (C : Set (NonemptyCompacts (BelState W))) :
    transportClass (g ∘ f) C = transportClass f (transportClass g C) := by
  have hpre : ∀ K : Set (BelState W),
      BelState.push (g ∘ f) ⁻¹' K
        = BelState.push f ⁻¹' (BelState.push g ⁻¹' K) := by
    intro K
    ext x
    simp only [Set.mem_preimage, BelState.push_comp]
  ext L
  constructor
  · rintro ⟨K, hK, hL⟩
    obtain ⟨x, hxL⟩ := L.nonempty
    have hxK : BelState.push f x
        ∈ BelState.push g ⁻¹' (K : Set (BelState W)) := by
      rw [Set.mem_preimage, ← BelState.push_comp]
      have hx : x ∈ BelState.push (g ∘ f) ⁻¹' (K : Set (BelState W)) :=
        hL ▸ hxL
      exact hx
    refine ⟨⟨⟨BelState.push g ⁻¹' (K : Set (BelState W)),
        (K.isCompact.isClosed.preimage (continuous_belPush g)).isCompact⟩,
      ⟨BelState.push f x, hxK⟩⟩, ⟨K, hK, rfl⟩, ?_⟩
    rw [hL]
    exact hpre _
  · rintro ⟨M, ⟨K, hK, hM⟩, hL⟩
    refine ⟨K, hK, ?_⟩
    rw [hL, hM]
    exact (hpre _).symm

end Comp

/-! ## The injective stratum: everything is saturated -/

section Injective

variable {V W : Type*} [Fintype V] [Fintype W]

omit [Fintype W] in
/-- Along an injective outcome map, the pushforward evaluates at the
image of a point to the weight at the point: the fibre is a
singleton. -/
theorem pushFun_apply_of_injective {ι : V → W} (hι : Function.Injective ι)
    (x : V → ℝ) (v : V) : pushFun ι x (ι v) = x v := by
  classical
  show (∑ v', if ι v' = ι v then x v' else 0) = x v
  rw [Finset.sum_eq_single v
    (fun v'' _ hne => if_neg fun he => hne (hι he))
    (fun h => absurd (Finset.mem_univ v) h)]
  exact if_pos rfl

omit [Fintype W] in
theorem pushFun_injective {ι : V → W} (hι : Function.Injective ι) :
    Function.Injective (pushFun (V := V) (W := W) ι) := by
  intro x x' h
  funext v
  have hv := congrFun h (ι v)
  rwa [pushFun_apply_of_injective hι, pushFun_apply_of_injective hι] at hv

/-- Injective outcome maps push distributions injectively. -/
theorem BelState.push_injective {ι : V → W} (hι : Function.Injective ι) :
    Function.Injective (BelState.push (V := V) (W := W) ι) := by
  intro x x' h
  exact Subtype.ext (pushFun_injective hι (congrArg Subtype.val h))

/-- On the injective stratum every class is saturated: the pushforward
loses nothing, so every class is a union of its own (singleton)
fibres. -/
theorem saturated_of_injective {ι : V → W} (hι : Function.Injective ι)
    (L : Set (BelState V)) : Saturated ι L :=
  (Set.preimage_image_eq L (BelState.push_injective hι)).symm

end Injective

/-! ## Saturation along the range factorization -/

section Factorization

variable {V W : Type*} [Fintype V] [Fintype W]

/-- Saturation is invariant under the range factorization: the outcome
map and its surjection onto the range induce the same fibre partition,
because the residual inclusion pushes injectively. -/
theorem saturated_rangeFactorization_iff {θ : V → W}
    [Fintype (Set.range θ)] {L : Set (BelState V)} :
    Saturated θ L ↔ Saturated (Set.rangeFactorization θ) L := by
  have hcomp : ∀ x : BelState V,
      BelState.push θ x
        = BelState.push (Subtype.val : Set.range θ → W)
            (BelState.push (Set.rangeFactorization θ) x) := by
    intro x
    rw [← BelState.push_comp, Set.coe_comp_rangeFactorization]
  have hkey : BelState.push θ ⁻¹' (BelState.push θ '' L)
      = BelState.push (Set.rangeFactorization θ) ⁻¹'
          (BelState.push (Set.rangeFactorization θ) '' L) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨y, hyL, hy⟩
      refine ⟨y, hyL, ?_⟩
      refine BelState.push_injective Subtype.val_injective ?_
      rw [← hcomp y, ← hcomp x]
      exact hy
    · rintro ⟨y, hyL, hy⟩
      exact ⟨y, hyL, by rw [hcomp y, hcomp x, hy]⟩
  constructor
  · intro h
    show L = _
    rw [← hkey]
    exact h
  · intro h
    show L = _
    rw [hkey]
    exact h

/-- **The saturated classes form a closed locus along EVERY outcome
map**: saturation transfers to the (surjective) range factorization,
where the landed brick applies.  No surjectivity hypothesis, and no new
topological content. -/
theorem isClosed_satClass_total {θ : V → W} :
    IsClosed {L : NonemptyCompacts (BelState V) |
      Saturated θ (L : Set (BelState V))} := by
  classical
  haveI : Fintype (Set.range θ) := (Set.finite_range θ).fintype
  have hset : {L : NonemptyCompacts (BelState V) |
        Saturated θ (L : Set (BelState V))}
      = {L : NonemptyCompacts (BelState V) |
          Saturated (Set.rangeFactorization θ) (L : Set (BelState V))} :=
    Set.ext fun _ => saturated_rangeFactorization_iff
  rw [hset]
  exact isClosed_satClass Set.rangeFactorization_surjective

end Factorization

/-! ## The biting case split, and the total structure theorem -/

section Biting

variable {V W : Type*} [Fintype V] [Fintype W]

/-- A liveness demand **bites** through an outcome map when its escape
region inside the safety body lies wholly on the range of the
pushforward: every escape witness a transported class member could use
is visible from upstairs, so the demand survives transport.  A
non-biting demand can be discharged by a supplement point off the range
and vanishes from the transported class's constraints. -/
def Biting (θ : V → W) (u v : ProbPenalty W) : Prop :=
  compile u ∩ (compile v)ᶜ
    ⊆ Set.range (BelState.push (V := V) (W := W) θ)

/-- Along a surjective outcome map every demand bites: the range is
everything. -/
theorem biting_of_surjective {θ : V → W} (hθ : Function.Surjective θ)
    (u v : ProbPenalty W) : Biting θ u v := fun x _ => by
  rw [(BelState.push_surjective hθ).range_eq]
  trivial

/-- **The total structure theorem**: along ANY outcome map, the
transported class of a crescent is the crescent of the transported atom
restricted to its biting demands, intersected with the saturated
classes.

Forward: safety and saturation are unconditional (body preimages), and
a biting demand's escape witness lies on the range, so it lifts into
the transported class member.  Reverse (the supplement construction):
push the class forward and adjoin, for each non-biting demand, one
chosen escape point *off the range* — the preimage never sees the
supplements, saturation collapses the rest, and the assembled body is a
member of the crescent upstairs.  Finiteness of the demand family
enters exactly once, for compactness of the supplement set. -/
theorem transportClass_crescentClass_total [Nonempty V] (θ : V → W)
    (u : ProbPenalty W) {𝒱 : Set (ProbPenalty W)} (h𝒱 : 𝒱.Finite) :
    transportClass θ (crescentClass u 𝒱)
      = crescentClass (pullPen θ u) (pullPen θ '' {v ∈ 𝒱 | Biting θ u v})
        ∩ {L : NonemptyCompacts (BelState V) |
            Saturated θ (L : Set (BelState V))} := by
  classical
  ext L
  constructor
  · rintro ⟨K, hK, hL⟩
    obtain ⟨hsub, hesc⟩ := mem_crescentClass_iff.mp hK
    refine ⟨mem_crescentClass_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [hL]
      exact transport_safety_face θ hsub
    · rintro v' ⟨v, ⟨hv𝒱, hbite⟩, rfl⟩
      obtain ⟨x, hxK, hxv⟩ := hesc v hv𝒱
      obtain ⟨z, hz⟩ := hbite ⟨hsub hxK, hxv⟩
      refine ⟨z, ?_, ?_⟩
      · rw [hL]
        show BelState.push θ z ∈ (K : Set (BelState W))
        rw [hz]
        exact hxK
      · intro hmem
        rw [compile_pullPen] at hmem
        exact hxv (hz ▸ hmem)
    · rw [Set.mem_setOf_eq, hL]
      exact saturated_preimage θ _
  · rintro ⟨hcres, hsat⟩
    obtain ⟨hsubL, hescL⟩ := mem_crescentClass_iff.mp hcres
    -- one chosen escape point off the range, per non-biting demand
    set pick : ProbPenalty W → BelState W := fun v =>
      if h : ∃ x, x ∈ compile u ∩ (compile v)ᶜ
          ∧ x ∉ Set.range (BelState.push (V := V) (W := W) θ)
      then h.choose else BelState.zero W
      with hpickdef
    have hpick : ∀ v, ¬ Biting θ u v →
        pick v ∈ compile u ∩ (compile v)ᶜ
          ∧ pick v ∉ Set.range (BelState.push (V := V) (W := W) θ) := by
      intro v hv
      have h : ∃ x, x ∈ compile u ∩ (compile v)ᶜ
          ∧ x ∉ Set.range (BelState.push (V := V) (W := W) θ) := by
        obtain ⟨x, hxE, hxr⟩ := Set.not_subset.mp hv
        exact ⟨x, hxE, hxr⟩
      rw [hpickdef]
      dsimp only
      rw [dif_pos h]
      exact h.choose_spec
    have hSfin : ({v ∈ 𝒱 | ¬ Biting θ u v}).Finite :=
      h𝒱.subset (Set.sep_subset _ _)
    set Kset : Set (BelState W) :=
      BelState.push θ '' (L : Set (BelState V))
        ∪ pick '' {v ∈ 𝒱 | ¬ Biting θ u v} with hKdef
    have hKcompact : IsCompact Kset :=
      (L.isCompact.image (continuous_belPush θ)).union
        (hSfin.image pick).isCompact
    have hKne : Kset.Nonempty :=
      (L.nonempty.image _).mono Set.subset_union_left
    refine ⟨⟨⟨Kset, hKcompact⟩, hKne⟩,
      mem_crescentClass_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · -- the assembled body sits inside the safety body
      show Kset ⊆ compile u
      refine Set.union_subset ?_ ?_
      · rw [Set.image_subset_iff, ← compile_pullPen]
        exact hsubL
      · rintro _ ⟨v, ⟨_, hnb⟩, rfl⟩
        exact (hpick v hnb).1.1
    · -- the assembled body escapes every demand
      intro v hv
      show (Kset ∩ (compile v)ᶜ).Nonempty
      by_cases hb : Biting θ u v
      · obtain ⟨z, hzL, hzv⟩ := hescL (pullPen θ v) ⟨v, ⟨hv, hb⟩, rfl⟩
        refine ⟨BelState.push θ z, Or.inl ⟨z, hzL, rfl⟩, fun hmem => ?_⟩
        exact hzv (by rw [compile_pullPen]; exact hmem)
      · exact ⟨pick v, Or.inr ⟨v, ⟨hv, hb⟩, rfl⟩, (hpick v hb).1.2⟩
    · -- the preimage recovers the class: saturation collapses the
      -- image part, and the supplements sit off the range
      show (L : Set (BelState V)) = BelState.push θ ⁻¹' Kset
      rw [hKdef, Set.preimage_union]
      have h2 : BelState.push θ ⁻¹' (pick '' {v ∈ 𝒱 | ¬ Biting θ u v})
          = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z hz
        obtain ⟨v, ⟨_, hnb⟩, hzv⟩ := hz
        exact (hpick v hnb).2 ⟨z, hzv.symm⟩
      rw [h2, Set.union_empty]
      exact hsat

/-- On the injective stratum the saturation factor is the whole space:
the transported class of a crescent is EXACTLY a crescent — of the
transported atom, restricted to its biting demands. -/
theorem transportClass_crescentClass_of_injective [Nonempty V]
    {ι : V → W} (hι : Function.Injective ι) (u : ProbPenalty W)
    {𝒱 : Set (ProbPenalty W)} (h𝒱 : 𝒱.Finite) :
    transportClass ι (crescentClass u 𝒱)
      = crescentClass (pullPen ι u)
          (pullPen ι '' {v ∈ 𝒱 | Biting ι u v}) := by
  rw [transportClass_crescentClass_total ι u h𝒱]
  have hsat : {L : NonemptyCompacts (BelState V) |
        Saturated ι (L : Set (BelState V))} = Set.univ :=
    Set.eq_univ_of_forall fun L => saturated_of_injective hι _
  rw [hsat, Set.inter_univ]

/-- **Per-piece topological citizenship on EVERY stratum**: the
transported class of a crescent is locally closed along any outcome
map — the total structure theorem writes it as a crescent intersected
with the (always closed) saturated locus. -/
theorem isLocallyClosed_transportClass_crescentClass_total [Nonempty V]
    (θ : V → W) {u : ProbPenalty W} {𝒱 : Set (ProbPenalty W)}
    (hu : LowerSemicontinuous u) (h𝒱 : 𝒱.Finite)
    (hlsc : ∀ v ∈ 𝒱, LowerSemicontinuous v) :
    IsLocallyClosed (transportClass θ (crescentClass u 𝒱)) := by
  rw [transportClass_crescentClass_total θ u h𝒱]
  exact IsLocallyClosed.inter
    (isLocallyClosed_crescentClass (lowerSemicontinuous_pullPen θ hu)
      ((h𝒱.subset (Set.sep_subset _ _)).image _)
      (by
        rintro v' ⟨v, ⟨hv, -⟩, rfl⟩
        exact lowerSemicontinuous_pullPen θ (hlsc v hv)))
    (IsClosed.isLocallyClosed isClosed_satClass_total)

/-- **Image-transport citizenship is total**: along EVERY outcome map,
the transported class of a citizen DNF class is constructible.  The
surjective statement (`isConstructibleUnion_transportClass_dnfClass`)
is the instance where every demand bites. -/
theorem isConstructibleUnion_transportClass_dnfClass_total [Nonempty V]
    (θ : V → W) {n : ℕ} {u : Fin n → ProbPenalty W}
    {𝒱 : Fin n → Set (ProbPenalty W)}
    (hu : ∀ i, LowerSemicontinuous (u i)) (h𝒱 : ∀ i, (𝒱 i).Finite)
    (hlsc : ∀ i, ∀ v ∈ 𝒱 i, LowerSemicontinuous v) :
    IsConstructibleUnion (transportClass θ (dnfClass u 𝒱)) := by
  have hdnf : transportClass θ (dnfClass u 𝒱)
      = ⋃ i, transportClass θ (crescentClass (u i) (𝒱 i)) := by
    rw [dnfClass, transportClass_iUnion]
  rw [hdnf]
  exact IsConstructibleUnion.iUnion_fin fun i =>
    IsLocallyClosed.isConstructibleUnion
      (isLocallyClosed_transportClass_crescentClass_total θ (hu i) (h𝒱 i)
        (hlsc i))

end Biting

/-! ## The filter is not vacuous: the seam, explained -/

section NonBiting

/-- **A non-biting demand, and what it does**: along the non-surjective
outcome map `Unit → Bool`, the wall demand of the transport seam is not
biting — its escape region is the off-range mass at the second
outcome — and the transported class of the crescent differs from the
unfiltered transported crescent intersected with the saturated classes.
The witness is the full-carrier class: it is transported from the
full-carrier member upstairs, but the unfiltered pulled demand is the
zero penalty, whose body nothing escapes.  Dropping non-biting demands
is not a convenience of the total structure theorem; it is forced. -/
theorem exists_not_biting_transportClass_ne :
    ∃ (θ : Unit → Bool) (u : ProbPenalty Bool)
      (𝒱 : Set (ProbPenalty Bool)),
      LowerSemicontinuous u ∧ (∀ v ∈ 𝒱, LowerSemicontinuous v)
        ∧ 𝒱.Finite ∧ (∃ v ∈ 𝒱, ¬ Biting θ u v)
        ∧ transportClass θ (crescentClass u 𝒱)
            ≠ crescentClass (pullPen θ u) (pullPen θ '' 𝒱)
              ∩ {L : NonemptyCompacts (BelState Unit) |
                  Saturated θ (L : Set (BelState Unit))} := by
  classical
  set D : Set (ProbState Bool) :=
    {μ | (1 : ℝ)/2 ≤ (μ : Bool → ℝ) false} with hD
  have hDclosed : IsClosed D :=
    isClosed_le continuous_const
      ((continuous_apply false).comp continuous_subtype_val)
  -- the escape witness upstairs, outside the wall body
  have hdmem : BelState.dirac true ∉ compile (probWall D) := by
    intro hmem
    have hd : ((BelState.dirac true : BelState Bool) : Bool → ℝ)
        = (1 : ℝ) • ((ProbState.dirac true : ProbState Bool) : Bool → ℝ) := by
      rw [one_smul]
      rfl
    have hb := compile_scale_le hmem one_pos hd
    have hnotD : (ProbState.dirac true : ProbState Bool) ∉ D := by
      rw [hD, Set.mem_setOf_eq, ProbState.dirac_apply_of_ne
        (by decide : (false : Bool) ≠ true)]
      norm_num
    rw [probWall_apply_of_not_mem hnotD, grade_top] at hb
    norm_num at hb
  -- ... and it sits off the range of the pushforward
  have hdrange : BelState.dirac true
      ∉ Set.range (BelState.push (fun _ : Unit => false)) := by
    rintro ⟨y, hy⟩
    have hval := congrArg
      (fun x : BelState Bool => (x : Bool → ℝ) true) hy
    simp only [BelState.push_coe] at hval
    have hzero : pushFun (fun _ : Unit => false) ((y : Unit → ℝ)) true
        = 0 := by
      rw [pushFun]
      simp
    rw [hzero, BelState.dirac_apply_same] at hval
    norm_num at hval
  have hnb : ¬ Biting (fun _ : Unit => false)
      (0 : ProbPenalty Bool) (probWall D) := by
    intro hbit
    exact hdrange (hbit ⟨by rw [compile_zero]; exact Set.mem_univ _, hdmem⟩)
  -- the pulled wall degenerates to the zero penalty
  have hpull : pullPen (fun _ : Unit => false) (probWall D) = 0 := by
    funext μ
    have hmemD : ProbState.push (fun _ : Unit => false) μ ∈ D := by
      rw [hD, Set.mem_setOf_eq, ProbState.push_coe]
      have hval : pushFun (fun _ : Unit => false) ((μ : Unit → ℝ)) false
          = (μ : Unit → ℝ) () := by
        rw [pushFun]
        rw [Fintype.sum_unique]
        simp
      rw [hval]
      have hone : (μ : Unit → ℝ) () = 1 := by
        have := μ.sum_eq_one
        rwa [Fintype.sum_unique] at this
      rw [hone]
      norm_num
    rw [pullPen_apply, probWall_apply_of_mem hmemD]
    rfl
  -- the full-carrier class is transported from the full-carrier member
  have hKmem : (⟨⟨Set.univ, isCompact_univ⟩,
      ⟨BelState.zero Bool, Set.mem_univ _⟩⟩ :
        NonemptyCompacts (BelState Bool))
      ∈ crescentClass (0 : ProbPenalty Bool) {probWall D} := by
    rw [mem_crescentClass_iff]
    constructor
    · rw [compile_zero]
      exact fun x _ => Set.mem_univ x
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact ⟨BelState.dirac true, Set.mem_univ _, hdmem⟩
  have hLmem : (⟨⟨Set.univ, isCompact_univ⟩,
      ⟨BelState.zero Unit, Set.mem_univ _⟩⟩ :
        NonemptyCompacts (BelState Unit))
      ∈ transportClass (fun _ : Unit => false)
          (crescentClass (0 : ProbPenalty Bool) {probWall D}) :=
    ⟨_, hKmem, (Set.preimage_univ).symm⟩
  refine ⟨fun _ => false, 0, {probWall D}, lowerSemicontinuous_const,
    ?_, Set.finite_singleton _, ⟨probWall D, Set.mem_singleton _, hnb⟩, ?_⟩
  · intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact lowerSemicontinuous_probWall_iff.mpr hDclosed
  · intro heq
    rw [heq] at hLmem
    obtain ⟨hcres, -⟩ := hLmem
    obtain ⟨-, hesc⟩ := mem_crescentClass_iff.mp hcres
    obtain ⟨y, -, hy⟩ := hesc (pullPen (fun _ : Unit => false) (probWall D))
      ⟨probWall D, Set.mem_singleton _, rfl⟩
    apply hy
    rw [hpull, compile_zero]
    exact Set.mem_univ y

end NonBiting

end SuFunctor.Universe
