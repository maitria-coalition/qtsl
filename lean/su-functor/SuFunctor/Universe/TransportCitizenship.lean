import SuFunctor.Universe.DisjunctionElim
import SuFunctor.Universe.ImageChar

/-! # Transport citizenship: how the fibre operations act on spec classes

The decoration tier's fibre operations — tight/cell transport (image of
penalty pullback along a carrier map) and the compositor (elementwise
pushforward-then-add, lifted to classes) — are functorial over arbitrary
classes.  This module settles how they interact with the *citizen*
classes of the hyperspace presentation: the locally closed crescents and
their constructible (finite-union) closure.

* **The transport dictionary** (`compile_pullPen`): the pullback of a
  penalty along an outcome map compiles to the **preimage** of its body
  under the induced pushforward of distributions — penalty transport is
  body preimage, not body image.  Citizens transport to citizens
  (`lowerSemicontinuous_pullPen`), and the induced operation on
  hyperspace classes (`transportClass`) distributes over unions
  (`transportClass_union`), so transport never disturbs the
  union-exactness of disjunction.
* **Faces transport asymmetrically**: the safety (containment) face
  transports unconditionally (`transport_safety_face`); the escape face
  transports exactly when the escape witness sits in the *range* of the
  pushforward (`transport_escape_iff`).  Non-surjective carrier maps
  lose escape witnesses.
* **The structure theorem of the surjective stratum**
  (`transportClass_crescentClass`): along a surjective outcome map, the
  transported class of a crescent is precisely the crescent of the
  transported atom intersected with the **saturated** classes (unions
  of fibres of the pushforward).  Surjectivity is consumed only in the
  forward inclusion's escape leg, and it is genuinely load-bearing:
  along a non-surjective map the transported class escapes the
  transported atom's crescent outright
  (`exists_transport_not_subset_pulled_crescent`).
* **Judgment invariance** (`coupledSat_pullPen_iff`): along a surjective
  outcome map, atom transport commutes with the coupled judgment — the
  semantic warrant that transporting the *atom* (rather than imaging
  the class) is the canonical fibre operation on citizens.
* **The compositor dictionary** (`compile_add_radProd`): the body of a
  sum of penalties is the fibrewise grade *product* of the bodies —
  the compositor's hyperspace face.  Penalty-level composition
  preserves citizenship (`lowerSemicontinuous_add_penalty`), the
  class-level compositor distributes over unions, and ideal points
  (singleton classes) are citizens outright and compose to ideal
  points: systems stay citizens under every fibre operation.
-/

namespace SuFunctor.Universe

open scoped ENNReal
open TopologicalSpace

/-! ## Pushforward of distributions along an outcome map -/

section Push

variable {V W : Type*} [Fintype V] [Fintype W]

open Classical in
/-- Pushforward of a weight function along an outcome map: fibrewise
summation.  The raw-function core of the pushforward on both carriers. -/
noncomputable def pushFun (θ : V → W) (x : V → ℝ) : W → ℝ :=
  fun w => ∑ v, if θ v = w then x v else 0

theorem pushFun_nonneg {θ : V → W} {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) (w : W) :
    0 ≤ pushFun θ x w :=
  Finset.sum_nonneg fun v _ => by
    by_cases h : θ v = w <;> simp [h, hx v]

/-- Pushforward preserves total mass on the nose: a finite sum
reindexed along its fibres. -/
theorem sum_pushFun (θ : V → W) (x : V → ℝ) :
    ∑ w, pushFun θ x w = ∑ v, x v := by
  classical
  simp only [pushFun]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_ite_eq Finset.univ (θ v) fun _ => x v]
  simp

omit [Fintype W] in
theorem pushFun_smul (θ : V → W) (m : ℝ) (x : V → ℝ) :
    pushFun θ (m • x) = m • pushFun θ x := by
  funext w
  simp only [pushFun, Pi.smul_apply, smul_eq_mul, mul_ite, mul_zero,
    Finset.mul_sum]

omit [Fintype W] in
theorem continuous_pushFun (θ : V → W) : Continuous (pushFun θ) := by
  refine continuous_pi fun w => continuous_finsetSum _ fun v _ => ?_
  by_cases h : θ v = w
  · simpa [h] using continuous_apply v
  · simpa [h] using continuous_const (y := (0 : ℝ))

/-- Pushforward of a distribution along an outcome map. -/
noncomputable def BelState.push (θ : V → W) (x : BelState V) : BelState W :=
  ⟨pushFun θ (x : V → ℝ), fun w => pushFun_nonneg x.nonneg w, by
    rw [sum_pushFun]
    exact x.mass_le_one⟩

@[simp] theorem BelState.push_coe (θ : V → W) (x : BelState V) :
    ((BelState.push θ x : BelState W) : W → ℝ) = pushFun θ (x : V → ℝ) := rfl

/-- Pushforward of a probability state along an outcome map. -/
noncomputable def ProbState.push (θ : V → W) (μ : ProbState V) : ProbState W :=
  ⟨pushFun θ (μ : V → ℝ), fun w => pushFun_nonneg μ.nonneg w, by
    rw [sum_pushFun]
    exact μ.sum_eq_one⟩

@[simp] theorem ProbState.push_coe (θ : V → W) (μ : ProbState V) :
    ((ProbState.push θ μ : ProbState W) : W → ℝ) = pushFun θ (μ : V → ℝ) := rfl

theorem continuous_belPush (θ : V → W) :
    Continuous (BelState.push θ) :=
  Continuous.subtype_mk ((continuous_pushFun θ).comp continuous_subtype_val) _

theorem continuous_probPush (θ : V → W) :
    Continuous (ProbState.push θ) :=
  Continuous.subtype_mk ((continuous_pushFun θ).comp continuous_subtype_val) _

@[simp] theorem BelState.push_zero (θ : V → W) :
    BelState.push θ (BelState.zero V) = BelState.zero W := by
  refine Subtype.ext (funext fun w => ?_)
  simp [pushFun]

/-! ## Penalty transport, and the dictionary -/

/-- Penalty transport along an outcome map: evaluate on the pushforward.
The finite-outcome face of the decoration tier's contravariant penalty
transport (pullback along the carrier map). -/
noncomputable def pullPen (θ : V → W) (f : ProbPenalty W) : ProbPenalty V :=
  fun μ => f (ProbState.push θ μ)

@[simp] theorem pullPen_apply (θ : V → W) (f : ProbPenalty W)
    (μ : ProbState V) : pullPen θ f μ = f (ProbState.push θ μ) := rfl

@[simp] theorem pullPen_zero (θ : V → W) :
    pullPen θ (0 : ProbPenalty W) = 0 := rfl

/-- Citizens transport to citizens: the pullback of a lower
semicontinuous penalty along the (continuous) pushforward is lower
semicontinuous. -/
theorem lowerSemicontinuous_pullPen (θ : V → W) {f : ProbPenalty W}
    (hf : LowerSemicontinuous f) :
    LowerSemicontinuous (pullPen θ f) := fun μ c hc =>
  ((continuous_probPush θ).tendsto μ).eventually (hf (ProbState.push θ μ) c hc)

/-- **The transport dictionary**: the pullback of a penalty compiles to
the *preimage* of its body under the pushforward of distributions.
Penalty transport is body preimage — the variance that decides
everything downstream: preimages preserve containment unconditionally
but produce escape witnesses only inside the range. -/
theorem compile_pullPen [Nonempty V] (θ : V → W) (f : ProbPenalty W) :
    compile (pullPen θ f) = BelState.push θ ⁻¹' compile f := by
  ext x
  constructor
  · rintro ⟨μ, γ, h0, hle, he⟩
    refine ⟨ProbState.push θ μ, γ, h0, hle, ?_⟩
    rw [BelState.push_coe, he, pushFun_smul]
    rfl
  · intro hx
    rcases BelState.exists_polar x with h0 | ⟨μ, m, hm0, hm1, he⟩
    · have hxz : x = BelState.zero V := Subtype.ext (by
        rw [h0]; rfl)
      rw [hxz]
      exact zero_mem_compile _
    · have hpe : ((BelState.push θ x : BelState W) : W → ℝ)
          = m • ((ProbState.push θ μ : ProbState W) : W → ℝ) := by
        rw [BelState.push_coe, he, pushFun_smul]
        rfl
      have hb : m ≤ grade (f (ProbState.push θ μ)) :=
        compile_scale_le hx hm0 hpe
      exact ⟨μ, m, hm0.le, hb, he⟩

end Push

/-! ## Sections of the pushforward, and surjectivity transport -/

section Surjective

variable {V W : Type*} [Fintype V] [Fintype W]

open Classical in
/-- The section weight function induced by a right inverse `s` of the
outcome map: all of `y`'s mass at `w`, placed on the fibre
representative `s w`. -/
noncomputable def sectFun (s : W → V) (θ : V → W) (y : W → ℝ) : V → ℝ :=
  fun v => if v = s (θ v) then y (θ v) else 0

theorem sectFun_nonneg {s : W → V} {θ : V → W} {y : W → ℝ}
    (hy : ∀ w, 0 ≤ y w) (v : V) : 0 ≤ sectFun s θ y v := by
  classical
  show 0 ≤ if v = s (θ v) then y (θ v) else 0
  by_cases h : v = s (θ v)
  · rw [if_pos h]
    exact hy (θ v)
  · rw [if_neg h]

/-- Pushing the section weights forward recovers the weights: the
pushforward retracts the section. -/
theorem pushFun_sectFun {s : W → V} {θ : V → W}
    (hs : Function.RightInverse s θ) (y : W → ℝ) :
    pushFun θ (sectFun s θ y) = y := by
  classical
  funext w
  show (∑ v, if θ v = w then sectFun s θ y v else 0) = y w
  rw [Finset.sum_eq_single (s w)]
  · have h1 : θ (s w) = w := hs w
    rw [if_pos h1]
    show (if s w = s (θ (s w)) then y (θ (s w)) else 0) = y w
    rw [h1, if_pos rfl]
  · intro v _ hv
    by_cases hθv : θ v = w
    · by_cases hsv : v = s (θ v)
      · exact absurd (hsv.trans (by rw [hθv])) hv
      · rw [if_pos hθv]
        exact if_neg hsv
    · exact if_neg hθv
  · intro h
    exact absurd (Finset.mem_univ (s w)) h

theorem BelState.push_surjective {θ : V → W} (hθ : Function.Surjective θ) :
    Function.Surjective (BelState.push (V := V) (W := W) θ) := by
  obtain ⟨s, hs⟩ := hθ.hasRightInverse
  intro y
  refine ⟨⟨sectFun s θ (y : W → ℝ), fun v => sectFun_nonneg y.nonneg v, ?_⟩,
    Subtype.ext ?_⟩
  · rw [← sum_pushFun θ, pushFun_sectFun hs]
    exact y.mass_le_one
  · rw [BelState.push_coe]
    exact pushFun_sectFun hs _

theorem ProbState.push_surjective {θ : V → W} (hθ : Function.Surjective θ) :
    Function.Surjective (ProbState.push (V := V) (W := W) θ) := by
  obtain ⟨s, hs⟩ := hθ.hasRightInverse
  intro y
  refine ⟨⟨sectFun s θ (y : W → ℝ), fun v => sectFun_nonneg y.nonneg v, ?_⟩,
    Subtype.ext ?_⟩
  · rw [← sum_pushFun θ, pushFun_sectFun hs]
    exact y.sum_eq_one
  · rw [ProbState.push_coe]
    exact pushFun_sectFun hs _

/-- **Judgment invariance of atom transport** along a surjective outcome
map: pulling every constituent of a coupled atom (system, safety floor,
liveness demands) back along the pushforward changes no verdict.  This
is the semantic warrant that transporting the *atom* is the canonical
fibre operation on citizens — it commutes with the judgment on the
nose.  (Along a non-surjective map the invariance fails in both
directions: dips can sit outside the range, and safety can be violated
outside the range — the class-level face of the failure is
`exists_transport_not_subset_pulled_crescent` below.) -/
theorem coupledSat_pullPen_iff {θ : V → W} (hθ : Function.Surjective θ)
    {σ u : ProbPenalty W} {𝒱 : Set (ProbPenalty W)} :
    CoupledSat (pullPen θ σ) (pullPen θ u) (pullPen θ '' 𝒱)
      ↔ CoupledSat σ u 𝒱 := by
  constructor
  · rintro ⟨hsafe, hlive⟩
    refine ⟨fun μ' => ?_, fun v hv => ?_⟩
    · obtain ⟨μ, rfl⟩ := ProbState.push_surjective hθ μ'
      exact hsafe μ
    · obtain ⟨μ, hμ⟩ := hlive (pullPen θ v) ⟨v, hv, rfl⟩
      exact ⟨ProbState.push θ μ, hμ⟩
  · rintro ⟨hsafe, hlive⟩
    refine ⟨fun μ => hsafe _, ?_⟩
    rintro v' ⟨v, hv, rfl⟩
    obtain ⟨μ', hμ'⟩ := hlive v hv
    obtain ⟨μ, rfl⟩ := ProbState.push_surjective hθ μ'
    exact ⟨μ, hμ'⟩

end Surjective

/-! ## The induced transport of hyperspace classes -/

section TransportClass

variable {V W : Type*} [Fintype V] [Fintype W]

/-- The transport of a hyperspace class along an outcome map: the image
of the class under the (partial) body-preimage map — exactly the
hyperspace shadow of the decoration tier's image-of-pullback fibre
operation, by the transport dictionary. -/
def transportClass (θ : V → W) (C : Set (NonemptyCompacts (BelState W))) :
    Set (NonemptyCompacts (BelState V)) :=
  {L | ∃ K ∈ C,
    (L : Set (BelState V)) = BelState.push θ ⁻¹' (K : Set (BelState W))}

theorem mem_transportClass_iff {θ : V → W}
    {C : Set (NonemptyCompacts (BelState W))}
    {L : NonemptyCompacts (BelState V)} :
    L ∈ transportClass θ C ↔ ∃ K ∈ C,
      (L : Set (BelState V)) = BelState.push θ ⁻¹' (K : Set (BelState W)) :=
  Iff.rfl

/-- Class transport distributes over binary unions: transport never
disturbs the union-exactness of disjunction (the ∨-compatibility
receipt, transport half). -/
theorem transportClass_union (θ : V → W)
    (C₁ C₂ : Set (NonemptyCompacts (BelState W))) :
    transportClass θ (C₁ ∪ C₂)
      = transportClass θ C₁ ∪ transportClass θ C₂ := by
  ext L
  simp only [transportClass, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨K, hK | hK, hL⟩
    · exact Or.inl ⟨K, hK, hL⟩
    · exact Or.inr ⟨K, hK, hL⟩
  · rintro (⟨K, hK, hL⟩ | ⟨K, hK, hL⟩)
    · exact ⟨K, Or.inl hK, hL⟩
    · exact ⟨K, Or.inr hK, hL⟩

/-- Class transport distributes over finite (indeed arbitrary) indexed
unions — the DNF form of the ∨-compatibility receipt: the transport of
a constructible class is the union of the transports of its
locally-closed disjuncts. -/
theorem transportClass_iUnion {ι : Sort*} (θ : V → W)
    (C : ι → Set (NonemptyCompacts (BelState W))) :
    transportClass θ (⋃ i, C i) = ⋃ i, transportClass θ (C i) := by
  ext L
  simp only [transportClass, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨K, ⟨i, hKi⟩, hL⟩
    exact ⟨i, K, hKi, hL⟩
  · rintro ⟨i, K, hKi, hL⟩
    exact ⟨K, ⟨i, hKi⟩, hL⟩

/-- The dictionary at hyperspace-point level: the transport of an ideal
point is the ideal point of the transported system.  Systems transport
to systems — no citizenship is ever at stake on singletons. -/
theorem transportClass_singleton_compileNC [Nonempty V] [Nonempty W]
    (θ : V → W) {f : ProbPenalty W} (hf : LowerSemicontinuous f) :
    transportClass θ {compileNC f hf}
      = {compileNC (pullPen θ f) (lowerSemicontinuous_pullPen θ hf)} := by
  ext L
  simp only [transportClass, Set.mem_setOf_eq, Set.mem_singleton_iff,
    exists_eq_left, coe_compileNC]
  constructor
  · intro hL
    exact SetLike.ext' (hL.trans (compile_pullPen θ f).symm)
  · rintro rfl
    rw [coe_compileNC]
    exact compile_pullPen θ f

/-- The safety face transports unconditionally: body preimages preserve
containment. -/
theorem transport_safety_face [Nonempty V] (θ : V → W) {u : ProbPenalty W}
    {K : Set (BelState W)} (hK : K ⊆ compile u) :
    BelState.push θ ⁻¹' K ⊆ compile (pullPen θ u) := by
  rw [compile_pullPen]
  exact Set.preimage_mono hK

/-- The escape face transports exactly onto the range: the transported
class escapes the transported liveness body iff the original body's
escape region meets the range of the pushforward.  Non-surjective
carrier maps lose escape witnesses — this is the seam the structure
theorem's surjectivity hypothesis guards. -/
theorem transport_escape_iff [Nonempty V] (θ : V → W) {v : ProbPenalty W}
    {K : Set (BelState W)} :
    ((BelState.push θ ⁻¹' K) ∩ (compile (pullPen θ v))ᶜ).Nonempty
      ↔ (K ∩ Set.range (BelState.push θ) ∩ (compile v)ᶜ).Nonempty := by
  rw [compile_pullPen]
  constructor
  · rintro ⟨y, hyK, hyv⟩
    exact ⟨BelState.push θ y, ⟨hyK, ⟨y, rfl⟩⟩, hyv⟩
  · rintro ⟨x, ⟨hxK, ⟨y, rfl⟩⟩, hxv⟩
    exact ⟨y, hxK, hxv⟩

/-- A class is saturated for an outcome map when it is a union of
fibres of the pushforward: the exact fingerprint of having arisen as a
body preimage. -/
def Saturated (θ : V → W) (L : Set (BelState V)) : Prop :=
  L = BelState.push θ ⁻¹' (BelState.push θ '' L)

/-- Preimages are saturated — no surjectivity consumed. -/
theorem saturated_preimage (θ : V → W) (S : Set (BelState W)) :
    Saturated θ (BelState.push θ ⁻¹' S) :=
  (Set.preimage_image_preimage).symm

/-- **The structure theorem of the surjective stratum**: along a
surjective outcome map, the transported class of a crescent is exactly
the crescent of the transported atom, intersected with the saturated
classes.  Surjectivity is consumed only in the forward inclusion's
escape leg (producing the escape witness inside the range); the
reverse inclusion is unconditional.  The saturation factor is the
honest residue of image-transport: it is not a spec class, and its
topological status (closedness in the Vietoris topology) is the one
brick this module does not lay. -/
theorem transportClass_crescentClass [Nonempty V] {θ : V → W}
    (hθ : Function.Surjective θ) (u : ProbPenalty W)
    (𝒱 : Set (ProbPenalty W)) :
    transportClass θ (crescentClass u 𝒱)
      = crescentClass (pullPen θ u) (pullPen θ '' 𝒱)
        ∩ {L | Saturated θ (L : Set (BelState V))} := by
  ext L
  constructor
  · rintro ⟨K, hK, hL⟩
    obtain ⟨hsub, hesc⟩ := mem_crescentClass_iff.mp hK
    refine ⟨mem_crescentClass_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [hL]
      exact transport_safety_face θ hsub
    · rintro v' ⟨v, hv, rfl⟩
      rw [hL]
      rw [transport_escape_iff θ]
      obtain ⟨x, hxK, hxv⟩ := hesc v hv
      have hrange : x ∈ Set.range (BelState.push θ) := by
        rw [(BelState.push_surjective hθ).range_eq]
        trivial
      exact ⟨x, ⟨hxK, hrange⟩, hxv⟩
    · rw [Set.mem_setOf_eq, hL]
      exact saturated_preimage θ _
  · rintro ⟨hcres, hsat⟩
    obtain ⟨hsubL, hescL⟩ := mem_crescentClass_iff.mp hcres
    refine ⟨⟨⟨BelState.push θ '' (L : Set (BelState V)),
      L.isCompact.image (continuous_belPush θ)⟩,
      L.nonempty.image _⟩, mem_crescentClass_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · show BelState.push θ '' (L : Set (BelState V)) ⊆ compile u
      rw [Set.image_subset_iff, ← compile_pullPen]
      exact hsubL
    · intro v hv
      show ((BelState.push θ '' (L : Set (BelState V)))
        ∩ (compile v)ᶜ).Nonempty
      obtain ⟨y, hyL, hyv⟩ := hescL (pullPen θ v) ⟨v, hv, rfl⟩
      refine ⟨BelState.push θ y, ⟨y, hyL, rfl⟩, ?_⟩
      intro hmem
      exact hyv (by
        rw [compile_pullPen]
        exact hmem)
    · show (L : Set (BelState V))
        = BelState.push θ ⁻¹' (BelState.push θ '' (L : Set (BelState V)))
      exact hsat

end TransportClass

/-! ## The non-surjective seam: escape witnesses die outside the range -/

section Seam

/-- **Surjectivity is load-bearing, not technical**: along the
non-surjective outcome map `Unit → Bool`, the transported class of a
crescent escapes the transported atom's crescent outright.  The
mechanism: the liveness mark's escape region sits entirely outside the
range of the pushforward, so its pullback is the zero penalty — whose
body is the whole carrier, against which no class can escape.  The
transported class member (the full-carrier body, transported from the
full-carrier body upstairs) is saturated and safety-compliant, and
fails exactly the escape face. -/
theorem exists_transport_not_subset_pulled_crescent :
    ∃ (θ : Unit → Bool) (u : ProbPenalty Bool) (𝒱 : Set (ProbPenalty Bool)),
      LowerSemicontinuous u ∧ (∀ v ∈ 𝒱, LowerSemicontinuous v) ∧ 𝒱.Finite ∧
      ¬ (transportClass θ (crescentClass u 𝒱)
          ⊆ crescentClass (pullPen θ u) (pullPen θ '' 𝒱)) := by
  classical
  set D : Set (ProbState Bool) :=
    {μ | (1 : ℝ)/2 ≤ (μ : Bool → ℝ) false} with hD
  have hDclosed : IsClosed D :=
    isClosed_le continuous_const
      ((continuous_apply false).comp continuous_subtype_val)
  refine ⟨fun _ => false, 0, {probWall D}, lowerSemicontinuous_const,
    fun v hv => ?_, Set.finite_singleton _, ?_⟩
  · rw [Set.mem_singleton_iff] at hv
    subst hv
    exact lowerSemicontinuous_probWall_iff.mpr hDclosed
  · intro hsub
    -- the upstairs full-carrier body, a member of the crescent
    have hKesc : BelState.dirac true ∉ compile (probWall D) := by
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
    have hKmem : (⟨⟨Set.univ, isCompact_univ⟩,
        ⟨BelState.zero Bool, Set.mem_univ _⟩⟩ :
          NonemptyCompacts (BelState Bool)) ∈ crescentClass 0 {probWall D} := by
      rw [mem_crescentClass_iff]
      constructor
      · rw [compile_zero]
        exact fun x _ => Set.mem_univ x
      · intro v hv
        rw [Set.mem_singleton_iff] at hv
        subst hv
        exact ⟨BelState.dirac true, Set.mem_univ _, hKesc⟩
    have hLmem : (⟨⟨Set.univ, isCompact_univ⟩,
        ⟨BelState.zero Unit, Set.mem_univ _⟩⟩ :
          NonemptyCompacts (BelState Unit))
        ∈ transportClass (fun _ => false) (crescentClass 0 {probWall D}) :=
      ⟨_, hKmem, (Set.preimage_univ).symm⟩
    have hLcres := hsub hLmem
    -- the pulled liveness mark is the zero penalty: its escape face is empty
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
    obtain ⟨-, hesc⟩ := mem_crescentClass_iff.mp hLcres
    obtain ⟨y, -, hy⟩ := hesc (pullPen (fun _ => false) (probWall D))
      ⟨probWall D, Set.mem_singleton _, rfl⟩
    apply hy
    rw [hpull, compile_zero]
    exact Set.mem_univ y

end Seam

/-! ## The compositor stratum -/

section Compositor

variable {V : Type*} [Fintype V]

/-- The radial (grade-product) composite of two bodies: on each ray,
the composite admits exactly the products of the component ray
lengths.  The body-level face of the compositor. -/
def radProd (A B : Set (BelState V)) : Set (BelState V) :=
  {x | ∃ (μ : ProbState V) (γ₁ γ₂ : ℝ), 0 ≤ γ₁ ∧ 0 ≤ γ₂
    ∧ (∃ a ∈ A, (a : V → ℝ) = γ₁ • (μ : V → ℝ))
    ∧ (∃ b ∈ B, (b : V → ℝ) = γ₂ • (μ : V → ℝ))
    ∧ (x : V → ℝ) = (γ₁ * γ₂) • (μ : V → ℝ)}

/-- **The compositor dictionary**: the body of a sum of penalties is
the radial product of the bodies — fibrewise grade multiplication,
`mem_compile_add_iff` repackaged as a set identity.  (Compare
`compile_sup`: the intersection of bodies is the *conjunction*, a
strictly larger body wherever both grades are strict; the compositor
is not a lattice operation on bodies.) -/
theorem compile_add_radProd [Nonempty V] (f g : ProbPenalty V) :
    compile (f + g) = radProd (compile f) (compile g) := by
  ext x
  constructor
  · intro hx
    obtain ⟨μ, γ₁, γ₂, h1, h2, hle1, hle2, he⟩ := mem_compile_add_iff.mp hx
    exact ⟨μ, γ₁, γ₂, h1, h2,
      ⟨scalePoint γ₁ h1 (hle1.trans (grade_le_one _)) μ,
        ⟨μ, γ₁, h1, hle1, rfl⟩, scalePoint_coe _ _ _ _⟩,
      ⟨scalePoint γ₂ h2 (hle2.trans (grade_le_one _)) μ,
        ⟨μ, γ₂, h2, hle2, rfl⟩, scalePoint_coe _ _ _ _⟩, he⟩
  · rintro ⟨μ, γ₁, γ₂, h1, h2, ⟨a, haA, hae⟩, ⟨b, hbB, hbe⟩, he⟩
    rcases h1.lt_or_eq with h1p | h1z
    · rcases h2.lt_or_eq with h2p | h2z
      · exact mem_compile_add_iff.mpr ⟨μ, γ₁, γ₂, h1, h2,
          compile_scale_le haA h1p hae, compile_scale_le hbB h2p hbe, he⟩
      · have hxz : x = BelState.zero V := Subtype.ext (by
          rw [he, ← h2z, mul_zero, zero_smul]
          rfl)
        rw [hxz]
        exact zero_mem_compile _
    · have hxz : x = BelState.zero V := Subtype.ext (by
        rw [he, ← h1z, zero_mul, zero_smul]
        rfl)
      rw [hxz]
      exact zero_mem_compile _

/-- Penalty-level composition preserves citizenship: the sum of two
lower semicontinuous penalties is lower semicontinuous. -/
theorem lowerSemicontinuous_add_penalty {f g : ProbPenalty V}
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) :
    LowerSemicontinuous (f + g) :=
  hf.add hg

/-- The compositor's Universe face — pull each component to the glued
apex, add — preserves citizenship at the penalty level: citizens
compose to citizens, pointwise, for *any* outcome maps (no
surjectivity: composition rides pullback continuity and sum
semicontinuity only). -/
theorem lowerSemicontinuous_boxplus {W₁ W₂ : Type*} [Fintype W₁] [Fintype W₂]
    (j₁ : V → W₁) (j₂ : V → W₂) {f : ProbPenalty W₁} {g : ProbPenalty W₂}
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) :
    LowerSemicontinuous (pullPen j₁ f + pullPen j₂ g) :=
  (lowerSemicontinuous_pullPen j₁ hf).add (lowerSemicontinuous_pullPen j₂ hg)

/-- The class-level compositor distributes over unions in its left
argument: the compositor never disturbs the union-exactness of
disjunction (∨-compatibility receipt, compositor half). -/
theorem compositorClass_union_left {α β γ : Type*} (op : α → β → γ)
    (F F' : Set α) (G : Set β) :
    Set.image2 op (F ∪ F') G = Set.image2 op F G ∪ Set.image2 op F' G :=
  Set.image2_union_left

/-- ... and in its right argument. -/
theorem compositorClass_union_right {α β γ : Type*} (op : α → β → γ)
    (F : Set α) (G G' : Set β) :
    Set.image2 op F (G ∪ G') = Set.image2 op F G ∪ Set.image2 op F G' :=
  Set.image2_union_right

/-- The class-level compositor sends ideal points to ideal points:
singleton classes compose to singleton classes. -/
theorem compositor_singleton {α β γ : Type*} (op : α → β → γ) (a : α) (b : β) :
    Set.image2 op ({a} : Set α) ({b} : Set β) = {op a b} :=
  Set.image2_singleton

/-- **Ideal points are citizens outright**: in any space where points
are closed, a singleton class is locally closed, hence constructible.
Combined with `compositor_singleton` and
`transportClass_singleton_compileNC`, systems remain citizens under
every fibre operation, with no surjectivity and no structure theorem
consumed. -/
theorem isConstructibleUnion_singleton {X : Type*} [TopologicalSpace X]
    [T1Space X] (x : X) : IsConstructibleUnion ({x} : Set X) :=
  IsLocallyClosed.isConstructibleUnion
    (IsClosed.isLocallyClosed (isClosed_singleton (x := x)))

end Compositor

end SuFunctor.Universe
