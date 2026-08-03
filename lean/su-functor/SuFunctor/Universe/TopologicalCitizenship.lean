import SuFunctor.Universe.TransportCitizenship
import Mathlib.Topology.LocallyClosed

/-! # Topological citizenship: the fibre operations preserve constructibility

`SuFunctor.Universe.TransportCitizenship` settled the order-side citizenship
of the fibre operations and reduced the topological side to one named brick:
whether the saturation locus — the classes that are unions of pushforward
fibres — is closed in the Vietoris topology.  This module lays that brick,
and with it the topological citizenship statements of the composition tier.

* **The pushforward is an open map** (`isOpenMap_belPush`): along a
  surjective outcome map, `BelState.push` admits a *continuous global
  section through every point* (`BelState.sectThrough`) — target fibre mass
  is distributed proportionally to the reference state on fibres where it
  has mass, and placed on a chosen representative on fibres where it has
  none.  The section is linear in its argument, so no selection theorems
  and no polyhedral regularity are consumed anywhere.
* **Saturation is a closed condition** (`isClosed_setOf_saturated`,
  generic; `isClosed_satClass`, instantiated): under any open continuous
  map, the saturated nonempty compacts form a Vietoris-closed locus.  The
  proof is one hit-and-miss neighborhood; openness of the map is
  load-bearing at exactly one step (openness of the image of a small ball),
  and gluing the endpoints of an interval shows the hypothesis cannot be
  dropped.
* **Per-piece citizenship survives transport on the surjective stratum**
  (`isLocallyClosed_transportClass_crescentClass`): the transported class
  of a crescent is crescent-of-transported-atom ∩ saturated — locally
  closed ∩ closed — hence locally closed.
* **The fibre operations preserve constructibility** — the citizenship
  statement at the level the fibres actually live at, since spec classes
  are DNF (finite unions): transport of a citizen DNF class is
  constructible (`isConstructibleUnion_transportClass_dnfClass`), and the
  disjunct-pairwise compositor of two citizen DNFs is constructible for
  *any* choice of liveness families on the composite atoms
  (`isConstructibleUnion_boxplusDnf`) — the citizenship half of the
  compositor is independent of the composite-liveness design question.
* **The constructible level is forced**
  (`exists_transportClass_constructible_not_locallyClosed`): a concrete
  citizen class on the two-outcome carrier — escape past a half-mass wall,
  joined with the sub-bodies of a spike — is constructible but *not*
  locally closed, and transports verbatim along the (surjective) identity.
  Local closedness is not the class invariant of the fibres; finite unions
  of locally closed classes are, and the operations preserve exactly that.
-/

namespace SuFunctor.Universe

open scoped ENNReal
open TopologicalSpace

/-! ## Sections of the pushforward through every point -/

section SectThrough

variable {V W : Type*} [Fintype V] [Fintype W]

open Classical in
/-- The section-through-a-point weight function: the target fibre mass
`y (θ v)` distributed over the fibre of `v` proportionally to the reference
weights `x₀` where the reference fibre mass is positive, and placed on the
chosen fibre representative `s (θ v)` where it vanishes. -/
noncomputable def sectThroughFun (θ : V → W) (s : W → V) (x₀ : V → ℝ)
    (y : W → ℝ) : V → ℝ :=
  fun v => y (θ v) *
    (if 0 < pushFun θ x₀ (θ v) then x₀ v / pushFun θ x₀ (θ v)
     else if v = s (θ v) then 1 else 0)

open Classical in
@[simp] theorem sectThroughFun_apply (θ : V → W) (s : W → V) (x₀ : V → ℝ)
    (y : W → ℝ) (v : V) :
    sectThroughFun θ s x₀ y v
      = y (θ v) *
        (if 0 < pushFun θ x₀ (θ v) then x₀ v / pushFun θ x₀ (θ v)
         else if v = s (θ v) then 1 else 0) := rfl

theorem sectThroughFun_nonneg {θ : V → W} {s : W → V} {x₀ : V → ℝ}
    {y : W → ℝ} (hx₀ : ∀ v, 0 ≤ x₀ v) (hy : ∀ w, 0 ≤ y w) (v : V) :
    0 ≤ sectThroughFun θ s x₀ y v := by
  classical
  rw [sectThroughFun_apply]
  refine mul_nonneg (hy (θ v)) ?_
  by_cases h : 0 < pushFun θ x₀ (θ v)
  · rw [if_pos h]
    exact div_nonneg (hx₀ v) h.le
  · rw [if_neg h]
    by_cases hv : v = s (θ v)
    · rw [if_pos hv]
      exact zero_le_one
    · rw [if_neg hv]

/-- Pushing the section-through-a-point weights forward recovers the target
weights: on fibres of positive reference mass the proportional coefficients
sum to one; on the rest the computation is the chosen-representative
section's. -/
theorem pushFun_sectThroughFun {θ : V → W} {s : W → V}
    (hs : Function.RightInverse s θ) {x₀ : V → ℝ} (hx₀ : ∀ v, 0 ≤ x₀ v)
    (y : W → ℝ) : pushFun θ (sectThroughFun θ s x₀ y) = y := by
  classical
  funext w
  show (∑ v, if θ v = w then sectThroughFun θ s x₀ y v else 0) = y w
  by_cases hw : 0 < pushFun θ x₀ w
  · have hcong : (∑ v, if θ v = w then sectThroughFun θ s x₀ y v else 0)
        = ∑ v, (y w / pushFun θ x₀ w) * (if θ v = w then x₀ v else 0) := by
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : θ v = w
      · rw [if_pos hv, if_pos hv, sectThroughFun_apply]
        have hcond : 0 < pushFun θ x₀ (θ v) := by
          rw [hv]
          exact hw
        rw [if_pos hcond, hv]
        ring
      · rw [if_neg hv, if_neg hv, mul_zero]
    rw [hcong, ← Finset.mul_sum]
    have hsum : (∑ v, if θ v = w then x₀ v else 0) = pushFun θ x₀ w := rfl
    rw [hsum, div_mul_cancel₀ _ (ne_of_gt hw)]
  · have hcong : (∑ v, if θ v = w then sectThroughFun θ s x₀ y v else 0)
        = ∑ v, if θ v = w then sectFun s θ y v else 0 := by
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : θ v = w
      · rw [if_pos hv, if_pos hv, sectThroughFun_apply]
        have hcond : ¬ 0 < pushFun θ x₀ (θ v) := by
          rw [hv]
          exact hw
        rw [if_neg hcond]
        show y (θ v) * (if v = s (θ v) then 1 else 0)
          = if v = s (θ v) then y (θ v) else 0
        by_cases hsv : v = s (θ v)
        · rw [if_pos hsv, if_pos hsv, mul_one]
        · rw [if_neg hsv, if_neg hsv, mul_zero]
      · rw [if_neg hv, if_neg hv]
    rw [hcong]
    exact congrFun (pushFun_sectFun hs y) w

/-- Total mass of the section weights is the total target mass. -/
theorem sum_sectThroughFun {θ : V → W} {s : W → V}
    (hs : Function.RightInverse s θ) {x₀ : V → ℝ} (hx₀ : ∀ v, 0 ≤ x₀ v)
    (y : W → ℝ) : ∑ v, sectThroughFun θ s x₀ y v = ∑ w, y w := by
  rw [← sum_pushFun θ (sectThroughFun θ s x₀ y),
    pushFun_sectThroughFun hs hx₀]

/-- The section passes through the reference point: at the reference
state's own pushforward, proportional redistribution is the identity, and
mass-zero fibres carry no reference mass to disturb. -/
theorem sectThroughFun_pushFun_self {θ : V → W} {s : W → V} {x₀ : V → ℝ}
    (hx₀ : ∀ v, 0 ≤ x₀ v) :
    sectThroughFun θ s x₀ (pushFun θ x₀) = x₀ := by
  classical
  funext v
  rw [sectThroughFun_apply]
  by_cases h : 0 < pushFun θ x₀ (θ v)
  · rw [if_pos h, mul_comm, div_mul_cancel₀ _ (ne_of_gt h)]
  · have hD0 : pushFun θ x₀ (θ v) = 0 :=
      le_antisymm (not_lt.mp h) (pushFun_nonneg hx₀ (θ v))
    have hx0 : x₀ v = 0 := by
      have hle : x₀ v ≤ pushFun θ x₀ (θ v) := by
        show x₀ v ≤ ∑ v', if θ v' = θ v then x₀ v' else 0
        have hterm := Finset.single_le_sum
          (f := fun v' => if θ v' = θ v then x₀ v' else 0)
          (fun i _ => by
            by_cases hi : θ i = θ v
            · rw [if_pos hi]; exact hx₀ i
            · rw [if_neg hi])
          (Finset.mem_univ v)
        simpa using hterm
      exact le_antisymm (hle.trans hD0.le) (hx₀ v)
    rw [hD0, hx0, zero_mul]

/-- The section through a point, wrapped: a global section of the
pushforward passing through the given reference state. -/
noncomputable def BelState.sectThrough (θ : V → W) (s : W → V)
    (hs : Function.RightInverse s θ) (x : BelState V) (y : BelState W) :
    BelState V :=
  ⟨sectThroughFun θ s (x : V → ℝ) (y : W → ℝ),
    fun v => sectThroughFun_nonneg x.nonneg y.nonneg v, by
      rw [sum_sectThroughFun hs x.nonneg]
      exact y.mass_le_one⟩

@[simp] theorem BelState.sectThrough_coe (θ : V → W) (s : W → V)
    (hs : Function.RightInverse s θ) (x : BelState V) (y : BelState W) :
    ((BelState.sectThrough θ s hs x y : BelState V) : V → ℝ)
      = sectThroughFun θ s (x : V → ℝ) (y : W → ℝ) := rfl

/-- The section is a genuine section: pushing forward recovers the
argument. -/
theorem BelState.push_sectThrough (θ : V → W) (s : W → V)
    (hs : Function.RightInverse s θ) (x : BelState V) (y : BelState W) :
    BelState.push θ (BelState.sectThrough θ s hs x y) = y :=
  Subtype.ext (by
    rw [BelState.push_coe, BelState.sectThrough_coe,
      pushFun_sectThroughFun hs x.nonneg])

/-- The section passes through its reference point. -/
theorem BelState.sectThrough_push_self (θ : V → W) (s : W → V)
    (hs : Function.RightInverse s θ) (x : BelState V) :
    BelState.sectThrough θ s hs x (BelState.push θ x) = x :=
  Subtype.ext (by
    rw [BelState.sectThrough_coe, BelState.push_coe,
      sectThroughFun_pushFun_self x.nonneg])

/-- The section is continuous: it is linear in its argument — each
coordinate is the evaluation at one target outcome times a constant. -/
theorem continuous_sectThrough (θ : V → W) (s : W → V)
    (hs : Function.RightInverse s θ) (x : BelState V) :
    Continuous (BelState.sectThrough θ s hs x) := by
  classical
  refine Continuous.subtype_mk (continuous_pi fun v => ?_) _
  show Continuous fun y : BelState W => (y : W → ℝ) (θ v) *
    (if 0 < pushFun θ (x : V → ℝ) (θ v)
      then (x : V → ℝ) v / pushFun θ (x : V → ℝ) (θ v)
      else if v = s (θ v) then 1 else 0)
  exact ((continuous_apply (θ v)).comp continuous_subtype_val).mul
    continuous_const

/-- **The pushforward along a surjective outcome map is an open map**: it
admits a continuous global section through every point, so the image of an
open set is a neighborhood of each of its points.  No polyhedral
regularity, no error bounds, no selection theorems — proportional fibre
redistribution is already a linear section family. -/
theorem isOpenMap_belPush {θ : V → W} (hθ : Function.Surjective θ) :
    IsOpenMap (BelState.push (V := V) (W := W) θ) := by
  obtain ⟨s, hs⟩ := hθ.hasRightInverse
  exact IsOpenMap.of_sections fun x =>
    ⟨BelState.sectThrough θ s hs x,
      (continuous_sectThrough θ s hs x).continuousAt,
      BelState.sectThrough_push_self θ s hs x,
      fun y => BelState.push_sectThrough θ s hs x y⟩

end SectThrough

/-! ## Saturation is a closed condition -/

section SaturatedClosed

/-- **Saturation is a closed condition under open continuous maps**: the
nonempty compacts that are unions of fibres of `q` form a Vietoris-closed
locus.  A saturation failure — a point outside the body sharing a fibre
with a point inside — spreads to a whole hit-and-miss neighborhood: *hit*
the fibre-saturation of a small ball at the outside point (open, because
`q` is an open map), *miss* the corresponding closed ball; then every body
in the neighborhood has a fibre-mate of one of its own points inside the
ball, hence outside itself.  Openness of `q` is load-bearing: gluing the
endpoints of an interval — continuous but not open — carries saturated
singletons arbitrarily close to the non-saturated glued-point singleton. -/
theorem isClosed_setOf_saturated {X Y : Type*} [MetricSpace X]
    [TopologicalSpace Y] {q : X → Y} (hcont : Continuous q)
    (hopen : IsOpenMap q) :
    IsClosed {K : NonemptyCompacts X |
      (K : Set X) = q ⁻¹' (q '' (K : Set X))} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro L₀ hL₀
  rw [Set.mem_compl_iff, Set.mem_setOf_eq] at hL₀
  have hne : ¬ q ⁻¹' (q '' (L₀ : Set X)) ⊆ (L₀ : Set X) := fun hcontra =>
    hL₀ (Set.Subset.antisymm (Set.subset_preimage_image q _) hcontra)
  obtain ⟨x, hxpre, hxL⟩ := Set.not_subset.mp hne
  obtain ⟨x', hx'L, hqx'⟩ := hxpre
  have hd : 0 < Metric.infDist x (L₀ : Set X) :=
    (IsClosed.notMem_iff_infDist_pos L₀.isCompact.isClosed L₀.nonempty).mp hxL
  set d := Metric.infDist x (L₀ : Set X) with hddef
  refine ⟨{K : NonemptyCompacts X |
        ((K : Set X) ∩ q ⁻¹' (q '' Metric.ball x (d / 2))).Nonempty}
      ∩ {K : NonemptyCompacts X |
        (K : Set X) ⊆ (Metric.closedBall x (d / 2))ᶜ}, ?_, ?_, ?_⟩
  · -- every body in the neighborhood fails saturation
    rintro K ⟨⟨z, hzK, hzpre⟩, hmiss⟩
    rw [Set.mem_compl_iff, Set.mem_setOf_eq]
    intro hKsat
    obtain ⟨u₀, hu₀ball, hqu₀⟩ := hzpre
    have hu₀pre : u₀ ∈ q ⁻¹' (q '' (K : Set X)) := ⟨z, hzK, hqu₀.symm⟩
    rw [← hKsat] at hu₀pre
    exact hmiss hu₀pre (Metric.ball_subset_closedBall hu₀ball)
  · -- the neighborhood is Vietoris-open: hit an open, miss a closed
    exact (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen
        ((hopen _ Metric.isOpen_ball).preimage hcont)).inter
      (NonemptyCompacts.isOpen_subsets_of_isOpen
        Metric.isClosed_closedBall.isOpen_compl)
  · constructor
    · -- hit: the inside fibre-mate x' sees the ball through its fibre
      exact ⟨x', hx'L, x, Metric.mem_ball_self (half_pos hd), hqx'.symm⟩
    · -- miss: all of L₀ sits at distance ≥ d from x
      intro y hy
      rw [Set.mem_compl_iff, Metric.mem_closedBall, not_le]
      calc d / 2 < d := half_lt_self hd
        _ ≤ dist x y := Metric.infDist_le_dist_of_mem hy
        _ = dist y x := dist_comm _ _

/-- **The saturated classes form a closed locus** along any surjective
outcome map — the one topological brick the transport structure theorem
left open, laid: the pushforward is open, and saturation is closed under
open continuous maps. -/
theorem isClosed_satClass {V W : Type*} [Fintype V] [Fintype W] {θ : V → W}
    (hθ : Function.Surjective θ) :
    IsClosed {L : NonemptyCompacts (BelState V) |
      Saturated θ (L : Set (BelState V))} :=
  isClosed_setOf_saturated (continuous_belPush θ) (isOpenMap_belPush hθ)

end SaturatedClosed

/-! ## The fibre operations preserve constructibility -/

section Citizenship

variable {V W : Type*} [Fintype V] [Fintype W]

/-- **Per-piece topological citizenship on the surjective stratum**: the
transported class of a crescent is locally closed — the structure theorem
writes it as crescent-of-transported-atom ∩ saturated, the crescent factor
is locally closed, and the saturation factor is closed. -/
theorem isLocallyClosed_transportClass_crescentClass [Nonempty V]
    {θ : V → W} (hθ : Function.Surjective θ) {u : ProbPenalty W}
    {𝒱 : Set (ProbPenalty W)} (hu : LowerSemicontinuous u)
    (h𝒱 : 𝒱.Finite) (hlsc : ∀ v ∈ 𝒱, LowerSemicontinuous v) :
    IsLocallyClosed (transportClass θ (crescentClass u 𝒱)) := by
  rw [transportClass_crescentClass hθ u 𝒱]
  exact IsLocallyClosed.inter
    (isLocallyClosed_crescentClass (lowerSemicontinuous_pullPen θ hu)
      (h𝒱.image _)
      (by
        rintro v' ⟨v, hv, rfl⟩
        exact lowerSemicontinuous_pullPen θ (hlsc v hv)))
    (IsClosed.isLocallyClosed (isClosed_satClass hθ))

/-- Finite indexed unions of constructible sets are constructible. -/
theorem IsConstructibleUnion.iUnion_fin {X : Type*} [TopologicalSpace X]
    {n : ℕ} {C : Fin n → Set X} (hC : ∀ i, IsConstructibleUnion (C i)) :
    IsConstructibleUnion (⋃ i, C i) := by
  induction n with
  | zero =>
      refine ⟨0, Fin.elim0, fun i => i.elim0, ?_⟩
      rw [Set.iUnion_of_empty, Set.iUnion_of_empty]
  | succ n ih =>
      have hsplit : (⋃ i : Fin (n + 1), C i)
          = C 0 ∪ ⋃ i : Fin n, C i.succ := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_union]
        constructor
        · rintro ⟨i, hi⟩
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
          · exact Or.inl hi
          · exact Or.inr ⟨j, hi⟩
        · rintro (h | ⟨j, hj⟩)
          · exact ⟨0, h⟩
          · exact ⟨j.succ, hj⟩
      rw [hsplit]
      exact (hC 0).union (ih fun i => hC i.succ)

/-- **Transport preserves constructibility** — the citizenship statement of
the composition tier's transport operations, at the level the fibres live
at: along a surjective outcome map, the transported class of a citizen DNF
class is constructible.  Transport distributes over the disjuncts
(`transportClass_iUnion`), and each disjunct's transport is locally
closed. -/
theorem isConstructibleUnion_transportClass_dnfClass [Nonempty V]
    {θ : V → W} (hθ : Function.Surjective θ) {n : ℕ}
    {u : Fin n → ProbPenalty W} {𝒱 : Fin n → Set (ProbPenalty W)}
    (hu : ∀ i, LowerSemicontinuous (u i)) (h𝒱 : ∀ i, (𝒱 i).Finite)
    (hlsc : ∀ i, ∀ v ∈ 𝒱 i, LowerSemicontinuous v) :
    IsConstructibleUnion (transportClass θ (dnfClass u 𝒱)) := by
  have hdnf : transportClass θ (dnfClass u 𝒱)
      = ⋃ i, transportClass θ (crescentClass (u i) (𝒱 i)) := by
    rw [dnfClass, transportClass_iUnion]
  rw [hdnf]
  exact IsConstructibleUnion.iUnion_fin fun i =>
    IsLocallyClosed.isConstructibleUnion
      (isLocallyClosed_transportClass_crescentClass hθ (hu i) (h𝒱 i)
        (hlsc i))

/-- **The compositor preserves constructibility at the atom level, for any
liveness assignment**: composed safety floors are citizens
(`lowerSemicontinuous_boxplus`), so the disjunct-pairwise composite of two
citizen DNFs is a citizen class whatever finite lsc liveness families the
composite atoms are assigned.  Citizenship and the composite-liveness
design question are independent: this is the citizenship half,
unconditional. -/
theorem isConstructibleUnion_boxplusDnf {V W₁ W₂ : Type*} [Fintype V]
    [Fintype W₁] [Fintype W₂] (j₁ : V → W₁) (j₂ : V → W₂) {n₁ n₂ : ℕ}
    {u₁ : Fin n₁ → ProbPenalty W₁} {u₂ : Fin n₂ → ProbPenalty W₂}
    (hu₁ : ∀ i, LowerSemicontinuous (u₁ i))
    (hu₂ : ∀ j, LowerSemicontinuous (u₂ j))
    (F : Fin n₁ → Fin n₂ → Set (ProbPenalty V))
    (hF : ∀ i j, (F i j).Finite)
    (hFlsc : ∀ i j, ∀ v ∈ F i j, LowerSemicontinuous v) :
    IsConstructibleUnion (⋃ i, ⋃ j,
      crescentClass (pullPen j₁ (u₁ i) + pullPen j₂ (u₂ j)) (F i j)) :=
  IsConstructibleUnion.iUnion_fin fun i =>
    IsConstructibleUnion.iUnion_fin fun j =>
      IsLocallyClosed.isConstructibleUnion
        (isLocallyClosed_crescentClass
          (lowerSemicontinuous_boxplus j₁ j₂ (hu₁ i) (hu₂ j)) (hF i j)
          (hFlsc i j))

end Citizenship

/-! ## The constructible level is forced -/

section Exhibit

theorem pushFun_id {V : Type*} [Fintype V] (x : V → ℝ) :
    pushFun (id : V → V) x = x := by
  classical
  funext v
  show (∑ v', if v' = v then x v' else 0) = x v
  rw [Finset.sum_ite_eq' Finset.univ v x]
  simp

theorem BelState.push_id {V : Type*} [Fintype V] :
    BelState.push (id : V → V) = (id : BelState V → BelState V) := by
  funext x
  exact Subtype.ext (by rw [BelState.push_coe, pushFun_id]; rfl)

/-- Identity transport is the identity on classes. -/
theorem transportClass_id {V : Type*} [Fintype V]
    (C : Set (NonemptyCompacts (BelState V))) :
    transportClass (id : V → V) C = C := by
  ext L
  simp only [transportClass, Set.mem_setOf_eq, BelState.push_id,
    Set.preimage_id]
  constructor
  · rintro ⟨K, hK, hL⟩
    rwa [show L = K from SetLike.ext' hL]
  · intro hL
    exact ⟨L, hL, rfl⟩

/-- The half-mass wall: the constant penalty whose body is the half-mass
ball. -/
noncomputable def halfPen : ProbPenalty Bool := fun _ => gradeInv (1 / 2)

/-- The spike: free up to half mass on the ray at `false`'s point mass,
hard violation elsewhere.  Its body is the half segment of a single ray. -/
noncomputable def spikePen : ProbPenalty Bool :=
  probWall {ProbState.dirac false} ⊔ halfPen

theorem grade_halfPen (μ : ProbState Bool) : grade (halfPen μ) = 1 / 2 :=
  grade_gradeInv (by norm_num) (by norm_num)

theorem lowerSemicontinuous_halfPen : LowerSemicontinuous halfPen :=
  lowerSemicontinuous_const

theorem spikePen_apply_same :
    spikePen (ProbState.dirac false) = gradeInv (1 / 2) := by
  show probWall {ProbState.dirac false} (ProbState.dirac false)
      ⊔ halfPen (ProbState.dirac false) = gradeInv (1 / 2)
  rw [probWall_apply_of_mem (Set.mem_singleton _)]
  exact sup_eq_right.mpr zero_le

theorem spikePen_apply_of_ne {μ : ProbState Bool}
    (h : μ ≠ ProbState.dirac false) : spikePen μ = ⊤ := by
  show probWall {ProbState.dirac false} μ ⊔ halfPen μ = ⊤
  rw [probWall_apply_of_not_mem (by simpa using h), top_sup_eq]

theorem lowerSemicontinuous_spikePen : LowerSemicontinuous spikePen := by
  classical
  rw [lowerSemicontinuous_prob_iff_isClosed_sublevel]
  intro s
  rcases eq_or_ne s ⊤ with rfl | hstop
  · have huniv : {μ : ProbState Bool | spikePen μ ≤ ⊤} = Set.univ := by
      ext μ
      simp
    rw [huniv]
    exact isClosed_univ
  by_cases hge : gradeInv (1 / 2) ≤ s
  · have hsingle : {μ : ProbState Bool | spikePen μ ≤ s}
        = {ProbState.dirac false} := by
      ext μ
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hμ
        by_contra hne
        rw [spikePen_apply_of_ne hne, top_le_iff] at hμ
        exact hstop hμ
      · rintro rfl
        rw [spikePen_apply_same]
        exact hge
    rw [hsingle]
    exact isClosed_singleton
  · have hlt : s < gradeInv (1 / 2) := not_le.mp hge
    have hempty : {μ : ProbState Bool | spikePen μ ≤ s} = ∅ := by
      ext μ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      rcases eq_or_ne μ (ProbState.dirac false) with rfl | hne
      · rw [spikePen_apply_same]
        exact hlt
      · rw [spikePen_apply_of_ne hne]
        exact hlt.trans_le le_top
    rw [hempty]
    exact isClosed_empty

/-- The intermediate states of the exhibit: mass `t` at `false`, the rest
at `true`. -/
noncomputable def stateAt (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ProbState Bool :=
  ⟨fun b => if b then 1 - t else t,
    fun b => by
      cases b
      · simpa using h0
      · simpa using h1, by
    rw [Fintype.sum_bool]
    simp⟩

@[simp] theorem stateAt_coe (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ((stateAt t h0 h1 : ProbState Bool) : Bool → ℝ)
      = fun b => if b then 1 - t else t := rfl

theorem stateAt_ne_dirac {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (ht : t ≠ 1) :
    stateAt t h0 h1 ≠ ProbState.dirac false := by
  intro heq
  have hval := congrArg (fun μ : ProbState Bool => (μ : Bool → ℝ) false) heq
  simp only [stateAt_coe, if_neg (by simp : ¬ (false : Bool) = true),
    ProbState.dirac_apply_same] at hval
  exact ht hval

/-- The scaled family used in the exhibit: `γ` times the intermediate
state. -/
noncomputable def scaledAt (γ t : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : BelState Bool :=
  scalePoint γ hγ0 hγ1 (stateAt t h0 h1)

/-- Rescaling along a fixed direction moves a point by at most the scale
difference. -/
theorem dist_scaledAt_scale_le (γ γ' t : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hγ'0 : 0 ≤ γ') (hγ'1 : γ' ≤ 1) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    dist (scaledAt γ t hγ0 hγ1 h0 h1) (scaledAt γ' t hγ'0 hγ'1 h0 h1)
      ≤ |γ - γ'| := by
  rw [Subtype.dist_eq]
  refine (dist_pi_le_iff (abs_nonneg _)).mpr fun b => ?_
  simp only [scaledAt, scalePoint_coe, stateAt_coe, Pi.smul_apply,
    smul_eq_mul, Real.dist_eq]
  rw [← sub_mul, abs_mul]
  have hcoord : |if b = true then 1 - t else t| ≤ 1 := by
    cases b
    · rw [if_neg (by simp), abs_of_nonneg h0]
      exact h1
    · rw [if_pos rfl, abs_of_nonneg (by linarith)]
      linarith
  calc |γ - γ'| * |if b = true then 1 - t else t|
      ≤ |γ - γ'| * 1 := mul_le_mul_of_nonneg_left hcoord (abs_nonneg _)
    _ = |γ - γ'| := mul_one _

/-- Scaling the point mass at `false`: the tip family of the spike. -/
noncomputable def scaledDirac (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    BelState Bool :=
  scalePoint γ hγ0 hγ1 (ProbState.dirac false)

theorem dist_scaledAt_scaledDirac (γ t : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    dist (scaledAt γ t hγ0 hγ1 h0 h1) (scaledDirac γ hγ0 hγ1)
      ≤ γ * (1 - t) := by
  have htarget : (0 : ℝ) ≤ γ * (1 - t) := mul_nonneg hγ0 (by linarith)
  rw [Subtype.dist_eq]
  refine (dist_pi_le_iff htarget).mpr fun b => ?_
  simp only [scaledAt, scaledDirac, scalePoint_coe, stateAt_coe,
    Pi.smul_apply, smul_eq_mul, Real.dist_eq]
  cases b
  · rw [if_neg (by simp), ProbState.dirac_apply_same, ← mul_sub, abs_mul,
      abs_of_nonneg hγ0, abs_of_nonpos (by linarith : t - 1 ≤ 0),
      show -(t - 1) = 1 - t from by ring]
  · rw [if_pos rfl,
      ProbState.dirac_apply_of_ne (by decide : (true : Bool) ≠ false),
      mul_zero, sub_zero, abs_mul, abs_of_nonneg hγ0,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)]

/-- Membership of scaled intermediate states in the half-mass body. -/
theorem scaledAt_mem_compile_halfPen {γ t : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (h0 : 0 ≤ t) (h1 : t ≤ 1) (hγ : γ ≤ 1 / 2) :
    scaledAt γ t hγ0 hγ1 h0 h1 ∈ compile halfPen :=
  ⟨stateAt t h0 h1, γ, hγ0, by rw [grade_halfPen]; exact hγ,
    scalePoint_coe _ _ _ _⟩

/-- Off-tip scaled states at positive mass escape the half-mass body as
soon as their mass exceeds one half. -/
theorem scaledAt_notMem_compile_halfPen {γ t : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (h0 : 0 ≤ t) (h1 : t ≤ 1) (hγ : 1 / 2 < γ) :
    scaledAt γ t hγ0 hγ1 h0 h1 ∉ compile halfPen := by
  intro hmem
  have hle := compile_scale_le hmem (lt_of_le_of_lt (by norm_num) hγ)
    (scalePoint_coe _ _ _ _)
  rw [grade_halfPen] at hle
  exact absurd hle (not_le.mpr hγ)

/-- Off-tip scaled states at positive mass are never in the spike body. -/
theorem scaledAt_notMem_compile_spikePen {γ t : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (h0 : 0 ≤ t) (h1 : t ≤ 1) (hγ : 0 < γ) (ht : t ≠ 1) :
    scaledAt γ t hγ0 hγ1 h0 h1 ∉ compile spikePen := by
  intro hmem
  have hle := compile_scale_le hmem hγ (scalePoint_coe _ _ _ _)
  rw [spikePen_apply_of_ne (stateAt_ne_dirac h0 h1 ht), grade_top] at hle
  exact absurd hle (not_le.mpr hγ)

/-- The exhibit's citizen class: escape past the half-mass wall, or sit
inside the spike. -/
noncomputable def exhibitDnfU : Fin 2 → ProbPenalty Bool := ![0, spikePen]

noncomputable def exhibitDnfV : Fin 2 → Set (ProbPenalty Bool) :=
  ![{halfPen}, ∅]

theorem exhibitDnf_eq :
    dnfClass exhibitDnfU exhibitDnfV
      = crescentClass (0 : ProbPenalty Bool) {halfPen}
        ∪ crescentClass spikePen ∅ := by
  ext K
  simp only [dnfClass, exhibitDnfU, exhibitDnfV, Set.mem_iUnion,
    Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.mem_union]

theorem exhibitDnf_lsc_u : ∀ i, LowerSemicontinuous (exhibitDnfU i) := by
  rw [Fin.forall_fin_two]
  exact ⟨lowerSemicontinuous_const, lowerSemicontinuous_spikePen⟩

theorem exhibitDnf_finite_v : ∀ i, (exhibitDnfV i).Finite := by
  rw [Fin.forall_fin_two]
  exact ⟨Set.finite_singleton _, Set.finite_empty⟩

theorem exhibitDnf_lsc_v :
    ∀ i, ∀ v ∈ exhibitDnfV i, LowerSemicontinuous v := by
  rw [Fin.forall_fin_two]
  constructor
  · intro v hv
    rw [show exhibitDnfV 0 = {halfPen} from rfl, Set.mem_singleton_iff] at hv
    subst hv
    exact lowerSemicontinuous_halfPen
  · intro v hv
    rw [show exhibitDnfV 1 = ∅ from rfl] at hv
    exact absurd hv (Set.notMem_empty v)

/-- The spike body, as a hyperspace point: the base point of the
refutation. -/
noncomputable def spikeBody : NonemptyCompacts (BelState Bool) :=
  compileNC spikePen lowerSemicontinuous_spikePen

theorem spikeBody_mem_crescent :
    spikeBody ∈ crescentClass spikePen (∅ : Set (ProbPenalty Bool)) := by
  rw [mem_crescentClass_iff]
  exact ⟨fun x hx => hx, fun v hv => absurd hv (Set.notMem_empty v)⟩

/-- The spike's half-mass tip lies in the spike body. -/
theorem scaledDirac_mem_spikeBody :
    scaledDirac (1 / 2) (by norm_num) (by norm_num)
      ∈ (spikeBody : Set (BelState Bool)) := by
  show scaledDirac (1 / 2) (by norm_num) (by norm_num) ∈ compile spikePen
  refine ⟨ProbState.dirac false, 1 / 2, by norm_num, ?_,
    scalePoint_coe _ _ _ _⟩
  rw [spikePen_apply_same, grade_gradeInv (by norm_num) (by norm_num)]


/-- The spike body sits inside the half-mass body. -/
theorem spikeBody_subset_compile_halfPen :
    (spikeBody : Set (BelState Bool)) ⊆ compile halfPen := by
  show compile spikePen ⊆ compile halfPen
  exact compile_subset_compile_iff.mpr le_sup_right

/-- **The exhibit class is not locally closed.**  If it were `U ∩ Z`, a
basic Vietoris neighborhood of the spike body inside `U` would admit the
spike body plus one off-tip point of the half-mass sphere — a class in the
closure of the escape crescent (approximate by adding a nearby point just
past the wall), hence in `Z`, hence in the class; but it neither escapes
the wall nor sits inside the spike. -/
theorem not_isLocallyClosed_exhibitClass :
    ¬ IsLocallyClosed (dnfClass exhibitDnfU exhibitDnfV) := by
  classical
  rintro ⟨U, Z, hUopen, hZclosed, hCeq⟩
  -- the base point of the refutation
  have hK₀C : spikeBody ∈ dnfClass exhibitDnfU exhibitDnfV := by
    rw [exhibitDnf_eq]
    exact Or.inr spikeBody_mem_crescent
  have hK₀U : spikeBody ∈ U := by
    rw [hCeq] at hK₀C
    exact hK₀C.1
  -- a basic Vietoris neighborhood of the spike body inside U
  obtain ⟨B, hBmem, hK₀B, hBU⟩ :=
    NonemptyCompacts.isTopologicalBasis.exists_subset_of_mem_open hK₀U hUopen
  obtain ⟨u₀, ⟨hu₀fin, hu₀ne, hu₀open⟩, rfl⟩ := hBmem
  obtain ⟨hK₀sub, hK₀hits⟩ := hK₀B
  -- the tip sees an ε-ball inside the containment open
  have htip : scaledDirac (1 / 2) (by norm_num) (by norm_num) ∈ ⋃₀ u₀ :=
    hK₀sub scaledDirac_mem_spikeBody
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp (isOpen_sUnion hu₀open) _ htip
  -- the off-tip parameter: close enough to the tip, strictly off it
  set δ₀ := min ε 1 with hδ₀def
  have hδ₀pos : 0 < δ₀ := lt_min hε one_pos
  have hδ₀le : δ₀ ≤ 1 := min_le_right _ _
  set t := 1 - δ₀ / 2 with htdef
  have ht0 : 0 ≤ t := by
    rw [htdef]
    linarith
  have ht1 : t ≤ 1 := by
    rw [htdef]
    linarith
  have htne : t ≠ 1 := by
    rw [htdef]
    intro h
    have hz : δ₀ = 0 := by linarith
    exact absurd hz (ne_of_gt hδ₀pos)
  -- the off-tip half-mass point
  set y := scaledAt (1 / 2) t (by norm_num) (by norm_num) ht0 ht1 with hydef
  have hyball : y ∈ Metric.ball
      (scaledDirac (1 / 2) (by norm_num) (by norm_num)) ε := by
    rw [Metric.mem_ball]
    calc dist y (scaledDirac (1 / 2) (by norm_num) (by norm_num))
        ≤ 1 / 2 * (1 - t) :=
          dist_scaledAt_scaledDirac _ _ _ _ ht0 ht1
      _ = δ₀ / 4 := by rw [htdef]; ring
      _ < ε := by
          have : δ₀ ≤ ε := min_le_left _ _
          linarith
  -- the probe class: spike body plus the off-tip point
  set K' : NonemptyCompacts (BelState Bool) :=
    ⟨⟨(spikeBody : Set (BelState Bool)) ∪ {y},
      spikeBody.isCompact.union isCompact_singleton⟩,
      spikeBody.nonempty.mono Set.subset_union_left⟩ with hK'def
  have hK'coe : (K' : Set (BelState Bool))
      = (spikeBody : Set (BelState Bool)) ∪ {y} := rfl
  have hyK' : y ∈ (K' : Set (BelState Bool)) := by
    rw [hK'coe]
    exact Or.inr rfl
  -- K' lands in the basic neighborhood, hence in U
  have hK'B : (K' : Set (BelState Bool)) ⊆ ⋃₀ u₀
      ∧ ∀ W ∈ u₀, ((K' : Set (BelState Bool)) ∩ W).Nonempty := by
    constructor
    · rw [hK'coe]
      refine Set.union_subset hK₀sub ?_
      rw [Set.singleton_subset_iff]
      exact hball hyball
    · intro W hW
      refine (hK₀hits W hW).mono (Set.inter_subset_inter_left W ?_)
      rw [hK'coe]
      exact Set.subset_union_left
  have hK'U : K' ∈ U := hBU hK'B
  -- K' lies in the closure of the escape crescent
  have hK'cl : K' ∈ closure
      (crescentClass (0 : ProbPenalty Bool) {halfPen}) := by
    rw [mem_closure_iff]
    intro O hOopen hK'O
    obtain ⟨B', hB'mem, hK'B', hB'O⟩ :=
      NonemptyCompacts.isTopologicalBasis.exists_subset_of_mem_open hK'O
        hOopen
    obtain ⟨u₁, ⟨hu₁fin, hu₁ne, hu₁open⟩, rfl⟩ := hB'mem
    obtain ⟨hK'sub₁, hK'hits₁⟩ := hK'B'
    -- the off-tip point sees an ε₁-ball inside the new containment open
    have hy₁ : y ∈ ⋃₀ u₁ := hK'sub₁ hyK'
    obtain ⟨ε₁, hε₁, hball₁⟩ :=
      Metric.isOpen_iff.mp (isOpen_sUnion hu₁open) _ hy₁
    -- one more point, just past the wall
    have hmin₁pos : 0 < min ε₁ (1 / 2) := lt_min hε₁ (by norm_num)
    have hmin₁le : min ε₁ (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have hγ'0 : (0 : ℝ) ≤ 1 / 2 + min ε₁ (1 / 2) / 2 := by linarith
    have hγ'1 : 1 / 2 + min ε₁ (1 / 2) / 2 ≤ 1 := by linarith
    have hγ'half : 1 / 2 < 1 / 2 + min ε₁ (1 / 2) / 2 := by linarith
    have hzball : scaledAt (1 / 2 + min ε₁ (1 / 2) / 2) t hγ'0 hγ'1 ht0 ht1
        ∈ Metric.ball y ε₁ := by
      rw [Metric.mem_ball]
      calc dist (scaledAt (1 / 2 + min ε₁ (1 / 2) / 2) t hγ'0 hγ'1 ht0 ht1) y
          ≤ |1 / 2 + min ε₁ (1 / 2) / 2 - 1 / 2| := by
            rw [hydef]
            exact dist_scaledAt_scale_le _ _ t hγ'0 hγ'1 (by norm_num)
              (by norm_num) ht0 ht1
        _ = min ε₁ (1 / 2) / 2 := by
            rw [abs_of_pos (by linarith)]
            ring
        _ < ε₁ := by
            have hle : min ε₁ (1 / 2) ≤ ε₁ := min_le_left _ _
            linarith
    -- the probe class one step further out: K' plus the past-the-wall point
    refine ⟨⟨⟨(K' : Set (BelState Bool))
        ∪ {scaledAt (1 / 2 + min ε₁ (1 / 2) / 2) t hγ'0 hγ'1 ht0 ht1},
        K'.isCompact.union isCompact_singleton⟩,
        K'.nonempty.mono Set.subset_union_left⟩, hB'O ⟨?_, ?_⟩, ?_⟩
    · -- containment in ⋃₀ u₁
      refine Set.union_subset hK'sub₁ ?_
      rw [Set.singleton_subset_iff]
      exact hball₁ hzball
    · -- hits: inherited from K'
      intro W hW
      exact (hK'hits₁ W hW).mono
        (Set.inter_subset_inter_left W Set.subset_union_left)
    · -- membership in the escape crescent
      rw [mem_crescentClass_iff]
      constructor
      · rw [compile_zero]
        exact fun x _ => Set.mem_univ x
      · intro v hv
        rw [Set.mem_singleton_iff] at hv
        subst hv
        refine ⟨scaledAt (1 / 2 + min ε₁ (1 / 2) / 2) t hγ'0 hγ'1 ht0 ht1,
          Or.inr rfl, ?_⟩
        exact scaledAt_notMem_compile_halfPen hγ'0 hγ'1 ht0 ht1 hγ'half
  -- the closure of the escape crescent sits inside Z
  have hcresC : crescentClass (0 : ProbPenalty Bool) {halfPen}
      ⊆ dnfClass exhibitDnfU exhibitDnfV := by
    rw [exhibitDnf_eq]
    exact Set.subset_union_left
  have hCZ : dnfClass exhibitDnfU exhibitDnfV ⊆ Z := by
    rw [hCeq]
    exact Set.inter_subset_right
  have hK'Z : K' ∈ Z :=
    (hZclosed.closure_subset_iff.mpr (hcresC.trans hCZ)) hK'cl
  have hK'C : K' ∈ dnfClass exhibitDnfU exhibitDnfV := by
    rw [hCeq]
    exact ⟨hK'U, hK'Z⟩
  -- but K' is in neither disjunct
  rw [exhibitDnf_eq] at hK'C
  rcases hK'C with hK'esc | hK'spike
  · -- K' does not escape the half-mass body: all its points sit inside
    obtain ⟨-, hesc⟩ := mem_crescentClass_iff.mp hK'esc
    obtain ⟨w, hwK', hwout⟩ := hesc halfPen (Set.mem_singleton _)
    rw [hK'coe] at hwK'
    rcases hwK' with hwK₀ | hwy
    · exact hwout (spikeBody_subset_compile_halfPen hwK₀)
    · rw [Set.mem_singleton_iff] at hwy
      subst hwy
      refine hwout ?_
      rw [hydef]
      exact scaledAt_mem_compile_halfPen (by norm_num) (by norm_num) ht0 ht1
        le_rfl
  · -- K' does not sit inside the spike body: the off-tip point protrudes
    obtain ⟨hsub, -⟩ := mem_crescentClass_iff.mp hK'spike
    have hymem := hsub hyK'
    rw [hydef] at hymem
    exact scaledAt_notMem_compile_spikePen (by norm_num) (by norm_num) ht0
      ht1 (by norm_num) htne hymem

/-- **The constructible level is forced** (the citizenship statement's
level is not a convenience): a citizen DNF class that is constructible but
not locally closed, transported verbatim by the surjective identity
transport.  Per-piece local closedness survives transport on the
surjective stratum (`isLocallyClosed_transportClass_crescentClass`); the
class-level typing of the fibres nevertheless cannot be "locally closed
subsets" — disjunction already forces the constructible level, and the
fibre operations preserve exactly that
(`isConstructibleUnion_transportClass_dnfClass`). -/
theorem exists_transportClass_constructible_not_locallyClosed :
    ∃ (u : Fin 2 → ProbPenalty Bool) (𝒱 : Fin 2 → Set (ProbPenalty Bool)),
      (∀ i, LowerSemicontinuous (u i)) ∧ (∀ i, (𝒱 i).Finite) ∧
      (∀ i, ∀ v ∈ 𝒱 i, LowerSemicontinuous v) ∧
      IsConstructibleUnion
        (transportClass (id : Bool → Bool) (dnfClass u 𝒱)) ∧
      ¬ IsLocallyClosed
        (transportClass (id : Bool → Bool) (dnfClass u 𝒱)) := by
  refine ⟨exhibitDnfU, exhibitDnfV, exhibitDnf_lsc_u, exhibitDnf_finite_v,
    exhibitDnf_lsc_v, ?_, ?_⟩
  · exact isConstructibleUnion_transportClass_dnfClass
      Function.surjective_id exhibitDnf_lsc_u exhibitDnf_finite_v
      exhibitDnf_lsc_v
  · rw [transportClass_id]
    exact not_isLocallyClosed_exhibitClass

end Exhibit

end SuFunctor.Universe
