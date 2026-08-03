import SuFunctor.Stochastic.NoiseSemantics

/-! # Kleisli functoriality of the noise-port semantics

Sequential composition of probabilistic hypernets with **disjoint noise
rosters** denotes the Kleisli composite of their denotations: the first
stage reads the first `N₁` ports, the second stage reads the first
stage's outcome together with the remaining `N₂` ports, and the
denotation of the composite is `bind` of the denotations.  This is the
functoriality law that upgrades "randomness enters at the interface,
never at a box" from a claim about one box to a law about composition:
the evaluator never samples, and every downstream consumer is entitled
to reason kernel-locally.

Main results:

* `Universe.ProbState.bind` — the finite-carrier Kleisli composition on
  the flat carrier: the mass-weighted mixture of the continuation's
  states over the intermediate outcome.  `dirac` is its unit
  (`dirac_bind`, `bind_dirac`), the composition is associative
  (`bind_assoc`), and the landed pushforward is its deterministic
  special case (`push_eq_bind_dirac`).
* `noiseCube_split` — **reading disjoint port blocks is independence**:
  the reference measure of the split cube assigns to a rectangle the
  product of the block measures.
* `noiseDenot_seqComp` — **the functoriality law**: with disjoint
  rosters, the denotation of the sequential composite is the Kleisli
  composite of the denotations.  `noiseDenot_seqComp_uncurried` is the
  same law against a jointly measurable second stage.
* `copy_ne_kleisli` — **disjointness is content, not bookkeeping**:
  with a shared roster the law fails.  Sharing one draw between the two
  stages is copy (`shared_eq_copyPair`, definitional), the Kleisli
  composite of the stage denotations resamples (`kleisli_eq_fresh`),
  and the landed copy-vs-resample separation (`copy_ne_fresh`) is the
  witness.
-/

namespace SuFunctor.Universe

variable {V : Type*} [Fintype V] {W : Type*} [Fintype W] {X : Type*} [Fintype X]

namespace ProbState

/-- The finite-carrier Kleisli composition on the flat carrier: the
mass-weighted mixture of the continuation's states over the
intermediate outcome.  Carrier-level — no measure theory; the two-point
mixture is `BelState.mix`, and migration next to the other carrier
operations is routine refactoring left for a quiet pass.  Mass one of
the composite consumes mass one of every continuation state: this
operation has no sub-stochastic analogue at this tier, by design. -/
noncomputable def bind (μ : ProbState V) (κ : V → ProbState W) : ProbState W :=
  ⟨fun w => ∑ v, (μ : V → ℝ) v * (κ v : W → ℝ) w,
   fun w => Finset.sum_nonneg fun v _ =>
     mul_nonneg (μ.nonneg v) ((κ v).nonneg w),
   by
     show ∑ w, ∑ v, (μ : V → ℝ) v * (κ v : W → ℝ) w = 1
     rw [Finset.sum_comm]
     simp_rw [← Finset.mul_sum, ProbState.sum_eq_one, mul_one]
     exact μ.sum_eq_one⟩

@[simp] theorem bind_coe (μ : ProbState V) (κ : V → ProbState W) :
    ((μ.bind κ : ProbState W) : W → ℝ)
      = fun w => ∑ v, (μ : V → ℝ) v * (κ v : W → ℝ) w := rfl

/-- The point mass is a left unit for the Kleisli composition. -/
theorem dirac_bind [DecidableEq V] (v₀ : V) (κ : V → ProbState W) :
    (dirac v₀).bind κ = κ v₀ := by
  refine Subtype.ext (funext fun w => ?_)
  show ∑ v, ((dirac v₀ : ProbState V) : V → ℝ) v * (κ v : W → ℝ) w
    = (κ v₀ : W → ℝ) w
  rw [Finset.sum_eq_single v₀
      (fun v _ hv => by rw [dirac_apply_of_ne hv, zero_mul])
      (fun h => absurd (Finset.mem_univ v₀) h),
    dirac_apply_same, one_mul]

/-- The point mass is a right unit for the Kleisli composition. -/
theorem bind_dirac [DecidableEq V] (μ : ProbState V) :
    μ.bind dirac = μ := by
  refine Subtype.ext (funext fun w => ?_)
  show ∑ v, (μ : V → ℝ) v * ((dirac v : ProbState V) : V → ℝ) w
    = (μ : V → ℝ) w
  rw [Finset.sum_eq_single w
      (fun v _ hv => by rw [dirac_apply_of_ne (Ne.symm hv), mul_zero])
      (fun h => absurd (Finset.mem_univ w) h),
    dirac_apply_same, mul_one]

/-- The Kleisli composition is associative. -/
theorem bind_assoc (μ : ProbState V) (κ : V → ProbState W)
    (κ' : W → ProbState X) :
    (μ.bind κ).bind κ' = μ.bind fun v => (κ v).bind κ' := by
  refine Subtype.ext (funext fun x => ?_)
  show ∑ w, (∑ v, (μ : V → ℝ) v * (κ v : W → ℝ) w) * (κ' w : X → ℝ) x
    = ∑ v, (μ : V → ℝ) v * ∑ w, (κ v : W → ℝ) w * (κ' w : X → ℝ) x
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- The landed pushforward is the deterministic special case of the
Kleisli composition: pushing along an outcome map is binding into point
masses. -/
theorem push_eq_bind_dirac [DecidableEq W] (θ : V → W) (μ : ProbState V) :
    ProbState.push θ μ = μ.bind fun v => dirac (θ v) := by
  refine Subtype.ext (funext fun w => ?_)
  show pushFun θ (μ : V → ℝ) w
    = ∑ v, (μ : V → ℝ) v * ((dirac (θ v) : ProbState W) : W → ℝ) w
  unfold pushFun
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : θ v = w
  · rw [if_pos h, h, dirac_apply_same, mul_one]
  · rw [if_neg h, dirac_apply_of_ne (Ne.symm h), mul_zero]

end ProbState

end SuFunctor.Universe

namespace SuFunctor.Stochastic

open MeasureTheory SuFunctor.Universe

/-! ## Reading disjoint port blocks is independence -/

variable {N₁ N₂ : ℕ}

/-- The first `N₁` coordinates of a split noise cube: the ports the
first stage reads. -/
def frontPorts (N₁ N₂ : ℕ) (u : Fin (N₁ + N₂) → ℝ) : Fin N₁ → ℝ :=
  fun i => u (Fin.castAdd N₂ i)

/-- The last `N₂` coordinates of a split noise cube: the ports the
second stage reads.  Disjoint from `frontPorts` by construction — the
roster arithmetic carries the disjointness in the type. -/
def backPorts (N₁ N₂ : ℕ) (u : Fin (N₁ + N₂) → ℝ) : Fin N₂ → ℝ :=
  fun j => u (Fin.natAdd N₁ j)

theorem measurable_frontPorts : Measurable (frontPorts N₁ N₂) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

theorem measurable_backPorts : Measurable (backPorts N₁ N₂) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- **Reading disjoint port blocks is independence**: the reference
measure of the split cube assigns to a rectangle the product of the
block measures.  (The split map is measure-preserving onto the product
of the block cubes; this is the finite-outcome Fubini step the
functoriality law rests on.) -/
theorem noiseCube_split (N₁ N₂ : ℕ) {A : Set (Fin N₁ → ℝ)}
    {B : Set (Fin N₂ → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    noiseCube (N₁ + N₂) (frontPorts N₁ N₂ ⁻¹' A ∩ backPorts N₁ N₂ ⁻¹' B)
      = noiseCube N₁ A * noiseCube N₂ B := by
  have h₁ : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (N₁ + N₂) => ℝ)
        finSumFinEquiv).symm
      (noiseCube (N₁ + N₂))
      (Measure.pi fun _ : Fin N₁ ⊕ Fin N₂ => unitUniform) :=
    MeasurePreserving.symm _
      (measurePreserving_piCongrLeft (fun _ => unitUniform) finSumFinEquiv)
  have h₂ : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin N₁ ⊕ Fin N₂ => ℝ)
      (Measure.pi fun _ : Fin N₁ ⊕ Fin N₂ => unitUniform)
      ((noiseCube N₁).prod (noiseCube N₂)) :=
    measurePreserving_sumPiEquivProdPi fun _ => unitUniform
  have hfun : (fun u => (frontPorts N₁ N₂ u, backPorts N₁ N₂ u))
      = ⇑(MeasurableEquiv.sumPiEquivProdPi fun _ : Fin N₁ ⊕ Fin N₂ => ℝ)
        ∘ ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin (N₁ + N₂) => ℝ)
            finSumFinEquiv).symm := by
    funext u
    refine Prod.ext ?_ ?_
    · funext i
      show u (Fin.castAdd N₂ i) = u (finSumFinEquiv (Sum.inl i))
      rw [finSumFinEquiv_apply_left]
    · funext j
      show u (Fin.natAdd N₁ j) = u (finSumFinEquiv (Sum.inr j))
      rw [finSumFinEquiv_apply_right]
  have hsplit : MeasurePreserving
      (fun u => (frontPorts N₁ N₂ u, backPorts N₁ N₂ u))
      (noiseCube (N₁ + N₂)) ((noiseCube N₁).prod (noiseCube N₂)) := by
    rw [hfun]
    exact h₂.comp h₁
  have hrect : frontPorts N₁ N₂ ⁻¹' A ∩ backPorts N₁ N₂ ⁻¹' B
      = (fun u => (frontPorts N₁ N₂ u, backPorts N₁ N₂ u)) ⁻¹' (A ×ˢ B) := by
    ext u
    simp [Set.mem_prod]
  rw [hrect, hsplit.measure_preimage (hA.prod hB).nullMeasurableSet,
    Measure.prod_prod]

/-! ## The sequential composite and the functoriality law -/

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
variable {W : Type*} [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]

/-- Sequential composition with disjoint noise rosters: the first stage
reads the first `N₁` ports, the second stage reads the first stage's
outcome together with the last `N₂` ports.  The composite reads
`N₁ + N₂` independent ports — fresh draws, never shared. -/
def seqComp (g : (Fin N₁ → ℝ) → V) (k : V → (Fin N₂ → ℝ) → W) :
    (Fin (N₁ + N₂) → ℝ) → W :=
  fun u => k (g (frontPorts N₁ N₂ u)) (backPorts N₁ N₂ u)

omit [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W] in
/-- The composite's outcome fibres split by the intermediate outcome:
the fibre over `w` is the union over `v` of front/back rectangles. -/
theorem seqComp_preimage_singleton (g : (Fin N₁ → ℝ) → V)
    (k : V → (Fin N₂ → ℝ) → W) (w : W) :
    seqComp g k ⁻¹' {w}
      = ⋃ v, frontPorts N₁ N₂ ⁻¹' (g ⁻¹' {v})
          ∩ backPorts N₁ N₂ ⁻¹' (k v ⁻¹' {w}) := by
  ext u
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
    Set.mem_inter_iff, seqComp]
  exact ⟨fun h => ⟨g (frontPorts N₁ N₂ u), rfl, h⟩,
    fun ⟨v, hv, h⟩ => by rw [hv]; exact h⟩

/-- Measurability of the sequential composite, from measurability of
the stages: the intermediate outcome space is finite, so the fibre
decomposition is a finite union of measurable rectangles. -/
theorem measurable_seqComp {g : (Fin N₁ → ℝ) → V} {k : V → (Fin N₂ → ℝ) → W}
    (hg : Measurable g) (hk : ∀ v, Measurable (k v)) :
    Measurable (seqComp g k) := by
  refine measurable_to_countable' fun w => ?_
  rw [seqComp_preimage_singleton]
  exact MeasurableSet.iUnion fun v =>
    (measurable_frontPorts (hg (measurableSet_singleton v))).inter
      (measurable_backPorts ((hk v) (measurableSet_singleton w)))

/-- **Kleisli functoriality of the noise-port semantics**: with
disjoint noise rosters, the denotation of the sequential composite is
the Kleisli composite of the denotations.  Independence of the port
blocks (`noiseCube_split`) is exactly what makes the mixture weights
multiply; the disjointness hypothesis is carried by the roster
arithmetic in the composite's type, and it is content, not bookkeeping
(`copy_ne_kleisli` below). -/
theorem noiseDenot_seqComp (g : (Fin N₁ → ℝ) → V) (k : V → (Fin N₂ → ℝ) → W)
    (hg : Measurable g) (hk : ∀ v, Measurable (k v)) :
    noiseDenot (seqComp g k) (measurable_seqComp hg hk)
      = (noiseDenot g hg).bind fun v => noiseDenot (k v) (hk v) := by
  classical
  refine Subtype.ext (funext fun w => ?_)
  show (noiseCube (N₁ + N₂) (seqComp g k ⁻¹' {w})).toReal
    = ∑ v, noiseDenotFun g v * noiseDenotFun (k v) w
  have hdisj : Pairwise (Function.onFun Disjoint fun v : V =>
      frontPorts N₁ N₂ ⁻¹' (g ⁻¹' {v})
        ∩ backPorts N₁ N₂ ⁻¹' (k v ⁻¹' {w})) := by
    intro v v' hvv'
    refine Set.disjoint_left.mpr fun u hu hu' => hvv' ?_
    have h1 : g (frontPorts N₁ N₂ u) = v := hu.1
    have h2 : g (frontPorts N₁ N₂ u) = v' := hu'.1
    rw [← h1, h2]
  have hmeas : ∀ v : V, MeasurableSet
      (frontPorts N₁ N₂ ⁻¹' (g ⁻¹' {v})
        ∩ backPorts N₁ N₂ ⁻¹' (k v ⁻¹' {w})) := fun v =>
    (measurable_frontPorts (hg (measurableSet_singleton v))).inter
      (measurable_backPorts ((hk v) (measurableSet_singleton w)))
  have hmeasure : noiseCube (N₁ + N₂) (seqComp g k ⁻¹' {w})
      = ∑ v, noiseCube N₁ (g ⁻¹' {v}) * noiseCube N₂ (k v ⁻¹' {w}) := by
    rw [seqComp_preimage_singleton g k w, measure_iUnion hdisj hmeas,
      tsum_fintype]
    exact Finset.sum_congr rfl fun v _ =>
      noiseCube_split N₁ N₂ (hg (measurableSet_singleton v))
        ((hk v) (measurableSet_singleton w))
  rw [hmeasure, ENNReal.toReal_sum fun v _ =>
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
  simp_rw [ENNReal.toReal_mul]
  rfl

/-- The functoriality law against a jointly measurable second stage:
sections of a jointly measurable map are measurable, so the curried
form applies. -/
theorem noiseDenot_seqComp_uncurried (g : (Fin N₁ → ℝ) → V)
    (k : V × (Fin N₂ → ℝ) → W) (hg : Measurable g) (hk : Measurable k) :
    noiseDenot (seqComp g fun v x => k (v, x))
        (measurable_seqComp hg fun _ => hk.comp measurable_prodMk_left)
      = (noiseDenot g hg).bind
          fun v => noiseDenot (fun x => k (v, x))
            (hk.comp measurable_prodMk_left) :=
  noiseDenot_seqComp g (fun v x => k (v, x)) hg
    fun _ => hk.comp measurable_prodMk_left

/-! ## Disjointness is content: the shared-roster failure

With disjoint rosters the law above holds; with a shared roster it
fails.  The two stages below compose on disjoint rosters to the fresh
pair and on a shared roster to the copy pair — and the landed
copy-vs-resample separation (`copy_ne_fresh`) says those denote
differently.  The Kleisli composite of the stage denotations always
resamples, so it can only ever be the fresh side. -/

/-- First stage: one fair bit of a one-port cube. -/
noncomputable def bitStage : (Fin 1 → ℝ) → Bool := fun u => bit (u 0)

/-- Second stage: carry the intermediate outcome, draw one more bit. -/
noncomputable def pairStage (v : Bool) : (Fin 1 → ℝ) → Bool × Bool :=
  fun u => (v, bit (u 0))

theorem measurable_bitStage : Measurable bitStage :=
  measurable_bitProj 0

theorem measurable_pairStage (v : Bool) : Measurable (pairStage v) :=
  measurable_const.prodMk (measurable_bitProj 0)

/-- On disjoint rosters the two stages compose to the fresh pair. -/
theorem seqComp_bitStage_pairStage :
    seqComp bitStage pairStage = freshPair := by
  funext u
  have h₀ : Fin.castAdd 1 (0 : Fin 1) = (0 : Fin (1 + 1)) := by decide
  have h₁ : Fin.natAdd 1 (0 : Fin 1) = (1 : Fin (1 + 1)) := by decide
  show (bit (u (Fin.castAdd 1 (0 : Fin 1))),
        bit (u (Fin.natAdd 1 (0 : Fin 1))))
    = (bit (u 0), bit (u 1))
  rw [h₀, h₁]

/-- On a shared roster — both stages reading port `0` of the same
one-port cube — the composite is the copy pair, definitionally. -/
theorem shared_eq_copyPair :
    (fun u : Fin 1 → ℝ => pairStage (bitStage u) u) = copyPair := rfl

/-- The Kleisli composite of the stage denotations is the fresh-pair
denotation: `bind` resamples.  (An instance of the functoriality law,
read right-to-left.) -/
theorem kleisli_eq_fresh :
    (noiseDenot bitStage measurable_bitStage).bind
        (fun v => noiseDenot (pairStage v) (measurable_pairStage v))
      = noiseDenot freshPair measurable_freshPair := by
  refine Eq.trans (noiseDenot_seqComp bitStage pairStage measurable_bitStage
    measurable_pairStage).symm ?_
  exact noiseDenot_congr seqComp_bitStage_pairStage _ _

/-- **With a shared roster the Kleisli law fails**: the shared-roster
composite of the two stages is the copy pair (`shared_eq_copyPair`),
the Kleisli composite of their denotations is the fresh-pair denotation
(`kleisli_eq_fresh`), and copy is not resampling (`copy_ne_fresh`).
The disjointness hypothesis of `noiseDenot_seqComp` is load-bearing. -/
theorem copy_ne_kleisli :
    noiseDenot copyPair measurable_copyPair
      ≠ (noiseDenot bitStage measurable_bitStage).bind
          (fun v => noiseDenot (pairStage v) (measurable_pairStage v)) := by
  rw [kleisli_eq_fresh]
  exact copy_ne_fresh

end SuFunctor.Stochastic

#print axioms SuFunctor.Universe.ProbState.bind
#print axioms SuFunctor.Universe.ProbState.dirac_bind
#print axioms SuFunctor.Universe.ProbState.bind_dirac
#print axioms SuFunctor.Universe.ProbState.bind_assoc
#print axioms SuFunctor.Universe.ProbState.push_eq_bind_dirac
#print axioms SuFunctor.Stochastic.noiseCube_split
#print axioms SuFunctor.Stochastic.noiseDenot_seqComp
#print axioms SuFunctor.Stochastic.noiseDenot_seqComp_uncurried
#print axioms SuFunctor.Stochastic.kleisli_eq_fresh
#print axioms SuFunctor.Stochastic.copy_ne_kleisli
