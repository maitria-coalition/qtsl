import QtslAux.QtslCompose.AGComposeMarks
import QtslAux.QtslCompose.AGComposeMarksTier
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # QWireComposeMarks — the STOCHASTIC instance of the soundness metatheorem
(discrete-token species, Ionescu–Tulcea assembly)

**Source spec**: the cyclic AG design's stochastic construction — the joint
law is assembled by Ionescu–Tulcea / Kolmogorov extension along the wiring's
stagewise dependency structure, so the joint distribution the design calls
for appears here, in the proof, at full measure-theoretic size. Statements
preregistered — committed before these proofs.

The species is **discrete-token** (`V` countable, measurable singletons):
per the r5 findings' own species table, atoms are honest here — a value pin
is not measure-zero on a countable carrier. The general-carrier species
(event/carve pins with positive conditional mass — exactly the measure-zero
concern that motivated the r5 carve generalization) is the r5 carve dial's
stochastic face and is deliberately NOT built here: it belongs to the
per-profile bridge of the carve engine.

## The model

`SMarkNet`: components are **Markov conditional laws** `κ i : (Fin n → V) →
PMF V` reading one wire snapshot at lag `lag i` (memoryless, like the
relational tier), plus initial-segment laws `ι i`. Its **support net**
(`SMarkNet.supportNet`) is the relational `MarkNet` with `F i w = (κ i w).support`
— the bridge through which the relational engine constructs the
skeleton run that the assembled law then charges with positive mass.

## The assembly (the joint law lives here and only here)

- `componentDraw` / `levelDraw` / `stageDraw`: the within-stage sequential
  composition — components drawn in an instant-topological order (an
  injective `ord` decreasing along instant dep edges; lagged components read
  earlier stages), one `PMF.bind` per order level. This is the finite tower
  of the Ionescu–Tulcea construction, within one stage.
- `stageKernel` / `pathLaw`: the stage draws packaged as history-fed kernels
  and extended to the infinite path law by mathlib's Ionescu–Tulcea
  trajectory kernel (`ProbabilityTheory.Kernel.traj`), with the stage-0 draw
  bound in front. **Nothing law-sized or behaviour-sized appears among any
  theorem's hypotheses** — the law is constructed under the conclusion's
  binder, exactly the confinement the r3 design demands.

## The headline

`smarks_of_conditional_delivery_pos`: on a walk-feasible, instant-acyclic
`SMarkNet` whose every component satisfies the **stochastic ∀∃ premise**
(`SCondDelivery`: through every mark-conforming input snapshot, the
component's law hits its own mark with positive probability), the assembled
path law assigns **positive probability** to "every mark realized at its
label". Positive, not a.s. — the honest modality for the ∃-face (a fair
coin delivers its mark with mass 1/2; `stageDraw_not_ae` is the battery
tooth pinning the modality).

Proof shape: the relational engine on the support net produces a skeleton
run realizing every mark (`marks_of_conditional_delivery_acyclic`, through a
lex order built from the walk labels + the instant order — walk-feasibility
makes every dep edge label-increasing or label-equal-and-instant); the
assembled law charges the skeleton's finite prefix cylinder with a positive
product of per-component masses (`levelDraw` positivity, stage by stage,
`partialTraj` step by step); the marks event contains the cylinder.

Scope fences, honest and loud: instant CYCLES are excluded at this tier
(the stochastic joint conditional around an instant cycle is a
conditional-specification problem — the r5 diagonal species dgContract/
dgConvex are its designed road); the demonic/selection reading of pinned
cycles at this tier is the cheap corollary `smarks_of_pinned_delivery_dirac`
(the Dirac law at the relational engine's run is selection-admitted —
supports only — and realizes marks a.s.).

Everything here is classical measure/probability theory, naturally
noncomputable; nothing is checker-facing (cf. `lean-conventions.md`).
-/

open scoped ENNReal

open MeasureTheory ProbabilityTheory Finset

namespace BernsteinLogic.QtslCompose.Marks

-- the traj/partialTraj plumbing manipulates large kernel terms; the default
-- heartbeat budget is exceeded at whnf during unification (measured r3)
set_option maxHeartbeats 4000000

variable {n : ℕ} {V : Type*}

/-- A stochastic mark network: per-component Markov conditional laws over a
wire snapshot read at the component's lag, plus initial-segment laws. -/
structure SMarkNet (n : ℕ) (V : Type*) where
  /-- in-neighbours -/
  dep : Fin n → Finset (Fin n)
  /-- delivery lag (0 = instantaneous) -/
  lag : Fin n → ℕ
  /-- the conditional law, given the lagged snapshot -/
  κ : Fin n → (Fin n → V) → PMF V
  /-- the initial-segment law (stages `k < lag i`) -/
  ι : Fin n → PMF V

namespace SMarkNet

/-- The relational support net: admitted values = support of the law. -/
def supportNet (M : SMarkNet n V) : MarkNet n V where
  dep := M.dep
  lag := M.lag
  F := fun i w => (M.κ i w).support
  init := fun i => (M.ι i).support

/-- Stochastic dep-locality: the conditional law reads only the `dep i`
coordinates of its snapshot. -/
def SDepLocal (M : SMarkNet n V) : Prop :=
  ∀ i (w w' : Fin n → V), (∀ j ∈ M.dep i, w j = w' j) → M.κ i w = M.κ i w'

/-- The stochastic ∀∃ premise (conditional delivery, positive-mass form):
through every mark-conforming input snapshot, the component's law hits its
own mark. -/
def SCondDelivery (M : SMarkNet n V) (mark : Fin n → Set V) (i : Fin n) : Prop :=
  ∀ w : Fin n → V, (∀ j ∈ M.dep i, w j ∈ mark j) →
    ∃ v ∈ mark i, M.κ i w v ≠ 0

/-- Instant-topological order: `ord` strictly decreasing along the dep edges
of instantaneous components (lagged components read history — no
constraint). -/
def InstantAcyclic (M : SMarkNet n V) (ord : Fin n → ℕ) : Prop :=
  ∀ i, M.lag i = 0 → ∀ j ∈ M.dep i, ord j < ord i

/-- The support net is serial for free: PMF supports are nonempty. -/
theorem supportNet_serial (M : SMarkNet n V) : Serial M.supportNet :=
  ⟨fun i => (M.ι i).support_nonempty, fun i w => (M.κ i w).support_nonempty⟩

/-- Stochastic dep-locality transfers to the support net. -/
theorem supportNet_depLocal {M : SMarkNet n V} (h : SDepLocal M) :
    DepLocal M.supportNet := fun i w w' hw => by
  show (M.κ i w).support = (M.κ i w').support
  rw [h i w w' hw]

/-- The stochastic premise IS the relational premise of the support net. -/
theorem sCondDelivery_iff_support (M : SMarkNet n V) (mark : Fin n → Set V)
    (i : Fin n) :
    SCondDelivery M mark i ↔ ConditionalDelivery M.supportNet mark i := by
  unfold SCondDelivery ConditionalDelivery
  refine forall₂_congr fun w _ => ?_
  refine exists_congr fun v => ?_
  rw [and_comm (a := v ∈ mark i)]
  simp [supportNet, PMF.mem_support_iff]

end SMarkNet

section Assembly

variable [Nonempty V]

open SMarkNet Classical

/-- One component's stage-`k` draw: initial law before the pipe fills, the
conditional law at the lagged snapshot after (instantaneous components read
the current partial vector `cur`). -/
noncomputable def componentDraw (M : SMarkNet n V) (k : ℕ)
    (hist : ℕ → Fin n → V) (cur : Fin n → V) (i : Fin n) : PMF V :=
  if k < M.lag i then M.ι i
  else if M.lag i = 0 then M.κ i cur
  else M.κ i (hist (k - M.lag i))

/-- The within-stage sequential composition, by order level: at level `m`,
the (unique, by injectivity of `ord` in the theorems) component with
`ord i = m` is drawn against the partial vector, and its coordinate updated.
Coordinates not yet drawn carry an arbitrary default that dep-locality keeps
unread. -/
noncomputable def levelDraw (M : SMarkNet n V) (ord : Fin n → ℕ) (k : ℕ)
    (hist : ℕ → Fin n → V) : ℕ → PMF (Fin n → V)
  | 0 => PMF.pure (Classical.arbitrary (Fin n → V))
  | m + 1 => (levelDraw M ord k hist m).bind fun prev =>
      if h : ∃ i, ord i = m then
        (componentDraw M k hist prev h.choose).map
          (fun v => Function.update prev h.choose v)
      else PMF.pure prev

/-- The full stage-`k` joint draw. -/
noncomputable def stageDraw (M : SMarkNet n V) (ord : Fin n → ℕ) (k : ℕ)
    (hist : ℕ → Fin n → V) : PMF (Fin n → V) :=
  levelDraw M ord k hist (Finset.univ.sup ord + 1)

/-- The partial target vector at level `m`: the target on drawn coordinates,
the default elsewhere. -/
noncomputable def mixTo (ord : Fin n → ℕ) (w : Fin n → V) (m : ℕ) :
    Fin n → V :=
  fun i => if ord i < m then w i else Classical.arbitrary (Fin n → V) i

theorem mixTo_zero (ord : Fin n → ℕ) (w : Fin n → V) :
    mixTo ord w 0 = Classical.arbitrary (Fin n → V) := by
  funext i
  simp [mixTo]

theorem mixTo_top (ord : Fin n → ℕ) (w : Fin n → V) :
    mixTo ord w (Finset.univ.sup ord + 1) = w := by
  funext i
  exact if_pos (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i)))

/-- **Level positivity**: if at each level the target's coordinate is
delivered with positive mass against the partial target vector, the level
draw charges the partial target with positive mass. The tower of the
Ionescu–Tulcea construction, within one stage. -/
theorem levelDraw_mix_ne_zero (M : SMarkNet n V) {ord : Fin n → ℕ}
    (hinj : Function.Injective ord) (k : ℕ) (hist : ℕ → Fin n → V)
    (w : Fin n → V)
    (hpos : ∀ i, componentDraw M k hist (mixTo ord w (ord i)) i (w i) ≠ 0) :
    ∀ m, levelDraw M ord k hist m (mixTo ord w m) ≠ 0 := by
  intro m
  induction m with
  | zero =>
    rw [mixTo_zero, levelDraw]
    simp [PMF.pure_apply]
  | succ m ih =>
    rw [levelDraw]
    rw [PMF.bind_apply]
    -- a zero tsum zeroes every summand; the level-m partial target's refuses
    intro hz
    have hterm := (ENNReal.tsum_eq_zero.mp hz) (mixTo ord w m)
    rcases mul_eq_zero.1 hterm with h0 | h0
    · exact ih h0
    · by_cases h : ∃ i, ord i = m
      · rw [dif_pos h] at h0
        have hchoose : ord h.choose = m := h.choose_spec
        -- the updated partial target IS the next partial target
        have hupd : Function.update (mixTo ord w m) h.choose (w h.choose)
            = mixTo ord w (m + 1) := by
          funext j
          by_cases hj : j = h.choose
          · subst hj
            rw [Function.update_self]
            exact (if_pos (by omega)).symm
          · rw [Function.update_of_ne hj]
            show mixTo ord w m j = mixTo ord w (m + 1) j
            unfold mixTo
            have hjm : ord j ≠ m := fun hc =>
              hj (hinj (hc.trans hchoose.symm))
            by_cases hlt : ord j < m
            · rw [if_pos hlt, if_pos (by omega)]
            · rw [if_neg hlt, if_neg (by omega)]
        rw [PMF.map_apply] at h0
        have hterm' := (ENNReal.tsum_eq_zero.mp h0) (w h.choose)
        rw [if_pos hupd.symm] at hterm'
        have hp := hpos h.choose
        rw [hchoose] at hp
        exact hp hterm'
      · rw [dif_neg h] at h0
        push_neg at h
        have hmix : mixTo ord w (m + 1) = mixTo ord w m := by
          funext j
          unfold mixTo
          have : ord j ≠ m := h j
          by_cases hlt : ord j < m
          · rw [if_pos hlt, if_pos (by omega)]
          · rw [if_neg hlt, if_neg (by omega)]
        rw [hmix, PMF.pure_apply, if_pos rfl] at h0
        exact one_ne_zero h0

/-- **Stage positivity**, packaged at the stage draw. -/
theorem stageDraw_ne_zero (M : SMarkNet n V) {ord : Fin n → ℕ}
    (hinj : Function.Injective ord) (k : ℕ) (hist : ℕ → Fin n → V)
    (w : Fin n → V)
    (hpos : ∀ i, componentDraw M k hist (mixTo ord w (ord i)) i (w i) ≠ 0) :
    stageDraw M ord k hist w ≠ 0 := by
  have := levelDraw_mix_ne_zero M hinj k hist w hpos (Finset.univ.sup ord + 1)
  rwa [mixTo_top] at this

end Assembly

section PathLaw

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
  [Nonempty V]

open SMarkNet

/-- The stage kernels, history-fed (the Ionescu–Tulcea family): the kernel at
time `k` draws stage `k + 1` reading the trajectory so far. -/
noncomputable def stageKernel (M : SMarkNet n V) (ord : Fin n → ℕ) (k : ℕ) :
    Kernel (Π _i : Iic k, (Fin n → V)) (Fin n → V) :=
  { toFun := fun h => (stageDraw M ord (k + 1)
      (fun m => if hm : m ≤ k then h ⟨m, mem_Iic.2 hm⟩
        else Classical.arbitrary (Fin n → V))).toMeasure
    measurable' := measurable_of_countable _ }

instance (M : SMarkNet n V) (ord : Fin n → ℕ) (k : ℕ) :
    IsMarkovKernel (stageKernel M ord k) :=
  ⟨fun _ => by
    show IsProbabilityMeasure (PMF.toMeasure _)
    infer_instance⟩

/-- **The assembled path law** — stage 0 drawn in front, stages `k + 1` by
the Ionescu–Tulcea trajectory kernel over the stage family. The joint law of
the composite, constructed; it appears in no hypothesis anywhere in this
module. -/
noncomputable def pathLaw (M : SMarkNet n V) (ord : Fin n → ℕ) :
    Measure (ℕ → Fin n → V) :=
  ((stageDraw M ord 0 (fun _ => Classical.arbitrary (Fin n → V))).toMeasure).bind
    (fun v => Kernel.traj (X := fun _ : ℕ => (Fin n → V))
      (κ := stageKernel M ord) 0 (fun _ => v))

/-- The `Iic`-prefix of a path, as a point of the finite marginal space. -/
noncomputable def prefixOf (w : ℕ → Fin n → V) (T : ℕ) :
    Π _i : Iic T, (Fin n → V) :=
  fun i => w i

/-- **The one-step prefix mass is the stage kernel's**: the `b → b + 1`
partial-trajectory kernel charges the extended prefix at least as much as
the stage kernel charges the next stage value (all monotonicity: the glued
pair sits in the preimage of the extended prefix). -/
theorem partialTraj_succ_prefix_ne_zero (M : SMarkNet n V) (ord : Fin n → ℕ)
    (w : ℕ → Fin n → V) (b : ℕ)
    (hstep : stageKernel M ord b (prefixOf w b) {w (b + 1)} ≠ 0) :
    Kernel.partialTraj (X := fun _ : ℕ => (Fin n → V))
      (stageKernel M ord) b (b + 1) (prefixOf w b) {prefixOf w (b + 1)} ≠ 0 := by
  set piS : (Fin n → V) ≃ᵐ Π _i : Ioc b (b + 1), (Fin n → V) :=
    MeasurableEquiv.piSingleton (X := fun _ : ℕ => (Fin n → V)) b with hpiSdef
  haveI : IsMarkovKernel ((stageKernel M ord b).map ⇑piS) :=
    Kernel.IsMarkovKernel.map _ piS.measurable
  have hmeasIic : Measurable
      (IicProdIoc (X := fun _ : ℕ => (Fin n → V)) b (b + 1)) := by
    rw [← MeasurableEquiv.coe_IicProdIoc (Nat.le_succ b)]
    exact (MeasurableEquiv.IicProdIoc (Nat.le_succ b)).measurable
  rw [Kernel.partialTraj_succ_self,
    Kernel.map_apply' _ hmeasIic _ (measurableSet_singleton _)]
  -- the glued pair (b-prefix, next value) lands on the (b+1)-prefix …
  have hglue : IicProdIoc (X := fun _ : ℕ => (Fin n → V)) b (b + 1)
      (prefixOf w b, piS (w (b + 1)))
      = prefixOf w (b + 1) := by
    funext i
    show (if h : i.1 ≤ b then _ else _) = _
    by_cases h : i.1 ≤ b
    · rw [dif_pos h]
      rfl
    · rw [dif_neg h]
      have hi : i.1 = b + 1 := by
        have := mem_Iic.1 i.2
        omega
      show piS (w (b + 1)) ⟨i.1, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩
        = prefixOf w (b + 1) i
      have hred : piS (w (b + 1)) ⟨i.1, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩
          = w (b + 1) := by
        simp [hpiSdef, MeasurableEquiv.piSingleton, eq_rec_constant]
      rw [hred]
      show w (b + 1) = w i.1
      rw [hi]
  -- … so the preimage's mass dominates the pair singleton's, which factors.
  have hsub : ({prefixOf w b} ×ˢ ({piS (w (b + 1))} : Set _))
      ⊆ IicProdIoc (X := fun _ : ℕ => (Fin n → V)) b (b + 1) ⁻¹'
        {prefixOf w (b + 1)} := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have hu' : u = prefixOf w b := hu
    have hv' : v = piS (w (b + 1)) := hv
    subst hu'
    subst hv'
    exact hglue
  have hpair : (Kernel.id ×ₖ ((stageKernel M ord b).map piS))
      (prefixOf w b)
      ({prefixOf w b} ×ˢ ({piS (w (b + 1))} : Set _)) ≠ 0 := by
    rw [Kernel.prod_apply, Measure.prod_prod, Kernel.id_apply,
      Measure.dirac_apply_of_mem (Set.mem_singleton _), one_mul,
      Kernel.map_apply' _ piS.measurable _ (measurableSet_singleton _)]
    intro hz
    have hle : stageKernel M ord b (prefixOf w b) {w (b + 1)}
        ≤ stageKernel M ord b (prefixOf w b) (⇑piS ⁻¹' {piS (w (b + 1))}) := by
      refine measure_mono ?_
      rintro x hx
      rw [Set.mem_singleton_iff.1 hx]
      exact rfl
    rw [hz] at hle
    exact hstep (le_antisymm hle zero_le)
  intro hz
  have hle := measure_mono
    (μ := (Kernel.id ×ₖ ((stageKernel M ord b).map piS)) (prefixOf w b)) hsub
  rw [hz] at hle
  exact hpair (le_antisymm hle zero_le)

/-- **partialTraj charges a target prefix positively** when every stage
kernel charges the target's next stage positively along it — the finite
Ionescu–Tulcea tower, walked one composition at a time. -/
theorem partialTraj_prefix_ne_zero (M : SMarkNet n V) (ord : Fin n → ℕ)
    (w : ℕ → Fin n → V)
    (hstep : ∀ b, stageKernel M ord b (prefixOf w b) {w (b + 1)} ≠ 0) :
    ∀ T, Kernel.partialTraj (X := fun _ : ℕ => (Fin n → V))
      (stageKernel M ord) 0 T (prefixOf w 0) {prefixOf w T} ≠ 0 := by
  intro T
  induction T with
  | zero =>
    rw [Kernel.partialTraj_self, Kernel.id_apply]
    simp
  | succ b ih =>
    rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le b),
      Kernel.comp_apply' _ _ _ (measurableSet_singleton _)]
    intro hz
    have hle : Kernel.partialTraj (X := fun _ : ℕ => (Fin n → V))
        (stageKernel M ord) b (b + 1) (prefixOf w b) {prefixOf w (b + 1)}
        * Kernel.partialTraj (X := fun _ : ℕ => (Fin n → V))
          (stageKernel M ord) 0 b (prefixOf w 0) {prefixOf w b}
        ≤ ∫⁻ y, Kernel.partialTraj (X := fun _ : ℕ => (Fin n → V))
            (stageKernel M ord) b (b + 1) y {prefixOf w (b + 1)}
          ∂(Kernel.partialTraj (X := fun _ : ℕ => (Fin n → V))
            (stageKernel M ord) 0 b (prefixOf w 0)) := by
      calc _ = ∫⁻ y in {prefixOf w b},
            Kernel.partialTraj (X := fun _ : ℕ => (Fin n → V))
              (stageKernel M ord) b (b + 1) y {prefixOf w (b + 1)}
            ∂(Kernel.partialTraj (X := fun _ : ℕ => (Fin n → V))
              (stageKernel M ord) 0 b (prefixOf w 0)) :=
            (lintegral_singleton _ _).symm
        _ ≤ _ := setLIntegral_le_lintegral _ _
    rw [hz] at hle
    rcases mul_eq_zero.1 (le_antisymm hle zero_le) with h0 | h0
    · exact partialTraj_succ_prefix_ne_zero M ord w b (hstep b) h0
    · exact ih h0

/-- **The trajectory law charges the target's finite cylinder positively.** -/
theorem traj_cylinder_ne_zero (M : SMarkNet n V) (ord : Fin n → ℕ)
    (w : ℕ → Fin n → V) (T : ℕ)
    (hstep : ∀ b, stageKernel M ord b (prefixOf w b) {w (b + 1)} ≠ 0) :
    Kernel.traj (X := fun _ : ℕ => (Fin n → V)) (stageKernel M ord) 0
      (prefixOf w 0) (Preorder.frestrictLe T ⁻¹' {prefixOf w T}) ≠ 0 := by
  intro hz
  have h1 : (Kernel.traj (X := fun _ : ℕ => (Fin n → V)) (stageKernel M ord) 0
        (prefixOf w 0)).map (Preorder.frestrictLe T) {prefixOf w T} = 0 := by
    rw [Measure.map_apply (Preorder.measurable_frestrictLe T)
      (measurableSet_singleton _)]
    exact hz
  rw [Kernel.traj_map_frestrictLe_apply] at h1
  exact partialTraj_prefix_ne_zero M ord w hstep T h1

/-- **The measure-side assembly, isolated over an abstract event**: a target
path with positive stage-0 mass and positive stage-kernel steps charges any
measurable superset of its `T`-cylinder positively under the assembled path
law (bind ≥ singleton-restricted lintegral ≥ product of positives). -/
theorem pathLaw_ne_zero_of_prefix (M : SMarkNet n V) (ord : Fin n → ℕ)
    (w : ℕ → Fin n → V) (T : ℕ) {E : Set (ℕ → Fin n → V)}
    (hE : MeasurableSet E)
    (hcyl : (Preorder.frestrictLe T ⁻¹' {prefixOf w T} : Set (ℕ → Fin n → V)) ⊆ E)
    (hstage0 : stageDraw M ord 0
      (fun _ => Classical.arbitrary (Fin n → V)) (w 0) ≠ 0)
    (hstep : ∀ b, stageKernel M ord b (prefixOf w b) {w (b + 1)} ≠ 0) :
    pathLaw M ord E ≠ 0 := by
  unfold pathLaw
  -- the domain is countable-discrete: EVERY function out of it is measurable,
  -- which dodges the traj-term defeq entirely (the r5-round isDefEq timeout)
  have hker : Measurable fun v : Fin n → V =>
      Kernel.traj (X := fun _ : ℕ => (Fin n → V)) (κ := stageKernel M ord) 0
        (fun _ => v) := measurable_of_countable _
  rw [Measure.bind_apply hE hker.aemeasurable]
  intro hz
  have hle : Kernel.traj (X := fun _ : ℕ => (Fin n → V)) (stageKernel M ord) 0
      (fun _ => w 0) E
      * (stageDraw M ord 0 (fun _ => Classical.arbitrary (Fin n → V))).toMeasure
        {w 0}
      ≤ ∫⁻ v, Kernel.traj (X := fun _ : ℕ => (Fin n → V)) (stageKernel M ord) 0
          (fun _ => v) E
        ∂(stageDraw M ord 0
          (fun _ => Classical.arbitrary (Fin n → V))).toMeasure := by
    calc _ = ∫⁻ v in {w 0},
          Kernel.traj (X := fun _ : ℕ => (Fin n → V)) (stageKernel M ord) 0
            (fun _ => v) E
          ∂(stageDraw M ord 0
            (fun _ => Classical.arbitrary (Fin n → V))).toMeasure :=
          (lintegral_singleton _ _).symm
      _ ≤ _ := setLIntegral_le_lintegral _ _
  rw [hz] at hle
  rcases mul_eq_zero.1 (le_antisymm hle zero_le) with h0 | h0
  · have hstart : (fun _ : Iic 0 => w 0) = prefixOf w 0 := by
      funext i
      exact (congrArg w (Nat.le_zero.1 (mem_Iic.1 i.2))).symm
    rw [hstart] at h0
    have hmono := measure_mono
      (μ := Kernel.traj (X := fun _ : ℕ => (Fin n → V)) (stageKernel M ord) 0
        (prefixOf w 0)) hcyl
    exact traj_cylinder_ne_zero M ord w T hstep
      (le_antisymm (h0 ▸ hmono) zero_le)
  · rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at h0
    exact hstage0 h0

end PathLaw

section Headline

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
  [Nonempty V]

open SMarkNet Classical

/-- The lex order that walk-feasibility + instant-acyclicity provide: labels
first, instant order within a label. Every dep edge decreases it (a lagged
edge decreases the label; an instant edge keeps it and decreases `ord`). -/
theorem exists_full_order (M : SMarkNet n V) {t : Fin n → ℕ}
    {ord : Fin n → ℕ} (hia : InstantAcyclic M ord)
    (hfeas : MarkFlowFeasible M.supportNet t) :
    ∃ ordF : Fin n → ℕ, ∀ i, ∀ j ∈ M.dep i, ordF j < ordF i := by
  classical
  set B := Finset.univ.sup ord + 1 with hB
  refine ⟨fun i => t i * B + ord i, fun i j hj => ?_⟩
  have hrow := hfeas.2 i j hj
  have hjB : ord j < B := by
    have := Finset.le_sup (f := ord) (Finset.mem_univ j)
    omega
  by_cases h0 : M.supportNet.lag i = 0
  · have hlab : t i = t j := by
      rw [hrow, h0, Nat.add_zero]
    have hoo : ord j < ord i := hia i h0 j hj
    have : t j * B + ord j < t i * B + ord i := by
      rw [hlab]
      omega
    exact this
  · have hlab : t j < t i := by omega
    have : t j * B + ord j < t i * B + ord i := by
      have h1 : t j * B + ord j < (t j + 1) * B := by
        have : (t j + 1) * B = t j * B + B := by ring
        omega
      have h2 : (t j + 1) * B ≤ t i * B := by
        exact mul_le_mul_right' hlab B
      omega
    exact this

/-- **THE STOCHASTIC INSTANCE of the soundness metatheorem** (discrete-token
species; the design's stochastic tier, machine-checked): on a
walk-feasible, instant-acyclic stochastic mark network whose every component
satisfies the stochastic ∀∃ conditional-delivery premise, the ASSEMBLED
composite path law — Ionescu–Tulcea over the stage kernels, stage 0 bound in
front — assigns POSITIVE probability to "every mark realized at its label".
The joint law appears only under this conclusion's binder; no hypothesis is
behaviour- or law-sized. -/
theorem smarks_of_conditional_delivery_pos (M : SMarkNet n V)
    (mark : Fin n → Set V) (t : Fin n → ℕ) (ord : Fin n → ℕ)
    (hinj : Function.Injective ord) (hia : InstantAcyclic M ord)
    (hloc : SDepLocal M) (hfeas : MarkFlowFeasible M.supportNet t)
    (hdel : ∀ i, SCondDelivery M mark i) :
    pathLaw M ord {ω : ℕ → Fin n → V | ∀ i, ω (t i) i ∈ mark i} ≠ 0 := by
  classical
  -- the relational skeleton: a support-net run realizing every mark
  obtain ⟨ordF, hordF⟩ := exists_full_order M hia hfeas
  obtain ⟨w, hrun, hmarks⟩ := marks_of_conditional_delivery_acyclic
    (M.supportNet_serial) (supportNet_depLocal hloc) ordF hordF hfeas
    (fun i => (sCondDelivery_iff_support M mark i).1 (hdel i))
  -- per-stage positivity of the assembled draws along the skeleton
  have hcomp : ∀ k (hist : ℕ → Fin n → V),
      (∀ m, m < k → hist m = w m) → ∀ i,
      componentDraw M k hist (mixTo ord (w k) (ord i)) i (w k i) ≠ 0 := by
    intro k hist hhist i
    unfold componentDraw
    by_cases hk : k < M.lag i
    · rw [if_pos hk]
      exact (PMF.mem_support_iff _ _).1 ((hrun k i).2 hk)
    · rw [if_neg hk]
      by_cases h0 : M.lag i = 0
      · rw [if_pos h0]
        have hagree : ∀ j ∈ M.dep i, mixTo ord (w k) (ord i) j = w k j := by
          intro j hj
          unfold mixTo
          exact if_pos (hia i h0 j hj)
        rw [hloc i _ _ hagree]
        have h0' : M.supportNet.lag i = 0 := h0
        have hsupp := (hrun k i).1 (Nat.le_of_not_lt hk)
        rw [h0', Nat.sub_zero] at hsupp
        exact (PMF.mem_support_iff _ _).1 hsupp
      · rw [if_neg h0]
        have hlag : M.lag i ≤ k := Nat.le_of_not_lt hk
        have hlt : k - M.lag i < k :=
          Nat.sub_lt (by omega) (Nat.pos_of_ne_zero h0)
        rw [hhist _ hlt]
        exact (PMF.mem_support_iff _ _).1 ((hrun k i).1 hlag)
  -- stage-0 mass and the stage-kernel steps along the skeleton prefix
  have hstage0 : stageDraw M ord 0
      (fun _ => Classical.arbitrary (Fin n → V)) (w 0) ≠ 0 :=
    stageDraw_ne_zero M hinj 0 _ (w 0)
      (hcomp 0 _ (fun m hm => absurd hm (Nat.not_lt_zero m)))
  have hstep : ∀ b, stageKernel M ord b (prefixOf w b) {w (b + 1)} ≠ 0 := by
    intro b
    show (stageDraw M ord (b + 1) _).toMeasure {w (b + 1)} ≠ 0
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    refine stageDraw_ne_zero M hinj (b + 1) _ (w (b + 1)) ?_
    refine hcomp (b + 1) _ (fun m hm => ?_)
    rw [dif_pos (Nat.lt_succ_iff.1 hm)]
    rfl
  -- the marks event and its cylinder, then the abstract measure-side lemma
  have hE : MeasurableSet {ω : ℕ → Fin n → V | ∀ i, ω (t i) i ∈ mark i} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun i =>
      ((measurable_pi_apply i).comp (measurable_pi_apply (t i)))
        ((Set.to_countable (mark i)).measurableSet)
  have hcyl : (Preorder.frestrictLe (Finset.univ.sup t) ⁻¹'
        {prefixOf w (Finset.univ.sup t)} : Set (ℕ → Fin n → V))
      ⊆ {ω | ∀ i, ω (t i) i ∈ mark i} := by
    intro ω hω i
    have hpre : Preorder.frestrictLe (Finset.univ.sup t) ω
        = prefixOf w (Finset.univ.sup t) :=
      Set.mem_singleton_iff.1 hω
    have hcoord : ω (t i) = w (t i) := by
      have := congrFun hpre ⟨t i, mem_Iic.2 (Finset.le_sup (Finset.mem_univ i))⟩
      exact this
    rw [hcoord]
    exact hmarks i
  exact pathLaw_ne_zero_of_prefix M ord w (Finset.univ.sup t) hE hcyl
    hstage0 hstep

/-- **The selection corollary at the pinned cyclic tier** (the demonic
stochastic reading, named honestly): pins + walk + the support net's
closure data produce a run whose Dirac path law is selection-admitted
(every coordinate lies in its conditional law's support — the run IS a
support-net joint run) and realizes every mark almost surely. The genuinely
mixing cyclic species — local characteristics around an instant cycle — is
the conditional-specification problem; its designed road is the r5 carve
dial's diagonal species (dgContract/dgConvex), a named successor. -/
theorem smarks_of_pinned_delivery_dirac (M : SMarkNet n V)
    {mark : Fin n → Set V} {a : Fin n → V} {t : Fin n → ℕ}
    (hpin : PinnedDelivery M.supportNet mark a)
    (hfeas : MarkFlowFeasible M.supportNet t)
    (hclose : InstantClosure M.supportNet a t) :
    ∃ ω : ℕ → Fin n → V, JointRun M.supportNet ω ∧
      Measure.dirac ω {ω' : ℕ → Fin n → V | ∀ i, ω' (t i) i ∈ mark i} = 1 := by
  obtain ⟨ω, hrun, hmk⟩ :=
    marks_of_pinned_delivery (M.supportNet_serial) hfeas hpin hclose
  refine ⟨ω, hrun, ?_⟩
  have hE : MeasurableSet {ω' : ℕ → Fin n → V | ∀ i, ω' (t i) i ∈ mark i} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun i =>
      ((measurable_pi_apply i).comp (measurable_pi_apply (t i)))
        ((Set.to_countable (mark i)).measurableSet)
  rw [Measure.dirac_apply' _ hE]
  exact Set.indicator_of_mem
    (show ω ∈ {ω' : ℕ → Fin n → V | ∀ i, ω' (t i) i ∈ mark i} from hmk) 1

end Headline

end BernsteinLogic.QtslCompose.Marks

/-! ## Axiom receipts -/

#print axioms BernsteinLogic.QtslCompose.Marks.SMarkNet.sCondDelivery_iff_support
#print axioms BernsteinLogic.QtslCompose.Marks.levelDraw_mix_ne_zero
#print axioms BernsteinLogic.QtslCompose.Marks.stageDraw_ne_zero
#print axioms BernsteinLogic.QtslCompose.Marks.partialTraj_prefix_ne_zero
#print axioms BernsteinLogic.QtslCompose.Marks.traj_cylinder_ne_zero
#print axioms BernsteinLogic.QtslCompose.Marks.smarks_of_conditional_delivery_pos
#print axioms BernsteinLogic.QtslCompose.Marks.smarks_of_pinned_delivery_dirac
