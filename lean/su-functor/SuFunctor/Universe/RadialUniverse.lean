import SuFunctor.Adequacy.SemanticUniverseWiring
import SuFunctor.Adequacy.MarginalGlue
import SuFunctor.Universe.General.CredalPoset

/-! # The radial universe: membership by type, walls by down-closure

The semantic universe *is* the radial stock.  This module states the
promotion at both strata and proves the redesign's acceptance
properties.

**The general carrier** (`SuFunctor.Universe.General`): the universe
over a record space is the type of credal bodies — nonempty, closed,
radial subsets of the subprobability carrier — and the radial compile
of the penalty↔body dictionary (`Definition su-penalty-functional`) is
packaged as the *definitional isomorphism* `compileEquiv`: lower
semicontinuous penalty functionals on the probability carrier ≃ credal
bodies.  Consequences, each a few lines over the landed anchor:

* hard violation compiles to the bottom body `{0}`, a lawful member,
  never the empty set (`compile_top_eq_bot`, `RadialUniverse.bot`);
  the empty set fails membership by type (`not_isCredalBody_empty`);
* the singleton at any nonzero state — the pinning shape — fails
  membership by type, because a radial set owns the bottom state
  (`not_isRadial_singleton`); no penalty functional whatsoever
  compiles to it (`compile_ne_singleton`).

**The exact stratum** (`SuFunctor.Adequacy`): the seam-reading of
radiality is `RadialPen` — a penalty on joints is radial when it is
monotone non-increasing along admitted downward scalings of laws.  The
membership characterization (`radialPen_cwall_iff`): a constraint wall
is radial exactly when the constraint is down-closed.  Constraints
enter the universe through one door, the **radial wall** `rwall` — the
wall on the credal completion (down-closure) of the satisfaction set —
and laws enter as their down-cones, the **ray point** `rayPoint`.  The
door is one and the same: the radial wall of the precise
(singleton) constraint *is* the ray point (`rwall_singletonC`), while
the un-radialized wall of the same constraint is the pinning floor
(`cwall_singletonC`), which fails membership
(`not_radialPen_pinningFloor`) — the type-level exclusion that
replaces the fence `coupledSat_rayWall_singleton_floor_fails`: what
the fence refuted by counterexample, the membership predicate now
rules out of the ontology.  The fence and the slice corollaries stay
landed as the before-specimen; nothing here modifies them.

* **Universal properness**: every radial wall admits the bottom law
  (`rwall_toJoint_zero`), so no radial floor is the everywhere-`⊤`
  penalty (`rwall_ne_top`) and the bottom law's entry satisfies every
  radial wall atom (`coupledSat_rayPoint_zero_rwall`).  An equality
  construct that excluded the inconsistent world would not be a valid
  belief state; radial walls cannot express such an exclusion.
* **The judgment bridge, ray-shaped**
  (`coupledSat_rayPoint_rwall_iff` and its two corollaries): the
  ray-embedded law satisfies a constraint's radial wall atom exactly
  when the law satisfies the constraint — for arbitrary constraints
  at full-mass laws (a radial set contains a ray exactly when it
  contains its tip, and a full-mass tip matches only full-mass
  members), and for down-closed constraints at every mass.  The
  transport layer rides along (`rayPoint_mem_radialDnf_iff`).
* **The contradictory-equality composite**: over the two-bit carrier,
  the three almost-sure constraints `x = y`, `x = false`, `y = true`
  are individually and pairwise satisfiable, jointly contradictory —
  and their composed radial wall is exactly the bottom law's entry
  (`contradictory_composite_denotes_bot`), not the everywhere-`⊤`
  wall (`contradictory_composite_ne_top`).  Infeasibility denotes
  bottom, lawfully; contrast `exists_cwall_and_ne_inf`, where the
  same composition shape over pinning floors produced the wall on the
  empty set.

Boundary, stated rather than smoothed: `RadialPen` is the exact-seam
*reading* of `General.IsRadial` — no formal bridge between the two
strata is claimed here; the topological reading remains the envelope
stratum's successor, exactly as at the wiring module's close. -/

open scoped NNReal ENNReal

/-! ## Part I — the general carrier: universe := radial stock -/

namespace SuFunctor.Universe.General

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

open CredalPoset

/-- **The semantic universe over a record space, as a type**: the
radial stock — nonempty, closed, radial subsets of the subprobability
carrier.  Membership is `IsCredalBody`, and nothing else. -/
def RadialUniverse (X : Type*) [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] : Type _ :=
  {R : Set (SubProbabilityMeasure X) // IsCredalBody R}

/-- **The dictionary as the definition**: lower semicontinuous penalty
functionals on the probability carrier are *the same thing* as members
of the radial universe — the radial compile, packaged as an
equivalence.  Forward: `compile` (membership by `zero_mem_compile`,
`isClosed_compile`, `isRadial_compile`); backward: the gauge penalty
`rayPenalty`; the round trips are `rayPenalty_compile` and
`compile_rayPenalty`. -/
noncomputable def compileEquiv [Nonempty X] :
    {f : Penalty X // LowerSemicontinuous f} ≃ RadialUniverse X where
  toFun f := ⟨compile f.1,
    ⟨_, zero_mem_compile f.1⟩, isClosed_compile f.2, isRadial_compile f.1⟩
  invFun R := ⟨rayPenalty R.1,
    lowerSemicontinuous_rayPenalty R.2.2.1 R.2.2.2 R.2.1⟩
  left_inv f := Subtype.ext (rayPenalty_compile f.1)
  right_inv R := Subtype.ext (compile_rayPenalty R.2.2.1 R.2.2.2 R.2.1)

@[simp] theorem compileEquiv_coe [Nonempty X] (f : Penalty X)
    (hf : LowerSemicontinuous f) :
    (compileEquiv ⟨f, hf⟩ : RadialUniverse X).1 = compile f :=
  rfl

@[simp] theorem compileEquiv_symm_coe [Nonempty X] (R : RadialUniverse X) :
    (compileEquiv.symm R).1 = rayPenalty R.1 :=
  rfl

/-- **Hard violation compiles to the bottom body** `{0}` — a lawful
member of the universe, never the empty set.  (The finite-stratum
witness of the same law is `CredalPoset.compile_top_eq_bottom`.) -/
theorem compile_top_eq_bot [Nonempty X] :
    compile (⊤ : Penalty X) = ({0} : Set (SubProbabilityMeasure X)) := by
  ext ν
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨μ, γ, hγ, he⟩
    rw [Pi.top_apply, gradeN_top] at hγ
    have h0 : γ = 0 := le_zero_iff.mp hγ
    refine SubProbabilityMeasure.ext ?_
    rw [he, h0, zero_smul, SubProbabilityMeasure.coe_zero]
  · rintro rfl
    exact zero_mem_compile _

/-- The bottom member of the radial universe: the compile of hard
violation. -/
noncomputable def RadialUniverse.bot [Nonempty X] : RadialUniverse X :=
  compileEquiv ⟨⊤, lowerSemicontinuous_const⟩

@[simp] theorem RadialUniverse.coe_bot [Nonempty X] :
    (RadialUniverse.bot (X := X)).1 = ({0} : Set (SubProbabilityMeasure X)) :=
  compile_top_eq_bot

/-- The bottom body is closed — for free, from its membership (no
separation hypothesis on the carrier is consumed). -/
theorem isClosed_singleton_zero [Nonempty X] :
    IsClosed ({0} : Set (SubProbabilityMeasure X)) := by
  rw [← compile_top_eq_bot]
  exact isClosed_compile lowerSemicontinuous_const

/-- The below-bottom object leaves the ontology by type: the empty set
is not a member of the radial universe. -/
theorem not_isCredalBody_empty :
    ¬ IsCredalBody (∅ : Set (SubProbabilityMeasure X)) :=
  fun h => Set.not_nonempty_empty h.1

/-- **The pinning shape is excluded by type**: the singleton at a
nonzero state is not radial, because a nonempty radial set owns the
bottom state. -/
theorem not_isRadial_singleton {ν : SubProbabilityMeasure X}
    (hν : ν ≠ 0) : ¬ IsRadial ({ν} : Set (SubProbabilityMeasure X)) :=
  fun h =>
    hν (Set.mem_singleton_iff.mp (zero_mem_of_isRadial ⟨ν, rfl⟩ h)).symm

/-- The singleton at a nonzero state is not a member of the radial
universe. -/
theorem not_isCredalBody_singleton {ν : SubProbabilityMeasure X}
    (hν : ν ≠ 0) : ¬ IsCredalBody ({ν} : Set (SubProbabilityMeasure X)) :=
  fun h => not_isRadial_singleton hν h.2.2

/-- No penalty functional whatsoever — lower semicontinuous or not —
compiles to a pinned point: radiality of every body excludes the
singleton at nonzero mass outright. -/
theorem compile_ne_singleton (f : Penalty X) {ν : SubProbabilityMeasure X}
    (hν : ν ≠ 0) : compile f ≠ ({ν} : Set (SubProbabilityMeasure X)) :=
  fun h => not_isRadial_singleton hν (h ▸ isRadial_compile f)

end SuFunctor.Universe.General

/-! ## Part II — the exact stratum: radial walls and the ray entry -/

namespace SuFunctor

universe u

variable {V : Type u}

namespace Adequacy

open SuFunctor.Universe (Dip CoupledSat SpecAtom SpecDnf)

/-- **The exact-seam membership predicate**: a penalty on joints is
radial when it is monotone non-increasing along admitted downward
scalings of laws, read at the scalar seam.  This is the seam-reading
of the general carrier's ray-down-closure. -/
def RadialPen (σ : Plain.Pen V) : Prop :=
  ∀ ⦃μ ν : SubPMF V⦄, rayC μ ν → σ ν.toJoint ≤ σ μ.toJoint

/-- The constraint wall prices `⊤` at the joint of every law outside
the constraint — injectivity of the scalar seam, consumed once more. -/
theorem cwall_toJoint_eq_top {c : SubPMF V → Prop} {μ : SubPMF V}
    (hc : ¬ c μ) : cwall c μ.toJoint = ⊤ := by
  rw [cwall_def]
  refine wallPen_apply_of_not_mem ?_
  rintro ⟨μ', hμ', he⟩
  exact hc (SubPMF.toJoint_injective he ▸ hμ')

/-- **The membership characterization**: a constraint wall is a member
of the radial universe exactly when the constraint is down-closed. -/
theorem radialPen_cwall_iff {c : SubPMF V → Prop} :
    RadialPen (cwall c) ↔ DownClosed c := by
  constructor
  · intro h μ ν hray hcμ
    have h0 := h hray
    rw [cwall_toJoint_eq_zero_iff.mpr hcμ] at h0
    exact cwall_toJoint_eq_zero_iff.mp (le_zero_iff.mp h0)
  · intro hc μ ν hray
    by_cases hcμ : c μ
    · rw [cwall_toJoint_eq_zero_iff.mpr (hc hray hcμ),
        cwall_toJoint_eq_zero_iff.mpr hcμ]
    · rw [cwall_toJoint_eq_top hcμ]
      exact le_top

/-- **The radial wall**: how a constraint enters the radial universe —
the wall on the credal completion (the down-closure) of its
satisfaction set.  Equivalently: the exact-stratum compile of the
constraint's indicator, through the lawfulness closure of the credal
denotation stratum. -/
noncomputable def rwall (c : SubPMF V → Prop) : Plain.Pen V :=
  cwall (credalCompile c)

theorem rwall_def (c : SubPMF V → Prop) :
    rwall c = cwall (credalCompile c) := rfl

/-- Every radial wall is a member of the radial universe. -/
theorem radialPen_rwall (c : SubPMF V → Prop) : RadialPen (rwall c) :=
  radialPen_cwall_iff.mpr (downClosed_credalCompile c)

/-- Already-radial constraints enter unchanged: on a down-closed,
bottom-admitting constraint the radial wall is the plain wall. -/
theorem rwall_eq_cwall_of_downClosed {c : SubPMF V → Prop}
    (hc : DownClosed c) (hz : c (SubPMF.zero V)) : rwall c = cwall c := by
  have hpred : credalCompile c = c := by
    funext ν
    exact propext ⟨fun h => credalCompile_least hz hc (fun _ h' => h') ν h,
      fun h => le_credalCompile c ν h⟩
  rw [rwall_def, hpred]

/-- The invertible safety merge survives on the radial stock:
conjunction of down-closed, bottom-admitting constraints merges radial
walls by pointwise `⊔`.  (For arbitrary constraints the merge law
fails — two pinning constraints on one ray witness the gap — and owes
nothing: pinning constraints are not members.) -/
theorem rwall_and_of_downClosed {c₁ c₂ : SubPMF V → Prop}
    (h₁ : DownClosed c₁) (hz₁ : c₁ (SubPMF.zero V))
    (h₂ : DownClosed c₂) (hz₂ : c₂ (SubPMF.zero V)) :
    rwall (fun μ => c₁ μ ∧ c₂ μ) = rwall c₁ ⊔ rwall c₂ := by
  rw [rwall_eq_cwall_of_downClosed h₁ hz₁,
    rwall_eq_cwall_of_downClosed h₂ hz₂,
    rwall_eq_cwall_of_downClosed
      (fun _ _ hray h => ⟨h₁ hray h.1, h₂ hray h.2⟩) ⟨hz₁, hz₂⟩]
  exact cwall_and c₁ c₂

/-- The un-radialized wall of the precise constraint is the pinning
point: the ideal point of the law.  (The contrast pair's first half;
the second is `rwall_singletonC`.) -/
theorem cwall_singletonC (μ : SubPMF V) :
    cwall (singletonC μ) = idealPoint μ := by
  rw [cwall_def, idealPoint_def]
  have h : {ν : SubPMF V | singletonC μ ν} = ({μ} : Set (SubPMF V)) := by
    ext ν
    exact Iff.rfl
  rw [h, Set.image_singleton]

/-- **The type-level exclusion that replaces the fence**: the pinning
floor — the plain wall of the singleton constraint at a nonzero law —
fails membership in the radial universe.  The witness is the fence's
own half-scaling, consumed here as a non-membership proof. -/
theorem not_radialPen_pinningFloor {μ : SubPMF V}
    (hμ : μ ≠ SubPMF.zero V) : ¬ RadialPen (cwall (singletonC μ)) := by
  intro h
  have hray : rayC μ (SubPMF.scale (1/2) (by norm_num) (by norm_num) μ) :=
    ⟨1/2, by norm_num, by norm_num, rfl⟩
  have hle := h hray
  rw [cwall_toJoint_eq_zero_iff.mpr (singletonC_self μ)] at hle
  have hsing := cwall_toJoint_eq_zero_iff.mp (le_zero_iff.mp hle)
  have heq : SubPMF.scale (1/2) (by norm_num) (by norm_num) μ = μ :=
    (singletonC_iff _ _).mp hsing
  have hw : μ.wt ≠ 0 := fun h0 => hμ ((SubPMF.eq_zero_iff_wt μ).mpr h0)
  have h12 : (1/2 : ℚ) = 1 := smul_wt_cancel hw (by
    rw [one_smul]
    exact congrArg SubPMF.wt heq)
  norm_num at h12

/-- **The ray entry**: how a law enters the radial universe — the wall
on its down-cone, the credal presentation's precise face. -/
noncomputable def rayPoint (μ : SubPMF V) : Plain.Pen V :=
  cwall (rayC μ)

theorem rayPoint_def (μ : SubPMF V) : rayPoint μ = cwall (rayC μ) := rfl

/-- **One door**: the radial wall of the precise constraint is the ray
entry of the law.  Systems and constraints enter the radial universe
through the same construction. -/
theorem rwall_singletonC (μ : SubPMF V) :
    rwall (singletonC μ) = rayPoint μ := by
  rw [rwall_def, rayPoint_def]
  have h : credalCompile (singletonC μ) = rayC μ := by
    funext ν
    refine propext ⟨?_, ?_⟩
    · rintro (rfl | ⟨ρ, hρ, hray⟩)
      · exact rayC_zero μ
      · rwa [(singletonC_iff μ ρ).mp hρ] at hray
    · intro h
      exact Or.inr ⟨μ, singletonC_self μ, h⟩
  rw [h]

/-- The ray entry of every law is a member of the radial universe —
the embedded system is itself a citizen of the universe it is judged
in. -/
theorem radialPen_rayPoint (μ : SubPMF V) : RadialPen (rayPoint μ) := by
  rw [← rwall_singletonC]
  exact radialPen_rwall _

/-- At the bottom law the ray and the singleton agree: the ray entry
of the zero law is its ideal point — the two embeddings' unique
meeting point. -/
theorem rayPoint_zero :
    rayPoint (SubPMF.zero V) = idealPoint (SubPMF.zero V) := by
  rw [← rwall_singletonC, ← cwall_singletonC]
  refine rwall_eq_cwall_of_downClosed ?_ (singletonC_self _)
  intro μ ν hray h
  have hμ : μ = SubPMF.zero V := h
  subst hμ
  exact ((rayC_eq_singletonC_iff.mpr rfl) ν).mp hray

/-! ### Universal properness

No radial wall excludes the bottom law: an equality construct that
excluded the inconsistent world would not be a valid belief state, and
radial walls cannot express such an exclusion — whatever the
constraint. -/

/-- Every radial wall admits the bottom law. -/
theorem rwall_toJoint_zero (c : SubPMF V → Prop) :
    rwall c (SubPMF.zero V).toJoint = 0 :=
  cwall_toJoint_eq_zero_iff.mpr (credalCompile_zero c)

/-- No radial wall is the everywhere-`⊤` penalty: the wall on the
empty set is not expressible through the radial door. -/
theorem rwall_ne_top (c : SubPMF V → Prop) :
    rwall c ≠ (⊤ : Plain.Pen V) := by
  intro h
  have h0 := congrFun h (SubPMF.zero V).toJoint
  rw [rwall_toJoint_zero, Pi.top_apply] at h0
  exact ENNReal.zero_ne_top h0

/-! ### The judgment bridge, ray-shaped -/

/-- The coupled judgment of a ray entry against a radial wall atom,
in full: safety is containment of the down-cone in the credal
completion; liveness against the properness demand is free (the cone
is never empty). -/
theorem coupledSat_rayPoint_rwall_iff {c : SubPMF V → Prop}
    {μ : SubPMF V} :
    CoupledSat (rayPoint μ) (rwall c) {(⊤ : Plain.Pen V)} ↔
      ∀ ν, rayC μ ν → credalCompile c ν := by
  rw [rayPoint_def, cwall_def, coupledSat_wallPen_iff]
  constructor
  · rintro ⟨hsafe, -⟩ ν hν
    exact cwall_toJoint_eq_zero_iff.mp (hsafe ν.toJoint ⟨ν, hν, rfl⟩)
  · intro h
    refine ⟨?_, ?_⟩
    · rintro j ⟨ν, hν, rfl⟩
      exact cwall_toJoint_eq_zero_iff.mpr (h ν hν)
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact ⟨μ.toJoint, ⟨μ, rayC_self μ, rfl⟩,
        by rw [Pi.top_apply]; exact lt_of_lt_of_le zero_lt_one le_top⟩

/-- The bottom law's entry satisfies every radial wall atom: the
all-safety claim is true of the zero-mass subject, whatever the
constraint. -/
theorem coupledSat_rayPoint_zero_rwall (c : SubPMF V → Prop) :
    CoupledSat (rayPoint (SubPMF.zero V)) (rwall c)
      {(⊤ : Plain.Pen V)} := by
  rw [coupledSat_rayPoint_rwall_iff]
  intro ν hν
  obtain ⟨t, -, -, hwt⟩ := hν
  have hν0 : ν = SubPMF.zero V := (SubPMF.eq_zero_iff_wt ν).mpr
    (by rw [hwt, SubPMF.zero_wt, smul_zero])
  rw [hν0]
  exact credalCompile_zero c

/-- On a full-mass law the credal completion reads the constraint
back: a full-mass member of the down-closure is a tip, and a tip
matches only the constraint's own members. -/
theorem credalCompile_iff_of_mass_one {c : SubPMF V → Prop}
    {μ : SubPMF V} (hμ : μ.mass = 1) : credalCompile c μ ↔ c μ := by
  constructor
  · rintro (rfl | ⟨ρ, hρ, t, ht0, ht1, hwt⟩)
    · rw [show (SubPMF.zero V).mass = 0 from SubPMF.zero_prob Set.univ]
        at hμ
      norm_num at hμ
    · have hm : μ.mass = t * ρ.mass := SubPMF.prob_of_wt_smul hwt Set.univ
      have hρm : ρ.mass ≤ 1 := ρ.mass_le_one'
      have h1t : 1 ≤ t := by nlinarith [mul_le_mul_of_nonneg_left hρm ht0]
      have ht : t = 1 := le_antisymm ht1 h1t
      have hμρ : μ = ρ := SubPMF.ext' (by rw [hwt, ht, one_smul])
      rwa [hμρ]
  · exact le_credalCompile c μ

/-- **The judgment bridge at full mass, for arbitrary constraints**:
the ray entry of a full-mass law satisfies a constraint's radial wall
atom exactly when the law satisfies the constraint.  A radial set
contains a ray exactly when it contains the ray's tip. -/
theorem coupledSat_rayPoint_rwall_iff_of_mass_one
    {c : SubPMF V → Prop} {μ : SubPMF V} (hμ : μ.mass = 1) :
    CoupledSat (rayPoint μ) (rwall c) {(⊤ : Plain.Pen V)} ↔ c μ := by
  rw [coupledSat_rayPoint_rwall_iff]
  constructor
  · intro h
    exact (credalCompile_iff_of_mass_one hμ).mp (h μ (rayC_self μ))
  · intro hc ν hν
    exact downClosed_credalCompile c hν (le_credalCompile c μ hc)

/-- **The judgment bridge at every mass, for radial constraints**: on
a down-closed, bottom-admitting constraint the bridge needs no mass
hypothesis. -/
theorem coupledSat_rayPoint_rwall_iff_of_downClosed
    {c : SubPMF V → Prop} (hc : DownClosed c) (hz : c (SubPMF.zero V))
    {μ : SubPMF V} :
    CoupledSat (rayPoint μ) (rwall c) {(⊤ : Plain.Pen V)} ↔ c μ := by
  rw [coupledSat_rayPoint_rwall_iff]
  constructor
  · intro h
    exact credalCompile_least hz hc (fun _ h' => h') μ (h μ (rayC_self μ))
  · intro hcμ ν hν
    exact Or.inr ⟨μ, hcμ, hν⟩

/-! ### The transport layer, ray-shaped -/

/-- The radial wall atom of a constraint diagram: floor the radial
wall of the conjunction, liveness family exactly the properness
demand. -/
noncomputable def radialAtom (L : List (SubPMF V → Prop)) :
    SpecAtom (Plain.Joint V) where
  floor := rwall (looseConj L)
  marks := {⊤}
  finite_marks := Set.finite_singleton _
  top_mem := rfl

@[simp] theorem radialAtom_floor (L : List (SubPMF V → Prop)) :
    (radialAtom L).floor = rwall (looseConj L) := rfl

@[simp] theorem radialAtom_marks (L : List (SubPMF V → Prop)) :
    (radialAtom L).marks = {(⊤ : Plain.Pen V)} := rfl

/-- The radially presented diagram: a single-disjunct coupled DNF
whose floor is the radial wall of the conjunction. -/
noncomputable def radialDnf (L : List (SubPMF V → Prop)) :
    SpecDnf (Plain.Joint V) where
  atoms := {radialAtom L}
  finite_atoms := Set.finite_singleton _

/-- **The transport layer, ray-shaped**: membership of a full-mass
law's ray entry in a radially presented diagram's model class is
exactly satisfaction of the diagram's conjunction. -/
theorem rayPoint_mem_radialDnf_iff (L : List (SubPMF V → Prop))
    {μ : SubPMF V} (hμ : μ.mass = 1) :
    rayPoint μ ∈ (radialDnf L).modelClass ↔ looseConj L μ := by
  rw [SpecDnf.mem_modelClass_iff]
  constructor
  · rintro ⟨a, ha, hsat⟩
    rw [show (radialDnf L).atoms = {radialAtom L} from rfl,
      Set.mem_singleton_iff] at ha
    subst ha
    simp only [radialAtom_floor, radialAtom_marks] at hsat
    exact (coupledSat_rayPoint_rwall_iff_of_mass_one hμ).mp hsat
  · intro h
    exact ⟨radialAtom L, rfl,
      (coupledSat_rayPoint_rwall_iff_of_mass_one hμ).mpr h⟩

/-- Ex falso at the radial presentation: the inconsistent system
belongs to no radially presented diagram's model class. -/
theorem top_notMem_radialDnf (L : List (SubPMF V → Prop)) :
    (⊤ : Plain.Pen V) ∉ (radialDnf L).modelClass :=
  (radialDnf L).top_notMem_modelClass

/-! ## Part III — the contradictory-equality composite

Assert `x = y`, `x = false`, `y = true` over the two-bit carrier, as
almost-sure (mass-pinning-free) constraints.  Each is individually —
indeed pairwise — satisfiable; the three together are satisfied by
exactly the bottom law, and their composed radial wall is exactly the
bottom law's entry: infeasibility denotes bottom, lawfully.  Contrast
`exists_cwall_and_ne_inf`: over pinning floors, the same composition
shape produced the wall on the empty set — the everywhere-`⊤` object
the radial universe excludes by type. -/

/-- The almost-sure event constraint: all weight inside the event —
the mass-pinning-free form of an equality construct.  Vacuously true
of the bottom law, whatever the event. -/
def asC (A : Set V) : SubPMF V → Prop :=
  fun μ => ∀ v ∉ A, μ.wt v = 0

/-- Almost-sure constraints are down-closed: scaling mass away
preserves null events. -/
theorem downClosed_asC (A : Set V) : DownClosed (asC A) := by
  rintro μ ν ⟨t, -, -, hwt⟩ hμ v hv
  rw [hwt, Finsupp.smul_apply, hμ v hv, smul_zero]

/-- Almost-sure constraints admit the bottom law. -/
theorem asC_zero (A : Set V) : asC A (SubPMF.zero V) := by
  intro v _
  simp

/-- A point mass inside the event satisfies the almost-sure
constraint. -/
theorem asC_dirac {A : Set V} {v : V} (hv : v ∈ A) :
    asC A (SubPMF.dirac v) := by
  intro w hw
  show (Finsupp.single v (1 : ℚ)) w = 0
  exact Finsupp.single_eq_of_ne (fun h => hw (h ▸ hv))

/-- `x = y`, almost surely. -/
def xyEqC : SubPMF (Bool × Bool) → Prop :=
  asC {p | p.1 = p.2}

/-- `x = false`, almost surely. -/
def xFalseC : SubPMF (Bool × Bool) → Prop :=
  asC {p | p.1 = false}

/-- `y = true`, almost surely. -/
def yTrueC : SubPMF (Bool × Bool) → Prop :=
  asC {p | p.2 = true}

/-- `x = y` and `x = false` hold together at a point mass: the pair is
satisfiable. -/
theorem xyEqC_and_xFalseC_dirac :
    xyEqC (SubPMF.dirac (false, false))
      ∧ xFalseC (SubPMF.dirac (false, false)) :=
  ⟨asC_dirac rfl, asC_dirac rfl⟩

/-- `x = y` and `y = true` hold together at a point mass: the pair is
satisfiable. -/
theorem xyEqC_and_yTrueC_dirac :
    xyEqC (SubPMF.dirac (true, true))
      ∧ yTrueC (SubPMF.dirac (true, true)) :=
  ⟨asC_dirac rfl, asC_dirac rfl⟩

/-- `x = false` and `y = true` hold together at a point mass: the pair
is satisfiable. -/
theorem xFalseC_and_yTrueC_dirac :
    xFalseC (SubPMF.dirac (false, true))
      ∧ yTrueC (SubPMF.dirac (false, true)) :=
  ⟨asC_dirac rfl, asC_dirac rfl⟩

/-- The three constraints together force the bottom law: any weight
would have to sit at a point with `x = y`, `x = false`, and
`y = true` at once, and no such point exists. -/
theorem eq_zero_of_contradictory {μ : SubPMF (Bool × Bool)}
    (h1 : xyEqC μ) (h2 : xFalseC μ) (h3 : yTrueC μ) :
    μ = SubPMF.zero (Bool × Bool) := by
  refine (SubPMF.eq_zero_iff_wt μ).mpr (Finsupp.ext fun p => ?_)
  by_cases h12 : p.1 = p.2
  · by_cases hx : p.1 = false
    · refine h3 p (fun hy => ?_)
      rw [Set.mem_setOf_eq, ← h12, hx] at hy
      exact Bool.false_ne_true hy
    · exact h2 p hx
  · exact h1 p h12

/-- Exactly the bottom law satisfies the composite: almost-sure
constraints are vacuous at zero mass, and jointly unsatisfiable at any
positive mass. -/
theorem contradictory_looseConj_iff (μ : SubPMF (Bool × Bool)) :
    looseConj [xyEqC, xFalseC, yTrueC] μ
      ↔ μ = SubPMF.zero (Bool × Bool) := by
  constructor
  · rintro ⟨hA, hB, hC, -⟩
    exact eq_zero_of_contradictory hA hB hC
  · rintro rfl
    exact ⟨asC_zero _, asC_zero _, asC_zero _, trivial⟩

/-- **Infeasibility denotes bottom**: the composed radial wall of the
three contradictory equality constraints — merged by the fibre's own
safety algebra — is exactly the bottom law's entry in the radial
universe. -/
theorem contradictory_composite_denotes_bot :
    rwall xyEqC ⊔ rwall xFalseC ⊔ rwall yTrueC
      = rayPoint (SubPMF.zero (Bool × Bool)) := by
  have h12 : rwall xyEqC ⊔ rwall xFalseC
      = rwall (fun μ => xyEqC μ ∧ xFalseC μ) :=
    (rwall_and_of_downClosed (downClosed_asC _) (asC_zero _)
      (downClosed_asC _) (asC_zero _)).symm
  have h123 : rwall (fun μ => xyEqC μ ∧ xFalseC μ) ⊔ rwall yTrueC
      = rwall (fun μ => (xyEqC μ ∧ xFalseC μ) ∧ yTrueC μ) :=
    (rwall_and_of_downClosed
      (fun _ _ hray h =>
        ⟨downClosed_asC _ hray h.1, downClosed_asC _ hray h.2⟩)
      ⟨asC_zero _, asC_zero _⟩ (downClosed_asC _) (asC_zero _)).symm
  have hpred : (fun μ => (xyEqC μ ∧ xFalseC μ) ∧ yTrueC μ)
      = singletonC (SubPMF.zero (Bool × Bool)) := by
    funext μ
    exact propext ⟨fun h => eq_zero_of_contradictory h.1.1 h.1.2 h.2,
      fun h => by subst h; exact ⟨⟨asC_zero _, asC_zero _⟩, asC_zero _⟩⟩
  rw [h12, h123, hpred, rwall_singletonC]

/-- The composed denotation is *not* the everywhere-`⊤` wall: the
contradictory composite stays inside the universe. -/
theorem contradictory_composite_ne_top :
    rwall xyEqC ⊔ rwall xFalseC ⊔ rwall yTrueC
      ≠ (⊤ : Plain.Pen (Bool × Bool)) := by
  rw [contradictory_composite_denotes_bot, rayPoint_zero]
  exact idealPoint_ne_top _

/-- The bottom law lawfully models the contradictory composite: the
composed floor is satisfied, with properness, by the bottom law's
entry. -/
theorem coupledSat_bot_contradictory :
    CoupledSat (rayPoint (SubPMF.zero (Bool × Bool)))
      (rwall xyEqC ⊔ rwall xFalseC ⊔ rwall yTrueC)
      {(⊤ : Plain.Pen (Bool × Bool))} := by
  rw [contradictory_composite_denotes_bot]
  refine ⟨le_rfl, fun v hv => ?_⟩
  rw [Set.mem_singleton_iff] at hv
  subst hv
  refine ⟨(SubPMF.zero (Bool × Bool)).toJoint, ?_⟩
  rw [show rayPoint (SubPMF.zero (Bool × Bool))
        (SubPMF.zero (Bool × Bool)).toJoint = 0
      from cwall_toJoint_eq_zero_iff.mpr (rayC_self _), Pi.top_apply]
  exact lt_of_lt_of_le zero_lt_one le_top

end Adequacy

end SuFunctor
