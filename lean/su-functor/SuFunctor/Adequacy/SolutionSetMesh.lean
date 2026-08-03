import SuFunctor.Adequacy.HeatTorus
import SuFunctor.Universe.FellDescentEqualizer
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Int

/-! # Adequacy: the solution-set mesh — Fell descent consumed in anger

The named successor to the heat-on-torus development: cells
carrying closed **sets** of records — nonuniqueness as imprecision —
glued by the equalizer descent.  This module is the first consumer of
`FellDescentEqualizer` (rung C′): the ambient is the mesh's
spacetime-value window `MeshPt M T E = ↥M.chart × ↥T × E` (the window
*is* the ambient, so graphs of window-continuous fields are closed with
no relativization), the cover is the three arcs' spatial preimages, and
`meshDescent` is the C′ homeomorphism instantiated there — descent of
closed record loci is **exact**, with the R1 fee paid entirely by
inherited instances.

What the set stratum then shows, against that exact descent:

* **Solution tubes.**  A *torus tube* is a union of graphs of global
  periodic solutions (`IsTorusTube`); cell and chart tubes analogous.
  Clips of torus tubes are cell tubes (`isCellTube_clip`), clip
  families are overlap-compatible by construction, and torus tubes
  satisfy the tube-level wrap wall (`tubeWrapWall_of_torusTube`) — the
  point-stratum `WrapWall` transposed to fiber equality.

* **The set-stratum holonomy is wall-invisible**
  (`setStratum_holonomy`).  The ℤ-orbit linear tube — all integer
  period-translates of the linear field at once,
  `{p | ∃ k : ℤ, y = x − k·L}` — is closed, has cell-tube clips
  (`isCellTube_orbit`), is overlap-compatible (clips of one global
  closed set), **satisfies the wrap wall** (`orbitEq_wrapWall`: the
  orbit is invariant under the period shift, fiberwise), and is even a
  *chart* tube (`orbitTube_is_chartTube` — the chain citizenship
  glues).  Yet it is not a torus tube (`orbitTube_not_torusTube`): any
  global solution threading the tube must follow a single branch
  (`x − u x t₀` is continuous on the preconnected chart with values in
  the discrete `Lℤ`, hence constant — the midpoint argument through
  `IsPreconnected.Icc_subset`), and single branches are not periodic.
  At the point stratum the wrap wall *purchased* periodicity
  (`heat_mesh_glues` consumed it); at the set stratum no wall in the
  landed vocabulary can: the missing datum is the **branch pairing**
  (which branch continues which across the ring — correspondence data
  with a cocycle condition, 2-descent), not any pointwise constraint.
  Equivalently: torus-tube-hood is **not of local character** over the
  ring cover (`not_isLocalLocusEq_torusTube`), where the heat rows'
  `HeatAt.congr` gave the record tier exactly that character.

* **The wall has teeth, and the orbit's infinitude is load-bearing**:
  the single-branch linear tube refuses the wrap wall
  (`not_tubeWrap_singleLin`) — the point-stratum holonomy witness
  transposed; only the full ℤ-orbit slips past it.

* **Con is free at the set stratum** (`isTorusTube_univ`,
  `tubeAtoms_consistent`): the top tube — total imprecision, every
  value at every point — is a torus tube (all constant equilibria at
  once) and satisfies every atom.  The point stratum's con needed
  actual equilibria; the set stratum's con obligation concentrates
  entirely on *non-vacuous* imprecision.

* **The one-sided square** (`solset_forward_cell`,
  `tubeAtoms_not_classical`): torus-tube-hood entails the compiled
  atoms — cell citizenship plus the wrap atom, the chain walls having
  migrated *into the carrier* (the equalizer's compatibility field) —
  but the atoms do not pin it: the Dirac at the orbit point separates
  them.  The heat leg's stratum-indexed-sidedness table gains a row:
  one-sided at the record-set stratum, obstruction type *branch
  holonomy*, not information loss.

* **Labelled ensembles glue** (`labelled_ensembles_glue`): indexed
  families with per-index walls glue elementwise through
  `heat_mesh_glues`.  The obstruction above is exactly the forgotten
  labelling.

* **The record-tier shadow** (`orbit_enclosure_forces_zero`): the
  suppC-of-set-family compositor — enclosure atoms constraining each
  cell field to thread its cell tube — conjoined with the six heat
  atoms is ⊥-forcing on the orbit tube: threading forces each cell
  field onto a single branch `x − kᵢ·L` (`thread_const`), the chain
  seams force `k₁ = k₂ = k₃`, and the wrap wall forces `k₃ = k₁ + 1` —
  an integer cocycle frustrated around the ring.  The set-stratum
  failure is thereby *detectable* at the record tier — but only as con
  failure of the composed object (a global satisfiability fact), never
  as any single wall's refusal.

`D`'s sign appears nowhere, as in the heat module.  Nothing
transcendental appears either: the witnesses are linear, so this leg
has no enclosure/script stratum — that genre returns with tube
*evolution* (the exact-ℚ mesh certificate successor). -/

namespace SuFunctor

namespace Universe

namespace FellCloseds

open Set

variable {α : Type*} [TopologicalSpace α] {ι : Type*}

/-! ## Local character, equalizer form

The equalizer-cover sibling of rung D's `IsLocalLocus`
(`FellRecordLocus`): a locus family is of local character over a
system of subsets when ambient-locus membership is equivalent to every
clip's level-locus membership.  Rung D packaged this over *directed*
covers (`ProjLim`); the mesh cover is non-directed, so the solution-set
mesh needs the statement at the equalizer carrier — and its headline is
a *refutation*: torus-tube-hood is not of local character over the
ring cover (`Adequacy.not_isLocalLocusEq_torusTube`). -/

/-- Local character of a locus family over a system of subsets:
ambient membership is clip-membership at every level.  (Identical in
form to `IsLocalLocus`; restated here as the hypothesis the equalizer
package consumes, so the refutation below names exactly the property
that fails.) -/
def IsLocalLocusEq (U : ι → Set α) (R₀ : Set (FellCloseds α))
    (R : ∀ i, Set (FellCloseds ↥(U i))) : Prop :=
  ∀ F : FellCloseds α, F ∈ R₀ ↔ ∀ i, clip (U i) F ∈ R i

/-- Under local character, an equalizer point with levelwise-locus
components glues into the ambient locus: the positive half of the
closed-subsheaf story, at the equalizer carrier. -/
theorem IsLocalLocusEq.glue_mem {U : ι → Set α} {R₀ : Set (FellCloseds α)}
    {R : ∀ i, Set (FellCloseds ↥(U i))} (hloc : IsLocalLocusEq U R₀ R)
    (hUo : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
    {p : Equalizer U} (hp : ∀ i, p.1 i ∈ R i) :
    glueEqualizer U hUo hcov p ∈ R₀ := by
  rw [hloc]
  intro i
  have h := congrArg (fun q : Equalizer U => q.1 i)
    (toEqualizer_glueEqualizer U hUo hcov p)
  have hclip : clip (U i) (glueEqualizer U hUo hcov p) = p.1 i := h
  rw [hclip]
  exact hp i

end FellCloseds

end Universe

namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Set Topology Filter
open SuFunctor.Universe

attribute [local instance] SuFunctor.Universe.fell

universe u

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The arc indexing and the mesh cover -/

namespace RingMesh

/-- The three arcs, indexed. -/
def arc (M : RingMesh) : Fin 3 → Set ℝ
  | 0 => M.I1
  | 1 => M.I2
  | 2 => M.I3

@[simp] theorem arc_zero (M : RingMesh) : M.arc 0 = M.I1 := rfl
@[simp] theorem arc_one (M : RingMesh) : M.arc 1 = M.I2 := rfl
@[simp] theorem arc_two (M : RingMesh) : M.arc 2 = M.I3 := rfl

theorem isOpen_arc (M : RingMesh) (i : Fin 3) : IsOpen (M.arc i) := by
  fin_cases i
  · exact M.isOpen_I1
  · exact M.isOpen_I2
  · exact M.isOpen_I3

theorem arc_subset_chart (M : RingMesh) (i : Fin 3) : M.arc i ⊆ M.chart := by
  fin_cases i
  · exact M.I1_subset_chart
  · exact M.I2_subset_chart
  · exact M.I3_subset_chart

/-- The three arcs cover the chart: the mesh cover is a genuine open
cover of the window. -/
theorem iUnion_arc (M : RingMesh) : ⋃ i, M.arc i = M.chart := by
  apply subset_antisymm
  · exact iUnion_subset M.arc_subset_chart
  · intro x hx
    obtain ⟨hxl, hxr⟩ := hx
    have hδ' := M.hδ
    have hab' := M.hab
    rcases lt_or_ge x (M.a + M.δ) with h1 | h1
    · exact mem_iUnion.mpr ⟨0, show x ∈ M.I1 from ⟨hxl, h1⟩⟩
    · rcases lt_or_ge x (M.b + M.δ) with h2 | h2
      · exact mem_iUnion.mpr ⟨1, show x ∈ M.I2 from ⟨by linarith, h2⟩⟩
      · exact mem_iUnion.mpr ⟨2, show x ∈ M.I3 from ⟨by linarith, hxr⟩⟩

end RingMesh

/-- The mesh's spacetime-value window: the ambient of the solution-set
tier.  The window is the ambient, so window-continuous graphs are
closed subsets outright. -/
abbrev MeshPt (M : RingMesh) (T : Set ℝ) (E : Type) : Type :=
  ↥M.chart × ↥T × E

/-- The mesh cover of the window: the arcs' spatial preimages.  (`E`
explicit: this set former appears inside type ascriptions, where an
implicit carrier would leave the expected type undetermined.) -/
def arcRegion (M : RingMesh) (T : Set ℝ) (E : Type) (i : Fin 3) :
    Set (MeshPt M T E) :=
  {p | (p.1 : ℝ) ∈ M.arc i}

theorem isOpen_arcRegion (M : RingMesh) (T : Set ℝ) (E : Type)
    [NormedAddCommGroup E] (i : Fin 3) :
    IsOpen (arcRegion M T E i) :=
  (M.isOpen_arc i).preimage (continuous_subtype_val.comp continuous_fst)

theorem iUnion_arcRegion (M : RingMesh) (T : Set ℝ) (E : Type) :
    ⋃ i, arcRegion M T E i = univ := by
  ext p
  simp only [arcRegion, mem_iUnion, mem_setOf_eq, mem_univ, iff_true]
  have hp : (p.1 : ℝ) ∈ ⋃ i, M.arc i := by
    rw [M.iUnion_arc]
    exact p.1.2
  exact mem_iUnion.mp hp

/-! ## The consumption: rung C′ at the mesh cover -/

/-- **Fell descent consumed at the ring mesh** — the first instance of
the equalizer descent theorem in anger: closed subsets of the
spacetime-value window are exactly overlap-compatible families of
closed subsets of the arc cylinders.  The R1 fee is paid by inherited
instances (`T2Space.r1Space` through the subtype and product
instances); the cover lemmas above are the entire instantiation cost.
Descent of record loci is *exact*; everything that fails at the set
stratum (below) fails in the interaction of descent with citizenship,
never in descent. -/
noncomputable def meshDescent (M : RingMesh) (T : Set ℝ) :
    FellCloseds (MeshPt M T E) ≃ₜ
      FellCloseds.Equalizer (arcRegion M T E) :=
  FellCloseds.equalizerHomeomorph (arcRegion M T E)
    (isOpen_arcRegion M T E) (iUnion_arcRegion M T E)

/-- The glue of an equalizer point at the mesh cover, named. -/
noncomputable def meshGlue (M : RingMesh) (T : Set ℝ)
    (p : FellCloseds.Equalizer (arcRegion M T E)) :
    FellCloseds (MeshPt M T E) :=
  FellCloseds.glueEqualizer (arcRegion M T E)
    (isOpen_arcRegion M T E) (iUnion_arcRegion M T E) p

omit [NormedSpace ℝ E] in
theorem meshGlue_toEqualizer (M : RingMesh) (T : Set ℝ)
    (F : FellCloseds (MeshPt M T E)) :
    meshGlue M T (FellCloseds.toEqualizer (arcRegion M T E) F) = F :=
  FellCloseds.glueEqualizer_toEqualizer _ _ _ F

omit [NormedSpace ℝ E] in
theorem toEqualizer_meshGlue (M : RingMesh) (T : Set ℝ)
    (p : FellCloseds.Equalizer (arcRegion M T E)) :
    FellCloseds.toEqualizer (arcRegion M T E) (meshGlue M T p) = p :=
  FellCloseds.toEqualizer_glueEqualizer _ _ _ p

/-! ## Solution tubes: citizenship at the set stratum -/

/-- The graph of a field over the window. -/
def graphA (M : RingMesh) (T : Set ℝ) (u : ℝ → ℝ → E) :
    Set (MeshPt M T E) :=
  {p | u (p.1 : ℝ) (p.2.1 : ℝ) = p.2.2}

/-- The graph of a field at an arc cylinder. -/
def graphCell (M : RingMesh) (T : Set ℝ) (i : Fin 3) (u : ℝ → ℝ → E) :
    Set ↥(arcRegion M T E i) :=
  {q | u ((q : MeshPt M T E).1 : ℝ) ((q : MeshPt M T E).2.1 : ℝ)
        = (q : MeshPt M T E).2.2}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem preimage_graphA (M : RingMesh) (T : Set ℝ) (i : Fin 3)
    (u : ℝ → ℝ → E) :
    ((↑) ⁻¹' graphA M T u : Set ↥(arcRegion M T E i))
      = graphCell M T i u := rfl

/-- A torus tube: the union of graphs of a family — any cardinality —
of global periodic solutions.  Nonuniqueness as imprecision, at the
observable stratum. -/
def IsTorusTube (M : RingMesh) (D : ℝ) (T : Set ℝ)
    (G : Set (MeshPt M T E)) : Prop :=
  ∃ 𝒮 : Set (ℝ → ℝ → E), (∀ u ∈ 𝒮, IsHeatTorusSol D M.L T u) ∧
    G = ⋃ u ∈ 𝒮, graphA M T u

/-- A chart tube: solutions on the whole window, periodicity not
demanded — the chain-citizenship class. -/
def IsChartTube (M : RingMesh) (D : ℝ) (T : Set ℝ)
    (G : Set (MeshPt M T E)) : Prop :=
  ∃ 𝒮 : Set (ℝ → ℝ → E), (∀ u ∈ 𝒮, IsHeatSol D M.chart T u) ∧
    G = ⋃ u ∈ 𝒮, graphA M T u

/-- A cell tube at arc `i`. -/
def IsCellTube (M : RingMesh) (D : ℝ) (T : Set ℝ) (i : Fin 3)
    (F : Set ↥(arcRegion M T E i)) : Prop :=
  ∃ 𝒮 : Set (ℝ → ℝ → E), (∀ u ∈ 𝒮, IsHeatSol D (M.arc i) T u) ∧
    F = ⋃ u ∈ 𝒮, graphCell M T i u

/-- The tube-level wrap wall: fiber equality across the period map on
the ring-closing collar — the point-stratum `WrapWall` transposed to
sets.  Stated on the plain component sets of an equalizer point. -/
def TubeWrapWall (M : RingMesh) (T : Set ℝ)
    (F1 : Set ↥(arcRegion M T E 0)) (F3 : Set ↥(arcRegion M T E 2)) :
    Prop :=
  ∀ (x t : ℝ) (y : E) (hx3 : x ∈ M.arc 2) (hx1 : x - M.L ∈ M.arc 0)
    (ht : t ∈ T),
    (⟨⟨⟨x, M.arc_subset_chart 2 hx3⟩, ⟨t, ht⟩, y⟩, hx3⟩ :
        ↥(arcRegion M T E 2)) ∈ F3
      ↔ (⟨⟨⟨x - M.L, M.arc_subset_chart 0 hx1⟩, ⟨t, ht⟩, y⟩, hx1⟩ :
          ↥(arcRegion M T E 0)) ∈ F1

variable {M : RingMesh} {D : ℝ} {T : Set ℝ}

/-- Clips of torus tubes are cell tubes: citizenship restricts.  (The
converse direction is the whole content of the set stratum's failure —
see `setStratum_holonomy`.) -/
theorem isCellTube_clip {G : FellCloseds (MeshPt M T E)}
    (hG : IsTorusTube M D T (G : Set (MeshPt M T E))) (i : Fin 3) :
    IsCellTube M D T i
      (FellCloseds.clip (arcRegion M T E i) G :
        Set ↥(arcRegion M T E i)) := by
  obtain ⟨𝒮, h𝒮, hGeq⟩ := hG
  refine ⟨𝒮, fun u hu x _ t ht => (h𝒮 u hu).sol x (mem_univ x) t ht, ?_⟩
  rw [FellCloseds.coe_clip, hGeq]
  rw [preimage_iUnion₂]
  rfl

omit [NormedSpace ℝ E] in
/-- The membership reading of a torus tube. -/
theorem mem_torusTube_iff {G : FellCloseds (MeshPt M T E)}
    {𝒮 : Set (ℝ → ℝ → E)}
    (hGeq : (G : Set (MeshPt M T E)) = ⋃ u ∈ 𝒮, graphA M T u)
    (z : MeshPt M T E) :
    z ∈ (G : Set (MeshPt M T E))
      ↔ ∃ u ∈ 𝒮, u (z.1 : ℝ) (z.2.1 : ℝ) = z.2.2 := by
  rw [hGeq]
  simp only [mem_iUnion, exists_prop, graphA, mem_setOf_eq]

/-- Torus tubes satisfy the wrap wall: each member's periodicity
carries its graph point across the period map, so the fibers agree as
sets. -/
theorem tubeWrapWall_of_torusTube {G : FellCloseds (MeshPt M T E)}
    (hG : IsTorusTube M D T (G : Set (MeshPt M T E))) :
    TubeWrapWall M T
      (FellCloseds.clip (arcRegion M T E 0) G :
        Set ↥(arcRegion M T E 0))
      (FellCloseds.clip (arcRegion M T E 2) G :
        Set ↥(arcRegion M T E 2)) := by
  obtain ⟨𝒮, h𝒮, hGeq⟩ := hG
  intro x t y hx3 hx1 ht
  constructor
  · intro h
    obtain ⟨u, hu, hval⟩ := (mem_torusTube_iff hGeq _).mp h
    refine (mem_torusTube_iff hGeq _).mpr ⟨u, hu, ?_⟩
    have hper := (h𝒮 u hu).periodic t (x - M.L)
    have hper' : u (x - M.L + M.L) t = u (x - M.L) t := hper
    rw [show x - M.L + M.L = x by ring] at hper'
    exact hper'.symm.trans hval
  · intro h
    obtain ⟨u, hu, hval⟩ := (mem_torusTube_iff hGeq _).mp h
    refine (mem_torusTube_iff hGeq _).mpr ⟨u, hu, ?_⟩
    have hper := (h𝒮 u hu).periodic t (x - M.L)
    have hper' : u (x - M.L + M.L) t = u (x - M.L) t := hper
    rw [show x - M.L + M.L = x by ring] at hper'
    exact hper'.trans hval

/-- The top tube is a torus tube: total imprecision is lawful — the
union of *all* constant equilibria fills the window.  This is the set
stratum's free con witness (the point stratum's con needed actual
equilibria; here maximal imprecision supplies consistency outright). -/
theorem isTorusTube_univ :
    IsTorusTube M D T (univ : Set (MeshPt M T E)) := by
  refine ⟨Set.range (fun k : E => (fun _ _ => k : ℝ → ℝ → E)), ?_, ?_⟩
  · rintro u ⟨k, rfl⟩
    exact isHeatTorusSol_const D M.L T k
  · ext p
    simp only [mem_univ, true_iff, mem_iUnion, exists_prop, graphA,
      mem_setOf_eq]
    exact ⟨fun _ _ => p.2.2, ⟨p.2.2, rfl⟩, rfl⟩

/-- The labelled positive face: indexed ensembles with per-index walls
glue elementwise through `heat_mesh_glues`.  Set-gluing fails exactly
where this labelling has been forgotten. -/
theorem labelled_ensembles_glue {ι' : Type*} (hT : IsOpen T)
    {c1 c2 c3 : ι' → ℝ → ℝ → E}
    (h1 : ∀ j, IsHeatSol D M.I1 T (c1 j))
    (h2 : ∀ j, IsHeatSol D M.I2 T (c2 j))
    (h3 : ∀ j, IsHeatSol D M.I3 T (c3 j))
    (hs12 : ∀ j, ∀ x ∈ M.I1 ∩ M.I2, ∀ t ∈ T, c1 j x t = c2 j x t)
    (hs23 : ∀ j, ∀ x ∈ M.I2 ∩ M.I3, ∀ t ∈ T, c2 j x t = c3 j x t)
    (hw : ∀ j, WrapWall M T (c1 j) (c3 j)) :
    ∃ u : ι' → ℝ → ℝ → E, ∀ j,
      IsHeatTorusSol D M.L T (u j) ∧
      (∀ x ∈ M.I1, ∀ t ∈ T, u j x t = c1 j x t) ∧
      (∀ x ∈ M.I2, ∀ t ∈ T, u j x t = c2 j x t) ∧
      (∀ x ∈ M.I3, ∀ t ∈ T, u j x t = c3 j x t) := by
  choose u hu hm1 hm2 hm3 using fun j =>
    heat_mesh_glues hT (h1 j) (h2 j) (h3 j) (hs12 j) (hs23 j) (hw j)
  exact ⟨u, fun j => ⟨hu j, hm1 j, hm2 j, hm3 j⟩⟩

/-! ## The ℤ-orbit witness (`E := ℝ`)

The set-stratum holonomy family: all integer period-translates of the
linear field at once.  Every wall in the landed vocabulary passes; the
citizenship fails only through the global branch structure. -/

section OrbitWitness

/-- The `k`-th period-translate of the linear field. -/
def linZ (M : RingMesh) (k : ℤ) : ℝ → ℝ → ℝ := fun x _ => x - k * M.L

/-- The translated linear fields solve the heat rows everywhere, for
every `D` — first spatial derivative constant, second zero,
time-constant. -/
theorem heatAt_linZ (M : RingMesh) (D : ℝ) (k : ℤ) (x t : ℝ) :
    HeatAt D (linZ M k) x t := by
  have hlin : ∀ y : ℝ, HasDerivAt (fun z : ℝ => z - (k : ℝ) * M.L) 1 y :=
    fun y => (hasDerivAt_id y).sub_const _
  have hderiv : (deriv fun z : ℝ => z - (k : ℝ) * M.L) = fun _ => 1 :=
    funext fun y => (hlin y).deriv
  refine ⟨?_, (hlin x).differentiableAt, ?_, ?_⟩
  · exact (continuous_fst.sub continuous_const).continuousAt
  · show DifferentiableAt ℝ (deriv fun y => linZ M k y t) x
    rw [show (fun y => linZ M k y t) = fun z : ℝ => z - (k : ℝ) * M.L
        from rfl, hderiv]
    exact differentiableAt_const 1
  · show HasDerivAt (fun s => linZ M k x s)
      (D • deriv (deriv fun y => linZ M k y t) x) t
    rw [show (fun y => linZ M k y t) = fun z : ℝ => z - (k : ℝ) * M.L
        from rfl, hderiv]
    simp only [deriv_const, smul_zero]
    exact hasDerivAt_const t (linZ M k x t)

/-- The ℤ-orbit linear tube: all period-translates of the linear
field, as one set of records. -/
def orbitTube (M : RingMesh) (T : Set ℝ) : Set (MeshPt M T ℝ) :=
  {p | ∃ k : ℤ, p.2.2 = (p.1 : ℝ) - k * M.L}

/-- The orbit tube is closed: it is the preimage of the closed set
`ℤ` under `(x, t, y) ↦ (x − y)/L` — discreteness of the branch set is
what closes the infinite union of graphs. -/
theorem isClosed_orbitTube (M : RingMesh) (T : Set ℝ) :
    IsClosed (orbitTube M T) := by
  have hL := M.hL0
  have hZ : IsClosed (Set.range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isClosed_range
  have hc : Continuous fun p : MeshPt M T ℝ =>
      (((p.1 : ℝ) - p.2.2) / M.L) := by
    apply Continuous.div_const
    exact (continuous_subtype_val.comp continuous_fst).sub
      (continuous_snd.comp continuous_snd)
  have heq : orbitTube M T
      = (fun p : MeshPt M T ℝ => (((p.1 : ℝ) - p.2.2) / M.L)) ⁻¹'
          (Set.range ((↑) : ℤ → ℝ)) := by
    ext p
    simp only [orbitTube, mem_setOf_eq, mem_preimage, Set.mem_range]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [eq_div_iff hL.ne', hk]
      ring
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [eq_div_iff hL.ne'] at hk
      linarith
  rw [heq]
  exact hZ.preimage hc

/-- The orbit tube's `FellCloseds` citizen. -/
noncomputable def orbitF (M : RingMesh) (T : Set ℝ) :
    FellCloseds (MeshPt M T ℝ) :=
  ⟨orbitTube M T, isClosed_orbitTube M T⟩

/-- The orbit tube's equalizer point: its clip family, compatible by
construction (clips of one global closed set — `toEqualizer`'s
compatibility is `rfl`). -/
noncomputable def orbitEq (M : RingMesh) (T : Set ℝ) :
    FellCloseds.Equalizer (arcRegion M T ℝ) :=
  FellCloseds.toEqualizer (arcRegion M T ℝ) (orbitF M T)

/-- Every clip of the orbit tube is a cell tube: the `linZ` branches,
each a cell solution. -/
theorem isCellTube_orbit (D : ℝ) (i : Fin 3) :
    IsCellTube M D T i
      (FellCloseds.clip (arcRegion M T ℝ i) (orbitF M T) :
        Set ↥(arcRegion M T ℝ i)) := by
  refine ⟨Set.range (linZ M), ?_, ?_⟩
  · rintro u ⟨k, rfl⟩ x _ t _
    exact heatAt_linZ M D k x t
  · rw [FellCloseds.coe_clip]
    ext q
    simp only [mem_preimage, mem_iUnion, exists_prop, Set.mem_range,
      graphCell, mem_setOf_eq]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨linZ M k, ⟨k, rfl⟩, hk.symm⟩
    · rintro ⟨u, ⟨k, rfl⟩, hk⟩
      exact ⟨k, hk.symm⟩

/-- **The orbit tube satisfies the wrap wall**: the branch set is
invariant under the period shift — fiberwise, `k ↦ k ∓ 1` reindexes
the wrap collar's values onto the base collar's.  The wall that
detected the point-stratum holonomy is blind to the set-stratum one. -/
theorem orbitEq_wrapWall :
    TubeWrapWall M T
      ((orbitEq M T).1 0 : Set ↥(arcRegion M T ℝ 0))
      ((orbitEq M T).1 2 : Set ↥(arcRegion M T ℝ 2)) := by
  intro x t y hx3 hx1 ht
  show (∃ k : ℤ, y = x - k * M.L) ↔ (∃ k : ℤ, y = x - M.L - k * M.L)
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k - 1, ?_⟩
    push_cast
    ring
  · rintro ⟨k, rfl⟩
    refine ⟨k + 1, ?_⟩
    push_cast
    ring

/-- The single-branch control: the plain linear tube — one branch,
`k = 0` — **refuses** the wrap wall, exactly as its point-stratum
sibling `not_wrap_lin` refused the point wall.  The orbit's
ℤ-infinitude is load-bearing: only the full orbit slips past. -/
theorem not_tubeWrap_singleLin {t₀ : ℝ} (ht₀ : t₀ ∈ T) :
    ¬ TubeWrapWall M T
        ((↑) ⁻¹' graphA M T (linZ M 0) : Set ↥(arcRegion M T ℝ 0))
        ((↑) ⁻¹' graphA M T (linZ M 0) : Set ↥(arcRegion M T ℝ 2)) := by
  intro h
  have hδ := M.hδ
  have hL := M.hL0
  have hbL := M.hbL
  have ha := M.ha
  have hx3 : M.L ∈ M.arc 2 := by
    show M.L ∈ M.I3
    exact ⟨by linarith, by linarith⟩
  have hx1 : M.L - M.L ∈ M.arc 0 := by
    show M.L - M.L ∈ M.I1
    rw [sub_self]
    exact ⟨by linarith, by linarith⟩
  have hw := h M.L t₀ M.L hx3 hx1 ht₀
  have hleft : linZ M 0 M.L t₀ = M.L := by simp [linZ]
  have hright : linZ M 0 (M.L - M.L) t₀ = M.L := hw.mp hleft
  simp only [linZ, Int.cast_zero, zero_mul, sub_self] at hright
  exact hL.ne hright

/-- The orbit tube is a **chart** tube: over the interval window — no
periodicity demanded — the branches are honest chart solutions, so the
chain citizenship glues.  Only the descent *to the circle* fails. -/
theorem orbitTube_is_chartTube (D : ℝ) :
    IsChartTube M D T (orbitTube M T) := by
  refine ⟨Set.range (linZ M), ?_, ?_⟩
  · rintro u ⟨k, rfl⟩ x _ t _
    exact heatAt_linZ M D k x t
  · ext p
    simp only [orbitTube, mem_setOf_eq, mem_iUnion, exists_prop,
      Set.mem_range, graphA]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨linZ M k, ⟨k, rfl⟩, hk.symm⟩
    · rintro ⟨u, ⟨k, rfl⟩, hk⟩
      exact ⟨k, hk.symm⟩

/-! ### The rigidity engine -/

/-- **Branch rigidity**: a function continuous on a preconnected set,
agreeing pointwise with *some* integer branch `x ↦ x − k·L` at every
point, follows a *single* branch throughout.  The midpoint argument:
`x − f x` has preconnected image inside the discrete `Lℤ`, and an
image containing two distinct branch values would contain the
half-branch value between them (`IsPreconnected.Icc_subset`), which is
on no branch. -/
theorem thread_const {L : ℝ} (hL : 0 < L) {S : Set ℝ}
    (hS : IsPreconnected S) {f : ℝ → ℝ} (hf : ContinuousOn f S)
    (hthread : ∀ x ∈ S, ∃ k : ℤ, f x = x - k * L)
    {x₀ : ℝ} (hx₀ : x₀ ∈ S) :
    ∃ k : ℤ, ∀ x ∈ S, f x = x - k * L := by
  obtain ⟨k₀, hk₀⟩ := hthread x₀ hx₀
  set g : ℝ → ℝ := fun z => z - f z with hg
  have hgc : ContinuousOn g S := continuousOn_id.sub hf
  have himg : ∀ r ∈ g '' S, ∃ k : ℤ, r = k * L := by
    rintro r ⟨z, hz, rfl⟩
    obtain ⟨k, hk⟩ := hthread z hz
    exact ⟨k, by rw [hg]; simp only [hk]; ring⟩
  have hpre : IsPreconnected (g '' S) := hS.image g hgc
  have key : ∀ r ∈ g '' S, ∀ s ∈ g '' S, r < s → False := by
    intro r hr s hs hlt
    obtain ⟨kr, hkr⟩ := himg r hr
    obtain ⟨ks, hks⟩ := himg s hs
    have hklt : kr < ks := by
      have h1 : (kr : ℝ) * L < (ks : ℝ) * L := by rw [← hkr, ← hks]; exact hlt
      exact_mod_cast lt_of_mul_lt_mul_right h1 hL.le
    have hgap : r + L ≤ s := by
      have h1 : (kr : ℝ) + 1 ≤ (ks : ℝ) := by exact_mod_cast hklt
      have h2 : ((kr : ℝ) + 1) * L ≤ (ks : ℝ) * L :=
        mul_le_mul_of_nonneg_right h1 hL.le
      rw [hkr, hks]
      nlinarith
    have hmid : r + L / 2 ∈ g '' S :=
      hpre.Icc_subset hr hs ⟨by linarith, by linarith⟩
    obtain ⟨km, hkm⟩ := himg _ hmid
    rw [hkr] at hkm
    have h2 : (2 * ((km : ℝ) - kr)) * L = 1 * L := by
      rw [one_mul]
      linarith
    have h3 : (2 * ((km : ℝ) - kr)) = 1 := mul_right_cancel₀ hL.ne' h2
    have h4 : (2 * (km - kr) : ℤ) = 1 := by exact_mod_cast h3
    omega
  have hconst : ∀ x ∈ S, g x = g x₀ := by
    intro x hx
    rcases lt_trichotomy (g x) (g x₀) with h | h | h
    · exact absurd h (fun h' =>
        key _ (mem_image_of_mem g hx) _ (mem_image_of_mem g hx₀) h')
    · exact h
    · exact absurd h (fun h' =>
        key _ (mem_image_of_mem g hx₀) _ (mem_image_of_mem g hx) h')
  refine ⟨k₀, fun x hx => ?_⟩
  have h1 := hconst x hx
  have h2 : g x₀ = (k₀ : ℝ) * L := by rw [hg]; simp only [hk₀]; ring
  have h3 : x - f x = (k₀ : ℝ) * L := by rw [← h2]; exact h1
  linarith

/-- Time-slice continuity from the heat rows' continuity row. -/
theorem contOn_slice {u : ℝ → ℝ → ℝ} {S : Set ℝ} {t₀ : ℝ}
    (h : ∀ x ∈ S, ContinuousAt (fun q : ℝ × ℝ => u q.1 q.2) (x, t₀)) :
    ContinuousOn (fun x => u x t₀) S := by
  intro x hx
  have h2 : ContinuousAt (fun x : ℝ => ((x, t₀) : ℝ × ℝ)) x :=
    (continuous_id.prodMk continuous_const).continuousAt
  have h3 : ContinuousAt
      ((fun q : ℝ × ℝ => u q.1 q.2) ∘ (fun x : ℝ => ((x, t₀) : ℝ × ℝ)))
      x := ContinuousAt.comp (h x hx) h2
  exact h3.continuousWithinAt

/-- **The orbit tube is not a torus tube.**  Any global periodic
solution threading the tube follows a single branch (`thread_const` on
the preconnected chart), and single branches are not `L`-periodic —
so no family of torus solutions covers the tube: the branch holonomy
around the ring is unrealizable, though every wall passed. -/
theorem orbitTube_not_torusTube (D : ℝ) {t₀ : ℝ} (ht₀ : t₀ ∈ T) :
    ¬ IsTorusTube M D T (orbitTube M T) := by
  rintro ⟨𝒮, h𝒮, htube⟩
  have hδ := M.hδ
  have hL := M.hL0
  have hδL := M.hδL
  have h0chart : (0 : ℝ) ∈ M.chart := ⟨by linarith, by linarith⟩
  -- the base point (0, t₀, 0) is in the tube: branch k = 0
  have hp0 : (⟨⟨0, h0chart⟩, ⟨t₀, ht₀⟩, (0 : ℝ)⟩ : MeshPt M T ℝ)
      ∈ orbitTube M T := ⟨0, by push_cast; ring⟩
  rw [htube] at hp0
  simp only [mem_iUnion, exists_prop, graphA, mem_setOf_eq] at hp0
  obtain ⟨u, hu𝒮, hu0⟩ := hp0
  have hu0' : u 0 t₀ = 0 := hu0
  have huT := h𝒮 u hu𝒮
  -- u threads the tube over the whole chart at time t₀
  have hthread : ∀ x ∈ M.chart, ∃ k : ℤ, u x t₀ = x - k * M.L := by
    intro x hx
    have hmem : (⟨⟨x, hx⟩, ⟨t₀, ht₀⟩, u x t₀⟩ : MeshPt M T ℝ)
        ∈ orbitTube M T := by
      rw [htube]
      simp only [mem_iUnion, exists_prop, graphA, mem_setOf_eq]
      exact ⟨u, hu𝒮, rfl⟩
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, hk⟩
  -- rigidity: u follows a single branch on the chart
  have hcont : ContinuousOn (fun x => u x t₀) M.chart :=
    contOn_slice fun x _ => (huT.sol x (mem_univ x) t₀ ht₀).cont
  have hpreS : IsPreconnected M.chart :=
    show IsPreconnected (Ioo (-M.δ) (M.L + M.δ)) from isPreconnected_Ioo
  obtain ⟨k, hk⟩ := thread_const hL hpreS hcont hthread h0chart
  -- periodicity kills the branch
  have hx1 : M.δ / 2 ∈ M.chart := ⟨by linarith, by linarith⟩
  have hx2 : M.δ / 2 + M.L ∈ M.chart := ⟨by linarith, by linarith⟩
  have hper := huT.periodic t₀ (M.δ / 2)
  have hper' : u (M.δ / 2 + M.L) t₀ = u (M.δ / 2) t₀ := hper
  rw [hk _ hx2, hk _ hx1] at hper'
  -- δ/2 + L − kL = δ/2 − kL  ⟹  L = 0
  have hL0 : M.L = 0 := by linarith
  exact hL.ne' hL0

/-- **The set-stratum holonomy, packaged**: an equalizer point of the
mesh cover whose components are all cell tubes, whose walls all hold —
compatibility by construction and the wrap wall on top — whose glue is
even a chart tube, and whose glue is *not* a torus tube.  Point-gluing
closed two-sided under exactly these walls (`heat_mesh_glues`);
set-gluing does not: the branch pairing is the missing datum, and no
pointwise wall carries it. -/
theorem setStratum_holonomy (D : ℝ) {t₀ : ℝ} (ht₀ : t₀ ∈ T) :
    ∃ p : FellCloseds.Equalizer (arcRegion M T ℝ),
      (∀ i, IsCellTube M D T i (p.1 i : Set ↥(arcRegion M T ℝ i))) ∧
      TubeWrapWall M T (p.1 0 : Set ↥(arcRegion M T ℝ 0))
        (p.1 2 : Set ↥(arcRegion M T ℝ 2)) ∧
      IsChartTube M D T (meshGlue M T p : Set (MeshPt M T ℝ)) ∧
      ¬ IsTorusTube M D T (meshGlue M T p : Set (MeshPt M T ℝ)) := by
  refine ⟨orbitEq M T, fun i => isCellTube_orbit D i, orbitEq_wrapWall,
    ?_, ?_⟩
  · rw [show meshGlue M T (orbitEq M T) = orbitF M T from
      meshGlue_toEqualizer M T (orbitF M T)]
    exact orbitTube_is_chartTube D
  · rw [show meshGlue M T (orbitEq M T) = orbitF M T from
      meshGlue_toEqualizer M T (orbitF M T)]
    exact orbitTube_not_torusTube D ht₀

/-! ### Local character refuted -/

/-- The torus-tube locus in the window's hyperspace. -/
def torusTubeLocus (M : RingMesh) (D : ℝ) (T : Set ℝ) :
    Set (FellCloseds (MeshPt M T ℝ)) :=
  {G | IsTorusTube M D T (G : Set (MeshPt M T ℝ))}

/-- The cell-tube loci at the arc cylinders. -/
def cellTubeLocus (M : RingMesh) (D : ℝ) (T : Set ℝ) (i : Fin 3) :
    Set (FellCloseds ↥(arcRegion M T ℝ i)) :=
  {F | IsCellTube M D T i (F : Set ↥(arcRegion M T ℝ i))}

/-- **Torus-tube-hood is not of local character over the ring cover**:
the orbit tube's every clip is a cell-tube citizen, and the ambient
set is no torus tube.  Where `HeatAt.congr` gave the record tier local
character — the engine of `heat_mesh_glues` — the record-*set* tier
loses it on the cyclic mesh: the rung-D subsheaf story
(`IsLocalLocus`, `FellRecordLocus`) has no equalizer-form analogue for
periodic-solution tubes. -/
theorem not_isLocalLocusEq_torusTube (D : ℝ) {t₀ : ℝ} (ht₀ : t₀ ∈ T) :
    ¬ FellCloseds.IsLocalLocusEq (arcRegion M T ℝ)
        (torusTubeLocus M D T) (cellTubeLocus M D T) := by
  intro h
  have hclips : ∀ i, FellCloseds.clip (arcRegion M T ℝ i) (orbitF M T)
      ∈ cellTubeLocus M D T i := fun i => isCellTube_orbit D i
  have hmem := (h (orbitF M T)).mpr hclips
  exact orbitTube_not_torusTube D ht₀ hmem

end OrbitWitness

/-! ## The compiled face: atoms over the equalizer carrier

The record space of the set stratum is the equalizer itself — the
chain walls have migrated *into the carrier* (its compatibility
field), so the compiled list holds only the cell-citizenship atoms and
the wrap atom.  A tube family enters the judgment as a *point* of this
carrier: imprecision at tier `n` is precision at tier `n + 1`, which
is how the singleton-entry constraint elsewhere in the development
and this module's non-singleton content coexist. -/

section CompiledFace

variable (M) (D) (T)

/-- The cell-citizenship atom at level `i`. -/
def cellAtomC (i : Fin 3) :
    Set (FellCloseds.Equalizer (arcRegion M T E)) :=
  {p | IsCellTube M D T i (p.1 i : Set ↥(arcRegion M T E i))}

/-- The wrap atom. -/
def wrapAtomC : Set (FellCloseds.Equalizer (arcRegion M T E)) :=
  {p | TubeWrapWall M T (p.1 0 : Set ↥(arcRegion M T E 0))
        (p.1 2 : Set ↥(arcRegion M T E 2))}

/-- The compiled atoms of the solution-set mesh. -/
def tubeAtoms :
    List (SubPMF (FellCloseds.Equalizer (arcRegion M T E)) → Prop) :=
  [suppC (cellAtomC M D T 0), suppC (cellAtomC M D T 1),
    suppC (cellAtomC M D T 2), suppC (wrapAtomC M T)]

/-- The classical object at the set stratum: equalizer points gluing
to torus tubes. -/
def torusTubeEqs : Set (FellCloseds.Equalizer (arcRegion M T E)) :=
  {p | IsTorusTube M D T (meshGlue M T p : Set (MeshPt M T E))}

variable {M} {D} {T}

/-- The forward entailment: the classical object satisfies every
compiled atom — citizenship clips, and the walls hold on torus
tubes. -/
theorem tubeAtoms_of_classical :
    ∀ μ : SubPMF (FellCloseds.Equalizer (arcRegion M T E)),
      suppC (torusTubeEqs M D T) μ → looseConj (tubeAtoms M D T) μ := by
  intro μ hμ
  have hcomp : ∀ p : FellCloseds.Equalizer (arcRegion M T E),
      ∀ i : Fin 3,
      p.1 i = FellCloseds.clip (arcRegion M T E i) (meshGlue M T p) :=
    fun p i =>
      (congrArg
        (fun q : FellCloseds.Equalizer (arcRegion M T E) => q.1 i)
        (toEqualizer_meshGlue M T p)).symm
  simp only [tubeAtoms, looseConj]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · intro p hp
    have hto : IsTorusTube M D T
        (meshGlue M T p : Set (MeshPt M T E)) := hμ p hp
    show IsCellTube M D T 0 (p.1 0 : Set ↥(arcRegion M T E 0))
    rw [hcomp p 0]
    exact isCellTube_clip hto 0
  · intro p hp
    have hto : IsTorusTube M D T
        (meshGlue M T p : Set (MeshPt M T E)) := hμ p hp
    show IsCellTube M D T 1 (p.1 1 : Set ↥(arcRegion M T E 1))
    rw [hcomp p 1]
    exact isCellTube_clip hto 1
  · intro p hp
    have hto : IsTorusTube M D T
        (meshGlue M T p : Set (MeshPt M T E)) := hμ p hp
    show IsCellTube M D T 2 (p.1 2 : Set ↥(arcRegion M T E 2))
    rw [hcomp p 2]
    exact isCellTube_clip hto 2
  · intro p hp
    have hto : IsTorusTube M D T
        (meshGlue M T p : Set (MeshPt M T E)) := hμ p hp
    show TubeWrapWall M T (p.1 0 : Set ↥(arcRegion M T E 0))
      (p.1 2 : Set ↥(arcRegion M T E 2))
    rw [hcomp p 0, hcomp p 2]
    exact tubeWrapWall_of_torusTube hto

/-- The forward cell of the set-stratum square, in `Crd`: classical
entails compiled.  One-sided — see `tubeAtoms_not_classical` for the
refutation of the converse; the invertible packaging every previous
square used (`Crd.looseIso_ofIff`) is unavailable here, and that
unavailability is the theorem. -/
theorem solset_forward_cell
    {a : Crd (FellCloseds.Equalizer (arcRegion M T E))} :
    ∃ _ : Cell (suppC (torusTubeEqs M D T) : Loose a a)
        (looseConj (tubeAtoms M D T)) (𝟙 a) (𝟙 a), True :=
  ⟨Crd.cellOfEntails tubeAtoms_of_classical, trivial⟩

/-- Consistency of the compiled atoms: the Dirac at the top tube's
equalizer point — free con via maximal imprecision. -/
theorem tubeAtoms_consistent :
    ∃ μ : SubPMF (FellCloseds.Equalizer (arcRegion M T E)),
      looseConj (tubeAtoms M D T) μ ∧
      μ ≠ SubPMF.zero (FellCloseds.Equalizer (arcRegion M T E)) := by
  have huniv : IsTorusTube M D T
      ((⟨univ, isClosed_univ⟩ : FellCloseds (MeshPt M T E)) :
        Set (MeshPt M T E)) :=
    isTorusTube_univ
  refine ⟨SubPMF.dirac (FellCloseds.toEqualizer (arcRegion M T E)
    (⟨univ, isClosed_univ⟩ : FellCloseds (MeshPt M T E))), ?_,
    SubPMF.dirac_ne_zero _⟩
  simp only [tubeAtoms, looseConj]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> refine (suppC_dirac _ _).mpr ?_
  · exact isCellTube_clip huniv 0
  · exact isCellTube_clip huniv 1
  · exact isCellTube_clip huniv 2
  · exact tubeWrapWall_of_torusTube huniv

/-- The top tube also satisfies the classical side: the positive face
of the square is inhabited two-sidedly at maximal imprecision. -/
theorem topTube_classical :
    FellCloseds.toEqualizer (arcRegion M T E)
        (⟨univ, isClosed_univ⟩ : FellCloseds (MeshPt M T E))
      ∈ torusTubeEqs M D T := by
  show IsTorusTube M D T _
  rw [show meshGlue M T (FellCloseds.toEqualizer (arcRegion M T E)
      (⟨univ, isClosed_univ⟩ : FellCloseds (MeshPt M T E)))
    = (⟨univ, isClosed_univ⟩ : FellCloseds (MeshPt M T E)) from
    meshGlue_toEqualizer M T _]
  exact isTorusTube_univ

/-- **The square does not close**: the compiled atoms do not pin the
classical object — the Dirac at the orbit point satisfies every atom
and is not classical.  Against `heat_adequacy`'s invertible cell one
stratum down, the set stratum is one-sided; the heat memo's
stratum-indexed sidedness gains its record-set row, with a new
obstruction type: branch holonomy. -/
theorem tubeAtoms_not_classical {t₀ : ℝ} (ht₀ : t₀ ∈ T) (D : ℝ) :
    ¬ ∀ μ : SubPMF (FellCloseds.Equalizer (arcRegion M T ℝ)),
        looseConj (tubeAtoms M D T) μ ↔ suppC (torusTubeEqs M D T) μ := by
  intro h
  have hatoms : looseConj (tubeAtoms M D T)
      (SubPMF.dirac (orbitEq M T)) := by
    simp only [tubeAtoms, looseConj]
    refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> refine (suppC_dirac _ _).mpr ?_
    · exact isCellTube_orbit D 0
    · exact isCellTube_orbit D 1
    · exact isCellTube_orbit D 2
    · exact orbitEq_wrapWall
  have hclass := (h _).mp hatoms
  have hmem : orbitEq M T ∈ torusTubeEqs M D T :=
    (suppC_dirac _ _).mp hclass
  have hbad : IsTorusTube M D T
      (meshGlue M T (orbitEq M T) : Set (MeshPt M T ℝ)) := hmem
  rw [show meshGlue M T (orbitEq M T) = orbitF M T from
    meshGlue_toEqualizer M T (orbitF M T)] at hbad
  exact orbitTube_not_torusTube D ht₀ hbad

end CompiledFace

/-! ## The record-tier shadow: the suppC-of-set-family compositor

A tube family compiles down to the record tier as *enclosure atoms* —
per-cell constraints requiring the record's field to thread the cell
tube.  On the orbit tube these are jointly ⊥-forcing with the six heat
atoms: the ℤ-cocycle around the ring is frustrated.  The set-stratum
failure is thereby *detectable* at the record tier — but only as con
failure of the composed object (a global satisfiability fact), never
as any single wall's refusal: the heat leg's deepest sentence, one
stratum up. -/

section RecordShadow

variable (M) (T)

/-- The plain orbit set (the record-tier face of `orbitTube`). -/
def orbitSet (M : RingMesh) : Set (ℝ × ℝ × ℝ) :=
  {q | ∃ k : ℤ, q.2.2 = q.1 - k * M.L}

/-- Enclosure atom, first cell: the record's field threads `F` on the
first arc.  (`suppC (enclose1C …)` is the suppC-of-set-family
compositor's cell-1 component.) -/
def enclose1C (F : Set (ℝ × ℝ × ℝ)) : Set (HeatRec ℝ) :=
  {p | ∀ x ∈ M.I1, ∀ t ∈ T, (x, t, p.c1 x t) ∈ F}

/-- Enclosure atom, middle cell. -/
def enclose2C (F : Set (ℝ × ℝ × ℝ)) : Set (HeatRec ℝ) :=
  {p | ∀ x ∈ M.I2, ∀ t ∈ T, (x, t, p.c2 x t) ∈ F}

/-- Enclosure atom, closing cell. -/
def enclose3C (F : Set (ℝ × ℝ × ℝ)) : Set (HeatRec ℝ) :=
  {p | ∀ x ∈ M.I3, ∀ t ∈ T, (x, t, p.c3 x t) ∈ F}

variable {M} {T}

/-- **The ℤ-cocycle frustration**: no mesh solution threads the orbit
tube.  Threading rigidifies each cell field onto a single branch
`x − kᵢ·L`; the chain seams force `k₁ = k₂ = k₃`; the wrap wall forces
`k₃ = k₁ + 1`. -/
theorem meshSols_inter_orbitEnclosure (D : ℝ) {t₀ : ℝ} (ht₀ : t₀ ∈ T) :
    ∀ p : HeatRec ℝ, p ∈ meshSols M D T →
      p ∈ enclose1C M T (orbitSet M) → p ∈ enclose2C M T (orbitSet M) →
      p ∈ enclose3C M T (orbitSet M) → False := by
  intro p hp he1 he2 he3
  have hp' : IsMeshSol M D T p := hp
  have hδ := M.hδ
  have hL := M.hL0
  have ha := M.ha
  have hab := M.hab
  have hbL := M.hbL
  -- per-cell rigidity
  have hpre1 : IsPreconnected M.I1 :=
    show IsPreconnected (Ioo (-M.δ) (M.a + M.δ)) from isPreconnected_Ioo
  have hpre2 : IsPreconnected M.I2 :=
    show IsPreconnected (Ioo (M.a - M.δ) (M.b + M.δ)) from
      isPreconnected_Ioo
  have hpre3 : IsPreconnected M.I3 :=
    show IsPreconnected (Ioo (M.b - M.δ) (M.L + M.δ)) from
      isPreconnected_Ioo
  have haI1 : M.a ∈ M.I1 := ⟨by linarith, by linarith⟩
  have haI2 : M.a ∈ M.I2 := ⟨by linarith, by linarith⟩
  have hbI2 : M.b ∈ M.I2 := ⟨by linarith, by linarith⟩
  have hbI3 : M.b ∈ M.I3 := ⟨by linarith, by linarith⟩
  have hLI3 : M.L ∈ M.I3 := ⟨by linarith, by linarith⟩
  have h0I1 : (0 : ℝ) ∈ M.I1 := ⟨by linarith, by linarith⟩
  obtain ⟨k₁, hk₁⟩ := thread_const hL hpre1
    (contOn_slice fun x hx => (hp'.cell1 x hx t₀ ht₀).cont)
    (fun x hx => he1 x hx t₀ ht₀) haI1
  obtain ⟨k₂, hk₂⟩ := thread_const hL hpre2
    (contOn_slice fun x hx => (hp'.cell2 x hx t₀ ht₀).cont)
    (fun x hx => he2 x hx t₀ ht₀) haI2
  obtain ⟨k₃, hk₃⟩ := thread_const hL hpre3
    (contOn_slice fun x hx => (hp'.cell3 x hx t₀ ht₀).cont)
    (fun x hx => he3 x hx t₀ ht₀) hbI3
  -- seams identify the branches
  have hs12 := hp'.seam12 M.a ⟨haI1, haI2⟩ t₀ ht₀
  rw [hk₁ M.a haI1, hk₂ M.a haI2] at hs12
  have hk12 : k₁ = k₂ := by
    have h1 : (k₁ : ℝ) * M.L = (k₂ : ℝ) * M.L := by linarith
    exact_mod_cast mul_right_cancel₀ hL.ne' h1
  have hs23 := hp'.seam23 M.b ⟨hbI2, hbI3⟩ t₀ ht₀
  rw [hk₂ M.b hbI2, hk₃ M.b hbI3] at hs23
  have hk23 : k₂ = k₃ := by
    have h1 : (k₂ : ℝ) * M.L = (k₃ : ℝ) * M.L := by linarith
    exact_mod_cast mul_right_cancel₀ hL.ne' h1
  -- the wrap wall shifts the branch
  have h0I1' : M.L - M.L ∈ M.I1 := by rw [sub_self]; exact h0I1
  have hw := hp'.wrap M.L hLI3 h0I1' t₀ ht₀
  rw [hk₃ M.L hLI3] at hw
  have hc1 : p.c1 (M.L - M.L) t₀ = M.L - M.L - k₁ * M.L := hk₁ _ h0I1'
  rw [hc1] at hw
  -- L − k₃L = (L − L) − k₁L  ⟹  k₃ = k₁ + 1
  have h3 : (k₃ : ℝ) * M.L = (k₁ : ℝ) * M.L + M.L := by linarith
  have h4 : (k₃ : ℝ) = (k₁ : ℝ) + 1 :=
    mul_right_cancel₀ hL.ne'
      (show (k₃ : ℝ) * M.L = ((k₁ : ℝ) + 1) * M.L by
        rw [add_mul, one_mul]; linarith)
  have h5 : k₃ = k₁ + 1 := by exact_mod_cast h4
  omega

/-- **The record-tier shadow is ⊥-forcing**: the six heat atoms plus
the orbit tube's enclosure atoms admit only the zero model.  Honest
imprecision at the composed object — the lawful denotation of the
frustrated composite is the bottom-supported class, carried, never
crashed (the Vorob'ev absorption pattern, deterministic flavor). -/
theorem orbit_enclosure_forces_zero (D : ℝ) {t₀ : ℝ} (ht₀ : t₀ ∈ T) :
    ∀ μ : SubPMF (HeatRec ℝ),
      looseConj (heatAtoms M D T (E := ℝ)
          ++ [suppC (enclose1C M T (orbitSet M)),
              suppC (enclose2C M T (orbitSet M)),
              suppC (enclose3C M T (orbitSet M))]) μ →
      μ = SubPMF.zero (HeatRec ℝ) := by
  intro μ hμ
  rw [looseConj_iff] at hμ
  have hmesh : suppC (meshSols M D T) μ := by
    rw [← heatAtoms_iff]
    rw [looseConj_iff]
    intro c hc
    exact hμ c (List.mem_append_left _ hc)
  have he1 : suppC (enclose1C M T (orbitSet M)) μ :=
    hμ _ (List.mem_append_right _ (by simp))
  have he2 : suppC (enclose2C M T (orbitSet M)) μ :=
    hμ _ (List.mem_append_right _ (by simp))
  have he3 : suppC (enclose3C M T (orbitSet M)) μ :=
    hμ _ (List.mem_append_right _ (by simp))
  rw [SubPMF.eq_zero_iff_wt]
  ext v
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  by_contra hv
  exact meshSols_inter_orbitEnclosure D ht₀ v (hmesh v hv)
    (he1 v hv) (he2 v hv) (he3 v hv)

end RecordShadow

end Adequacy

end SuFunctor

#print axioms SuFunctor.Universe.FellCloseds.IsLocalLocusEq.glue_mem
#print axioms SuFunctor.Adequacy.meshDescent
#print axioms SuFunctor.Adequacy.isCellTube_clip
#print axioms SuFunctor.Adequacy.tubeWrapWall_of_torusTube
#print axioms SuFunctor.Adequacy.isTorusTube_univ
#print axioms SuFunctor.Adequacy.labelled_ensembles_glue
#print axioms SuFunctor.Adequacy.isClosed_orbitTube
#print axioms SuFunctor.Adequacy.isCellTube_orbit
#print axioms SuFunctor.Adequacy.orbitEq_wrapWall
#print axioms SuFunctor.Adequacy.not_tubeWrap_singleLin
#print axioms SuFunctor.Adequacy.orbitTube_is_chartTube
#print axioms SuFunctor.Adequacy.thread_const
#print axioms SuFunctor.Adequacy.orbitTube_not_torusTube
#print axioms SuFunctor.Adequacy.setStratum_holonomy
#print axioms SuFunctor.Adequacy.not_isLocalLocusEq_torusTube
#print axioms SuFunctor.Adequacy.tubeAtoms_of_classical
#print axioms SuFunctor.Adequacy.solset_forward_cell
#print axioms SuFunctor.Adequacy.tubeAtoms_consistent
#print axioms SuFunctor.Adequacy.topTube_classical
#print axioms SuFunctor.Adequacy.tubeAtoms_not_classical
#print axioms SuFunctor.Adequacy.meshSols_inter_orbitEnclosure
#print axioms SuFunctor.Adequacy.orbit_enclosure_forces_zero
