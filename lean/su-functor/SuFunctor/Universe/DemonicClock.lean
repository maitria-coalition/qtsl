import SuFunctor.Universe.LocallyClosedLayer

/-! # Demonic transport and the seam conjunct

Two theorem groups for composing systems across relational (demonic)
time morphisms — jittered samplers whose transport relates each record
to *many* admissible retimings rather than one.

**Group 1: the Egli–Milner lift is functorial on the nose.**  At the
record tier a demonic transport is a genuine relation, not a function
(`exists_no_functional_transport`), so no record-level transport
functor can exist without choosing realizations.  One storey up the
choice dissolves: lifting a relation to *bodies* — closed classes of
records — by the generalized Egli–Milner condition (`emLift`, after
Abbadini–Bezhanishvili–Carai, arXiv:2308.16823) preserves identities
(`emLift_id`) and compositions (`emLift_comp`) exactly, with the
composition middle constructed, never chosen
(`B := relImage r A ∩ relPre s C`).  The demonic image of a body is
itself an admissible transport of that body (`emLift_relImage`) and
composes exactly (`relImage_comp`): bodies to bodies, all realizations
at once.  What genuinely fails is *meets*: the lift of an intersection
of relations is strictly below the intersection of the lifts
(`exists_emLift_inf_not`, the allegory counterexample of
arXiv:2308.16823 in one-bit form) — so distinct realization
constraints must be intersected *before* lifting, never after.

**Group 2: the seam conjunct rides the blocking criterion.**  The
union-refinement criterion (`coupled_union_refinement_iff`) is pure
order theory over an arbitrary carrier, and its canonical adversaries
are finite joins of the atoms' own data.  A seam wall — the indicator
penalty pinning a joint record space to a transport relation's
admissible set — therefore enters entailment as one more conjunct on
the premise floor, and the criterion applies verbatim on the joint
carrier: `selSup_sup_left` relocates the wall through the adversary
construction, `coupledSat_sup_wall_iff` is the conjunct reading of the
joined floor, and `cross_site_union_refinement_iff` is the criterion
with the wall installed.  The lower-semicontinuous class supplies the
adversaries (`lowerSemicontinuous_selSup`), so the packaged forms
(`cross_site_union_refinement_iff_lsc`, `…_probWall`) discharge the
class hypothesis outright; at the class level the wall conjunct is
exact (`crescentClass_inter_wall`, from
`crescentClass_inter_crescentClass`).
-/

namespace SuFunctor.Universe

open scoped ENNReal

/-! ## Relational transport: images, preimages, composition

Self-contained relation vocabulary on `X → Y → Prop`, kept local so
the lift's algebra depends on nothing movable.  `relImage r A` is the
demonic transport of the body `A`: every point reachable from `A`
through any admissible pair — all realizations at once. -/

section RelKernel

variable {X Y Z : Type*}

/-- The relational image of a body: everything reachable from `A`
through `r`. -/
def relImage (r : X → Y → Prop) (A : Set X) : Set Y :=
  {y | ∃ x ∈ A, r x y}

/-- The relational preimage of a body: everything that reaches `B`
through `r`. -/
def relPre (r : X → Y → Prop) (B : Set Y) : Set X :=
  {x | ∃ y ∈ B, r x y}

/-- Diagrammatic composition: `r` then `s`. -/
def relComp (r : X → Y → Prop) (s : Y → Z → Prop) : X → Z → Prop :=
  fun x z => ∃ y, r x y ∧ s y z

@[simp] theorem relImage_id (A : Set X) : relImage (· = ·) A = A := by
  ext y
  exact ⟨fun ⟨x, hx, hxy⟩ => hxy ▸ hx, fun hy => ⟨y, hy, rfl⟩⟩

@[simp] theorem relPre_id (B : Set X) : relPre (· = ·) B = B := by
  ext x
  exact ⟨fun ⟨y, hy, hxy⟩ => hxy ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

/-- Demonic images compose exactly: the transport of a body along a
composite relation is the transport of the transport.  Pure logic — no
choice of realization anywhere. -/
theorem relImage_comp (r : X → Y → Prop) (s : Y → Z → Prop) (A : Set X) :
    relImage (relComp r s) A = relImage s (relImage r A) := by
  ext z
  constructor
  · rintro ⟨x, hx, y, hr, hs⟩
    exact ⟨y, ⟨x, hx, hr⟩, hs⟩
  · rintro ⟨y, ⟨x, hx, hr⟩, hs⟩
    exact ⟨x, hx, y, hr, hs⟩

theorem relPre_comp (r : X → Y → Prop) (s : Y → Z → Prop) (C : Set Z) :
    relPre (relComp r s) C = relPre r (relPre s C) := by
  ext x
  constructor
  · rintro ⟨z, hz, y, hr, hs⟩
    exact ⟨y, ⟨z, hz, hs⟩, hr⟩
  · rintro ⟨y, ⟨z, hz, hs⟩, hr⟩
    exact ⟨z, hz, y, hr, hs⟩

/-- Monotonicity of the image in the relation. -/
theorem relImage_mono {r r' : X → Y → Prop} (h : ∀ x y, r x y → r' x y)
    {A : Set X} : relImage r A ⊆ relImage r' A := by
  rintro y ⟨x, hx, hr⟩
  exact ⟨x, hx, h x y hr⟩

/-- Monotonicity of the preimage in the relation. -/
theorem relPre_mono {r r' : X → Y → Prop} (h : ∀ x y, r x y → r' x y)
    {B : Set Y} : relPre r B ⊆ relPre r' B := by
  rintro x ⟨y, hy, hr⟩
  exact ⟨y, hy, h x y hr⟩

end RelKernel

/-! ## The Egli–Milner lift: an honest functor on bodies -/

section EgliMilner

variable {X Y Z : Type*}

/-- The Egli–Milner lift of a relation to bodies
(arXiv:2308.16823): `A` and `B` are related iff `B` lies inside the
transports of `A` and every point of `A` transports into `B`.  Both
conjuncts are load-bearing: dropping either turns the identity law
false (the one-sided lifts are semi-functors only). -/
def emLift (r : X → Y → Prop) (A : Set X) (B : Set Y) : Prop :=
  B ⊆ relImage r A ∧ A ⊆ relPre r B

/-- The lift preserves identities. -/
theorem emLift_id {A B : Set X} : emLift (· = ·) A B ↔ A = B := by
  simp only [emLift, relImage_id, relPre_id]
  exact ⟨fun ⟨h1, h2⟩ => Set.Subset.antisymm h2 h1,
    fun h => h ▸ ⟨Set.Subset.rfl, Set.Subset.rfl⟩⟩

/-- **The lift preserves composition on the nose.**  Forward, the
middle body is *constructed* — `relImage r A ∩ relPre s C`, all
admissible middles at once — never chosen; backward is the transitive
chase.  This is the set-level core of the endofunctor theorem of
arXiv:2308.16823, and the sense in which demonic transport is an
honest functor one storey above the record tier. -/
theorem emLift_comp (r : X → Y → Prop) (s : Y → Z → Prop)
    (A : Set X) (C : Set Z) :
    emLift (relComp r s) A C ↔ ∃ B, emLift r A B ∧ emLift s B C := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨relImage r A ∩ relPre s C, ⟨Set.inter_subset_left, ?_⟩,
      ?_, Set.inter_subset_right⟩
    · -- A ⊆ relPre r (middle): route each point through its composite witness
      intro x hx
      obtain ⟨z, hz, y, hr, hs⟩ := h2 hx
      exact ⟨y, ⟨⟨x, hx, hr⟩, ⟨z, hz, hs⟩⟩, hr⟩
    · -- C ⊆ relImage s (middle): same witness, read from the far end
      intro z hz
      obtain ⟨x, hx, y, hr, hs⟩ := h1 hz
      exact ⟨y, ⟨⟨x, hx, hr⟩, ⟨z, hz, hs⟩⟩, hs⟩
  · rintro ⟨B, ⟨hBim, hBpre⟩, hCim, hCpre⟩
    constructor
    · -- C ⊆ relImage (relComp r s) A
      intro z hz
      obtain ⟨y, hyB, hs⟩ := hCim hz
      obtain ⟨x, hx, hr⟩ := hBim hyB
      exact ⟨x, hx, y, hr, hs⟩
    · -- A ⊆ relPre (relComp r s) C
      intro x hx
      obtain ⟨y, hyB, hr⟩ := hBpre hx
      obtain ⟨z, hz, hs⟩ := hCpre hyB
      exact ⟨z, hz, y, hr, hs⟩

/-- The demonic image of a body is an admissible Egli–Milner transport
of it, provided every point of the body transports at all (the
regularity clause of admissible realization classes).  The functor
form of demonic transport — bodies to bodies — thus exists wherever
the record-tier function cannot. -/
theorem emLift_relImage {r : X → Y → Prop} {A : Set X}
    (h : ∀ x ∈ A, ∃ y, r x y) : emLift r A (relImage r A) := by
  refine ⟨Set.Subset.rfl, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := h x hx
  exact ⟨y, ⟨x, hx, hy⟩, hy⟩

/-- **The record-tier kernel of the no-go**: a relational transport
with two admissible targets for one record is the graph of no
function.  Choosing a realization is the only way down to functions,
and any choice is a choice — the lift above never makes one. -/
theorem exists_no_functional_transport :
    ∃ r : Bool → Bool → Prop, ¬ ∃ f : Bool → Bool, ∀ x y, r x y ↔ f x = y := by
  refine ⟨fun _ _ => True, ?_⟩
  rintro ⟨f, hf⟩
  have h1 : f true = true := (hf true true).mp trivial
  have h2 : f true = false := (hf true false).mp trivial
  exact Bool.noConfusion (h1.symm.trans h2)

/-- The lift respects intersections laxly: the easy inclusion. -/
theorem emLift_inf {r r' : X → Y → Prop} {A : Set X} {B : Set Y}
    (h : emLift (fun x y => r x y ∧ r' x y) A B) :
    emLift r A B ∧ emLift r' A B :=
  ⟨⟨h.1.trans (relImage_mono fun _ _ hxy => hxy.1),
      h.2.trans (relPre_mono fun _ _ hxy => hxy.1)⟩,
    ⟨h.1.trans (relImage_mono fun _ _ hxy => hxy.2),
      h.2.trans (relPre_mono fun _ _ hxy => hxy.2)⟩⟩

/-- **Meets are where the lift is genuinely lax** (the allegory
counterexample of arXiv:2308.16823, one-bit form): equality and
inequality on `Bool` each lift to relate `univ` to `univ`, but their
intersection is empty and lifts to relate nothing nonempty.
Consequence for seam design: realization constraints that share a
clock instance must be intersected *before* lifting — lifting per
constraint and intersecting the lifts over-approximates. -/
theorem exists_emLift_inf_not :
    ∃ (r r' : Bool → Bool → Prop) (A : Set Bool) (B : Set Bool),
      emLift r A B ∧ emLift r' A B
        ∧ ¬ emLift (fun x y => r x y ∧ r' x y) A B := by
  refine ⟨(· = ·), (· ≠ ·), Set.univ, Set.univ, emLift_id.mpr rfl,
    ⟨fun y _ => ⟨!y, Set.mem_univ _, by cases y <;> decide⟩,
      fun x _ => ⟨!x, Set.mem_univ _, by cases x <;> decide⟩⟩, ?_⟩
  rintro ⟨h1, -⟩
  obtain ⟨x, -, hxy, hne⟩ := h1 (Set.mem_univ true)
  exact hne hxy

end EgliMilner

/-! ## The seam conjunct rides the blocking criterion

The blocking criterion (`coupled_union_refinement_iff`) never inspects
its carrier: it is order theory over any `K`, with adversaries built
as finite joins of the premise floor and selected demands.  Composing
across a relational seam adds exactly one datum — the seam wall, an
indicator penalty pinning the joint record space to the transport
relation's admissible set — and a wall enters an atom as a conjunct on
the safety floor.  The lemmas below relocate the wall through every
piece of the criterion, so entailment across the seam is decided by
the same finite selection table with the wall joined in. -/

section SeamConjunct

variable {K : Type*} {m : ℕ}

/-- The canonical adversaries of a wall-conjoined premise are the
wall-joins of the original adversaries. -/
theorem selSup_sup_left (u w : K → ℝ≥0∞) (c : Fin m → Option (K → ℝ≥0∞)) :
    selSup (u ⊔ w) c = selSup u c ⊔ w := by
  simp only [selSup]
  exact sup_right_comm u w _

/-- Joining a wall into the premise floor is exactly one more
conjunct: satisfaction of the joined atom is satisfaction of the
original atom plus domination of the wall. -/
theorem coupledSat_sup_wall_iff {σ u w : K → ℝ≥0∞} {𝒱 : Set (K → ℝ≥0∞)} :
    CoupledSat σ (u ⊔ w) 𝒱 ↔ w ≤ σ ∧ CoupledSat σ u 𝒱 := by
  constructor
  · rintro ⟨hsafe, hlive⟩
    exact ⟨sup_le_iff.mp hsafe |>.2, sup_le_iff.mp hsafe |>.1, hlive⟩
  · rintro ⟨hw, hu, hlive⟩
    exact ⟨sup_le hu hw, hlive⟩

/-- **The seam-crossing entailment criterion**: union-refinement from
a wall-conjoined premise atom is decided by the blocking table of the
joined atom — the same finite selections, the same pointwise
domination rows, over any carrier.  The only hypothesis the wall adds
is that the adversary class absorb wall-joins. -/
theorem cross_site_union_refinement_iff {P : (K → ℝ≥0∞) → Prop}
    {u w : K → ℝ≥0∞} {𝒱 : Set (K → ℝ≥0∞)} {u' : Fin m → K → ℝ≥0∞}
    {𝒱' : Fin m → Set (K → ℝ≥0∞)}
    (hPc : ∀ c, SelValid 𝒱' c → P (selSup u c ⊔ w)) :
    (∀ σ, P σ → CoupledSat σ (u ⊔ w) 𝒱 → ∃ j, CoupledSat σ (u' j) (𝒱' j))
      ↔ ∀ c, SelValid 𝒱' c → Blocked (u ⊔ w) 𝒱 u' c :=
  coupled_union_refinement_iff fun c hc => by
    rw [selSup_sup_left]
    exact hPc c hc

/-! ### The lower-semicontinuous class supplies the adversaries -/

variable [TopologicalSpace K]

/-- Canonical adversaries are lower semicontinuous whenever the
premise floor and the selected demands are: the adversary class the
blocking criterion needs is closed under its own construction. -/
theorem lowerSemicontinuous_selSup {u : K → ℝ≥0∞}
    {c : Fin m → Option (K → ℝ≥0∞)} (hu : LowerSemicontinuous u)
    (hc : ∀ j w, c j = some w → LowerSemicontinuous w) :
    LowerSemicontinuous (selSup u c) := by
  have hsup : LowerSemicontinuous (⨆ j, (c j).getD 0) := by
    have heq : (⨆ j, (c j).getD 0) = fun x => ⨆ j, ((c j).getD 0) x :=
      funext fun _ => iSup_apply
    rw [heq]
    refine lowerSemicontinuous_iSup fun j => ?_
    rcases hj : c j with _ | w
    · simp only [Option.getD_none]
      exact lowerSemicontinuous_const
    · simp only [Option.getD_some]
      exact hc j w hj
  show LowerSemicontinuous (u ⊔ ⨆ j, (c j).getD 0)
  exact hu.sup hsup

/-- The seam-crossing criterion, packaged over the
lower-semicontinuous class: with floor, wall, and all conclusion
demands lower semicontinuous, the adversary hypothesis discharges and
entailment across the seam is the blocking table, verbatim. -/
theorem cross_site_union_refinement_iff_lsc {u w : K → ℝ≥0∞}
    {𝒱 : Set (K → ℝ≥0∞)} {u' : Fin m → K → ℝ≥0∞}
    {𝒱' : Fin m → Set (K → ℝ≥0∞)}
    (hu : LowerSemicontinuous u) (hw : LowerSemicontinuous w)
    (h𝒱' : ∀ j, ∀ v ∈ 𝒱' j, LowerSemicontinuous v) :
    (∀ σ, LowerSemicontinuous σ → CoupledSat σ (u ⊔ w) 𝒱 →
        ∃ j, CoupledSat σ (u' j) (𝒱' j))
      ↔ ∀ c, SelValid 𝒱' c → Blocked (u ⊔ w) 𝒱 u' c :=
  cross_site_union_refinement_iff fun _c hc =>
    (lowerSemicontinuous_selSup hu fun j v hj => h𝒱' j v (hc j v hj)).sup hw

end SeamConjunct

/-! ### The wall species and the class level -/

section WallSpecies

variable {V : Type*} [Fintype V] {m : ℕ}

/-- At the class level the wall conjunct is exact: intersecting an
atom's crescent with a pure-safety wall crescent is the crescent of
the wall-conjoined atom.  Immediate from
`crescentClass_inter_crescentClass` with an empty demand family. -/
theorem crescentClass_inter_wall (u w : ProbPenalty V)
    (𝒱 : Set (ProbPenalty V)) :
    crescentClass u 𝒱 ∩ crescentClass w ∅ = crescentClass (u ⊔ w) 𝒱 := by
  rw [crescentClass_inter_crescentClass, Set.union_empty]

/-- The seam-crossing criterion with the wall in its concrete species:
an indicator wall over a closed admissible set of the joint carrier —
the compiled form of a transport relation's realization constraint —
is lower semicontinuous, and the packaged criterion applies. -/
theorem cross_site_union_refinement_iff_probWall {B : Set (ProbState V)}
    (hB : IsClosed B) {u : ProbPenalty V} {𝒱 : Set (ProbPenalty V)}
    {u' : Fin m → ProbPenalty V} {𝒱' : Fin m → Set (ProbPenalty V)}
    (hu : LowerSemicontinuous u)
    (h𝒱' : ∀ j, ∀ v ∈ 𝒱' j, LowerSemicontinuous v) :
    (∀ σ, LowerSemicontinuous σ → CoupledSat σ (u ⊔ probWall B) 𝒱 →
        ∃ j, CoupledSat σ (u' j) (𝒱' j))
      ↔ ∀ c, SelValid 𝒱' c → Blocked (u ⊔ probWall B) 𝒱 u' c :=
  cross_site_union_refinement_iff_lsc hu
    (lowerSemicontinuous_probWall_iff.mpr hB) h𝒱'

end WallSpecies

end SuFunctor.Universe
