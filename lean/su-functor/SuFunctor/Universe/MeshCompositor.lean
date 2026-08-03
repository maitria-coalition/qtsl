import SuFunctor.Universe.DemonicClock
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # The mesh compositor: conjoin every wall, envelope once, last

Composing systems over a *mesh* — finitely (or infinitely) many cells
joined along many interface walls at once — under the discipline that
generalizes the one-seam conjunct: **all interface walls join into one
premise floor, and the envelope is taken exactly once, after
everything is conjoined**.  Three theorem groups.

**Group 1: the mesh conjunct is order-canonical.**  The single
conjunct all walls make (`meshWall`, a supremum over an arbitrary seam
index) is invariant under re-enumeration (`meshWall_comp_equiv`), and
adjoining seams one at a time, in any order and any association,
yields the *same object* — not merely an equivalent verdict:
`seamFold_eq_meshWall` computes any iterated conjunction to the mesh
floor, `seamFold_perm` is permutation-invariance of the iteration, and
`seamFold_comp_equiv` is the headline.  The judgment reads the mesh
atom as the plain conjunction of its parts
(`coupledSat_sup_meshWall_iff`), the blocking criterion decides
entailment across all seams at once with no new mechanism
(`mesh_union_refinement_iff` and packagings), for indicator walls the
mesh conjunct is the indicator of the *intersected* admissible region
(`meshWall_probWall`), and at the class level the conjunction is exact
(`crescentClass_inter_meshWall`, via `compile_iSup`).  Nothing here
consumes finiteness of the seam family: the criterion's finiteness
lives on the conclusion side, and premise-floor conjuncts are never
counted.

**Group 2: the contrast — enveloping per seam is lossy, and not even
well-defined.**  The envelope operator on bodies is the demonic image
(all realizations at once).  When two seams *share* a realization
parameter, discharging the realization quantifier seam-locally
(`seamEnvelope`) before composing over-approximates the once-enveloped
composite (`sharedComp`): soundly
(`relImage_sharedComp_subset_perSeam` — conservative for upper
bounds), but strictly (`exists_perSeam_envelope_strict`, a one-bit
writer/reader pair), and with the intermediate envelope's *locus*
changing the answer (`exists_perSeam_envelope_order_dependent`) — the
per-seam scheme is order-dependent where the conjoin-first discipline
is order-canonical by Group 1.  This is the shared-realization face of
the meet failure of the Egli–Milner lift (`exists_emLift_inf_not`,
after arXiv:2308.16823): both say *bundle first, envelope last*.

**Group 3: the mesh consistency obligation.**  Joint admissibility of
all walls (`MeshCon`) is a genuine hypothesis of every mesh instance:
it follows from nothing local.  Pairwise consistency of the walls
(`PairwiseCon`) is implied by it (`MeshCon.pairwiseCon`) but does not
imply it back — `exists_pairwiseCon_not_meshCon` exhibits three closed
walls in a ring, every two of which meet, whose conjunction is empty.
(The measure-theoretic sharpening is classical: Vorob'ev exhibited
pairwise-consistent *marginal laws* over a cyclic cover with no joint
law at all [N. N. Vorob'ev, *Consistent families of measures and their
extensions*, Theory Probab. Appl. **7** (1962), 147–163] — there the
supports still glue and only the laws obstruct; here already the
supports refuse, which is the possibilistic face of the same
non-locality.)  The failure of the obligation is carried, never
crashed on: the inconsistent mesh's conjoined wall is the top penalty
(`not_meshCon_iff_meshWall_eq_top`), whose compile is the bottom body,
and the blocking criterion consumes no satisfiability hypothesis.
Dropping a wall from the conjunction is detectable by a
lower-semicontinuous witness (`exists_drop_wall_weakens`): every wall
in the conjunction is load-bearing.
-/

namespace SuFunctor.Universe

open scoped ENNReal

/-! ## Group 1: the mesh conjunct is order-canonical -/

section MeshWall

variable {K : Type*} {ι : Sort*}

/-- The mesh wall: the single conjunct all interface walls make.  The
seam index is arbitrary — in particular it need not be finite: nothing
in the compositor counts premise-floor conjuncts. -/
noncomputable def meshWall (w : ι → K → ℝ≥0∞) : K → ℝ≥0∞ :=
  ⨆ Γ, w Γ

theorem le_meshWall (w : ι → K → ℝ≥0∞) (Γ : ι) : w Γ ≤ meshWall w :=
  le_iSup w Γ

theorem meshWall_le {w : ι → K → ℝ≥0∞} {σ : K → ℝ≥0∞}
    (h : ∀ Γ, w Γ ≤ σ) : meshWall w ≤ σ :=
  iSup_le h

/-- Re-enumeration invariance: the mesh conjunct does not depend on
how the seams are indexed. -/
theorem meshWall_comp_equiv {ι' : Sort*} (e : ι' ≃ ι) (w : ι → K → ℝ≥0∞) :
    meshWall (fun Γ' => w (e Γ')) = meshWall w := by
  refine le_antisymm (meshWall_le fun Γ' => le_meshWall w (e Γ')) ?_
  refine meshWall_le fun Γ => ?_
  simpa using le_meshWall (fun Γ' => w (e Γ')) (e.symm Γ)

/-- The mesh conjunct over `Fin (n + 1)` peels its first wall. -/
theorem meshWall_fin_succ {n : ℕ} (w : Fin (n + 1) → K → ℝ≥0∞) :
    meshWall w = w 0 ⊔ meshWall (fun Γ : Fin n => w Γ.succ) := by
  refine le_antisymm (meshWall_le fun Γ => ?_)
    (sup_le (le_meshWall w 0) (meshWall_le fun Γ => le_meshWall w Γ.succ))
  rcases Fin.eq_zero_or_eq_succ Γ with rfl | ⟨Γ', rfl⟩
  · exact le_sup_left
  · exact (le_meshWall (fun Γ : Fin n => w Γ.succ) Γ').trans le_sup_right

/-- Adjoining the mesh's seams one at a time computes the
once-conjoined mesh floor: iterated one-seam conjunction is the mesh
conjunct.  (The one-seam step is `coupledSat_sup_wall_iff`'s floor
operation, folded over an enumeration of the seams.) -/
theorem seamFold_eq_meshWall :
    ∀ {n : ℕ} (w : Fin n → K → ℝ≥0∞) (u : K → ℝ≥0∞),
      (List.ofFn w).foldr (· ⊔ ·) u = u ⊔ meshWall w
  | 0, w, u => by
    simp [meshWall, iSup_of_empty]
  | n + 1, w, u => by
    rw [List.ofFn_succ, List.foldr_cons,
      seamFold_eq_meshWall (fun Γ : Fin n => w Γ.succ) u,
      meshWall_fin_succ, sup_left_comm]

/-- The `foldl` twin: the association order of the iteration is
immaterial too. -/
theorem seamFoldl_eq_meshWall :
    ∀ {n : ℕ} (w : Fin n → K → ℝ≥0∞) (u : K → ℝ≥0∞),
      (List.ofFn w).foldl (· ⊔ ·) u = u ⊔ meshWall w
  | 0, w, u => by
    simp [meshWall, iSup_of_empty]
  | n + 1, w, u => by
    rw [List.ofFn_succ, List.foldl_cons,
      seamFoldl_eq_meshWall (fun Γ : Fin n => w Γ.succ) (u ⊔ w 0),
      meshWall_fin_succ, sup_assoc]

/-- Permutation invariance of the iterated conjunction, list form: two
enumerations of the same seams build the same floor. -/
theorem seamFold_perm {l l' : List (K → ℝ≥0∞)} (h : l.Perm l')
    (u : K → ℝ≥0∞) : l.foldr (· ⊔ ·) u = l'.foldr (· ⊔ ·) u := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [List.foldr_cons, ih]
  | swap a b l => simp only [List.foldr_cons]; exact sup_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- **Seam-order independence of mesh composition**: under the
conjoin-all-then-envelope-once discipline, composing a finite mesh's
walls in any order yields the same object — equal premise floors, not
merely equivalent verdicts.  Joins are associative and commutative;
the envelope, taken once and last, never sees an order. -/
theorem seamFold_comp_equiv {n : ℕ} (e : Fin n ≃ Fin n)
    (w : Fin n → K → ℝ≥0∞) (u : K → ℝ≥0∞) :
    (List.ofFn fun Γ => w (e Γ)).foldr (· ⊔ ·) u
      = (List.ofFn w).foldr (· ⊔ ·) u := by
  rw [seamFold_eq_meshWall, seamFold_eq_meshWall, meshWall_comp_equiv]

/-- The judgment reads the mesh atom as the conjunction of its parts:
satisfaction of the mesh-conjoined atom is domination of every wall
plus satisfaction of the original atom.  (The many-seam form of
`coupledSat_sup_wall_iff`; the seam index stays arbitrary.) -/
theorem coupledSat_sup_meshWall_iff {σ u : K → ℝ≥0∞}
    {𝒱 : Set (K → ℝ≥0∞)} {w : ι → K → ℝ≥0∞} :
    CoupledSat σ (u ⊔ meshWall w) 𝒱
      ↔ (∀ Γ, w Γ ≤ σ) ∧ CoupledSat σ u 𝒱 := by
  rw [coupledSat_sup_wall_iff]
  simp only [meshWall, iSup_le_iff]

/-- **The mesh-crossing entailment criterion**: union-refinement from
a mesh-conjoined premise atom is decided by the blocking table of the
joined atom — the same finite selections, the same pointwise
domination rows, with every interface wall entering the premise floor
at once.  Instantiation of `cross_site_union_refinement_iff`; no new
mechanism, and no finiteness demanded of the seam family. -/
theorem mesh_union_refinement_iff {m : ℕ} {P : (K → ℝ≥0∞) → Prop}
    {u : K → ℝ≥0∞} {w : ι → K → ℝ≥0∞} {𝒱 : Set (K → ℝ≥0∞)}
    {u' : Fin m → K → ℝ≥0∞} {𝒱' : Fin m → Set (K → ℝ≥0∞)}
    (hPc : ∀ c, SelValid 𝒱' c → P (selSup u c ⊔ meshWall w)) :
    (∀ σ, P σ → CoupledSat σ (u ⊔ meshWall w) 𝒱
        → ∃ j, CoupledSat σ (u' j) (𝒱' j))
      ↔ ∀ c, SelValid 𝒱' c → Blocked (u ⊔ meshWall w) 𝒱 u' c :=
  cross_site_union_refinement_iff hPc

end MeshWall

section MeshWallTopology

variable {K : Type*} {ι : Sort*} [TopologicalSpace K]

/-- The mesh wall is lower semicontinuous whenever every wall is: the
citizen class is closed under the mesh conjunction, for seam families
of any size. -/
theorem lowerSemicontinuous_meshWall {w : ι → K → ℝ≥0∞}
    (hw : ∀ Γ, LowerSemicontinuous (w Γ)) :
    LowerSemicontinuous (meshWall w) := by
  have heq : meshWall w = fun μ => ⨆ Γ, w Γ μ :=
    funext fun _ => iSup_apply
  rw [heq]
  exact lowerSemicontinuous_iSup hw

/-- The mesh-crossing criterion over the lower-semicontinuous class:
with the floor, every wall, and all conclusion demands lower
semicontinuous, the adversary hypothesis discharges and entailment
across the whole mesh is the blocking table, verbatim. -/
theorem mesh_union_refinement_iff_lsc {m : ℕ} {u : K → ℝ≥0∞}
    {w : ι → K → ℝ≥0∞} {𝒱 : Set (K → ℝ≥0∞)} {u' : Fin m → K → ℝ≥0∞}
    {𝒱' : Fin m → Set (K → ℝ≥0∞)}
    (hu : LowerSemicontinuous u) (hw : ∀ Γ, LowerSemicontinuous (w Γ))
    (h𝒱' : ∀ j, ∀ v ∈ 𝒱' j, LowerSemicontinuous v) :
    (∀ σ, LowerSemicontinuous σ → CoupledSat σ (u ⊔ meshWall w) 𝒱 →
        ∃ j, CoupledSat σ (u' j) (𝒱' j))
      ↔ ∀ c, SelValid 𝒱' c → Blocked (u ⊔ meshWall w) 𝒱 u' c :=
  cross_site_union_refinement_iff_lsc hu (lowerSemicontinuous_meshWall hw)
    h𝒱'

end MeshWallTopology

/-! ### The indicator species: conjoined walls intersect their regions -/

section MeshWallSpecies

variable {V : Type*} [Fintype V] {ι : Sort*}

/-- For indicator walls the mesh conjunct is the indicator of the
*intersected* admissible region: conjoining walls is intersecting
their regions, and set intersection never sees an order. -/
theorem meshWall_probWall (B : ι → Set (ProbState V)) :
    meshWall (fun Γ => probWall (B Γ)) = probWall (⋂ Γ, B Γ) := by
  funext μ
  have happ : meshWall (fun Γ => probWall (B Γ)) μ
      = ⨆ Γ, probWall (B Γ) μ := iSup_apply
  rw [happ]
  by_cases h : μ ∈ ⋂ Γ, B Γ
  · rw [probWall_apply_of_mem h]
    simp only [Set.mem_iInter] at h
    exact le_antisymm
      (iSup_le fun Γ => le_of_eq (probWall_apply_of_mem (h Γ))) zero_le
  · rw [probWall_apply_of_not_mem h]
    simp only [Set.mem_iInter, not_forall] at h
    obtain ⟨Γ, hΓ⟩ := h
    refine top_le_iff.mp ?_
    calc (⊤ : ℝ≥0∞) = probWall (B Γ) μ :=
          (probWall_apply_of_not_mem hΓ).symm
      _ ≤ ⨆ Γ', probWall (B Γ') μ :=
          le_iSup (fun Γ' => probWall (B Γ') μ) Γ

/-- The mesh-crossing criterion with the walls in their concrete
species: indicator walls over closed admissible sets conjoin into the
indicator wall of the closed intersection, and the packaged criterion
applies. -/
theorem mesh_union_refinement_iff_probWall {m : ℕ}
    {B : ι → Set (ProbState V)} (hB : ∀ Γ, IsClosed (B Γ))
    {u : ProbPenalty V} {𝒱 : Set (ProbPenalty V)}
    {u' : Fin m → ProbPenalty V} {𝒱' : Fin m → Set (ProbPenalty V)}
    (hu : LowerSemicontinuous u)
    (h𝒱' : ∀ j, ∀ v ∈ 𝒱' j, LowerSemicontinuous v) :
    (∀ σ, LowerSemicontinuous σ →
        CoupledSat σ (u ⊔ meshWall fun Γ => probWall (B Γ)) 𝒱 →
        ∃ j, CoupledSat σ (u' j) (𝒱' j))
      ↔ ∀ c, SelValid 𝒱' c →
          Blocked (u ⊔ meshWall fun Γ => probWall (B Γ)) 𝒱 u' c := by
  rw [meshWall_probWall]
  exact cross_site_union_refinement_iff_probWall (isClosed_iInter hB) hu h𝒱'

end MeshWallSpecies

/-! ### The class level: mesh conjunction is exact

`compile_sup` (conjunction is body intersection) extends to suprema of
arbitrary families; the one new ingredient is that the ray-length
bound survives the supremum (`le_grade_iSup`), which is pure order
bookkeeping — no continuity of the grading beyond monotonicity. -/

section MeshWallClass

variable {ι : Sort*}

/-- The ray-length bound survives arbitrary suprema: a positive grade
bound holding against every member holds against their supremum.  (The
bound caps every member's magnitude, hence the supremum's, hence its
real part; the exponential is only inverted at the fixed bound.) -/
theorem le_grade_iSup [Nonempty ι] {γ : ℝ} (hγ : 0 < γ)
    {a : ι → ℝ≥0∞} (h : ∀ Γ, γ ≤ grade (a Γ)) :
    γ ≤ grade (⨆ Γ, a Γ) := by
  have hc0 : 0 ≤ -Real.log γ := by
    obtain ⟨Γ₀⟩ := ‹Nonempty ι›
    have h1 : γ ≤ 1 := (h Γ₀).trans (grade_le_one _)
    simpa using Real.log_nonpos hγ.le h1
  -- every member is capped by the fixed bound
  have hbound : ∀ Γ, a Γ ≤ ENNReal.ofReal (-Real.log γ) := by
    intro Γ
    have hne : a Γ ≠ ⊤ := by
      intro htop
      have hΓ := h Γ
      rw [htop, grade_top] at hΓ
      exact absurd hΓ (not_le.mpr hγ)
    have hexp : γ ≤ Real.exp (-(a Γ).toReal) := by
      rw [← grade_of_ne_top hne]
      exact h Γ
    have hlog : Real.log γ ≤ -(a Γ).toReal :=
      (Real.log_le_iff_le_exp hγ).mpr hexp
    rw [ENNReal.le_ofReal_iff_toReal_le hne hc0]
    linarith
  -- hence the supremum is capped, finite, and its real part is capped
  have hsup : (⨆ Γ, a Γ) ≤ ENNReal.ofReal (-Real.log γ) := iSup_le hbound
  have hne : (⨆ Γ, a Γ) ≠ ⊤ :=
    (lt_of_le_of_lt hsup ENNReal.ofReal_lt_top).ne
  have htoReal : (⨆ Γ, a Γ).toReal ≤ -Real.log γ := by
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsup
    rwa [ENNReal.toReal_ofReal hc0] at hmono
  rw [grade_of_ne_top hne]
  calc γ = Real.exp (Real.log γ) := (Real.exp_log hγ).symm
    _ ≤ Real.exp (-(⨆ Γ, a Γ).toReal) := Real.exp_le_exp.mpr (by linarith)

variable {V : Type*} [Fintype V]

/-- **Conjunction compiles to intersection, at any arity**: the body
of a supremum of penalties is the intersection of the bodies.  (The
binary case is `compile_sup`; the supremum case rides `le_grade_iSup`
and the uniqueness of positive polar decompositions, exactly as the
binary proof did.) -/
theorem compile_iSup [Nonempty ι] (w : ι → ProbPenalty V) :
    compile (⨆ Γ, w Γ) = ⋂ Γ, compile (w Γ) := by
  refine Set.Subset.antisymm
    (Set.subset_iInter fun Γ =>
      compile_subset_compile_iff.mpr (le_iSup w Γ)) ?_
  intro x hx
  obtain ⟨Γ₀⟩ := ‹Nonempty ι›
  obtain ⟨μ, γ, h0, hle, he⟩ := Set.mem_iInter.mp hx Γ₀
  rcases h0.lt_or_eq with hpos | hzero
  · have hall : ∀ Γ, γ ≤ grade (w Γ μ) := fun Γ =>
      compile_scale_le (Set.mem_iInter.mp hx Γ) hpos he
    refine ⟨μ, γ, h0, ?_, he⟩
    have happ : (⨆ Γ, w Γ) μ = ⨆ Γ, w Γ μ := iSup_apply
    rw [happ]
    exact le_grade_iSup hpos hall
  · refine ⟨μ, γ, h0, ?_, he⟩
    rw [← hzero]
    exact grade_nonneg _

/-- **The mesh conjunction is exact at the class level**: the crescent
of the mesh-conjoined atom is the intersection of the atom's crescent
with every wall's crescent.  (The one-seam case is
`crescentClass_inter_wall`; no per-seam enveloping, no laxity — walls
conjoin exactly at every level of the construction.  The loss the
contrast group prices lives only where enveloping interleaves with
*transport*.) -/
theorem crescentClass_inter_meshWall [Nonempty ι] (u : ProbPenalty V)
    (𝒱 : Set (ProbPenalty V)) (w : ι → ProbPenalty V) :
    crescentClass u 𝒱 ∩ (⋂ Γ, crescentClass (w Γ) ∅)
      = crescentClass (u ⊔ meshWall w) 𝒱 := by
  ext k
  simp only [Set.mem_inter_iff, Set.mem_iInter, mem_crescentClass_iff,
    Set.mem_empty_iff_false, false_implies, implies_true, and_true]
  constructor
  · rintro ⟨⟨hu, hlive⟩, hw⟩
    refine ⟨?_, hlive⟩
    rw [compile_sup]
    refine Set.subset_inter hu ?_
    show (k : Set (BelState V)) ⊆ compile (⨆ Γ, w Γ)
    rw [compile_iSup]
    exact Set.subset_iInter hw
  · rintro ⟨hsup, hlive⟩
    rw [compile_sup] at hsup
    have hmesh : (k : Set (BelState V)) ⊆ compile (⨆ Γ, w Γ) :=
      (Set.subset_inter_iff.mp hsup).2
    rw [compile_iSup] at hmesh
    exact ⟨⟨(Set.subset_inter_iff.mp hsup).1, hlive⟩,
      fun Γ => Set.subset_iInter_iff.mp hmesh Γ⟩

end MeshWallClass

/-! ## Group 2: the contrast — per-seam enveloping is order-dependent
and strictly lossier

The envelope operator on bodies is the demonic image: all realizations
at once.  A *shared-realization seam pair* is two transport relations
depending on one realization parameter.  The discipline composes at
the relation tier first and envelopes once (`sharedComp`); the
per-seam scheme discharges the realization quantifier at each seam
(`seamEnvelope`) and pays for it: the composite forgets which
realization its seams shared. -/

section PerSeamContrast

variable {Θ X Y Z : Type*}

/-- The per-seam envelope of a realization-parameterized transport:
the realization quantifier discharged seam-locally. -/
def seamEnvelope (r : Θ → X → Y → Prop) : X → Y → Prop :=
  fun x y => ∃ θ, r θ x y

/-- The envelope-once composite of a shared-realization seam pair:
compose at the relation tier first, one realization quantifier,
last. -/
def sharedComp (r : Θ → X → Y → Prop) (s : Θ → Y → Z → Prop) :
    X → Z → Prop :=
  fun x z => ∃ θ, relComp (r θ) (s θ) x z

/-- The sound direction, general: per-seam enveloping only ever
over-approximates the once-enveloped composite.  (Conservative for
upper bounds — which is why the discipline is a canonicity and
precision matter, never a soundness repair.) -/
theorem relImage_sharedComp_subset_perSeam (r : Θ → X → Y → Prop)
    (s : Θ → Y → Z → Prop) (A : Set X) :
    relImage (sharedComp r s) A
      ⊆ relImage (relComp (seamEnvelope r) (seamEnvelope s)) A := by
  rintro z ⟨x, hx, θ, y, hr, hs⟩
  exact ⟨x, hx, y, ⟨θ, hr⟩, ⟨θ, hs⟩⟩

/-- **Envelope-then-envelope is not envelope-once**: a two-seam mesh
whose per-seam-enveloped composite strictly exceeds the once-enveloped
composite, in one-bit form.  The first seam *writes* the shared
realization (`y = θ`), the second *reads* it back (`z = (y == θ)`):
bundled, the read always succeeds and the composite pins `z = true`;
enveloped per seam, the composite forgets which `θ` was written and
admits everything. -/
theorem exists_perSeam_envelope_strict :
    ∃ (r s : Bool → Bool → Bool → Prop) (A : Set Bool),
      relImage (relComp (seamEnvelope r) (seamEnvelope s)) A
        ≠ relImage (sharedComp r s) A := by
  refine ⟨fun θ _ y => y = θ, fun θ y z => z = (y == θ), Set.univ,
    ne_of_mem_of_not_mem' (a := false) ?_ ?_⟩
  · exact ⟨true, Set.mem_univ _, true, ⟨true, rfl⟩, ⟨false, by decide⟩⟩
  · rintro ⟨x, -, θ, y, rfl, hz⟩
    simp at hz

/-- **The per-seam scheme is order-dependent**: on a three-seam chain
sharing one realization, enveloping after the first seam and
enveloping after the second give *different* composites.  (Same
writer/reader pair, with an inert third seam appended: enveloping
after seam one discards the realization before the reader consumes it;
enveloping after seam two does not.)  Together with
`seamFold_comp_equiv`, the two halves of the adjudication: the
conjoin-first discipline is order-canonical, and the per-seam
alternative is not merely lossier but not even well-defined until an
envelope locus is chosen. -/
theorem exists_perSeam_envelope_order_dependent :
    ∃ (r s t : Bool → Bool → Bool → Prop) (A : Set Bool),
      relImage (relComp (seamEnvelope r)
          (fun y w => ∃ θ, relComp (s θ) (t θ) y w)) A
        ≠ relImage (relComp (sharedComp r s) (seamEnvelope t)) A := by
  refine ⟨fun θ _ y => y = θ, fun θ y z => z = (y == θ),
    fun _ z w => w = z, Set.univ,
    ne_of_mem_of_not_mem' (a := false) ?_ ?_⟩
  · exact ⟨true, Set.mem_univ _, true, ⟨true, rfl⟩,
      ⟨false, false, by decide, rfl⟩⟩
  · rintro ⟨x, -, z, ⟨θ, y, rfl, hz⟩, θ', hw⟩
    simp only [beq_self_eq_true] at hz
    subst hz
    exact Bool.noConfusion hw

end PerSeamContrast

/-! ## Group 3: the mesh consistency obligation -/

section MeshCon

variable {ι : Sort*} {α : Type*}

/-- **The mesh consistency obligation**: the conjoined admissible
region of all interface walls is nonempty.  This is a *hypothesis* of
every mesh instance, to be stated visibly: it follows from nothing
local (`exists_pairwiseCon_not_meshCon`), and its failure — while
lawfully carried by the semantics (`not_meshCon_iff_meshWall_eq_top`)
— makes the composite's premise the top penalty. -/
def MeshCon (B : ι → Set α) : Prop :=
  (⋂ Γ, B Γ).Nonempty

/-- Pairwise consistency of a wall family: what per-seam checking can
certify. -/
def PairwiseCon (B : ι → Set α) : Prop :=
  ∀ Γ Δ, (B Γ ∩ B Δ).Nonempty

/-- Joint consistency implies pairwise consistency — the direction
that does hold. -/
theorem MeshCon.pairwiseCon {B : ι → Set α} (h : MeshCon B) :
    PairwiseCon B := by
  obtain ⟨μ, hμ⟩ := h
  simp only [Set.mem_iInter] at hμ
  exact fun Γ Δ => ⟨μ, hμ Γ, hμ Δ⟩

end MeshCon

section MeshConSpecies

variable {ι : Sort*} {V : Type*} [Fintype V]

/-- The wall of the empty region is the top penalty. -/
theorem probWall_empty : probWall (∅ : Set (ProbState V)) = ⊤ :=
  funext fun μ => probWall_apply_of_not_mem (Set.notMem_empty μ)

/-- An indicator wall is the top penalty exactly when its region is
empty. -/
theorem probWall_eq_top_iff {C : Set (ProbState V)} :
    probWall C = ⊤ ↔ C = ∅ := by
  constructor
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro μ hμ
    have h0 : probWall C μ = 0 := probWall_apply_of_mem hμ
    have htop : probWall C μ = ⊤ := congrFun h μ
    rw [h0] at htop
    exact ENNReal.zero_ne_top htop
  · rintro rfl
    exact probWall_empty

/-- **The absorption**: the obligation fails exactly when the mesh's
conjoined wall is the top penalty — whose compile is the bottom body.
An inconsistent mesh is a detectable presentation defect, carried by
the semantics rather than crashed on: the blocking criterion consumes
no satisfiability hypothesis, so entailment from the inconsistent
premise is derived ex falso, never postulated. -/
theorem not_meshCon_iff_meshWall_eq_top {B : ι → Set (ProbState V)} :
    ¬ MeshCon B ↔ meshWall (fun Γ => probWall (B Γ)) = ⊤ := by
  rw [meshWall_probWall, probWall_eq_top_iff, MeshCon,
    Set.not_nonempty_iff_eq_empty]

end MeshConSpecies

/-! ### The obligation follows from nothing local

Three closed walls in a ring, every two of which meet, whose
conjunction is empty: per-seam consistency does not discharge the mesh
obligation on cyclic meshes.  This is the possibilistic face; the
measure-theoretic face is sharper still (Vorob'ev's obstruction, cited
in the module docstring: pairwise-consistent marginal *laws* over a
cyclic cover with no joint law even where the supports glue), and both
point the same moral — `MeshCon` is a genuine hypothesis of the mesh
instance, never a consequence of its cells. -/

section CyclicWitness

/-- The lower half-space wall on the two-outcome carrier. -/
private def lowerHalf : Set (ProbState (Fin 2)) :=
  {μ | (μ : Fin 2 → ℝ) 0 ≤ 1/2}

/-- The upper half-space wall on the two-outcome carrier. -/
private def upperHalf : Set (ProbState (Fin 2)) :=
  {μ | 1/2 ≤ (μ : Fin 2 → ℝ) 0}

/-- The two-point wall straddling the half-spaces. -/
private def twoPoint : Set (ProbState (Fin 2)) :=
  {μ | (μ : Fin 2 → ℝ) 0 = 1/4} ∪ {μ | (μ : Fin 2 → ℝ) 0 = 3/4}

private theorem isClosed_lowerHalf : IsClosed lowerHalf :=
  isClosed_le ((continuous_apply 0).comp continuous_subtype_val)
    continuous_const

private theorem isClosed_upperHalf : IsClosed upperHalf :=
  isClosed_le continuous_const
    ((continuous_apply 0).comp continuous_subtype_val)

private theorem isClosed_twoPoint : IsClosed twoPoint :=
  (isClosed_eq ((continuous_apply 0).comp continuous_subtype_val)
      continuous_const).union
    (isClosed_eq ((continuous_apply 0).comp continuous_subtype_val)
      continuous_const)

/-- The witness states. -/
private noncomputable def quarterState : ProbState (Fin 2) :=
  ProbState.ofPair (1/4) (3/4) (by norm_num) (by norm_num) (by norm_num)

private noncomputable def halfState : ProbState (Fin 2) :=
  ProbState.ofPair (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)

private noncomputable def threeQuarterState : ProbState (Fin 2) :=
  ProbState.ofPair (3/4) (1/4) (by norm_num) (by norm_num) (by norm_num)

private theorem quarterState_apply :
    ((quarterState : ProbState (Fin 2)) : Fin 2 → ℝ) 0 = 1/4 :=
  ProbState.ofPair_apply_zero _ _ _ _ _

private theorem halfState_apply :
    ((halfState : ProbState (Fin 2)) : Fin 2 → ℝ) 0 = 1/2 :=
  ProbState.ofPair_apply_zero _ _ _ _ _

private theorem threeQuarterState_apply :
    ((threeQuarterState : ProbState (Fin 2)) : Fin 2 → ℝ) 0 = 3/4 :=
  ProbState.ofPair_apply_zero _ _ _ _ _

private theorem quarterState_mem_lowerHalf : quarterState ∈ lowerHalf := by
  simp only [lowerHalf, Set.mem_setOf_eq, quarterState_apply]
  norm_num

private theorem quarterState_mem_twoPoint : quarterState ∈ twoPoint := by
  simp only [twoPoint, Set.mem_union, Set.mem_setOf_eq, quarterState_apply]
  norm_num

private theorem halfState_mem_lowerHalf : halfState ∈ lowerHalf := by
  simp only [lowerHalf, Set.mem_setOf_eq, halfState_apply]
  norm_num

private theorem halfState_mem_upperHalf : halfState ∈ upperHalf := by
  simp only [upperHalf, Set.mem_setOf_eq, halfState_apply]
  norm_num

private theorem threeQuarterState_mem_upperHalf :
    threeQuarterState ∈ upperHalf := by
  simp only [upperHalf, Set.mem_setOf_eq, threeQuarterState_apply]
  norm_num

private theorem threeQuarterState_mem_twoPoint :
    threeQuarterState ∈ twoPoint := by
  simp only [twoPoint, Set.mem_union, Set.mem_setOf_eq,
    threeQuarterState_apply]
  norm_num

/-- **Pairwise consistency does not discharge the mesh obligation**:
three closed walls on the two-outcome carrier — a lower half-space, an
upper half-space, and a two-point wall straddling them — meet
pairwise, yet their conjunction is empty.  A cyclic mesh's consistency
is not local-to-global. -/
theorem exists_pairwiseCon_not_meshCon :
    ∃ B : Fin 3 → Set (ProbState (Fin 2)),
      (∀ Γ, IsClosed (B Γ)) ∧ PairwiseCon B ∧ ¬ MeshCon B := by
  refine ⟨![lowerHalf, upperHalf, twoPoint], ?_, ?_, ?_⟩
  · intro Γ
    fin_cases Γ
    · exact isClosed_lowerHalf
    · exact isClosed_upperHalf
    · exact isClosed_twoPoint
  · intro Γ Δ
    fin_cases Γ <;> fin_cases Δ
    · exact ⟨halfState, halfState_mem_lowerHalf, halfState_mem_lowerHalf⟩
    · exact ⟨halfState, halfState_mem_lowerHalf, halfState_mem_upperHalf⟩
    · exact ⟨quarterState, quarterState_mem_lowerHalf,
        quarterState_mem_twoPoint⟩
    · exact ⟨halfState, halfState_mem_upperHalf, halfState_mem_lowerHalf⟩
    · exact ⟨halfState, halfState_mem_upperHalf, halfState_mem_upperHalf⟩
    · exact ⟨threeQuarterState, threeQuarterState_mem_upperHalf,
        threeQuarterState_mem_twoPoint⟩
    · exact ⟨quarterState, quarterState_mem_twoPoint,
        quarterState_mem_lowerHalf⟩
    · exact ⟨threeQuarterState, threeQuarterState_mem_twoPoint,
        threeQuarterState_mem_upperHalf⟩
    · exact ⟨quarterState, quarterState_mem_twoPoint,
        quarterState_mem_twoPoint⟩
  · rintro ⟨μ, hμ⟩
    simp only [Set.mem_iInter] at hμ
    have h0 : (μ : Fin 2 → ℝ) 0 ≤ 1/2 := hμ 0
    have h1 : 1/2 ≤ (μ : Fin 2 → ℝ) 0 := hμ 1
    have h2 : (μ : Fin 2 → ℝ) 0 = 1/4 ∨ (μ : Fin 2 → ℝ) 0 = 3/4 := hμ 2
    have heq : (μ : Fin 2 → ℝ) 0 = 1/2 := le_antisymm h0 h1
    rcases h2 with h | h <;> rw [heq] at h <;> norm_num at h

/-- **Every wall in the conjunction is load-bearing**: dropping one
wall from a mesh's conjunction weakens the composite detectably — a
lower-semicontinuous citizen satisfies the one-wall atom and is
refused by the two-wall mesh atom. -/
theorem exists_drop_wall_weakens :
    ∃ (B : Fin 2 → Set (ProbState (Fin 2))) (σ : ProbPenalty (Fin 2)),
      (∀ Γ, IsClosed (B Γ)) ∧ LowerSemicontinuous σ
        ∧ CoupledSat σ ((⊥ : ProbPenalty (Fin 2)) ⊔ probWall (B 0)) ∅
        ∧ ¬ CoupledSat σ
            ((⊥ : ProbPenalty (Fin 2))
              ⊔ meshWall fun Γ => probWall (B Γ)) ∅ := by
  refine ⟨![lowerHalf, upperHalf], probWall lowerHalf, ?_,
    lowerSemicontinuous_probWall_iff.mpr isClosed_lowerHalf,
    ⟨?_, fun v hv => absurd hv (Set.notMem_empty v)⟩, ?_⟩
  · intro Γ
    fin_cases Γ
    · exact isClosed_lowerHalf
    · exact isClosed_upperHalf
  · -- the one-wall floor is dominated by the one-wall citizen
    rw [bot_sup_eq]
    exact le_rfl
  · -- the mesh atom refuses the same citizen at the dropped wall
    rintro ⟨hsafe, -⟩
    have hnot : quarterState ∉ upperHalf := by
      simp only [upperHalf, Set.mem_setOf_eq, quarterState_apply]
      norm_num
    have hwall : probWall upperHalf quarterState = ⊤ :=
      probWall_apply_of_not_mem hnot
    have hle1 : probWall upperHalf quarterState
        ≤ meshWall (fun Γ => probWall ((![lowerHalf, upperHalf]) Γ))
            quarterState := by
      have happ : meshWall (fun Γ => probWall ((![lowerHalf, upperHalf]) Γ))
          quarterState
          = ⨆ Γ, probWall ((![lowerHalf, upperHalf]) Γ) quarterState :=
        iSup_apply
      rw [happ]
      exact le_iSup
        (fun Γ => probWall ((![lowerHalf, upperHalf]) Γ) quarterState)
        (1 : Fin 2)
    rw [hwall] at hle1
    have hle := hsafe quarterState
    rw [Pi.sup_apply] at hle
    have hσ : probWall lowerHalf quarterState = 0 :=
      probWall_apply_of_mem quarterState_mem_lowerHalf
    have htop : (⊤ : ℝ≥0∞) ≤ 0 := by
      calc (⊤ : ℝ≥0∞)
          ≤ meshWall (fun Γ => probWall ((![lowerHalf, upperHalf]) Γ))
              quarterState := hle1
        _ ≤ (⊥ : ProbPenalty (Fin 2)) quarterState
              ⊔ meshWall (fun Γ => probWall ((![lowerHalf, upperHalf]) Γ))
                  quarterState := le_sup_right
        _ ≤ probWall lowerHalf quarterState := hle
        _ = 0 := hσ
    simp at htop

end CyclicWitness

end SuFunctor.Universe
