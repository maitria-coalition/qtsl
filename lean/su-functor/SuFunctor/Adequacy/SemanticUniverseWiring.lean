import SuFunctor.SingleSiteSemanticUniverse
import SuFunctor.Adequacy.MdpDemonic
import SuFunctor.Adequacy.Pgm
import SuFunctor.Adequacy.CtmcJumpChain
import SuFunctor.Adequacy.MarkovAutomaton
import SuFunctor.Adequacy.MaDemonic

/-! # Wiring the adequacy squares to the semantic universe

The adequacy squares are stated one stratum below the semantic
universe: over the thin double category of per-element constraints on
exact-rational subprobability mass functions, each square exhibits an
invertible cell between the compiled system's constraint diagram and
the inclusion of its classical law.  The semantic universe's fibres
live at the exact stratum — coupled DNF presentations over
subprobability joints, judged by `CoupledSat` (pointwise floor
domination at the safety face, dips under a finite liveness family at
the ∃-face).  This module ties the two strata together, per square,
with no new induction: the squares' feeding lemmas are consumed whole.

The tie has three parts.

* **Systems enter the judgment as ideal points** (`idealPoint`): a law
  embeds as the wall penalty on its singleton image — `0` at the law's
  joint, `⊤` elsewhere.  The scalar seam is crossed by
  `SubPMF.toJoint` (rational weights into nonnegative-real weights),
  which is injective: no information is lost entering the universe.
  The *singleton* (rather than the credal ray) is forced by the fibre
  order itself: the safety face of the coupled judgment reads the whole
  body of the system penalty, and the compiled floors are
  equality-constraint walls, which vanish only at the pinned point —
  the ray-embedded system fails its own pinning floor away from bottom
  (`coupledSat_rayWall_singleton_floor_fails`, the fence).  Slice
  discipline — reading a credal set at its radially maximal slice — is
  a verdict-layer operation, and the reconciliation with the credal
  presentation is the envelope stratum's theorem, consumed here as
  two-line corollaries (`su_dtmc_slice`, `su_mdp_demonic_slice`): the
  singleton *is* the maximal slice of the ray.

* **Compiled diagrams become citizens of the fibre** (`diagramDnf`): a
  constraint list presents as a single-disjunct DNF whose floor is the
  wall of the conjunction's image and whose liveness family is exactly
  the properness demand `{⊤}` — the compiled atoms are equalities,
  pure safety-face content.  The presentation keeps the diagram's
  structure: conjunction of constraints merges floors by pointwise
  `⊔`, the invertible safety merge of the coupled judgment
  (`cwall_and`, `cwall_looseConj` — and the `⊓`-merge is refuted
  outright, `exists_cwall_and_ne_inf`).  Citizenship at the exact
  stratum is finite presentation, carried by construction.

* **The judgment bridge** (`coupledSat_idealPoint_cwall_iff`): an ideal
  point satisfies a constraint's wall atom exactly when the law
  satisfies the constraint.  All four squares feed through this one
  equivalence (`idealPoint_mem_diagramDnf_iff`), composed with their
  own feeding lemmas: membership of the law's ideal point in the
  compiled presentation's model class is equivalent to the law being
  the classical semantics — for the chain, the graphical model, the
  fixed-policy decision process, and (at the set stratum) the demonic
  face, where the compiled presentation is the *policy-free* one-atom
  projection of the scheduler mechanism and the model class restricted
  to ideal points is exactly the demonic law-set.

Option-A behavior rides along: every law's ideal point satisfies the
vacuous atom `(0, {⊤})` (`idealPoint_proper` — properness is free at
ideal points, the bottom law included: the lawful denotation of
infeasibility is proper), no law enters as the inconsistent system
(`idealPoint_ne_top`), and the inconsistent system belongs to no
presented diagram's model class (`top_notMem_diagramDnf`, by the
structural ex-falso inversion of the DNF stratum).

Two boundaries, stated rather than smoothed.  The wiring is
*per-carrier*: statements live over the fibre carrier
`SpecDnf (Joint V)` with the record space `V` supplied directly — this
is the fibre of the semantic universe over any wire object whose state
space is `V`, and the construction of that wire object from the
compiled system is a separate, named stratum.  And the constraint
walls are exact-stratum objects (the image extension prices non-
rational joints at `⊤`; the judgment at ideal points never reads those
values); the topological reading — real-closure floors, lower
semicontinuous over the probability carrier, feeding the hyperspace
citizenship theorems — is the envelope stratum's successor, not built
here. -/

namespace SuFunctor

open scoped NNReal ENNReal

universe u

variable {V : Type u}

/-! ## The scalar seam: rational laws into subprobability joints -/

namespace SubPMF

/-- The exact-stratum image of a rational law: cast the weights into
`ℝ≥0`.  Mass at most one transfers, so the image is a subprobability
joint. -/
noncomputable def toJoint (μ : SubPMF V) : Plain.Joint V where
  wt := μ.wt.mapRange (fun (q : ℚ) => Real.toNNReal (q : ℝ)) (by simp)
  mass_le_one := by
    classical
    rw [Finsupp.sum_mapRange_index (fun _ => rfl)]
    rw [Finsupp.sum]
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, NNReal.coe_one]
    rw [Finset.sum_congr rfl fun a _ =>
      Real.coe_toNNReal ((μ.wt a : ℝ)) (by exact_mod_cast μ.nonneg a)]
    have hcast : (∑ a ∈ μ.wt.support, (μ.wt a : ℝ))
        = ((∑ a ∈ μ.wt.support, μ.wt a : ℚ) : ℝ) := by
      push_cast
      rfl
    rw [hcast]
    exact_mod_cast μ.mass_le_one

@[simp] theorem toJoint_wt_apply (μ : SubPMF V) (a : V) :
    (μ.toJoint).wt a = Real.toNNReal ((μ.wt a : ℝ)) :=
  rfl

/-- **No information is lost at the scalar seam**: the embedding of
rational laws into joints is injective (the cast is injective on the
nonnegative rationals). -/
theorem toJoint_injective : Function.Injective (toJoint (V := V)) := by
  intro μ ν h
  apply SubPMF.ext'
  ext a
  have h1 : (μ.toJoint).wt a = (ν.toJoint).wt a := by rw [h]
  rw [toJoint_wt_apply, toJoint_wt_apply] at h1
  have h2 := congrArg (fun x : ℝ≥0 => (x : ℝ)) h1
  simp only [Real.coe_toNNReal ((μ.wt a : ℝ)) (by exact_mod_cast μ.nonneg a),
    Real.coe_toNNReal ((ν.wt a : ℝ)) (by exact_mod_cast ν.nonneg a)] at h2
  exact_mod_cast h2

end SubPMF

namespace Adequacy

open SuFunctor.Universe (Dip CoupledSat SpecAtom SpecDnf)

/-! ## Wall penalties at the exact stratum -/

open Classical in
/-- The wall penalty of a set of joints: `0` inside, `⊤` outside — the
exact-stratum sibling of the probability carrier's wall. -/
noncomputable def wallPen (W : Set (Plain.Joint V)) : Plain.Pen V :=
  fun ν => if ν ∈ W then 0 else ⊤

theorem wallPen_apply_of_mem {W : Set (Plain.Joint V)}
    {ν : Plain.Joint V} (h : ν ∈ W) : wallPen W ν = 0 := by
  simp [wallPen, h]

theorem wallPen_apply_of_not_mem {W : Set (Plain.Joint V)}
    {ν : Plain.Joint V} (h : ν ∉ W) : wallPen W ν = ⊤ := by
  simp [wallPen, h]

/-- **The wall-system reading of the coupled judgment**: a wall system
satisfies an atom iff the floor vanishes on the wall's support and
every liveness mark is strictly positive somewhere on it.  Safety
binds only on the support (off it the wall is `⊤`), and dips happen
only on the support (off it nothing is below `⊤`). -/
theorem coupledSat_wallPen_iff {W : Set (Plain.Joint V)}
    {u : Plain.Pen V} {𝒱 : Set (Plain.Pen V)} :
    CoupledSat (wallPen W) u 𝒱 ↔
      (∀ ν ∈ W, u ν = 0) ∧ ∀ v ∈ 𝒱, ∃ ν ∈ W, 0 < v ν := by
  constructor
  · rintro ⟨hsafe, hlive⟩
    refine ⟨fun ν hν => ?_, fun v hv => ?_⟩
    · have h := hsafe ν
      rw [wallPen_apply_of_mem hν] at h
      exact le_zero_iff.mp h
    · obtain ⟨ν, hν⟩ := hlive v hv
      by_cases hm : ν ∈ W
      · rw [wallPen_apply_of_mem hm] at hν
        exact ⟨ν, hm, hν⟩
      · rw [wallPen_apply_of_not_mem hm] at hν
        exact absurd hν not_top_lt
  · rintro ⟨hsafe, hlive⟩
    refine ⟨fun ν => ?_, fun v hv => ?_⟩
    · by_cases hm : ν ∈ W
      · rw [wallPen_apply_of_mem hm]
        exact (hsafe ν hm).le
      · rw [wallPen_apply_of_not_mem hm]
        exact le_top
    · obtain ⟨ν, hm, hν⟩ := hlive v hv
      refine ⟨ν, ?_⟩
      rw [wallPen_apply_of_mem hm]
      exact hν

/-- Walls of intersections merge by pointwise `⊔` — the exact-stratum
face of the invertible safety merge of the coupled judgment. -/
theorem wallPen_inter (W₁ W₂ : Set (Plain.Joint V)) :
    wallPen (W₁ ∩ W₂) = wallPen W₁ ⊔ wallPen W₂ := by
  funext ν
  rw [Pi.sup_apply]
  by_cases h₁ : ν ∈ W₁
  · by_cases h₂ : ν ∈ W₂
    · rw [wallPen_apply_of_mem (Set.mem_inter h₁ h₂),
        wallPen_apply_of_mem h₁, wallPen_apply_of_mem h₂]
      simp
    · rw [wallPen_apply_of_not_mem (fun hc => h₂ hc.2),
        wallPen_apply_of_mem h₁, wallPen_apply_of_not_mem h₂]
      simp
  · rw [wallPen_apply_of_not_mem (fun hc => h₁ hc.1),
      wallPen_apply_of_not_mem h₁]
    simp

/-! ## Ideal points: how a law enters the judgment -/

/-- **The ideal point of a law**: the wall on its singleton image —
the judgment-side representation of a system in the semantic
universe's fibres.  The singleton (not the credal ray) is forced by
the fibre order; the reconciliation with the credal presentation runs
through the radially maximal slice, at the verdict layer. -/
noncomputable def idealPoint (μ : SubPMF V) : Plain.Pen V :=
  wallPen {μ.toJoint}

theorem idealPoint_def (μ : SubPMF V) :
    idealPoint μ = wallPen {μ.toJoint} := rfl

/-- The ideal-point reading of the coupled judgment: safety and
liveness both read at the law's joint, and nowhere else. -/
theorem coupledSat_idealPoint_iff {μ : SubPMF V} {u : Plain.Pen V}
    {𝒱 : Set (Plain.Pen V)} :
    CoupledSat (idealPoint μ) u 𝒱 ↔
      u μ.toJoint = 0 ∧ ∀ v ∈ 𝒱, 0 < v μ.toJoint := by
  rw [idealPoint_def, coupledSat_wallPen_iff]
  constructor
  · rintro ⟨hs, hl⟩
    refine ⟨hs _ rfl, fun v hv => ?_⟩
    obtain ⟨ν, hν, h⟩ := hl v hv
    rw [Set.mem_singleton_iff] at hν
    subst hν
    exact h
  · rintro ⟨hs, hl⟩
    refine ⟨fun ν hν => ?_, fun v hv => ⟨μ.toJoint, rfl, hl v hv⟩⟩
    rw [Set.mem_singleton_iff] at hν
    subst hν
    exact hs

/-- **Every law's ideal point is proper**: the vacuous atom `(0, {⊤})`
— the option-A properness demand — is satisfied by every ideal point,
the bottom law included.  The lawful denotation of infeasibility is
proper, never inconsistent. -/
theorem idealPoint_proper (μ : SubPMF V) :
    CoupledSat (idealPoint μ) (0 : Plain.Pen V) {(⊤ : Plain.Pen V)} := by
  rw [coupledSat_idealPoint_iff]
  refine ⟨rfl, ?_⟩
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  subst hv
  rw [Pi.top_apply]
  exact lt_of_lt_of_le zero_lt_one le_top

/-- No law enters as the inconsistent system. -/
theorem idealPoint_ne_top (μ : SubPMF V) :
    idealPoint μ ≠ (⊤ : Plain.Pen V) := by
  intro h
  have h0 := congrFun h μ.toJoint
  rw [idealPoint_def, wallPen_apply_of_mem (Set.mem_singleton μ.toJoint),
    Pi.top_apply] at h0
  exact ENNReal.zero_ne_top h0

/-! ## Constraint walls: the compiled diagrams as fibre floors -/

/-- The constraint wall: a per-element constraint of the squares'
stratum, as an exact-stratum floor — the wall on the image of its
extension.  Off the rational locus the floor prices `⊤`; the judgment
at ideal points never reads those values. -/
noncomputable def cwall (c : SubPMF V → Prop) : Plain.Pen V :=
  wallPen (SubPMF.toJoint '' {μ | c μ})

theorem cwall_def (c : SubPMF V → Prop) :
    cwall c = wallPen (SubPMF.toJoint '' {μ | c μ}) := rfl

/-- The constraint wall reads the constraint back at every ideal
point — injectivity of the scalar seam is consumed exactly here. -/
theorem cwall_toJoint_eq_zero_iff {c : SubPMF V → Prop} {μ : SubPMF V} :
    cwall c μ.toJoint = 0 ↔ c μ := by
  constructor
  · intro h
    by_cases hm : μ.toJoint ∈ SubPMF.toJoint '' {μ' | c μ'}
    · obtain ⟨μ', hμ', he⟩ := hm
      have heq := SubPMF.toJoint_injective he
      rw [heq] at hμ'
      exact hμ'
    · rw [cwall_def, wallPen_apply_of_not_mem hm] at h
      exact absurd h ENNReal.top_ne_zero
  · intro hc
    rw [cwall_def]
    exact wallPen_apply_of_mem ⟨μ, hc, rfl⟩

/-- **The judgment bridge**: an ideal point satisfies a constraint's
wall atom — floor the constraint wall, liveness the properness demand
— exactly when the law satisfies the constraint.  Every square feeds
through this equivalence. -/
theorem coupledSat_idealPoint_cwall_iff {c : SubPMF V → Prop}
    {μ : SubPMF V} :
    CoupledSat (idealPoint μ) (cwall c) {(⊤ : Plain.Pen V)} ↔ c μ := by
  rw [coupledSat_idealPoint_iff]
  constructor
  · rintro ⟨hs, -⟩
    exact cwall_toJoint_eq_zero_iff.mp hs
  · intro hc
    refine ⟨cwall_toJoint_eq_zero_iff.mpr hc, ?_⟩
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    rw [Pi.top_apply]
    exact lt_of_lt_of_le zero_lt_one le_top

/-- Conjunction of constraints merges walls by pointwise `⊔` — the
compiled diagrams' `⊙`-composition realized in the fibre's own safety
algebra (and injectivity consumed once more, for the image of the
intersection). -/
theorem cwall_and (c₁ c₂ : SubPMF V → Prop) :
    cwall (fun μ => c₁ μ ∧ c₂ μ) = cwall c₁ ⊔ cwall c₂ := by
  show wallPen (SubPMF.toJoint '' {μ | c₁ μ ∧ c₂ μ}) = _
  rw [Set.setOf_and, Set.image_inter SubPMF.toJoint_injective,
    wallPen_inter]
  rfl

/-- The wall of a constraint diagram is the `⊔`-fold of its atoms'
walls: the compiled list structure survives into the presentation. -/
theorem cwall_looseConj (L : List (SubPMF V → Prop)) :
    cwall (looseConj L)
      = L.foldr (fun c u => cwall c ⊔ u)
          (cwall (looseConj ([] : List (SubPMF V → Prop)))) := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    rw [List.foldr_cons, ← ih]
    exact cwall_and c (looseConj L)

/-- **The `⊓`-merge is false, not merely unproven**: two incompatible
singleton constraints witness that walls of conjunctions do not merge
by pointwise `⊓` — the doomed direction of the safety-disjunction
impossibility, refuted concretely at the exact stratum. -/
theorem exists_cwall_and_ne_inf :
    ∃ c₁ c₂ : SubPMF Unit → Prop,
      cwall (fun μ => c₁ μ ∧ c₂ μ) ≠ cwall c₁ ⊓ cwall c₂ := by
  refine ⟨singletonC (SubPMF.dirac ()), singletonC (SubPMF.zero Unit),
    fun h => ?_⟩
  have h0 := congrFun h (SubPMF.dirac ()).toJoint
  have hempty : {μ : SubPMF Unit |
      singletonC (SubPMF.dirac ()) μ ∧ singletonC (SubPMF.zero Unit) μ}
        = ∅ := by
    ext μ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    rw [singletonC_iff] at h1 h2
    exact SubPMF.dirac_ne_zero () (h1.symm.trans h2)
  have hL : cwall (fun μ => singletonC (SubPMF.dirac ()) μ
      ∧ singletonC (SubPMF.zero Unit) μ) (SubPMF.dirac ()).toJoint = ⊤ := by
    rw [cwall_def, hempty, Set.image_empty]
    exact wallPen_apply_of_not_mem (Set.notMem_empty _)
  have hR : (cwall (singletonC (SubPMF.dirac ()))
      ⊓ cwall (singletonC (SubPMF.zero Unit)))
        (SubPMF.dirac ()).toJoint = 0 := by
    rw [Pi.inf_apply,
      cwall_toJoint_eq_zero_iff.mpr (singletonC_self (SubPMF.dirac ()))]
    exact inf_eq_left.mpr zero_le
  exact ENNReal.top_ne_zero (hL.symm.trans (h0.trans hR))

/-! ## The presented diagrams: single-disjunct citizens of the fibre -/

/-- The wall atom of a constraint diagram: floor the wall of the
conjunction, liveness family exactly the properness demand — the
compiled atoms are equalities, pure safety-face content, so option A's
`{⊤}` is the whole ∃-face. -/
noncomputable def diagramAtom (L : List (SubPMF V → Prop)) :
    SpecAtom (Plain.Joint V) where
  floor := cwall (looseConj L)
  marks := {⊤}
  finite_marks := Set.finite_singleton _
  top_mem := rfl

@[simp] theorem diagramAtom_floor (L : List (SubPMF V → Prop)) :
    (diagramAtom L).floor = cwall (looseConj L) := rfl

@[simp] theorem diagramAtom_marks (L : List (SubPMF V → Prop)) :
    (diagramAtom L).marks = {(⊤ : Plain.Pen V)} := rfl

/-- The presented diagram: a single-disjunct coupled DNF — a citizen
of the semantic universe's fibre over the record space, by
construction (one atom, one mark, the properness demand carried). -/
noncomputable def diagramDnf (L : List (SubPMF V → Prop)) :
    SpecDnf (Plain.Joint V) where
  atoms := {diagramAtom L}
  finite_atoms := Set.finite_singleton _

/-- **The transport layer**: membership of a law's ideal point in a
presented diagram's model class is exactly satisfaction of the
diagram's conjunction — the squares' constraint stratum lifts
wholesale to the semantic universe's judgment. -/
theorem idealPoint_mem_diagramDnf_iff (L : List (SubPMF V → Prop))
    (μ : SubPMF V) :
    idealPoint μ ∈ (diagramDnf L).modelClass ↔ looseConj L μ := by
  rw [SpecDnf.mem_modelClass_iff]
  constructor
  · rintro ⟨a, ha, hsat⟩
    rw [show (diagramDnf L).atoms = {diagramAtom L} from rfl,
      Set.mem_singleton_iff] at ha
    subst ha
    simp only [diagramAtom_floor, diagramAtom_marks] at hsat
    exact coupledSat_idealPoint_cwall_iff.mp hsat
  · intro h
    exact ⟨diagramAtom L, rfl, coupledSat_idealPoint_cwall_iff.mpr h⟩

/-- The inconsistent system belongs to no presented diagram's model
class — the structural ex-falso inversion of the DNF stratum, at the
compiled presentations. -/
theorem top_notMem_diagramDnf (L : List (SubPMF V → Prop)) :
    (⊤ : Plain.Pen V) ∉ (diagramDnf L).modelClass :=
  (diagramDnf L).top_notMem_modelClass

/-! ## The fence: why the singleton, not the ray

The credal presentation's precise face is the down-closed ray; the
judgment-side entry is the singleton.  The choice is forced: the
safety face of the coupled judgment reads the *whole* body of the
system penalty, and an equality floor vanishes only at the pinned
point — so the ray-embedded system fails its own pinning floor away
from bottom, while the ideal point satisfies it.  Slice discipline
(read a credal set at its radially maximal slice) is a verdict-layer
operation; the fibre order does not carry it, and the reconciliation
is the envelope stratum's theorem, consumed by the slice corollaries
below. -/

/-- **The fence**: at the point mass on the one-outcome carrier, the
ideal point satisfies the singleton pinning floor while the
ray-embedded system does not — safety is refuted at the half-scaling's
image point, which lies on the ray but not in the singleton. -/
theorem coupledSat_rayWall_singleton_floor_fails :
    CoupledSat (idealPoint (SubPMF.dirac (() : Unit)))
        (cwall (singletonC (SubPMF.dirac ()))) {(⊤ : Plain.Pen Unit)}
      ∧ ¬ CoupledSat (cwall (rayC (SubPMF.dirac (() : Unit))))
          (cwall (singletonC (SubPMF.dirac ()))) {(⊤ : Plain.Pen Unit)} := by
  constructor
  · exact coupledSat_idealPoint_cwall_iff.mpr
      (singletonC_self (SubPMF.dirac ()))
  · rintro ⟨hsafe, -⟩
    set μd : SubPMF Unit := SubPMF.dirac () with hμd
    set μh : SubPMF Unit :=
      SubPMF.scale (1/2) (by norm_num) (by norm_num) μd with hμh
    have hray : rayC μd μh := ⟨1/2, by norm_num, by norm_num, rfl⟩
    have hmem : μh.toJoint ∈ SubPMF.toJoint '' {μ : SubPMF Unit | rayC μd μ} :=
      ⟨μh, hray, rfl⟩
    have h0 : cwall (singletonC μd) μh.toJoint = 0 := by
      have h := hsafe μh.toJoint
      rw [show cwall (rayC μd) μh.toJoint = 0 from
        wallPen_apply_of_mem hmem] at h
      exact le_zero_iff.mp h
    have hsing : singletonC μd μh := cwall_toJoint_eq_zero_iff.mp h0
    have heq : μh = μd := (singletonC_iff μd μh).mp hsing
    have hm1 : μh.mass = 1/2 * μd.mass := SubPMF.mass_scale _ _ _ _
    have hm2 : μd.mass = 1 := SubPMF.dirac_prob_of_mem (Set.mem_univ ())
    rw [heq, hm2] at hm1
    norm_num at hm1

/-! ## The chain square, wired -/

section DtmcWiring

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The compiled chain's presentation in the semantic universe's fibre
over horizon-`k` trajectories: its constraint diagram, wall-ified. -/
noncomputable def dtmcDnf (R : DtmcRows S) (k : ℕ) :
    SpecDnf (Plain.Joint (Traj S k)) :=
  diagramDnf (atoms R k)

/-- The rows-grain wiring: an ideal point models the compiled rows'
presentation exactly when its law is the rows' path law — the chain
square's feeding lemma, read at the semantic universe's judgment. -/
theorem su_dtmc_wiring {R : DtmcRows S} (hR : R.WF) (k : ℕ)
    (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈ (dtmcDnf R k).modelClass ↔ μ = rowsLaw R hR k :=
  (idealPoint_mem_diagramDnf_iff (atoms R k) μ).trans (satAtoms_iff hR μ)

/-- **The chain square, wired to the semantic universe**: the ideal
point of a law models the compiled chain's presentation exactly when
the law is the chain's classical path law. -/
theorem su_dtmc_adequacy (M : FinDTMC S) (k : ℕ) (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈ (dtmcDnf (compile M) k).modelClass ↔ μ = M.pathLaw k := by
  rw [su_dtmc_wiring (compile_wf M) k μ, compile_rowsLaw]

/-- The positive face: the chain's own law models its compiled
presentation. -/
theorem su_dtmc_pathLaw_mem (M : FinDTMC S) (k : ℕ) :
    idealPoint (M.pathLaw k) ∈ (dtmcDnf (compile M) k).modelClass :=
  (su_dtmc_adequacy M k (M.pathLaw k)).mpr rfl

/-- Option A at the chain's corner: the law's ideal point satisfies
the vacuous atom. -/
theorem su_dtmc_vacuous (M : FinDTMC S) (k : ℕ) :
    CoupledSat (idealPoint (M.pathLaw k)) (0 : Plain.Pen (Traj S k))
      {(⊤ : Plain.Pen (Traj S k))} :=
  idealPoint_proper _

omit [DecidableEq S] in
/-- Ex falso at the chain's corner: the inconsistent system does not
model the compiled chain. -/
theorem su_dtmc_bottom (M : FinDTMC S) (k : ℕ) :
    (⊤ : Plain.Pen (Traj S k)) ∉ (dtmcDnf (compile M) k).modelClass :=
  top_notMem_diagramDnf _

/-- A stochastic chain's law is never the bottom law (its mass is
one). -/
theorem FinDTMC.pathLaw_ne_zero (M : FinDTMC S) (k : ℕ) :
    M.pathLaw k ≠ SubPMF.zero (Traj S k) := by
  intro h
  have h1 := M.pathLaw_mass k
  rw [h] at h1
  have h2 : (SubPMF.zero (Traj S k)).mass = 0 := SubPMF.zero_prob Set.univ
  rw [h2] at h1
  exact one_ne_zero h1.symm

/-- The credal reading, recovered through the landed slice
reconciliation: membership at the semantic universe's judgment is
exactly radial maximality in the chain law's credal ray. -/
theorem su_dtmc_slice (M : FinDTMC S) (k : ℕ) (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈ (dtmcDnf (compile M) k).modelClass
      ↔ maxSlice (rayC (M.pathLaw k)) μ :=
  (su_dtmc_adequacy M k μ).trans
    (maxSlice_rayC (FinDTMC.pathLaw_ne_zero M k) μ).symm

end DtmcWiring

/-! ## The decision-process squares, wired -/

section MdpWiring

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- The compiled decision former's fixed-policy presentation: the
action-keyed rows closed through the policy rows at the row level,
then wall-ified — the shipped factoring, in the fibre. -/
noncomputable def mdpDnf (R : MdpRows S A) (σp : PolicyRows S A) (k : ℕ) :
    SpecDnf (Plain.Joint (Traj S k)) :=
  diagramDnf (atoms (closeRows R σp) k)

omit [DecidableEq A] in
/-- **The fixed-policy square, wired**: the ideal point of a law
models the closed-loop presentation exactly when the law is the
fixed-policy trajectory law — the chain wiring at the closed loop, by
the compile-commutes triangle; no new computation. -/
theorem su_mdp_adequacy (M : FinMDP S A) (π : Policy S A) (k : ℕ)
    (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈ (mdpDnf (compileMdp M) (compilePolicy π) k).modelClass
      ↔ μ = M.pathLaw π k := by
  have h := su_dtmc_wiring (compile_wf (M.closedLoop π)) k μ
  rw [compile_rowsLaw] at h
  exact h

omit [DecidableEq A] in
/-- The positive face: the fixed-policy law models its compiled
presentation. -/
theorem su_mdp_pathLaw_mem (M : FinMDP S A) (π : Policy S A) (k : ℕ) :
    idealPoint (M.pathLaw π k)
      ∈ (mdpDnf (compileMdp M) (compilePolicy π) k).modelClass :=
  (su_mdp_adequacy M π k (M.pathLaw π k)).mpr rfl

omit [DecidableEq S] [DecidableEq A] in
/-- Ex falso at the fixed-policy corner. -/
theorem su_mdp_bottom (M : FinMDP S A) (π : Policy S A) (k : ℕ) :
    (⊤ : Plain.Pen (Traj S k))
      ∉ (mdpDnf (compileMdp M) (compilePolicy π) k).modelClass :=
  top_notMem_diagramDnf _

omit [DecidableEq A] in
/-- A fixed-policy law is never the bottom law. -/
theorem FinMDP.pathLaw_ne_zero (M : FinMDP S A) (π : Policy S A) (k : ℕ) :
    M.pathLaw π k ≠ SubPMF.zero (Traj S k) :=
  FinDTMC.pathLaw_ne_zero (M.closedLoop π) k

omit [DecidableEq A] in
/-- The credal reading at the fixed-policy corner, through the slice. -/
theorem su_mdp_slice (M : FinMDP S A) (π : Policy S A) (k : ℕ)
    (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈ (mdpDnf (compileMdp M) (compilePolicy π) k).modelClass
      ↔ maxSlice (rayC (M.pathLaw π k)) μ :=
  (su_mdp_adequacy M π k μ).trans
    (maxSlice_rayC (FinMDP.pathLaw_ne_zero M π k) μ).symm

/-- The compiled decision former's demonic presentation: the
policy-free rows with the existentially quantified scheduler
mechanism, as a one-atom projection — the set-valued face presents as
a single wall atom, so citizenship (finite presentation) is untouched
by the policy family's infinitude. -/
noncomputable def mdpDemonicDnf (R : MdpRows S A) (k : ℕ) :
    SpecDnf (Plain.Joint (Traj S k)) :=
  diagramDnf [demonicC R k]

/-- **The demonic square, wired — the set stratum**: the ideal point
of a law models the policy-free demonic presentation exactly when the
law is a member of the demonic law-set.  The model class of the
compiled presentation, restricted to ideal points, is exactly the
adversary-quantified semantics. -/
theorem su_mdp_demonic_wiring (M : FinMDP S A) (k : ℕ)
    (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈ (mdpDemonicDnf (compileMdp M) k).modelClass
      ↔ M.demonicLaws k μ := by
  have h := idealPoint_mem_diagramDnf_iff [demonicC (compileMdp M) k] μ
  constructor
  · intro hm
    obtain ⟨h1, -⟩ := h.mp hm
    exact (demonicC_iff M k μ).mp h1
  · intro hd
    exact h.mpr ⟨(demonicC_iff M k μ).mpr hd, trivial⟩

/-- The policy-explicit face of the demonic wiring. -/
theorem su_mdp_demonic_wiring' (M : FinMDP S A) (k : ℕ)
    (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈ (mdpDemonicDnf (compileMdp M) k).modelClass
      ↔ ∃ π : Policy S A, μ = M.pathLaw π k :=
  su_mdp_demonic_wiring M k μ

omit [DecidableEq S] [DecidableEq A] in
/-- Ex falso at the demonic corner. -/
theorem su_mdp_demonic_bottom (M : FinMDP S A) (k : ℕ) :
    (⊤ : Plain.Pen (Traj S k))
      ∉ (mdpDemonicDnf (compileMdp M) k).modelClass :=
  top_notMem_diagramDnf _

/-- The credal reading at the demonic corner: membership at the
semantic universe's judgment is exactly radial maximality in the
union-of-rays credal object — the equal-mass slice reconciliation
(every closed-loop law has mass one) consumed whole. -/
theorem su_mdp_demonic_slice (M : FinMDP S A) (k : ℕ)
    (ν : SubPMF (Traj S k)) :
    idealPoint ν ∈ (mdpDemonicDnf (compileMdp M) k).modelClass
      ↔ maxSlice (M.demonicCredal k) ν :=
  (su_mdp_demonic_wiring M k ν).trans (demonic_maxSlice M k ν).symm

end MdpWiring

/-! ## The graphical-model square, wired -/

section PgmWiring

variable {n : ℕ} {Val : Fin (n + 1) → Type} [∀ i, Fintype (Val i)]

/-- The compiled network's presentation in the semantic universe's
fibre over joint assignments: its constraint diagram, wall-ified —
the wiring off the time-line, through the same generic bridge. -/
noncomputable def pgmDnf (R : Pgm.PgmRows n Val) :
    SpecDnf (Plain.Joint (Pgm.Asn Val)) :=
  diagramDnf (Pgm.atoms R)

/-- The rows-grain wiring for graphical models. -/
theorem su_pgm_wiring {R : Pgm.PgmRows n Val} (hR : R.WF)
    (μ : SubPMF (Pgm.Asn Val)) :
    idealPoint μ ∈ (pgmDnf R).modelClass ↔ μ = Pgm.rowsLaw R hR :=
  (idealPoint_mem_diagramDnf_iff (Pgm.atoms R) μ).trans
    (Pgm.satAtoms_iff hR μ)

/-- **The graphical-model square, wired**: the ideal point of a law
models the compiled network's presentation exactly when the law is
the chain-rule joint. -/
theorem su_pgm_adequacy (B : Pgm.FinBN n Val) (μ : SubPMF (Pgm.Asn Val)) :
    idealPoint μ ∈ (pgmDnf (Pgm.compile B)).modelClass
      ↔ μ = B.jointLaw := by
  rw [su_pgm_wiring (Pgm.compile_wf B) μ, Pgm.compile_rowsLaw]

/-- The positive face: the network's joint law models its compiled
presentation. -/
theorem su_pgm_jointLaw_mem (B : Pgm.FinBN n Val) :
    idealPoint B.jointLaw ∈ (pgmDnf (Pgm.compile B)).modelClass :=
  (su_pgm_adequacy B B.jointLaw).mpr rfl

/-- Ex falso at the network's corner. -/
theorem su_pgm_bottom (B : Pgm.FinBN n Val) :
    (⊤ : Plain.Pen (Pgm.Asn Val))
      ∉ (pgmDnf (Pgm.compile B)).modelClass :=
  top_notMem_diagramDnf _

/-- A network's joint law is never the bottom law. -/
theorem Pgm.FinBN.jointLaw_ne_zero (B : Pgm.FinBN n Val) :
    B.jointLaw ≠ SubPMF.zero (Pgm.Asn Val) := by
  intro h
  have h1 := B.jointLaw_mass
  rw [h] at h1
  have h2 : (SubPMF.zero (Pgm.Asn Val)).mass = 0 :=
    SubPMF.zero_prob Set.univ
  rw [h2] at h1
  exact one_ne_zero h1.symm

/-- The credal reading at the network's corner, through the slice. -/
theorem su_pgm_slice (B : Pgm.FinBN n Val) (μ : SubPMF (Pgm.Asn Val)) :
    idealPoint μ ∈ (pgmDnf (Pgm.compile B)).modelClass
      ↔ maxSlice (rayC B.jointLaw) μ :=
  (su_pgm_adequacy B μ).trans
    (maxSlice_rayC (Pgm.FinBN.jointLaw_ne_zero B) μ).symm

end PgmWiring

/-! ## The continuous-time square, wired at its jump-chain face -/

section CtmcWiring

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The compiled continuous-time chain's presentation at its jump-chain
face: the jump closure of the off-diagonal rate rows, as a chain
presentation in the fibre. -/
noncomputable def ctmcJumpDnf (R : CtmcRows S) (k : ℕ) :
    SpecDnf (Plain.Joint (Traj S k)) :=
  dtmcDnf (jumpRows R) k

/-- **The jump-chain square, wired to the semantic universe**: the
ideal point of a law models the compiled rate rows' jump-closed
presentation exactly when the law is the classical jump chain's path
law — the chain wiring at the jump chain, through the compile-commutes
triangle; no new computation. -/
theorem su_ctmc_jump_adequacy (M : FinCTMC S) (k : ℕ)
    (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈ (ctmcJumpDnf (compileCtmc M) k).modelClass
      ↔ μ = M.jumpLaw k := by
  have h := su_dtmc_wiring (compile_wf M.jumpChain) k μ
  rw [compile_rowsLaw] at h
  show idealPoint μ ∈ (dtmcDnf (jumpRows (compileCtmc M)) k).modelClass
    ↔ μ = M.jumpLaw k
  rw [compile_jump_comm]
  exact h

/-- The positive face: the jump-chain law models its compiled
presentation. -/
theorem su_ctmc_jump_jumpLaw_mem (M : FinCTMC S) (k : ℕ) :
    idealPoint (M.jumpLaw k)
      ∈ (ctmcJumpDnf (compileCtmc M) k).modelClass :=
  (su_ctmc_jump_adequacy M k (M.jumpLaw k)).mpr rfl

/-- Ex falso at the jump-chain corner. -/
theorem su_ctmc_jump_bottom (M : FinCTMC S) (k : ℕ) :
    (⊤ : Plain.Pen (Traj S k))
      ∉ (ctmcJumpDnf (compileCtmc M) k).modelClass :=
  top_notMem_diagramDnf _

/-- A jump-chain law is never the bottom law — inherited from the chain
engine at the jump chain. -/
theorem FinCTMC.jumpLaw_ne_zero (M : FinCTMC S) (k : ℕ) :
    M.jumpLaw k ≠ SubPMF.zero (Traj S k) :=
  FinDTMC.pathLaw_ne_zero M.jumpChain k

/-- The credal reading at the jump-chain corner, through the slice. -/
theorem su_ctmc_jump_slice (M : FinCTMC S) (k : ℕ)
    (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈ (ctmcJumpDnf (compileCtmc M) k).modelClass
      ↔ maxSlice (rayC (M.jumpLaw k)) μ :=
  (su_ctmc_jump_adequacy M k μ).trans
    (maxSlice_rayC (FinCTMC.jumpLaw_ne_zero M k) μ).symm

end CtmcWiring

/-! ## The Markov-automaton square, wired at its fixed-scheduler face -/

section MaWiring

variable {S I A : Type} [Fintype S] [DecidableEq S]
  [Fintype I] [DecidableEq I] [Fintype A]

/-- The compiled Markov automaton's presentation at its closed,
jump-chain face: the scheduler closure of the compiled rows at the
given absorption fuel, then the jump closure, as a chain presentation
in the fibre. -/
noncomputable def maDnf (R : MaRows S I A) (σr : PolicyRows I A)
    (n k : ℕ) : SpecDnf (Plain.Joint (Traj S k)) :=
  ctmcJumpDnf (closeMaRows R σr n) k

/-- **The fixed-scheduler square, wired to the semantic universe**:
the ideal point of a law models the compiled automaton-and-scheduler
presentation exactly when the law is the closed chain's jump-chain
path law — the continuous-time wiring at the closed automaton, through
the rate-closure triangle; no new computation. -/
theorem su_ma_adequacy (M : FinMA S I A) (σ : Policy I A) (r : I → ℕ)
    (hr : ZenoFree (M.imStep σ) r) (k : ℕ) (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈
        (maDnf (compileMa M) (compilePolicy σ) (absFuel r) k).modelClass
      ↔ μ = M.pathLaw σ r hr k := by
  have h := su_ctmc_jump_adequacy (M.close σ r hr) k μ
  show idealPoint μ ∈ (ctmcJumpDnf
      (closeMaRows (compileMa M) (compilePolicy σ) (absFuel r))
      k).modelClass ↔ μ = M.pathLaw σ r hr k
  rw [compile_closeMa_comm M σ r hr]
  exact h

/-- The positive face: the fixed-scheduler law models its compiled
presentation. -/
theorem su_ma_pathLaw_mem (M : FinMA S I A) (σ : Policy I A)
    (r : I → ℕ) (hr : ZenoFree (M.imStep σ) r) (k : ℕ) :
    idealPoint (M.pathLaw σ r hr k) ∈
      (maDnf (compileMa M) (compilePolicy σ) (absFuel r) k).modelClass :=
  (su_ma_adequacy M σ r hr k (M.pathLaw σ r hr k)).mpr rfl

/-- Ex falso at the fixed-scheduler corner. -/
theorem su_ma_bottom (M : FinMA S I A) (σ : Policy I A) (r : I → ℕ)
    (k : ℕ) :
    (⊤ : Plain.Pen (Traj S k)) ∉
      (maDnf (compileMa M) (compilePolicy σ) (absFuel r) k).modelClass :=
  top_notMem_diagramDnf _

/-- A fixed-scheduler law is never the bottom law — inherited through
both closures. -/
theorem FinMA.pathLaw_ne_zero (M : FinMA S I A) (σ : Policy I A)
    (r : I → ℕ) (hr : ZenoFree (M.imStep σ) r) (k : ℕ) :
    M.pathLaw σ r hr k ≠ SubPMF.zero (Traj S k) :=
  FinCTMC.jumpLaw_ne_zero (M.close σ r hr) k

/-- The credal reading at the fixed-scheduler corner, through the
slice. -/
theorem su_ma_slice (M : FinMA S I A) (σ : Policy I A) (r : I → ℕ)
    (hr : ZenoFree (M.imStep σ) r) (k : ℕ) (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈
        (maDnf (compileMa M) (compilePolicy σ) (absFuel r) k).modelClass
      ↔ maxSlice (rayC (M.pathLaw σ r hr k)) μ :=
  (su_ma_adequacy M σ r hr k μ).trans
    (maxSlice_rayC (M.pathLaw_ne_zero σ r hr k) μ).symm

end MaWiring

/-! ## The Markov-automaton square, wired at its demonic face -/

section MaDemonicWiring

variable {S I A : Type} [Fintype S] [DecidableEq S]
  [Fintype I] [DecidableEq I] [Fintype A]

/-- The compiled Markov automaton's demonic presentation: the
scheduler-free rows with the existentially quantified scheduler-row
mechanism at the given absorption fuel, as a one-atom projection —
the set-valued face presents as a single wall atom, so citizenship
(finite presentation) is untouched by the scheduler family's
infinitude, exactly as at the decision former's demonic corner. -/
noncomputable def maDemonicDnf (R : MaRows S I A) (n k : ℕ) :
    SpecDnf (Plain.Joint (Traj S k)) :=
  diagramDnf [maDemonicC R n k]

/-- **The demonic automaton square, wired — the set stratum**: the
ideal point of a law models the scheduler-free demonic presentation,
at the certificate's working fuel, exactly when the law is a member of
the demonic law-set.  The model class of the compiled presentation,
restricted to ideal points, is exactly the scheduler-quantified
semantics. -/
theorem su_ma_demonic_wiring (M : FinMA S I A) {r : I → ℕ}
    (hb : M.BranchZenoFree r) (k : ℕ) (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈ (maDemonicDnf (compileMa M) (absFuel r) k).modelClass
      ↔ M.demonicLaws r hb k μ := by
  have h := idealPoint_mem_diagramDnf_iff
    [maDemonicC (compileMa M) (absFuel r) k] μ
  constructor
  · intro hm
    obtain ⟨h1, -⟩ := h.mp hm
    exact (maDemonicC_iff M hb k μ).mp h1
  · intro hd
    exact h.mpr ⟨(maDemonicC_iff M hb k μ).mpr hd, trivial⟩

/-- The scheduler-explicit face of the demonic wiring. -/
theorem su_ma_demonic_wiring' (M : FinMA S I A) {r : I → ℕ}
    (hb : M.BranchZenoFree r) (k : ℕ) (μ : SubPMF (Traj S k)) :
    idealPoint μ ∈ (maDemonicDnf (compileMa M) (absFuel r) k).modelClass
      ↔ ∃ σ : Policy I A, μ = M.pathLaw σ r (hb.zenoFree σ) k :=
  su_ma_demonic_wiring M hb k μ

/-- Ex falso at the demonic corner of the automaton frame. -/
theorem su_ma_demonic_bottom (M : FinMA S I A) (n k : ℕ) :
    (⊤ : Plain.Pen (Traj S k))
      ∉ (maDemonicDnf (compileMa M) n k).modelClass :=
  top_notMem_diagramDnf _

/-- The credal reading at the demonic corner: membership at the
semantic universe's judgment is exactly radial maximality in the
union-of-rays credal object — the equal-mass slice reconciliation
(every closed law has mass one) consumed whole, at continuous time. -/
theorem su_ma_demonic_slice (M : FinMA S I A) {r : I → ℕ}
    (hb : M.BranchZenoFree r) (k : ℕ) (ν : SubPMF (Traj S k)) :
    idealPoint ν ∈ (maDemonicDnf (compileMa M) (absFuel r) k).modelClass
      ↔ maxSlice (M.demonicCredal r hb k) ν :=
  (su_ma_demonic_wiring M hb k ν).trans
    (ma_demonic_maxSlice M hb k ν).symm

end MaDemonicWiring

end Adequacy

end SuFunctor
