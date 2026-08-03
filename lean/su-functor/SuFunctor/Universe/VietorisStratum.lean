import SuFunctor.Universe.VietorisDictionary
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Sets.VietorisTopology

/-! # The topological stratum of the radial-compile dictionary

`SuFunctor.Universe.VietorisDictionary` carries the order/algebra half
of the dictionary between penalties and their epistemic bodies; this
module carries the topology it deliberately deferred.

* **Bodies are closed (indeed compact) exactly for citizens**
  (`isClosed_compile_iff`): the radial compile turns lower
  semicontinuity of the penalty into closedness of the body — the
  set-side face of citizenship.  The forward implication factors
  through the grade transport `upperSemicontinuous_grade_comp` (lsc
  penalties have usc grade functions, via the order-inverse
  `gradeInv`), and the body is exhibited as the continuous image of a
  compact scale-graph; the converse reads sublevel sets off ray
  membership.
* **The system space is the hyperspace.**  Bodies of citizens are
  points of `NonemptyCompacts (BelState V)` (`compileNC`), the space
  of nonempty compact subsets with the Vietoris topology — which, on
  the compact metric carrier, is also the Hausdorff-metric topology
  (mathlib's `NonemptyCompacts.instEMetricSpace` is built on the
  Vietoris uniformity).
* **Radial sets are closed under hyperspace limits**
  (`isClosed_setOf_isRadial`): ray-down-closure survives Vietoris
  limits, so the radial locus — the image of the compile — is a
  compact sub-hyperspace (`isCompact_setOf_isRadial`).
* **Spec classes are hit-and-miss crescents.**  The class of bodies
  satisfying a spec atom (`crescentClass`) transports the coupled
  judgment (`compileNC_mem_crescentClass_iff`): containment in the
  safety body is an upper-Vietoris *closed* demand
  (`isClosed_safety_face`), escape past a liveness body is a
  lower-Vietoris *open* demand (`isOpen_escape_face`), and a whole
  atom class is locally closed (`isLocallyClosed_crescentClass`) —
  upper-closed ∩ finitely-many-lower-opens, never a basic open.  The
  liveness disjunction law is the hit-union law of the lower face
  (`escape_face_sup`).
* **Full-mass tips** (`toBel_mem_compile_iff`): the mass-one point of
  the ray at `μ₀` lies in a body iff the penalty vanishes at `μ₀` —
  the citizen-side reading of the upper-Vietoris basic open
  `{K | μ₀ ∉ K}`, whose judgment-inexpressibility is proved in
  `SuFunctor.Universe.Points`.
* **Graded atoms on the hyperspace** (`supAtom`, `infAtom`): for an
  lsc parameter both atoms are Vietoris-lsc, through *opposite* faces
  — the sup-atom's superlevels are hit classes (`lt_supAtom_iff`),
  the inf-atom's are containment classes (`lt_infAtom_iff`, where
  lower semicontinuity buys attainment of the infimum on each compact
  point).  Atoms are polarity-pure: each is a citizen of the
  hyperspace universe through exactly one face of the sub-base.
-/

namespace SuFunctor.Universe

open scoped ENNReal
open TopologicalSpace

/-! ## The grade inverse, and semicontinuity transport -/

/-- The order-inverse of the grade map: `−log c` as a penalty height,
with nonpositive grades sent to hard violation.  On `(0, 1]` it is a
two-sided inverse to `grade` (`grade_gradeInv`). -/
noncomputable def gradeInv (c : ℝ) : ℝ≥0∞ :=
  if c ≤ 0 then ⊤ else ENNReal.ofReal (-Real.log c)

theorem grade_gradeInv {c : ℝ} (h0 : 0 < c) (h1 : c ≤ 1) :
    grade (gradeInv c) = c := by
  rw [gradeInv, if_neg (not_le.mpr h0), grade_of_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (neg_nonneg.mpr (Real.log_nonpos h0.le h1)),
    neg_neg, Real.exp_log h0]

theorem le_grade_iff {c : ℝ} {a : ℝ≥0∞} (h0 : 0 < c) (h1 : c ≤ 1) :
    c ≤ grade a ↔ a ≤ gradeInv c := by
  conv_lhs => rw [← grade_gradeInv h0 h1]
  exact grade_le_grade_iff

variable {V : Type*} [Fintype V]

/-- Citizens have upper semicontinuous grade functions: the compile
sends the lsc penalty scale to the usc grade scale through the
antitone `grade`. -/
theorem upperSemicontinuous_grade_comp {f : ProbPenalty V}
    (hf : LowerSemicontinuous f) :
    UpperSemicontinuous fun μ => grade (f μ) := by
  intro μ c hc
  rcases eq_or_ne (f μ) 0 with h0 | h0
  · have hc1 : (1 : ℝ) < c := by
      rw [← grade_zero, ← h0]
      exact hc
    exact Filter.Eventually.of_forall fun ν =>
      lt_of_le_of_lt (grade_le_one _) hc1
  · have hcpos : 0 < c := lt_of_le_of_lt (grade_nonneg _) hc
    have hy : ∃ y, y < f μ ∧ grade y < c := by
      by_cases hc1 : c ≤ 1
      · have hlt : gradeInv c < f μ :=
          grade_lt_grade_iff.mp (by rw [grade_gradeInv hcpos hc1]; exact hc)
        obtain ⟨y, hy1, hy2⟩ := exists_between hlt
        exact ⟨y, hy2, by
          rw [← grade_gradeInv hcpos hc1]
          exact grade_strictAnti hy1⟩
      · exact ⟨0, pos_iff_ne_zero.mpr h0, by
          rw [grade_zero]
          exact not_le.mp hc1⟩
    obtain ⟨y, hy1, hy2⟩ := hy
    filter_upwards [hf μ y hy1] with ν hν
    exact lt_of_le_of_lt (grade_anti hν.le) hy2

/-! ## Bodies are compact and closed exactly for citizens -/

/-- The scale graph of a citizen — the region under its grade function
— is closed: the hypograph of the usc grade. -/
private theorem isClosed_scaleGraph {f : ProbPenalty V}
    (hf : LowerSemicontinuous f) :
    IsClosed {p : ProbState V × ℝ | 0 ≤ p.2 ∧ p.2 ≤ grade (f p.1)} := by
  have h1 : IsClosed {p : ProbState V × ℝ | 0 ≤ p.2} :=
    isClosed_le continuous_const continuous_snd
  have h2 : IsClosed {p : ProbState V × ℝ | p.2 ≤ grade (f p.1)} :=
    (upperSemicontinuous_grade_comp hf).IsClosed_hypograph
  have h12 := h1.inter h2
  rwa [← Set.setOf_and] at h12

/-- **Bodies of citizens are compact**: the compile is the continuous
image of the (closed, hence compact) scale graph under the radial
map. -/
theorem isCompact_compile {f : ProbPenalty V} (hf : LowerSemicontinuous f) :
    IsCompact (compile f) := by
  rw [Topology.IsInducing.subtypeVal.isCompact_iff]
  have hKK : IsCompact {p : ProbState V × ℝ | 0 ≤ p.2 ∧ p.2 ≤ grade (f p.1)} :=
    IsCompact.of_isClosed_subset (isCompact_univ.prod isCompact_Icc)
      (isClosed_scaleGraph hf)
      (fun p hp => ⟨Set.mem_univ _, hp.1, hp.2.trans (grade_le_one _)⟩)
  have him : Subtype.val '' compile f
      = (fun p : ProbState V × ℝ => p.2 • ((p.1 : ProbState V) : V → ℝ))
          '' {p | 0 ≤ p.2 ∧ p.2 ≤ grade (f p.1)} := by
    ext y
    constructor
    · rintro ⟨x, ⟨μ, γ, h0, hle, he⟩, rfl⟩
      exact ⟨(μ, γ), ⟨h0, hle⟩, he.symm⟩
    · rintro ⟨⟨μ, γ⟩, ⟨h0, hle⟩, rfl⟩
      exact ⟨scalePoint γ h0 (hle.trans (grade_le_one _)) μ,
        ⟨μ, γ, h0, hle, rfl⟩, rfl⟩
  rw [him]
  refine hKK.image (continuous_pi fun v => ?_)
  exact continuous_snd.mul
    (((continuous_apply v).comp continuous_subtype_val).comp continuous_fst)

theorem isClosed_compile {f : ProbPenalty V} (hf : LowerSemicontinuous f) :
    IsClosed (compile f) :=
  (isCompact_compile hf).isClosed

/-- **The topological face of citizenship**: the body is closed iff the
penalty is a citizen.  The converse direction reads each sublevel set
off ray membership: `f μ ≤ s` holds exactly when the `grade s`-scaled
point of the ray at `μ` lies in the body. -/
theorem isClosed_compile_iff [Nonempty V] {f : ProbPenalty V} :
    IsClosed (compile f) ↔ LowerSemicontinuous f := by
  refine ⟨fun hcl => ?_, isClosed_compile⟩
  rw [lowerSemicontinuous_prob_iff_isClosed_sublevel]
  intro s
  rcases eq_or_ne s ⊤ with rfl | hs
  · simp only [le_top, Set.setOf_true]
    exact isClosed_univ
  · have h0 : (0 : ℝ) < grade s := grade_pos hs
    have hval : IsClosed (Subtype.val '' compile f) :=
      (hcl.isCompact.image continuous_subtype_val).isClosed
    have hsub : {μ : ProbState V | f μ ≤ s}
        = (fun μ : ProbState V => grade s • (μ : V → ℝ)) ⁻¹'
            (Subtype.val '' compile f) := by
      ext μ
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      constructor
      · intro h
        exact ⟨scalePoint (grade s) h0.le (grade_le_one s) μ,
          ⟨μ, grade s, h0.le, grade_anti h, rfl⟩, rfl⟩
      · rintro ⟨x, hx, hxe⟩
        exact grade_le_grade_iff.mp (compile_scale_le hx h0 hxe)
    have hcont : Continuous fun μ : ProbState V => grade s • (μ : V → ℝ) := by
      refine continuous_pi fun v => ?_
      show Continuous fun μ : ProbState V => grade s * (μ : V → ℝ) v
      exact continuous_const.mul ((continuous_apply v).comp continuous_subtype_val)
    rw [hsub]
    exact hval.preimage hcont

/-- Full-mass tips: the mass-one point of the ray at `μ₀` lies in a
body iff the penalty vanishes at `μ₀`.  (The citizen-side reading of
the upper-Vietoris basic open `{K | μ₀ ∉ K}`: its trace on bodies is
`{σ | σ μ₀ ≠ 0}`, which `SuFunctor.Universe.Points` proves is not a
spec class.) -/
theorem toBel_mem_compile_iff {f : ProbPenalty V} {μ₀ : ProbState V} :
    μ₀.toBel ∈ compile f ↔ f μ₀ = 0 := by
  constructor
  · intro h
    have hd : ((μ₀.toBel : BelState V) : V → ℝ) = (1 : ℝ) • (μ₀ : V → ℝ) := by
      rw [one_smul]; rfl
    have h1 : (1 : ℝ) ≤ grade (f μ₀) := compile_scale_le h one_pos hd
    have h2 : grade 0 ≤ grade (f μ₀) := by
      rw [grade_zero]; exact h1
    exact nonpos_iff_eq_zero.mp (grade_le_grade_iff.mp h2)
  · intro h
    exact ⟨μ₀, 1, zero_le_one, by rw [h, grade_zero], by rw [one_smul]; rfl⟩

/-! ## The compile as a hyperspace point -/

/-- The body of a citizen, packaged as a point of the hyperspace of
nonempty compact subsets of the subprobability carrier. -/
noncomputable def compileNC [Nonempty V] (f : ProbPenalty V)
    (hf : LowerSemicontinuous f) : NonemptyCompacts (BelState V) :=
  ⟨⟨compile f, isCompact_compile hf⟩, ⟨BelState.zero V, zero_mem_compile f⟩⟩

@[simp] theorem coe_compileNC [Nonempty V] (f : ProbPenalty V)
    (hf : LowerSemicontinuous f) :
    (compileNC f hf : Set (BelState V)) = compile f := rfl

/-! ## Radial sets, and the radial locus of the hyperspace -/

/-- Scaling a distribution by `t ∈ [0, 1]`: the ray-down motion of the
carrier. -/
def BelState.scale (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (x : BelState V) :
    BelState V :=
  ⟨t • (x : V → ℝ), fun v => mul_nonneg h0 (x.nonneg v), by
    have hsum : ∑ v, (t • (x : V → ℝ)) v = t * ∑ v, (x : V → ℝ) v := by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum]
    rw [hsum]
    calc t * ∑ v, (x : V → ℝ) v ≤ 1 * 1 := by
          exact mul_le_mul h1 x.mass_le_one
            (Finset.sum_nonneg fun v _ => x.nonneg v) zero_le_one
      _ = 1 := one_mul 1⟩

@[simp] theorem BelState.coe_scale (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (x : BelState V) :
    ((BelState.scale t h0 h1 x : BelState V) : V → ℝ) = t • (x : V → ℝ) := rfl

/-- Scaling by `t ∈ [0, 1]` is `1`-Lipschitz on the carrier. -/
theorem BelState.dist_scale_le (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (x y : BelState V) :
    dist (BelState.scale t h0 h1 x) (BelState.scale t h0 h1 y) ≤ dist x y := by
  rw [Subtype.dist_eq]
  refine (dist_pi_le_iff dist_nonneg).mpr fun v => ?_
  simp only [BelState.coe_scale, Pi.smul_apply, smul_eq_mul, Real.dist_eq,
    ← mul_sub, abs_mul, abs_of_nonneg h0]
  calc t * |(x : V → ℝ) v - (y : V → ℝ) v|
      ≤ 1 * |(x : V → ℝ) v - (y : V → ℝ) v| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = |(x : V → ℝ) v - (y : V → ℝ) v| := one_mul _
    _ ≤ dist x y := by
        rw [Subtype.dist_eq, ← Real.dist_eq]
        exact dist_le_pi_dist _ _ v

/-- Ray-down-closure: the defining property of epistemic bodies. -/
def IsRadial (R : Set (BelState V)) : Prop :=
  ∀ x ∈ R, ∀ (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1), BelState.scale t h0 h1 x ∈ R

/-- Every body is radial. -/
theorem isRadial_compile (f : ProbPenalty V) : IsRadial (compile f) := by
  rintro x ⟨μ, γ, h0, hle, he⟩ t ht0 ht1
  refine ⟨μ, t * γ, mul_nonneg ht0 h0, (mul_le_of_le_one_left h0 ht1).trans hle, ?_⟩
  rw [BelState.coe_scale, he, smul_smul]

/-- **Radial sets are closed under hyperspace limits**: the radial
locus is closed in the Vietoris topology.  A failure of ray-closure at
`x` is witnessed by a hit-and-miss neighborhood — hit a small ball at
`x`, miss a closed ball at the escaped scaled point — and scaling's
`1`-Lipschitz bound transports the failure to every nearby body. -/
theorem isClosed_setOf_isRadial :
    IsClosed {K : NonemptyCompacts (BelState V) | IsRadial (K : Set (BelState V))} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  rintro K hK
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, IsRadial] at hK
  push Not at hK
  obtain ⟨x, hxK, t, h0, h1, hout⟩ := hK
  have hpos : 0 < Metric.infDist (BelState.scale t h0 h1 x : BelState V) (K : Set (BelState V)) :=
    (IsClosed.notMem_iff_infDist_pos K.isCompact.isClosed K.nonempty).mp hout
  set ε := Metric.infDist (BelState.scale t h0 h1 x : BelState V) (K : Set (BelState V)) with hε
  refine ⟨{K' : NonemptyCompacts (BelState V) |
        ((K' : Set (BelState V)) ∩ Metric.ball x (ε / 2)).Nonempty}
      ∩ {K' : NonemptyCompacts (BelState V) |
        (K' : Set (BelState V)) ⊆ (Metric.closedBall (BelState.scale t h0 h1 x) (ε / 2))ᶜ},
    ?_, ?_, ?_⟩
  · -- every body in the neighborhood fails ray-closure
    rintro K' ⟨⟨x', hx'K, hx'ball⟩, hmiss⟩
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, IsRadial]
    push Not
    refine ⟨x', hx'K, t, h0, h1, fun hmem => ?_⟩
    have hd : dist (BelState.scale t h0 h1 x') (BelState.scale t h0 h1 x) ≤ dist x' x :=
      BelState.dist_scale_le t h0 h1 x' x
    have hin : BelState.scale t h0 h1 x'
        ∈ Metric.closedBall (BelState.scale t h0 h1 x) (ε / 2) :=
      Metric.mem_closedBall.mpr (hd.trans (Metric.mem_ball.mp hx'ball).le)
    exact hmiss hmem hin
  · exact (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen Metric.isOpen_ball).inter
      (NonemptyCompacts.isOpen_subsets_of_isOpen Metric.isClosed_closedBall.isOpen_compl)
  · constructor
    · exact ⟨x, hxK, Metric.mem_ball_self (by positivity)⟩
    · intro y hyK
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le]
      calc ε / 2 < ε := by linarith
        _ ≤ dist (BelState.scale t h0 h1 x : BelState V) y :=
            Metric.infDist_le_dist_of_mem hyK
        _ = dist y (BelState.scale t h0 h1 x : BelState V) := dist_comm _ _

/-- The radial locus is a compact sub-hyperspace: the system space in
its own right. -/
theorem isCompact_setOf_isRadial :
    IsCompact {K : NonemptyCompacts (BelState V) | IsRadial (K : Set (BelState V))} :=
  isClosed_setOf_isRadial.isCompact

/-! ## Spec classes are hit-and-miss crescents -/

/-- The hyperspace class of a spec atom `(u, 𝒱)`: bodies contained in
the safety body that escape every liveness body.  Upper-closed ∩
finitely-many-lower-opens — a Vietoris crescent. -/
def crescentClass (u : ProbPenalty V) (𝒱 : Set (ProbPenalty V)) :
    Set (NonemptyCompacts (BelState V)) :=
  {K | (K : Set (BelState V)) ⊆ compile u}
    ∩ ⋂ v ∈ 𝒱, {K | ((K : Set (BelState V)) ∩ (compile v)ᶜ).Nonempty}

theorem mem_crescentClass_iff {u : ProbPenalty V} {𝒱 : Set (ProbPenalty V)}
    {K : NonemptyCompacts (BelState V)} :
    K ∈ crescentClass u 𝒱
      ↔ (K : Set (BelState V)) ⊆ compile u
        ∧ ∀ v ∈ 𝒱, ((K : Set (BelState V)) ∩ (compile v)ᶜ).Nonempty := by
  simp [crescentClass]

/-- **The judgment transports to crescent membership**: a citizen
satisfies a spec atom iff its body lies in the atom's crescent
class. -/
theorem compileNC_mem_crescentClass_iff [Nonempty V] {σ u : ProbPenalty V}
    {𝒱 : Set (ProbPenalty V)} (hσ : LowerSemicontinuous σ) :
    compileNC σ hσ ∈ crescentClass u 𝒱 ↔ CoupledSat σ u 𝒱 := by
  rw [mem_crescentClass_iff, coe_compileNC, coupledSat_iff_compile]
  refine and_congr Iff.rfl (forall₂_congr fun v _ => ?_)
  constructor
  · rintro ⟨x, hx1, hx2⟩
    exact ⟨x, hx1, hx2⟩
  · rintro ⟨x, hx1, hx2⟩
    exact ⟨x, hx1, hx2⟩

/-- The safety face is upper-Vietoris closed: containment in a
citizen's body is a closed demand. -/
theorem isClosed_safety_face {u : ProbPenalty V} (hu : LowerSemicontinuous u) :
    IsClosed {K : NonemptyCompacts (BelState V) | (K : Set (BelState V)) ⊆ compile u} :=
  NonemptyCompacts.isClosed_subsets_of_isClosed (isClosed_compile hu)

/-- The escape face is lower-Vietoris open: protruding past a
citizen's body is an open demand. -/
theorem isOpen_escape_face {v : ProbPenalty V} (hv : LowerSemicontinuous v) :
    IsOpen {K : NonemptyCompacts (BelState V) |
      ((K : Set (BelState V)) ∩ (compile v)ᶜ).Nonempty} :=
  NonemptyCompacts.isOpen_inter_nonempty_of_isOpen (isClosed_compile hv).isOpen_compl

/-- **Spec-atom classes are locally closed**: one closed containment
demand, finitely many open escape demands.  (They are not basic opens:
the miss-face parameter is closed, and must be —
`SuFunctor.Universe.Points.upper_open_not_definable` shows the open
miss-face classes are not spec classes at all.) -/
theorem isLocallyClosed_crescentClass {u : ProbPenalty V}
    {𝒱 : Set (ProbPenalty V)} (hu : LowerSemicontinuous u)
    (h𝒱 : 𝒱.Finite) (hlsc : ∀ v ∈ 𝒱, LowerSemicontinuous v) :
    IsLocallyClosed (crescentClass u 𝒱) :=
  ⟨⋂ v ∈ 𝒱, {K | ((K : Set (BelState V)) ∩ (compile v)ᶜ).Nonempty},
    {K | (K : Set (BelState V)) ⊆ compile u},
    h𝒱.isOpen_biInter fun v hv => isOpen_escape_face (hlsc v hv),
    isClosed_safety_face hu,
    Set.inter_comm _ _⟩

/-- **The hit-union law**: escape past a max-merged liveness body is
escape past one of the merged bodies — the lower face turns the
liveness disjunction (`dip_sup_iff`) into an exact identity of open
classes. -/
theorem escape_face_sup (v₁ v₂ : ProbPenalty V) :
    {K : NonemptyCompacts (BelState V) |
        ((K : Set (BelState V)) ∩ (compile (v₁ ⊔ v₂))ᶜ).Nonempty}
      = {K : NonemptyCompacts (BelState V) |
          ((K : Set (BelState V)) ∩ (compile v₁)ᶜ).Nonempty}
        ∪ {K : NonemptyCompacts (BelState V) |
            ((K : Set (BelState V)) ∩ (compile v₂)ᶜ).Nonempty} := by
  ext K
  rw [Set.mem_setOf_eq, compile_sup, Set.compl_inter,
    Set.inter_union_distrib_left]
  exact Set.union_nonempty

/-! ## Graded atoms on the hyperspace

For an lsc parameter `h`, the worst-case atom `supAtom h` and the
best-witness atom `infAtom h` are both lsc on the hyperspace — through
opposite faces of the Vietoris sub-base.  The statements are generic
in the base space; the universe instantiates them at
`X := BelState V`. -/

section Atoms

variable {X : Type*} [TopologicalSpace X]

/-- The hit-graded atom: the worst height the body commits to.  With
`h` a violation cost, this is the graded ∀-face penalty. -/
noncomputable def supAtom (h : X → ℝ≥0∞) (K : NonemptyCompacts X) : ℝ≥0∞ :=
  ⨆ x ∈ (K : Set X), h x

/-- The miss-graded atom: the cheapest witness the body contains.
With `h` a witness cost, this is the graded ∃-face penalty. -/
noncomputable def infAtom (h : X → ℝ≥0∞) (K : NonemptyCompacts X) : ℝ≥0∞ :=
  ⨅ x ∈ (K : Set X), h x

/-- Superlevels of the sup-atom are hit classes: the lower face. -/
theorem lt_supAtom_iff {h : X → ℝ≥0∞} {c : ℝ≥0∞} {K : NonemptyCompacts X} :
    c < supAtom h K ↔ ∃ x ∈ (K : Set X), c < h x :=
  lt_biSup_iff

/-- Superlevels of the inf-atom are containment classes: the upper
face.  Lower semicontinuity of the parameter buys attainment of the
infimum on the compact body. -/
theorem lt_infAtom_iff {h : X → ℝ≥0∞} (hh : LowerSemicontinuous h)
    {c : ℝ≥0∞} {K : NonemptyCompacts X} :
    c < infAtom h K ↔ ∀ x ∈ (K : Set X), c < h x := by
  constructor
  · intro hc x hx
    exact lt_of_lt_of_le hc (iInf₂_le x hx)
  · intro hall
    obtain ⟨x₀, hx₀, hmin⟩ :=
      (hh.lowerSemicontinuousOn (K : Set X)).exists_isMinOn K.nonempty K.isCompact
    have hval : infAtom h K = h x₀ :=
      le_antisymm (iInf₂_le x₀ hx₀) (le_iInf₂ fun x hx => hmin hx)
    rw [hval]
    exact hall x₀ hx₀

/-- **The sup-atom of an lsc parameter is Vietoris-lsc**, through the
lower (hit) face. -/
theorem lowerSemicontinuous_supAtom {h : X → ℝ≥0∞}
    (hh : LowerSemicontinuous h) :
    LowerSemicontinuous (supAtom h) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro c
  have heq : supAtom (X := X) h ⁻¹' Set.Ioi c
      = {K : NonemptyCompacts X | ((K : Set X) ∩ {x | c < h x}).Nonempty} := by
    ext K
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq, lt_supAtom_iff]
    constructor
    · rintro ⟨x, hx1, hx2⟩
      exact ⟨x, hx1, hx2⟩
    · rintro ⟨x, hx1, hx2⟩
      exact ⟨x, hx1, hx2⟩
  rw [heq]
  exact NonemptyCompacts.isOpen_inter_nonempty_of_isOpen
    (lowerSemicontinuous_iff_isOpen_preimage.mp hh c)

/-- **The inf-atom of an lsc parameter is Vietoris-lsc**, through the
upper (containment) face. -/
theorem lowerSemicontinuous_infAtom {h : X → ℝ≥0∞}
    (hh : LowerSemicontinuous h) :
    LowerSemicontinuous (infAtom h) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro c
  have heq : infAtom (X := X) h ⁻¹' Set.Ioi c
      = {K : NonemptyCompacts X | (K : Set X) ⊆ {x | c < h x}} := by
    ext K
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq,
      lt_infAtom_iff hh]
    rfl
  rw [heq]
  exact NonemptyCompacts.isOpen_subsets_of_isOpen
    (lowerSemicontinuous_iff_isOpen_preimage.mp hh c)

end Atoms

end SuFunctor.Universe
