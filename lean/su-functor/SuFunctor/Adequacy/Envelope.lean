import SuFunctor.Adequacy.Inclusions
import Mathlib.Data.Finsupp.SMul
import Mathlib.Tactic.NormNum

/-! # The envelope stratum: rays, the radially maximal slice, and credal verdicts

The credal presentation of the semantic universe is downward-scaling-
closed by convention: the precise face of a model `μ` is not the
one-point set `{μ}` but the closed ray `[0,1]·μ` (a credal denotation is
never a one-point set except at bottom).  The adequacy squares, by
contrast, state their bottom edges at the constraint stratum, where the
inclusion of a precise model is the exact singleton (`singletonC`):
equality constraints pin the point.  This module reconciles the two
presentations, following the slice discipline of the semantic-universe
chapter: the two readings agree on the **radially maximal slice** —
which is what the verdict operators read.

* `rayC μ` — membership in the closed ray `[0,1]·μ`, as a per-element
  constraint (a loose arrow of `Crd V`); `SubPMF.scale` is the witness
  constructor, with `SubPMF.prob_of_wt_smul` the scaling law for event
  probabilities.
* `maxSlice C` — the radially maximal slice of a constraint: members
  admitting no admitted upward scaling within the constraint.  This is
  the chapter's `S^max`, stated by upward-scaling escape; scalings that
  leave the subprobability space have no representative and escape
  vacuously, exactly as they lie outside every credal set.
* `maxSlice_rayC` — **the reconciliation**: for `μ ≠ 0`, the maximal
  slice of the ray is the singleton, `maxSlice (rayC μ) = singletonC μ`.
  At `μ = 0` the slice is *empty* (`maxSlice_rayC_zero`): the zero
  model is never radially maximal, since scaling zero is zero — the
  bottom credal object is the unique credal set with empty slice
  (`maxSlice_rayC_empty_iff`).
* `SatCredal` — the kind-selected credal satisfaction: a *lower*-kind
  constraint is read on the maximal slice, an *upper*-kind constraint
  on the whole set (`EnvelopeKind`).  The split is forced: the ray
  contains the zero model, so a whole-set reading of any lower bound
  with positive threshold refuses uniformly
  (`not_satCredal_upper_rayC_geC`), while the slice reading recovers
  the precise verdict exactly (`satCredal_lower_rayC_geC`).
* **Verdict agreement** — on either kind, the ray and the singleton
  agree: `satCredal_lower_ray_singleton` (on the slice, for `μ ≠ 0`)
  and `satCredal_upper_ray_singleton` (on the whole set, for
  *down-closed* constraints — the constraint-level form of the
  chapter's observation that the upper envelope is unaffected by
  down-closure on nonnegative gambles; event-probability upper bounds
  are down-closed, `downClosed_leC`).
* `ray_singleton_reconciliation` — the packaging: `maxSlice (rayC μ)`
  and `singletonC μ` are isomorphic as loose arrows of `Crd V` (an
  invertible globular cell), for `μ ≠ 0`.  The unsliced constraints are
  *not* isomorphic: `singletonC μ` entails `rayC μ`
  (`cellSingletonRay`) but the converse fails away from zero —
  `rayC_eq_singletonC_iff` locates the agreement of the raw
  constraints exactly at the bottom object.

Consumers: precise-frame squares may keep their exact singleton bottom
edges and inherit the chapter's credal reading through the slice; the
set-valued bottom edges (demonic choice, input boxes, mixtures) state
their credal sets at this stratum and read verdicts through
`SatCredal`.
-/

namespace SuFunctor

open CategoryTheory PseudoDoubleCategoryStruct

universe u

variable {V : Type u}

/-! ## Scaling subprobability mass functions -/

namespace SubPMF

@[simp] theorem zero_wt : (SubPMF.zero V).wt = 0 := rfl

/-- The scaling of a subprobability mass function by `t ∈ [0,1]`. -/
noncomputable def scale (t : ℚ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ : SubPMF V) : SubPMF V where
  wt := t • μ.wt
  nonneg v := by
    rw [Finsupp.smul_apply, smul_eq_mul]
    exact mul_nonneg h0 (μ.nonneg v)
  mass_le_one := by
    have hstep : ∑ v ∈ (t • μ.wt).support, (t • μ.wt) v
        = ∑ v ∈ μ.wt.support, (t • μ.wt) v :=
      Finset.sum_subset Finsupp.support_smul fun v _ hv =>
        Classical.byContradiction fun h => hv (Finsupp.mem_support_iff.mpr h)
    have hfac : ∑ v ∈ μ.wt.support, (t • μ.wt) v
        = t * ∑ v ∈ μ.wt.support, μ.wt v := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by
        rw [Finsupp.smul_apply, smul_eq_mul]
    rw [hstep, hfac]
    nlinarith [μ.mass_le_one]

@[simp] theorem scale_wt (t : ℚ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ : SubPMF V) :
    (scale t h0 h1 μ).wt = t • μ.wt := rfl

/-- Event probabilities scale with the weights: if `ν` is the
`t`-scaling of `μ` then every event's probability scales by `t`. -/
theorem prob_of_wt_smul {ν μ : SubPMF V} {t : ℚ} (h : ν.wt = t • μ.wt)
    (A : Set V) : ν.prob A = t * μ.prob A := by
  classical
  unfold SubPMF.prob
  rw [h]
  rw [Finset.sum_subset (Finsupp.support_smul (b := t) (g := μ.wt))
    (fun v _ hv => ?_)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, mul_ite, mul_zero]
  · have h0 : (t • μ.wt) v = 0 :=
      Classical.byContradiction fun h' => hv (Finsupp.mem_support_iff.mpr h')
    rw [h0, ite_self]

theorem mass_scale (t : ℚ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ : SubPMF V) :
    (scale t h0 h1 μ).mass = t * μ.mass :=
  prob_of_wt_smul rfl Set.univ

theorem eq_zero_iff_wt (μ : SubPMF V) : μ = SubPMF.zero V ↔ μ.wt = 0 :=
  ⟨fun h => by rw [h, zero_wt], fun h => SubPMF.ext' (by rw [h, zero_wt])⟩

/-- The point mass is never the zero model: the deterministic face
discharges the nonzero hypotheses of this module for free. -/
theorem dirac_ne_zero (v : V) : SubPMF.dirac v ≠ SubPMF.zero V := by
  intro h
  have h1 : (SubPMF.dirac v).wt v = 1 := by simp [SubPMF.dirac]
  rw [h] at h1
  simp at h1

end SubPMF

/-- Nonzero weight functions cancel scalars: two scalings of a nonzero
weight agree only at equal scale. -/
theorem smul_wt_cancel {w : V →₀ ℚ} (hw : w ≠ 0) {a b : ℚ}
    (h : a • w = b • w) : a = b := by
  by_contra hab
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  apply hw
  have h' : (a - b) • w = 0 := by rw [sub_smul, h, sub_self]
  calc w = (a - b)⁻¹ • ((a - b) • w) := by
        rw [smul_smul, inv_mul_cancel₀ hab', one_smul]
    _ = 0 := by rw [h', smul_zero]

/-! ## The ray and its radially maximal slice -/

/-- The closed-ray constraint: `ν` is an admitted downward scaling of
`μ`.  This is the credal presentation's precise face — the compile of
the indicator penalty at `μ` is the ray `[0,1]·μ`, not the singleton. -/
def rayC (μ : SubPMF V) : SubPMF V → Prop :=
  fun ν => ∃ t : ℚ, 0 ≤ t ∧ t ≤ 1 ∧ ν.wt = t • μ.wt

theorem rayC_self (μ : SubPMF V) : rayC μ μ :=
  ⟨1, zero_le_one, le_refl 1, (one_smul ℚ μ.wt).symm⟩

theorem rayC_zero (μ : SubPMF V) : rayC μ (SubPMF.zero V) :=
  ⟨0, le_refl 0, zero_le_one, by rw [SubPMF.zero_wt, zero_smul]⟩

/-- The singleton constraint entails the ray constraint: the exact
inclusion is *stronger* than the credal presentation's face. -/
theorem singletonC_le_rayC (μ ν : SubPMF V) (h : singletonC μ ν) :
    rayC μ ν := by
  rw [(singletonC_iff μ ν).mp h]
  exact rayC_self μ

/-- The radially maximal slice of a constraint: members admitting no
admitted upward scaling within the constraint.  Scalings with no
subprobability representative (mass beyond one) escape vacuously, as
they lie outside every credal set. -/
def maxSlice (C : SubPMF V → Prop) : SubPMF V → Prop :=
  fun ν => C ν ∧ ∀ l : ℚ, 1 < l → ∀ ν' : SubPMF V, ν'.wt = l • ν.wt → ¬ C ν'

/-- **The reconciliation, first half**: away from the bottom object,
the radially maximal slice of the ray is exactly the singleton.  The
credal presentation's precise face and the constraint stratum's exact
inclusion agree on the slice — which is what the verdict operators
read. -/
theorem maxSlice_rayC {μ : SubPMF V} (hμ : μ ≠ SubPMF.zero V)
    (ν : SubPMF V) : maxSlice (rayC μ) ν ↔ singletonC μ ν := by
  have hw : μ.wt ≠ 0 := fun h => hμ ((SubPMF.eq_zero_iff_wt μ).mpr h)
  constructor
  · rintro ⟨⟨t, ht0, ht1, hwt⟩, hmax⟩
    rcases lt_or_eq_of_le ht1 with ht | ht
    · exfalso
      rcases eq_or_lt_of_le ht0 with ht0' | ht0'
      · rw [← ht0', zero_smul] at hwt
        exact hmax 2 one_lt_two (SubPMF.zero V)
          (by rw [SubPMF.zero_wt, hwt, smul_zero]) (rayC_zero μ)
      · have hinv : 1 < t⁻¹ := by
          have h1 : t * t⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt ht0')
          nlinarith [inv_pos.mpr ht0']
        exact hmax t⁻¹ hinv μ
          (by rw [hwt, smul_smul, inv_mul_cancel₀ (ne_of_gt ht0'), one_smul])
          (rayC_self μ)
    · exact (singletonC_iff μ ν).mpr (SubPMF.ext' (by rw [hwt, ht, one_smul]))
  · intro h
    have hν : ν = μ := (singletonC_iff μ ν).mp h
    refine ⟨by rw [hν]; exact rayC_self μ, ?_⟩
    intro l hl ν' hwt' hray'
    obtain ⟨s, _, hs1, hs⟩ := hray'
    rw [hν] at hwt'
    have hls : l = s := smul_wt_cancel hw (hwt'.symm.trans hs)
    rw [hls] at hl
    exact absurd hs1 (not_le.mpr hl)

/-- **The bottom boundary**: the zero model is never radially maximal
(scaling zero is zero), so the ray at the bottom object has *empty*
slice — not the singleton `{0}`. -/
theorem maxSlice_rayC_zero (ν : SubPMF V) :
    ¬ maxSlice (rayC (SubPMF.zero V)) ν := by
  rintro ⟨⟨t, _, _, hwt⟩, hmax⟩
  rw [SubPMF.zero_wt, smul_zero] at hwt
  exact hmax 2 one_lt_two (SubPMF.zero V)
    (by rw [SubPMF.zero_wt, hwt, smul_zero]) (rayC_zero _)

/-- The bottom credal object is the unique ray with empty maximal
slice. -/
theorem maxSlice_rayC_empty_iff {μ : SubPMF V} :
    (∀ ν, ¬ maxSlice (rayC μ) ν) ↔ μ = SubPMF.zero V := by
  constructor
  · intro h
    by_contra hμ
    exact h μ ((maxSlice_rayC hμ μ).mpr (singletonC_self μ))
  · rintro rfl
    exact maxSlice_rayC_zero

/-- Away from the bottom object the singleton is its own maximal
slice, so the reconciliation statement is symmetric in its two
presentations. -/
theorem maxSlice_singletonC {μ : SubPMF V} (hμ : μ ≠ SubPMF.zero V)
    (ν : SubPMF V) : maxSlice (singletonC μ) ν ↔ singletonC μ ν := by
  have hw : μ.wt ≠ 0 := fun h => hμ ((SubPMF.eq_zero_iff_wt μ).mpr h)
  constructor
  · exact fun h => h.1
  · intro h
    have hν : ν = μ := (singletonC_iff μ ν).mp h
    refine ⟨h, ?_⟩
    intro l hl ν' hwt' h'
    have hν' : ν' = μ := (singletonC_iff μ ν').mp h'
    rw [hν, hν'] at hwt'
    have h1l : (1 : ℚ) = l :=
      smul_wt_cancel hw (by rw [one_smul]; exact hwt')
    rw [← h1l] at hl
    exact lt_irrefl 1 hl

/-- **The raw constraints diverge away from bottom**: the ray equals
the singleton exactly at the zero model.  (Forward: the half-scaling of
a nonzero `μ` lies on the ray but is not `μ` — mass below one or at one
alike; backward: the ray of zero collapses to the point.)  The
reconciliation of `maxSlice_rayC` is therefore genuinely *through the
slice*: no pointwise identification of the unsliced constraints
exists. -/
theorem rayC_eq_singletonC_iff {μ : SubPMF V} :
    (∀ ν, rayC μ ν ↔ singletonC μ ν) ↔ μ = SubPMF.zero V := by
  constructor
  · intro h
    by_contra hμ
    have hw : μ.wt ≠ 0 := fun h' => hμ ((SubPMF.eq_zero_iff_wt μ).mpr h')
    have hhalf : rayC μ (SubPMF.scale (1/2) (by norm_num) (by norm_num) μ) :=
      ⟨1/2, by norm_num, by norm_num, rfl⟩
    have heq : SubPMF.scale (1/2) (by norm_num) (by norm_num) μ = μ :=
      (singletonC_iff _ _).mp ((h _).mp hhalf)
    have heq' : (1/2 : ℚ) • μ.wt = μ.wt := by
      rw [← SubPMF.scale_wt (1/2) (by norm_num) (by norm_num) μ, heq]
    have hhalf1 : (1/2 : ℚ) = 1 :=
      smul_wt_cancel hw (by rw [one_smul]; exact heq')
    norm_num at hhalf1
  · rintro rfl
    intro ν
    constructor
    · rintro ⟨t, _, _, hwt⟩
      refine (singletonC_iff _ _).mpr (SubPMF.ext' ?_)
      rw [hwt, SubPMF.zero_wt, smul_zero]
    · exact singletonC_le_rayC _ ν

/-! ## Kind-selected credal satisfaction -/

/-- The two envelope components of the credal verdict pair.  A
lower-kind judgment is read on the radially maximal slice; an
upper-kind judgment on the whole set. -/
inductive EnvelopeKind : Type
  | lower
  | upper

/-- Kind-selected satisfaction of a per-element constraint by a credal
set (both presented as constraints): the lower kind quantifies over the
radially maximal slice, the upper kind over the whole set.  The split
is the slice discipline of the semantic-universe chapter: every credal
set contains the zero model, so a whole-set reading of a lower bound is
degenerate. -/
def SatCredal (k : EnvelopeKind) (C c : SubPMF V → Prop) : Prop :=
  match k with
  | .lower => ∀ ν, maxSlice C ν → c ν
  | .upper => ∀ ν, C ν → c ν

theorem satCredal_lower_def (C c : SubPMF V → Prop) :
    SatCredal .lower C c ↔ ∀ ν, maxSlice C ν → c ν := Iff.rfl

theorem satCredal_upper_def (C c : SubPMF V → Prop) :
    SatCredal .upper C c ↔ ∀ ν, C ν → c ν := Iff.rfl

/-- A constraint closed under admitted downward scalings.  This is the
constraint-level form of "nonnegative gamble": event-probability upper
bounds are down-closed, and down-closure is exactly what makes the
whole-set reading of an upper-kind judgment blind to a ray's
interior. -/
def DownClosed (c : SubPMF V → Prop) : Prop :=
  ∀ ⦃μ ν : SubPMF V⦄, rayC μ ν → c μ → c ν

/-- The lower-bound event atom (lower kind: read on the slice). -/
def geC (A : Set V) (q : ℚ) : SubPMF V → Prop := fun ν => q ≤ ν.prob A

/-- The upper-bound event atom (upper kind: read on the whole set). -/
def leC (A : Set V) (q : ℚ) : SubPMF V → Prop := fun ν => ν.prob A ≤ q

/-- Upper-bound event atoms are down-closed: scaling mass away only
shrinks event probabilities.  (No sign condition on the threshold: the
indicator gamble is nonnegative regardless.) -/
theorem downClosed_leC (A : Set V) (q : ℚ) : DownClosed (leC A q) := by
  rintro μ ν ⟨t, ht0, ht1, hwt⟩ hμ
  have hμ' : μ.prob A ≤ q := hμ
  have h0 := μ.prob_nonneg A
  show ν.prob A ≤ q
  rw [SubPMF.prob_of_wt_smul hwt]
  nlinarith

/-! ## Verdict agreement between the ray and the singleton -/

theorem satCredal_lower_rayC {μ : SubPMF V} (hμ : μ ≠ SubPMF.zero V)
    (c : SubPMF V → Prop) : SatCredal .lower (rayC μ) c ↔ c μ := by
  constructor
  · intro h
    exact h μ ((maxSlice_rayC hμ μ).mpr (singletonC_self μ))
  · intro hc ν hν
    have hν' : ν = μ := (singletonC_iff μ ν).mp ((maxSlice_rayC hμ ν).mp hν)
    rw [hν']
    exact hc

theorem satCredal_lower_singletonC {μ : SubPMF V} (hμ : μ ≠ SubPMF.zero V)
    (c : SubPMF V → Prop) : SatCredal .lower (singletonC μ) c ↔ c μ := by
  constructor
  · intro h
    exact h μ ((maxSlice_singletonC hμ μ).mpr (singletonC_self μ))
  · intro hc ν hν
    have hν' : ν = μ :=
      (singletonC_iff μ ν).mp ((maxSlice_singletonC hμ ν).mp hν)
    rw [hν']
    exact hc

theorem satCredal_upper_singletonC (μ : SubPMF V) (c : SubPMF V → Prop) :
    SatCredal .upper (singletonC μ) c ↔ c μ := by
  constructor
  · intro h
    exact h μ (singletonC_self μ)
  · intro hc ν hν
    rw [(singletonC_iff μ ν).mp hν]
    exact hc

theorem satCredal_upper_rayC {μ : SubPMF V} {c : SubPMF V → Prop}
    (hc : DownClosed c) : SatCredal .upper (rayC μ) c ↔ c μ :=
  ⟨fun h => h μ (rayC_self μ), fun hcμ _ hν => hc hν hcμ⟩

/-- **Verdict agreement, lower kind**: on the radially maximal slice,
the ray and the singleton give the same verdict to every constraint. -/
theorem satCredal_lower_ray_singleton {μ : SubPMF V}
    (hμ : μ ≠ SubPMF.zero V) (c : SubPMF V → Prop) :
    SatCredal .lower (rayC μ) c ↔ SatCredal .lower (singletonC μ) c := by
  rw [satCredal_lower_rayC hμ, satCredal_lower_singletonC hμ]

/-- **Verdict agreement, upper kind**: on down-closed constraints the
whole-set readings of the ray and the singleton agree — with no
hypothesis on `μ`. -/
theorem satCredal_upper_ray_singleton (μ : SubPMF V)
    {c : SubPMF V → Prop} (hc : DownClosed c) :
    SatCredal .upper (rayC μ) c ↔ SatCredal .upper (singletonC μ) c := by
  rw [satCredal_upper_rayC hc, satCredal_upper_singletonC]

/-- **Why the slice discipline is not optional**: reading a lower-bound
atom with the whole-set reader refuses every positive threshold, for
every model — the ray's zero element is the universal refuter.  Beside
`satCredal_lower_rayC_geC`, this locates the entire content of the
lower/upper split. -/
theorem not_satCredal_upper_rayC_geC (μ : SubPMF V) {A : Set V} {q : ℚ}
    (hq : 0 < q) : ¬ SatCredal .upper (rayC μ) (geC A q) := by
  intro h
  have h0 : q ≤ (SubPMF.zero V).prob A := h (SubPMF.zero V) (rayC_zero μ)
  rw [SubPMF.zero_prob] at h0
  linarith

/-- The slice reading recovers the precise verdict exactly: the ray's
lower-kind verdict on an event atom is the model's own. -/
theorem satCredal_lower_rayC_geC {μ : SubPMF V} (hμ : μ ≠ SubPMF.zero V)
    (A : Set V) (q : ℚ) :
    SatCredal .lower (rayC μ) (geC A q) ↔ q ≤ μ.prob A :=
  satCredal_lower_rayC hμ _

/-! ## Double-categorical packaging -/

/-- The one-way cell: the singleton constraint entails the ray
constraint.  Its inverse exists only at the bottom object
(`rayC_eq_singletonC_iff`); the two presentations are reconciled
through the slice, not pointwise. -/
def cellSingletonRay (μ : SubPMF V) {a : Crd V} :
    Cell (singletonC μ : Loose a a) (rayC μ) (𝟙 a) (𝟙 a) :=
  Crd.cellOfEntails fun ν => singletonC_le_rayC μ ν

/-- **The reconciliation, packaged**: away from the bottom object, the
radially maximal slice of the ray and the singleton inclusion are
isomorphic as loose arrows of `Crd V` — an invertible globular cell,
the form in which the adequacy squares consume this stratum. -/
theorem ray_singleton_reconciliation {μ : SubPMF V}
    (hμ : μ ≠ SubPMF.zero V) {a : Crd V} :
    ∃ α : Cell (maxSlice (rayC μ) : Loose a a) (singletonC μ)
        (𝟙 a) (𝟙 a), Cell.IsInvertible α :=
  Crd.looseIso_ofIff (maxSlice_rayC hμ)

end SuFunctor
