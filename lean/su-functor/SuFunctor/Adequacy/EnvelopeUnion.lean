import SuFunctor.Adequacy.Envelope

/-! # The envelope stratum, set-valued: unions of rays and the equal-mass slice

The set-valued bottom edges of the adequacy squares — demonic policy
choice, input boxes, mixtures — include a *family* of laws rather than a
single one.  The credal presentation of such a family is the union of
the precise faces of its members: one closed ray `[0,1]·μᵢ` per member
(`unionRays`), downward-scaling-closed as the semantic-universe
chapter's axioms require.  The exact constraint-stratum inclusion is the
family itself, one singleton per member (`unionSingletons`).  This
module reconciles the two presentations, extending the single-ray
reconciliation of `SuFunctor.Adequacy.Envelope` to families:

* `maxSlice_unionRays_subset` — **the slice is inside the family,
  unconditionally**: a strictly interior ray point escapes upward to its
  own base, and a zero-weight member escapes via itself, so no
  hypothesis is needed on this direction — stronger than the equal-mass
  statement suggests.
* `maxSlice_unionRays` — **the reconciliation**: for a family of
  *equal nonzero mass*, the radially maximal slice of the union of rays
  is exactly the family.  Equal mass is spent on the reverse inclusion,
  and it is spent on *cross-ray* domination: whether one member's ray
  admits an upward scaling of another is a comparison of masses
  (`SubPMF.prob_of_wt_smul` at `Set.univ`), not of scalars — the
  same-base cancellation of the single-ray case cannot see it.  The
  fixture pair below witnesses necessity.
* `maxSlice_unionSingletons` — the family is its own slice (same
  hypotheses), so the reconciliation statement is symmetric in its two
  presentations, as in the single-ray case.
* Boundaries, honestly: the equal-mass statement covers the **empty
  family vacuously** (both sides false) — but the empty union is not a
  lawful credal object (the chapter's axioms force `⊥ ∈ S`; the lawful
  denotation of infeasibility is `{0}`, never `∅`): the union contains
  the zero model exactly when the family is inhabited
  (`unionRays_zero_iff`).  The **all-zero family** is the union-level
  face of the chapter's bottom boundary: the union collapses to `{0}`
  and the slice is empty while the family is not
  (`maxSlice_unionRays_mass_zero`).
* `SatCredal` transfer — the verdict operators on a set-valued credal
  denotation reduce to universal quantification over the family: the
  lower kind through the slice (equal mass), the upper kind through
  down-closure of the constraint (mass-free), and the upper kind on the
  exact family unconditionally.  On either kind, the ray and singleton
  presentations agree under their respective guards.
* **The fixture pair** (`halfPair`): a member and its half-scaling.  The
  half element is in the family (`unionSingletons_halfPair`) and never
  in the slice (`not_maxSlice_unionRays_halfPair`, hypothesis-free: for
  a nonzero base this is the unequal-mass failure — the half member is
  radially dominated *across* rays — and for the zero base it is the
  bottom boundary).  This is the preregistered witness that the
  equal-mass hypothesis of the reconciliation is not decorative.
* `union_ray_singleton_reconciliation` — the packaging: the maximal
  slice of the union of rays and the union of singletons are isomorphic
  as loose arrows of `Crd V` (an invertible globular cell), for an
  equal-mass family; with the one-way cell `cellUnionSingletonsRays`
  (the family entails its rays; invertibility fails away from the
  slice, as the fixture shows already at two members).
-/

namespace SuFunctor

open CategoryTheory PseudoDoubleCategoryStruct

universe u

variable {V : Type u} {ι : Sort*}

/-! ## Mass zero is the zero model -/

namespace SubPMF

/-- A subprobability mass function of zero mass is the zero model:
nonnegative weights summing to zero all vanish. -/
theorem eq_zero_of_mass_eq_zero {μ : SubPMF V} (h : μ.mass = 0) :
    μ = SubPMF.zero V := by
  classical
  rw [SubPMF.eq_zero_iff_wt]
  have hh : μ.mass = ∑ v ∈ μ.wt.support, μ.wt v := by
    unfold SubPMF.mass SubPMF.prob
    exact Finset.sum_congr rfl fun v _ => if_pos (Set.mem_univ v)
  have hz : ∀ v ∈ μ.wt.support, μ.wt v = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun v _ => μ.nonneg v).mp
      (hh.symm.trans h)
  ext v
  by_cases hv : μ.wt v = 0
  · simpa using hv
  · simpa using hz v (Finsupp.mem_support_iff.mpr hv)

end SubPMF

/-! ## Unions of rays and unions of singletons -/

/-- The union-of-rays constraint of a family: `ν` is an admitted
downward scaling of *some* member.  This is the credal presentation of
a set-valued inclusion — one precise face per member, glued by
disjunction. -/
def unionRays (μs : ι → SubPMF V) : SubPMF V → Prop :=
  fun ν => ∃ i, rayC (μs i) ν

/-- The union-of-singletons constraint of a family: `ν` *is* some
member.  This is the exact constraint-stratum inclusion of a set of
laws. -/
def unionSingletons (μs : ι → SubPMF V) : SubPMF V → Prop :=
  fun ν => ∃ i, singletonC (μs i) ν

theorem unionRays_self (μs : ι → SubPMF V) (i : ι) :
    unionRays μs (μs i) :=
  ⟨i, rayC_self _⟩

theorem unionSingletons_self (μs : ι → SubPMF V) (i : ι) :
    unionSingletons μs (μs i) :=
  ⟨i, singletonC_self _⟩

/-- The exact family entails its union of rays — the set-valued face of
`singletonC_le_rayC`. -/
theorem unionSingletons_le_unionRays (μs : ι → SubPMF V) (ν : SubPMF V)
    (h : unionSingletons μs ν) : unionRays μs ν := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, singletonC_le_rayC _ _ hi⟩

/-- The union of rays contains the zero model exactly when the family
is inhabited.  (The chapter's credal axioms force `⊥ ∈ S`, so the empty
union — while covered vacuously by every slice statement below — is not
a lawful credal object: the lawful denotation of infeasibility is the
bottom object `{0}`, never `∅`.) -/
theorem unionRays_zero_iff (μs : ι → SubPMF V) :
    unionRays μs (SubPMF.zero V) ↔ Nonempty ι :=
  ⟨fun ⟨i, _⟩ => ⟨i⟩, fun ⟨i⟩ => ⟨i, rayC_zero (μs i)⟩⟩

/-! ## The radially maximal slice of a union of rays -/

/-- **The slice is inside the family, unconditionally.**  A radially
maximal element of the union of rays is a member: strictly interior ray
points (`0 < t < 1`) escape upward to their own base, and zero-weight
points escape via themselves (`l • 0 = 0` stays in the union).  No mass
hypothesis. -/
theorem maxSlice_unionRays_subset {μs : ι → SubPMF V} {ν : SubPMF V}
    (h : maxSlice (unionRays μs) ν) : unionSingletons μs ν := by
  obtain ⟨⟨i, t, ht0, ht1, hwt⟩, hmax⟩ := h
  by_cases hν0 : ν.wt = 0
  · exact absurd ⟨i, t, ht0, ht1, hwt⟩
      (hmax 2 one_lt_two ν (by rw [hν0, smul_zero]))
  · have htpos : 0 < t := by
      rcases eq_or_lt_of_le ht0 with h' | h'
      · exact absurd (by rw [hwt, ← h', zero_smul]) hν0
      · exact h'
    rcases lt_or_eq_of_le ht1 with ht | ht
    · refine absurd (unionRays_self μs i) (hmax t⁻¹ ?_ (μs i) ?_)
      · have h1 : t * t⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt htpos)
        nlinarith [inv_pos.mpr htpos]
      · rw [hwt, smul_smul, inv_mul_cancel₀ (ne_of_gt htpos), one_smul]
    · exact ⟨i, (singletonC_iff _ _).mpr
        (SubPMF.ext' (by rw [hwt, ht, one_smul]))⟩

/-- **Every member of an equal-mass family is radially maximal in the
union of its rays.**  This is where equal mass is spent: an upward
scaling of one member lying on *another* member's ray is excluded by
comparing masses along both weight identities — `l·m = s·m` with
`m ≠ 0` forces `l = s ≤ 1`, contradicting `1 < l`.  Scalar cancellation
(`smul_wt_cancel`) cannot see across rays; the mass functional can. -/
theorem mem_maxSlice_unionRays {μs : ι → SubPMF V} {m : ℚ}
    (hm : ∀ i, (μs i).mass = m) (hm0 : m ≠ 0) (i : ι) :
    maxSlice (unionRays μs) (μs i) := by
  refine ⟨unionRays_self μs i, ?_⟩
  intro l hl ν' hwt'
  rintro ⟨j, s, _hs0, hs1, hs⟩
  have h1 : ν'.mass = l * (μs i).mass :=
    SubPMF.prob_of_wt_smul hwt' Set.univ
  have h2 : ν'.mass = s * (μs j).mass :=
    SubPMF.prob_of_wt_smul hs Set.univ
  rw [hm i] at h1
  rw [hm j] at h2
  have hls : l = s := mul_right_cancel₀ hm0 (h1.symm.trans h2)
  rw [hls] at hl
  exact absurd hs1 (not_le.mpr hl)

/-- **The reconciliation, set-valued**: for a family of equal nonzero
mass, the radially maximal slice of the union of rays is exactly the
family.  The credal presentation of a set of laws and its exact
constraint-stratum inclusion agree on the slice — which is what the
verdict operators read. -/
theorem maxSlice_unionRays {μs : ι → SubPMF V} {m : ℚ}
    (hm : ∀ i, (μs i).mass = m) (hm0 : m ≠ 0) (ν : SubPMF V) :
    maxSlice (unionRays μs) ν ↔ unionSingletons μs ν := by
  constructor
  · exact maxSlice_unionRays_subset
  · rintro ⟨i, hi⟩
    rw [(singletonC_iff _ _).mp hi]
    exact mem_maxSlice_unionRays hm hm0 i

/-- The exact family is its own maximal slice (equal nonzero mass), so
the reconciliation statement is symmetric in its two presentations. -/
theorem maxSlice_unionSingletons {μs : ι → SubPMF V} {m : ℚ}
    (hm : ∀ i, (μs i).mass = m) (hm0 : m ≠ 0) (ν : SubPMF V) :
    maxSlice (unionSingletons μs) ν ↔ unionSingletons μs ν := by
  constructor
  · exact fun h => h.1
  · rintro ⟨i, hi⟩
    rw [(singletonC_iff _ _).mp hi]
    refine ⟨unionSingletons_self μs i, ?_⟩
    intro l hl ν' hwt'
    rintro ⟨j, hj⟩
    have h1 : ν'.mass = l * (μs i).mass :=
      SubPMF.prob_of_wt_smul hwt' Set.univ
    rw [(singletonC_iff _ _).mp hj, hm j, hm i] at h1
    have h2 : (1 : ℚ) * m = l * m := by rw [one_mul]; exact h1
    rw [← mul_right_cancel₀ hm0 h2] at hl
    exact lt_irrefl 1 hl

/-- **The all-zero boundary**: for a family of mass zero the union of
rays collapses to the bottom object `{0}`, whose slice is empty — while
the family itself need not be.  The union-level face of the chapter's
`S^max = ∅` iff `S = {0}`. -/
theorem maxSlice_unionRays_mass_zero {μs : ι → SubPMF V}
    (hm : ∀ i, (μs i).mass = 0) (ν : SubPMF V) :
    ¬ maxSlice (unionRays μs) ν := by
  rintro ⟨⟨i, t, ht0, ht1, hwt⟩, hmax⟩
  have hzi : μs i = SubPMF.zero V :=
    SubPMF.eq_zero_of_mass_eq_zero (hm i)
  have hν : ν.wt = 0 := by rw [hwt, hzi, SubPMF.zero_wt, smul_zero]
  exact hmax 2 one_lt_two ν (by rw [hν, smul_zero])
    ⟨i, t, ht0, ht1, hwt⟩

/-! ## Verdict transfer: the set-valued credal reading is the
universal quantification over the family -/

theorem satCredal_lower_unionRays {μs : ι → SubPMF V} {m : ℚ}
    (hm : ∀ i, (μs i).mass = m) (hm0 : m ≠ 0) (c : SubPMF V → Prop) :
    SatCredal .lower (unionRays μs) c ↔ ∀ i, c (μs i) := by
  constructor
  · intro h i
    exact h (μs i)
      ((maxSlice_unionRays hm hm0 (μs i)).mpr (unionSingletons_self μs i))
  · intro hc ν hν
    obtain ⟨i, hi⟩ := (maxSlice_unionRays hm hm0 ν).mp hν
    rw [(singletonC_iff _ _).mp hi]
    exact hc i

theorem satCredal_lower_unionSingletons {μs : ι → SubPMF V} {m : ℚ}
    (hm : ∀ i, (μs i).mass = m) (hm0 : m ≠ 0) (c : SubPMF V → Prop) :
    SatCredal .lower (unionSingletons μs) c ↔ ∀ i, c (μs i) := by
  constructor
  · intro h i
    exact h (μs i)
      ((maxSlice_unionSingletons hm hm0 (μs i)).mpr
        (unionSingletons_self μs i))
  · intro hc ν hν
    obtain ⟨i, hi⟩ := (maxSlice_unionSingletons hm hm0 ν).mp hν
    rw [(singletonC_iff _ _).mp hi]
    exact hc i

/-- The whole-set reading of a down-closed constraint on a union of
rays is the universal quantification over the family — mass-free, as
in the single-ray case: down-closure is exactly blindness to the rays'
interiors. -/
theorem satCredal_upper_unionRays {μs : ι → SubPMF V}
    {c : SubPMF V → Prop} (hc : DownClosed c) :
    SatCredal .upper (unionRays μs) c ↔ ∀ i, c (μs i) := by
  constructor
  · intro h i
    exact h (μs i) (unionRays_self μs i)
  · rintro hcs ν ⟨i, hray⟩
    exact hc hray (hcs i)

/-- The whole-set reading on the exact family is the universal
quantification, unconditionally. -/
theorem satCredal_upper_unionSingletons {μs : ι → SubPMF V}
    (c : SubPMF V → Prop) :
    SatCredal .upper (unionSingletons μs) c ↔ ∀ i, c (μs i) := by
  constructor
  · intro h i
    exact h (μs i) (unionSingletons_self μs i)
  · rintro hcs ν ⟨i, hi⟩
    rw [(singletonC_iff _ _).mp hi]
    exact hcs i

/-- **Verdict agreement, lower kind, set-valued**: on the radially
maximal slice, the union of rays and the union of singletons give the
same verdict to every constraint — for an equal-mass family. -/
theorem satCredal_lower_union_ray_singleton {μs : ι → SubPMF V} {m : ℚ}
    (hm : ∀ i, (μs i).mass = m) (hm0 : m ≠ 0) (c : SubPMF V → Prop) :
    SatCredal .lower (unionRays μs) c ↔
      SatCredal .lower (unionSingletons μs) c := by
  rw [satCredal_lower_unionRays hm hm0,
    satCredal_lower_unionSingletons hm hm0]

/-- **Verdict agreement, upper kind, set-valued**: on down-closed
constraints the whole-set readings agree — with no mass hypothesis. -/
theorem satCredal_upper_union_ray_singleton {μs : ι → SubPMF V}
    {c : SubPMF V → Prop} (hc : DownClosed c) :
    SatCredal .upper (unionRays μs) c ↔
      SatCredal .upper (unionSingletons μs) c := by
  rw [satCredal_upper_unionRays hc, satCredal_upper_unionSingletons]

/-! ## The fixture pair: equal mass is not decorative -/

/-- The unequal-mass pair: a model and its half-scaling, Bool-indexed
(`true ↦ μ`, `false ↦ ½·μ`). -/
noncomputable def halfPair (μ : SubPMF V) : Bool → SubPMF V :=
  fun b => bif b then μ
    else SubPMF.scale (1 / 2) (by norm_num) (by norm_num) μ

/-- The half element is in the family… -/
theorem unionSingletons_halfPair (μ : SubPMF V) :
    unionSingletons (halfPair μ) (halfPair μ false) :=
  unionSingletons_self _ false

/-- …and never in the slice of the union of rays: it is radially
dominated *across* rays by the full member (`2 · (½·μ) = μ`).  For a
nonzero base this is precisely the unequal-mass failure the
reconciliation's hypothesis excludes (`½·μ` has half the mass of `μ`);
for the zero base it degenerates into the bottom boundary.  Together
with `unionSingletons_halfPair` this witnesses that the equal-mass
hypothesis of `maxSlice_unionRays` cannot be dropped. -/
theorem not_maxSlice_unionRays_halfPair (μ : SubPMF V) :
    ¬ maxSlice (unionRays (halfPair μ)) (halfPair μ false) := by
  rintro ⟨-, hmax⟩
  refine hmax 2 one_lt_two μ ?_ ⟨true, rayC_self μ⟩
  show μ.wt = (2 : ℚ) • ((1 / 2 : ℚ) • μ.wt)
  rw [smul_smul, show (2 : ℚ) * (1 / 2) = 1 by norm_num, one_smul]

/-! ## Double-categorical packaging -/

/-- The one-way cell: the exact family entails its union of rays.  As
in the single-ray case, the converse fails away from the slice — the
fixture pair exhibits it already at two members. -/
def cellUnionSingletonsRays (μs : ι → SubPMF V) {a : Crd V} :
    Cell (unionSingletons μs : Loose a a) (unionRays μs) (𝟙 a) (𝟙 a) :=
  Crd.cellOfEntails fun ν => unionSingletons_le_unionRays μs ν

/-- **The reconciliation, packaged**: for an equal-mass family, the
radially maximal slice of the union of rays and the union of
singletons are isomorphic as loose arrows of `Crd V` — an invertible
globular cell, the form in which the set-valued adequacy squares
consume this stratum. -/
theorem union_ray_singleton_reconciliation {μs : ι → SubPMF V} {m : ℚ}
    (hm : ∀ i, (μs i).mass = m) (hm0 : m ≠ 0) {a : Crd V} :
    ∃ α : Cell (maxSlice (unionRays μs) : Loose a a)
        (unionSingletons μs) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  Crd.looseIso_ofIff (maxSlice_unionRays hm hm0)

end SuFunctor
