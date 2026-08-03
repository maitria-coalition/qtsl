import QtslAux.Imprecise.CouplingGlue
import QtslAux.Imprecise.PenaltyCredalIso

/-! # Feasibility: properness of a composite ⟺ marginal compatibility

The composite penalty `f₁ ⊞ f₂` admits a finite-penalty joint over the
glued foot if and only if some pair of finite-penalty component laws
agrees over the shared foot — and a compatible pair, once exhibited,
yields an explicit witnessing joint by exact conditional-product gluing.

**Two strata**:

* **Standard Borel** (`boxplus_proper_iff_marginal_compatible`): the iff
  wrapper over `CouplingGlue.exists_coupling_of_map_eq`. The only-if
  direction is marginalization functoriality alone
  (`map_eq_of_concentrated`: a coupling concentrated on the fiber product
  has agreeing foot pushforwards — proved through one a.e. rewrite, the
  single place any measure theory enters); the if direction is the
  mechanized conditional-product glue, with penalty finiteness riding
  `WithTop.add_lt_top`. Penalties are bare functions
  `Measure Ω → ENNRat` — properness is an order fact, and no structure on
  the functionals is consumed (the `MarginalCompat` discipline).

* **Finite-rational** (`finite_boxplus_proper_iff`): the
  certificate-stratum face. The witnessing joint is an **exact rational
  formula** — `FinPMF.condProduct`:
  `ν(x₁,x₂) = p₁(x₁)·p₂(x₂)/foot(r x₁)` on the fiber product, `0` off it
  — checker-recomputable, with its marginal laws
  (`condProduct_map_fst/snd`) and support law proved from the formula.
  `finpmf_coupling_of_map_eq` packages it as the finite twin of the
  measure-level glue (finite spaces are standard Borel; here the witness
  is *constructed*, not chosen).

Note the composite-properness quantifier ranges over couplings
**concentrated on the fiber product** — joints over the glued apex: at
the finite stratum the support condition
`∀ q, r q.1 ≠ s q.2 → ν q = 0` is the subtype-free spelling of "a joint
over the fiber product of the two component spaces".

**Mutant + control** (kernel-checked): `mutant_no_agreement_fails` — drop
the foot-agreement clause from the compatibility side and the implication
to properness is refused (two point-mass probes on a shared binary
variable, incompatible feet: no diagonal-supported coupling can serve
both); `glue_control` — the same probe shape with agreeing feet, glued by
the theorem. The agreement clause is load-bearing, not decorative. -/

open MeasureTheory

namespace Qtsl.Imprecise

open Finset

/-! ## The standard-Borel stratum: the iff wrapper over the glue -/

section MeasureLevel

variable {Ω₁ Ω₂ Y : Type*}
  [MeasurableSpace Ω₁] [StandardBorelSpace Ω₁]
  [MeasurableSpace Ω₂] [StandardBorelSpace Ω₂]
  [MeasurableSpace Y] [MeasurableEq Y]

omit [StandardBorelSpace Ω₁] [StandardBorelSpace Ω₂] in
/-- **Only-if direction's core** (marginalization functoriality): a
probability measure concentrated on the fiber product has agreeing
pushforwards to the shared foot. (No standard-Borel hypothesis — the
`omit` is the honest-hypothesis receipt.) -/
theorem map_eq_of_concentrated (ν : Measure (Ω₁ × Ω₂))
    [IsProbabilityMeasure ν] {r : Ω₁ → Y} {s : Ω₂ → Y}
    (hr : Measurable r) (hs : Measurable s)
    (hconc : ν {p : Ω₁ × Ω₂ | r p.1 = s p.2} = 1) :
    (ν.map Prod.fst).map r = (ν.map Prod.snd).map s := by
  have hGmeas : MeasurableSet {p : Ω₁ × Ω₂ | r p.1 = s p.2} :=
    measurableSet_eq_fun (hr.comp measurable_fst) (hs.comp measurable_snd)
  have hmem : {p : Ω₁ × Ω₂ | r p.1 = s p.2} ∈ ae ν := by
    rw [mem_ae_iff]
    exact (prob_compl_eq_zero_iff hGmeas).mpr hconc
  have hae : (fun p : Ω₁ × Ω₂ => r p.1) =ᵐ[ν] fun p => s p.2 :=
    Filter.eventuallyEq_of_mem hmem fun p hp => hp
  rw [Measure.map_map hr measurable_fst, Measure.map_map hs measurable_snd]
  exact Measure.map_congr hae

/-- **The properness-iff wrapper (standard Borel)**: the composite penalty
`f₁ ⊞ f₂` admits a finite-penalty joint over the glued foot **iff** some
pair of finite-penalty component laws agrees over the shared foot. The if
direction's witness is the conditional-product coupling of
`exists_coupling_of_map_eq`; the only-if direction is marginalization
functoriality. Properness failure is first-class infeasibility — this iff
is its existential characterization, shape-of-check and witness format
included. -/
theorem boxplus_proper_iff_marginal_compatible
    (f₁ : Measure Ω₁ → ENNRat) (f₂ : Measure Ω₂ → ENNRat)
    {r : Ω₁ → Y} {s : Ω₂ → Y} (hr : Measurable r) (hs : Measurable s) :
    (∃ ν : Measure (Ω₁ × Ω₂), IsProbabilityMeasure ν ∧
        ν {p : Ω₁ × Ω₂ | r p.1 = s p.2} = 1 ∧
        f₁ (ν.map Prod.fst) + f₂ (ν.map Prod.snd) < ⊤)
      ↔ (∃ (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂),
          IsProbabilityMeasure μ₁ ∧ IsProbabilityMeasure μ₂ ∧
          μ₁.map r = μ₂.map s ∧ f₁ μ₁ < ⊤ ∧ f₂ μ₂ < ⊤) := by
  constructor
  · rintro ⟨ν, hν, hconc, hfin⟩
    haveI := hν
    have hf := WithTop.add_lt_top.mp hfin
    exact ⟨ν.map Prod.fst, ν.map Prod.snd,
      Measure.isProbabilityMeasure_map measurable_fst.aemeasurable,
      Measure.isProbabilityMeasure_map measurable_snd.aemeasurable,
      map_eq_of_concentrated ν hr hs hconc, hf.1, hf.2⟩
  · rintro ⟨μ₁, μ₂, h1, h2, hpush, hf1, hf2⟩
    haveI := h1
    haveI := h2
    obtain ⟨ν, hνP, hfst, hsnd, hconc⟩ :=
      exists_coupling_of_map_eq μ₁ μ₂ hr hs hpush
    refine ⟨ν, hνP, hconc, ?_⟩
    rw [hfst, hsnd]
    exact WithTop.add_lt_top.mpr ⟨hf1, hf2⟩

end MeasureLevel

/-! ## The finite-rational stratum: the exact conditional product -/

section FiniteStratum

variable {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]
  [DecidableEq X₁] [DecidableEq X₂] [DecidableEq Y]

omit [DecidableEq X₂] in
/-- Slice a product-space fiber sum along the first coordinate. -/
theorem sum_filter_fst_eq (a : X₁) (G : X₁ × X₂ → ℚ) :
    ∑ q ∈ univ.filter (fun q : X₁ × X₂ => q.1 = a), G q
      = ∑ x₂, G (a, x₂) := by
  rw [Finset.sum_filter]
  refine (Fintype.sum_prod_type _).trans ?_
  refine (Finset.sum_congr rfl fun x₁ _ =>
    show (∑ x₂, if x₁ = a then G (x₁, x₂) else 0)
        = if x₁ = a then ∑ x₂, G (x₁, x₂) else 0 from by
      by_cases h : x₁ = a <;> simp [h]).trans ?_
  rw [Finset.sum_ite_eq' univ a fun x₁ => ∑ x₂, G (x₁, x₂)]
  simp

omit [DecidableEq X₁] in
/-- Slice a product-space fiber sum along the second coordinate. -/
theorem sum_filter_snd_eq (b : X₂) (G : X₁ × X₂ → ℚ) :
    ∑ q ∈ univ.filter (fun q : X₁ × X₂ => q.2 = b), G q
      = ∑ x₁, G (x₁, b) := by
  rw [Finset.sum_filter]
  refine (Fintype.sum_prod_type _).trans ?_
  exact Finset.sum_congr rfl fun x₁ _ => by
    simp

omit [DecidableEq X₂] in
/-- Marginal of a product-space pmf along the first coordinate, as a
slice sum. -/
theorem prob_map_fst (ν : FinPMF (X₁ × X₂)) (a : X₁) :
    (ν.map Prod.fst).prob a = ∑ x₂, ν.prob (a, x₂) :=
  sum_filter_fst_eq a ν.prob

omit [DecidableEq X₁] in
/-- Marginal of a product-space pmf along the second coordinate, as a
slice sum. -/
theorem prob_map_snd (ν : FinPMF (X₁ × X₂)) (b : X₂) :
    (ν.map Prod.snd).prob b = ∑ x₁, ν.prob (x₁, b) :=
  sum_filter_snd_eq b ν.prob

omit [DecidableEq X₁] in
/-- A pmf's mass at a point is dominated by its pushforward's mass at the
image point. -/
theorem prob_le_map_prob (p : FinPMF X₁) (r : X₁ → Y) (x : X₁) :
    p.prob x ≤ (p.map r).prob (r x) :=
  Finset.single_le_sum (f := p.prob) (fun y _ => p.nonneg y)
    (Finset.mem_filter.mpr ⟨mem_univ x, rfl⟩)

/-- Pushforward composes (`map` is functorial). -/
theorem FinPMF.map_map {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C]
    (p : FinPMF A) (g : A → B) (h : B → C) :
    (p.map g).map h = p.map (h ∘ g) := by
  apply FinPMF.ext
  intro z
  show ∑ y ∈ univ.filter (fun y => h y = z),
        ∑ x ∈ univ.filter (fun x => g x = y), p.prob x
      = ∑ x ∈ univ.filter (fun x => (h ∘ g) x = z), p.prob x
  rw [Finset.sum_fiberwise_eq_sum_filter univ
    (univ.filter fun y => h y = z) g p.prob]
  refine Finset.sum_congr ?_ fun x _ => rfl
  apply Finset.filter_congr
  intro x _
  simp [Function.comp]

section CondProduct

variable (p₁ : FinPMF X₁) (p₂ : FinPMF X₂) (r : X₁ → Y) (s : X₂ → Y)

omit [DecidableEq X₁] [DecidableEq X₂] in
/-- The per-`x₁` slice of the conditional product sums to `p₁ x₁` —
the computation both the total-mass and fst-marginal laws ride. -/
private theorem condProduct_slice (hpush : p₁.map r = p₂.map s) (x₁ : X₁) :
    (∑ x₂, if r x₁ = s x₂ then
        p₁.prob x₁ * p₂.prob x₂ / (p₁.map r).prob (r x₁) else 0)
      = p₁.prob x₁ := by
  have hterm : ∀ x₂ : X₂,
      (if r x₁ = s x₂ then
          p₁.prob x₁ * p₂.prob x₂ / (p₁.map r).prob (r x₁) else 0)
        = (if s x₂ = r x₁ then p₂.prob x₂ else 0)
            * (p₁.prob x₁ / (p₁.map r).prob (r x₁)) := fun x₂ => by
    by_cases h : r x₁ = s x₂
    · rw [if_pos h, if_pos h.symm]
      ring
    · rw [if_neg h, if_neg fun hc => h hc.symm, zero_mul]
  rw [Finset.sum_congr rfl fun x₂ _ => hterm x₂, ← Finset.sum_mul,
    ← Finset.sum_filter]
  have hfiber : (∑ x₂ ∈ univ.filter fun x₂ => s x₂ = r x₁, p₂.prob x₂)
      = (p₁.map r).prob (r x₁) := by
    rw [hpush]
    rfl
  rw [hfiber]
  rcases eq_or_lt_of_le
      (Finset.sum_nonneg fun y (_ : y ∈ univ.filter fun x => r x = r x₁) =>
        p₁.nonneg y) with hz | hpos
  · -- zero foot mass ⟹ `p₁ x₁ = 0`, and the product is `0` outright
    have hfz : (p₁.map r).prob (r x₁) = 0 := hz.symm
    have hp0 : p₁.prob x₁ = 0 :=
      le_antisymm (hfz ▸ prob_le_map_prob p₁ r x₁) (p₁.nonneg x₁)
    rw [hfz, hp0]
    simp
  · have hfpos : 0 < (p₁.map r).prob (r x₁) := hpos
    rw [mul_comm]
    exact div_mul_cancel₀ (p₁.prob x₁) hfpos.ne'

/-- **The exact conditional product** (a finite rational formula,
checker-recomputable): the coupling
`ν(x₁,x₂) = p₁(x₁)·p₂(x₂)/foot(r x₁)` on the fiber product, `0` off it.
Requires agreeing foot marginals — precisely the compatibility the
properness iff trades in. -/
def FinPMF.condProduct (hpush : p₁.map r = p₂.map s) :
    FinPMF (X₁ × X₂) where
  prob := fun q =>
    if r q.1 = s q.2 then
      p₁.prob q.1 * p₂.prob q.2 / (p₁.map r).prob (r q.1) else 0
  nonneg := fun q => by
    split_ifs
    · exact div_nonneg (mul_nonneg (p₁.nonneg q.1) (p₂.nonneg q.2))
        ((p₁.map r).nonneg (r q.1))
    · exact le_rfl
  total :=
    (Fintype.sum_prod_type _).trans
      ((Finset.sum_congr rfl fun x₁ _ =>
        condProduct_slice p₁ p₂ r s hpush x₁).trans p₁.total)

omit [DecidableEq X₁] [DecidableEq X₂] in
/-- The conditional product is concentrated on the fiber product. -/
theorem condProduct_support (hpush : p₁.map r = p₂.map s)
    (q : X₁ × X₂) (hq : r q.1 ≠ s q.2) :
    (FinPMF.condProduct p₁ p₂ r s hpush).prob q = 0 :=
  if_neg hq

/-- First marginal law of the conditional product. -/
theorem condProduct_map_fst (hpush : p₁.map r = p₂.map s) :
    (FinPMF.condProduct p₁ p₂ r s hpush).map Prod.fst = p₁ := by
  apply FinPMF.ext
  intro a
  rw [prob_map_fst]
  exact condProduct_slice p₁ p₂ r s hpush a

/-- Second marginal law of the conditional product. -/
theorem condProduct_map_snd (hpush : p₁.map r = p₂.map s) :
    (FinPMF.condProduct p₁ p₂ r s hpush).map Prod.snd = p₂ := by
  apply FinPMF.ext
  intro b
  rw [prob_map_snd]
  show (∑ x₁, if r x₁ = s b then
      p₁.prob x₁ * p₂.prob b / (p₁.map r).prob (r x₁) else 0) = p₂.prob b
  have hterm : ∀ x₁ : X₁,
      (if r x₁ = s b then
          p₁.prob x₁ * p₂.prob b / (p₁.map r).prob (r x₁) else 0)
        = (if r x₁ = s b then p₁.prob x₁ else 0)
            * (p₂.prob b / (p₁.map r).prob (s b)) := fun x₁ => by
    by_cases h : r x₁ = s b
    · rw [if_pos h, if_pos h, h]
      ring
    · rw [if_neg h, if_neg h, zero_mul]
  rw [Finset.sum_congr rfl fun x₁ _ => hterm x₁, ← Finset.sum_mul,
    ← Finset.sum_filter]
  have hfiber : (∑ x₁ ∈ univ.filter fun x₁ => r x₁ = s b, p₁.prob x₁)
      = (p₁.map r).prob (s b) := rfl
  rw [hfiber]
  rcases eq_or_lt_of_le
      (Finset.sum_nonneg fun y (_ : y ∈ univ.filter fun x => r x = s b) =>
        p₁.nonneg y) with hz | hpos
  · have hfz : (p₁.map r).prob (s b) = 0 := hz.symm
    have hp0 : p₂.prob b = 0 := by
      have hle := prob_le_map_prob p₂ s b
      rw [← hpush] at hle
      rw [hfz] at hle
      exact le_antisymm hle (p₂.nonneg b)
    rw [hfz, hp0]
    simp
  · have hfpos : 0 < (p₁.map r).prob (s b) := hpos
    rw [mul_comm]
    exact div_mul_cancel₀ (p₂.prob b) hfpos.ne'

/-- **The finite twin of `exists_coupling_of_map_eq`**: agreeing foot
marginals admit a coupling concentrated on the fiber product — with the
witness an explicit rational formula rather than a disintegration. -/
theorem finpmf_coupling_of_map_eq (hpush : p₁.map r = p₂.map s) :
    ∃ ν : FinPMF (X₁ × X₂), ν.map Prod.fst = p₁ ∧ ν.map Prod.snd = p₂ ∧
      ∀ q : X₁ × X₂, r q.1 ≠ s q.2 → ν.prob q = 0 :=
  ⟨FinPMF.condProduct p₁ p₂ r s hpush,
    condProduct_map_fst p₁ p₂ r s hpush,
    condProduct_map_snd p₁ p₂ r s hpush,
    condProduct_support p₁ p₂ r s hpush⟩

end CondProduct

/-- A fiber-concentrated finite coupling has agreeing foot pushforwards
(the finite only-if core: marginalization functoriality alone). -/
theorem finpmf_map_eq_of_support (ν : FinPMF (X₁ × X₂))
    (r : X₁ → Y) (s : X₂ → Y)
    (hsupp : ∀ q : X₁ × X₂, r q.1 ≠ s q.2 → ν.prob q = 0) :
    (ν.map Prod.fst).map r = (ν.map Prod.snd).map s := by
  rw [FinPMF.map_map, FinPMF.map_map]
  apply FinPMF.ext
  intro z
  show ∑ q ∈ univ.filter (fun q : X₁ × X₂ => r q.1 = z), ν.prob q
      = ∑ q ∈ univ.filter (fun q : X₁ × X₂ => s q.2 = z), ν.prob q
  have hzero₁ : ∑ q ∈ (univ.filter fun q : X₁ × X₂ => r q.1 = z).filter
      (fun q => ¬ r q.1 = s q.2), ν.prob q = 0 :=
    Finset.sum_eq_zero fun q hq => hsupp q (Finset.mem_filter.mp hq).2
  have hzero₂ : ∑ q ∈ (univ.filter fun q : X₁ × X₂ => s q.2 = z).filter
      (fun q => ¬ r q.1 = s q.2), ν.prob q = 0 :=
    Finset.sum_eq_zero fun q hq => hsupp q (Finset.mem_filter.mp hq).2
  rw [← Finset.sum_filter_add_sum_filter_not
      (univ.filter fun q : X₁ × X₂ => r q.1 = z)
      (fun q => r q.1 = s q.2) ν.prob,
    ← Finset.sum_filter_add_sum_filter_not
      (univ.filter fun q : X₁ × X₂ => s q.2 = z)
      (fun q => r q.1 = s q.2) ν.prob,
    hzero₁, hzero₂, add_zero, add_zero]
  have hset : (univ.filter fun q : X₁ × X₂ => r q.1 = z).filter
        (fun q => r q.1 = s q.2)
      = (univ.filter fun q : X₁ × X₂ => s q.2 = z).filter
        (fun q => r q.1 = s q.2) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨hz, hag⟩ => ⟨hag.symm.trans hz, hag⟩,
      fun ⟨hz, hag⟩ => ⟨hag.trans hz, hag⟩⟩
  rw [hset]

/-- **The properness iff, finite-rational stratum**: the composite
penalty `f₁ ⊞ f₂` admits a finite-penalty joint over the glued foot
(a coupling concentrated on the fiber product) **iff** some pair of
finite-penalty component pmfs agrees over the shared foot. The witness is
`FinPMF.condProduct` — exact rational arithmetic, checker-recomputable. -/
theorem finite_boxplus_proper_iff
    (f₁ : FinPMF X₁ → ENNRat) (f₂ : FinPMF X₂ → ENNRat)
    (r : X₁ → Y) (s : X₂ → Y) :
    (∃ ν : FinPMF (X₁ × X₂),
        (∀ q : X₁ × X₂, r q.1 ≠ s q.2 → ν.prob q = 0) ∧
        f₁ (ν.map Prod.fst) + f₂ (ν.map Prod.snd) < ⊤)
      ↔ (∃ (p₁ : FinPMF X₁) (p₂ : FinPMF X₂),
          p₁.map r = p₂.map s ∧ f₁ p₁ < ⊤ ∧ f₂ p₂ < ⊤) := by
  constructor
  · rintro ⟨ν, hsupp, hfin⟩
    have hf := WithTop.add_lt_top.mp hfin
    exact ⟨ν.map Prod.fst, ν.map Prod.snd,
      finpmf_map_eq_of_support ν r s hsupp, hf.1, hf.2⟩
  · rintro ⟨p₁, p₂, hpush, hf1, hf2⟩
    refine ⟨FinPMF.condProduct p₁ p₂ r s hpush,
      condProduct_support p₁ p₂ r s hpush, ?_⟩
    rw [condProduct_map_fst, condProduct_map_snd]
    exact WithTop.add_lt_top.mpr ⟨hf1, hf2⟩

end FiniteStratum

/-! ## Mutant + control: the agreement clause is load-bearing -/

section Mutants

/-- Probe penalty: finite only at laws putting full mass on `0`. -/
def probeZero : FinPMF (Fin 2) → ENNRat :=
  fun p => if p.prob 0 = 1 then 0 else ⊤

/-- Probe penalty: finite only at laws putting full mass on `1`. -/
def probeOne : FinPMF (Fin 2) → ENNRat :=
  fun p => if p.prob 1 = 1 then 0 else ⊤

private theorem lt_top_of_probe {c : Prop} [Decidable c]
    (h : (if c then (0 : ENNRat) else ⊤) < ⊤) : c := by
  by_contra hc
  rw [if_neg hc] at h
  exact lt_irrefl ⊤ h

/-- **Mutant: drop the foot-agreement clause and the compatibility-to-
properness implication is refused.** Two finite-penalty component laws
exist (`δ₀` for the first probe, `δ₁` for the second), but with the
identity foot no fiber-concentrated coupling carries both: diagonal
support forces equal marginals, and the probes then demand
`ν(0,0) = ν(1,1) = 1` inside total mass `1`. -/
theorem mutant_no_agreement_fails :
    ¬ ((∃ p₁ p₂ : FinPMF (Fin 2), probeZero p₁ < ⊤ ∧ probeOne p₂ < ⊤) →
        (∃ ν : FinPMF (Fin 2 × Fin 2),
          (∀ q : Fin 2 × Fin 2, id q.1 ≠ id q.2 → ν.prob q = 0) ∧
          probeZero (ν.map Prod.fst) + probeOne (ν.map Prod.snd) < ⊤)) := by
  intro h
  have hpair : ∃ p₁ p₂ : FinPMF (Fin 2), probeZero p₁ < ⊤ ∧ probeOne p₂ < ⊤ := by
    refine ⟨deltaZero, deltaOne, ?_, ?_⟩
    · simp only [probeZero]
      rw [if_pos (by norm_num [deltaZero])]
      exact WithTop.coe_lt_top 0
    · simp only [probeOne]
      rw [if_pos (by norm_num [deltaOne])]
      exact WithTop.coe_lt_top 0
  obtain ⟨ν, hsupp, hfin⟩ := h hpair
  have hf := WithTop.add_lt_top.mp hfin
  have h1 : (ν.map Prod.fst).prob 0 = 1 := lt_top_of_probe hf.1
  have h2 : (ν.map Prod.snd).prob 1 = 1 := lt_top_of_probe hf.2
  have hoff₁ : ν.prob (0, 1) = 0 := hsupp (0, 1) (by decide)
  have hoff₂ : ν.prob (1, 0) = 0 := hsupp (1, 0) (by decide)
  rw [prob_map_fst, Fin.sum_univ_two, hoff₁, add_zero] at h1
  rw [prob_map_snd, Fin.sum_univ_two, hoff₁, zero_add] at h2
  have htot := ν.total
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at htot
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at htot
  rw [h1, h2, hoff₁, hoff₂] at htot
  norm_num at htot

/-- Paired positive control: the same probe shape with **agreeing** feet
is glued by the theorem — properness delivered constructively. -/
theorem glue_control :
    ∃ ν : FinPMF (Fin 2 × Fin 2),
      (∀ q : Fin 2 × Fin 2, id q.1 ≠ id q.2 → ν.prob q = 0) ∧
      probeZero (ν.map Prod.fst) + probeZero (ν.map Prod.snd) < ⊤ := by
  refine (finite_boxplus_proper_iff probeZero probeZero id id).mpr
    ⟨deltaZero, deltaZero, rfl, ?_, ?_⟩ <;>
  · simp only [probeZero]
    rw [if_pos (by norm_num [deltaZero])]
    exact WithTop.coe_lt_top 0

end Mutants

/-! ## Axiom receipts -/

#print axioms map_eq_of_concentrated
#print axioms boxplus_proper_iff_marginal_compatible
#print axioms FinPMF.map_map
#print axioms FinPMF.condProduct
#print axioms condProduct_support
#print axioms condProduct_map_fst
#print axioms condProduct_map_snd
#print axioms finpmf_coupling_of_map_eq
#print axioms finpmf_map_eq_of_support
#print axioms finite_boxplus_proper_iff
#print axioms mutant_no_agreement_fails
#print axioms glue_control

end Qtsl.Imprecise
