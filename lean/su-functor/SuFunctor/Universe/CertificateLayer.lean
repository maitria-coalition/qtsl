import SuFunctor.SingleSiteSemanticUniverse

/-! # The certificate layer: fibrewise morphisms, one storey

A certificate is a fibrewise *morphism* into a larger spec-class — a
system (an ideal point of the fibre order) included in the class a spec
presents, or one presented class included in a weaker one.  This module
certifies that the certificate layer rides the semantic universe as the
*order structure of its fibres* — one storey, no second Grothendieck
construction — by mechanizing the composition laws the reading needs
and the two counterexamples that locate where composition demands
witness data.  Contents:

* **The transported judgment factors through a fibrewise infimum**
  (`coupledSat_comap_iff_fibInf`): for an *arbitrary* carrier map
  `g : K₁ → K₂`, a system `τ` over `K₁` satisfies the transported atom
  iff its fibrewise infimum `fibInf g τ` (empty fibres read `⊤`)
  satisfies the original.  Transported model classes are therefore
  *preimages* (`comap_modelClass_eq_preimage`) — the lossy infimum
  through which penalties would have to be pulled back is located
  exactly here, as the reflection through which every transported
  judgment factors.  The landed surjective-stratum dictionary is the
  special case `fibInf g (σ ∘ g) = σ` (`fibInf_precomp`,
  `coupledSat_comp_iff_of_surjective`).
* **Spec-to-spec certificate transport is unconditionally monotone**
  (`SpecDnf.comap_modelClass_mono`): inclusion of model classes is
  preserved by transport along *every* carrier map — preimages are
  monotone.  No surjectivity, no semicontinuity, no finiteness beyond
  the presentation's own.  Only *system points* consume surjectivity
  (`comp_mem_modelClass_comap`), because a non-surjective transport
  rewrites a point's off-range reflection to `⊤`; the fence
  (`exists_comp_notMem_modelClass_comap`) shows that consumption is
  exact.
* **Presentation-order monotonicity** (`SpecDnf.comap_mono`,
  `dnfPull_mono`, `dnfBoxplus_mono`): adding disjuncts is a fibrewise
  morphism, and every fibre operation of the semantic universe
  preserves it — the composition law of the certificate layer at the
  presentation order, unconditional.
* **The composite certificate carries a witness**
  (`coupledSat_comp_add_of_dips`, `boxplus_mem_modelClass_dnfBoxplus`):
  two component certificates compose to a certificate on the pairwise
  composite atom exactly when the composite system's liveness family is
  re-witnessed — the safety faces compose unconditionally
  (`add_comp_safety_le`), the component dip witnesses are *deliberately
  unconsumed* (the landed `exists_coupledSat_add_fails` proves they
  cannot be), and the demanded family of composite dips is precisely
  the certificate data of the composite.
* **The pairwise compositor does not descend to semantic classes**
  (`exists_boxplus_not_semantically_monotone`): two presentations of
  the *same* model class whose composites with one fixed atom present
  genuinely different classes, distinguished by an explicit model.
  Composition of specs is an operation on presentations; the
  certificate layer's horizontal composition is witness-gated, and any
  bare-inclusion shortcut through the semantic order is refuted.

Everything here is order-theoretic: no topology, no `Fintype`, no
semicontinuity enters any hypothesis.
-/

namespace SuFunctor.Universe

noncomputable section

open scoped ENNReal

universe u

/-! ## The fibrewise infimum, and the transport dictionary at arbitrary
carrier maps -/

section FibInf

variable {K₁ K₂ : Type u}

/-- The fibrewise infimum along a carrier map: the reflection of a
system over `K₁` to a system over `K₂`, reading `⊤` on empty fibres.
This is the lossy infimum through which every transported judgment
factors. -/
def fibInf (g : K₁ → K₂) (τ : K₁ → ℝ≥0∞) : K₂ → ℝ≥0∞ :=
  fun y => ⨅ x ∈ g ⁻¹' {y}, τ x

/-- The fibrewise infimum sits below the system at every point of the
fibre. -/
theorem fibInf_le_of_eq {g : K₁ → K₂} {τ : K₁ → ℝ≥0∞} {y : K₂} {x : K₁}
    (hx : g x = y) : fibInf g τ y ≤ τ x := by
  show (⨅ x' ∈ g ⁻¹' {y}, τ x') ≤ τ x
  exact le_trans
    (iInf_le (fun x' : K₁ => ⨅ _ : x' ∈ g ⁻¹' {y}, τ x') x)
    (iInf_le (fun _ : x ∈ g ⁻¹' {y} => τ x) hx)

/-- A bound below the system pulls to a bound below the fibrewise
infimum. -/
theorem le_fibInf {g : K₁ → K₂} {τ : K₁ → ℝ≥0∞} {u : K₂ → ℝ≥0∞}
    (h : u ∘ g ≤ τ) : u ≤ fibInf g τ := by
  intro y
  show u y ≤ ⨅ x ∈ g ⁻¹' {y}, τ x
  refine le_iInf fun x => le_iInf fun hx => ?_
  have hgx : g x = y := hx
  have hux : u (g x) ≤ τ x := h x
  exact hgx ▸ hux

/-- The safety adjunction: a floor sits below the fibrewise infimum iff
its pull sits below the system.  Arbitrary carrier maps; empty fibres
are vacuous at `⊤`. -/
theorem le_fibInf_iff {g : K₁ → K₂} {τ : K₁ → ℝ≥0∞} {u : K₂ → ℝ≥0∞} :
    u ≤ fibInf g τ ↔ u ∘ g ≤ τ :=
  ⟨fun h x => le_trans (h (g x)) (fibInf_le_of_eq rfl), le_fibInf⟩

/-- The liveness transfer: the fibrewise infimum dips under a mark iff
the system dips under the pulled mark.  Arbitrary carrier maps; empty
fibres produce no dips, since nothing exceeds `⊤`. -/
theorem dip_fibInf_iff {g : K₁ → K₂} {τ : K₁ → ℝ≥0∞} {v : K₂ → ℝ≥0∞} :
    Dip (fibInf g τ) v ↔ Dip τ (v ∘ g) := by
  constructor
  · rintro ⟨y, hy⟩
    have h : ∃ x, g x = y ∧ τ x < v y := by
      simpa [fibInf, iInf_lt_iff, exists_prop] using hy
    obtain ⟨x, rfl, hlt⟩ := h
    exact ⟨x, hlt⟩
  · rintro ⟨x, hx⟩
    exact ⟨g x, lt_of_le_of_lt (fibInf_le_of_eq rfl) hx⟩

/-- **The transported judgment factors through the fibrewise infimum**:
along an arbitrary carrier map, a system satisfies the transported atom
iff its fibrewise-infimum reflection satisfies the original atom.  The
surjective-stratum judgment invariance is the special case where the
reflection retracts precomposition (`fibInf_precomp`). -/
theorem coupledSat_comap_iff_fibInf {g : K₁ → K₂} {τ : K₁ → ℝ≥0∞}
    {u : K₂ → ℝ≥0∞} {𝒱 : Set (K₂ → ℝ≥0∞)} :
    CoupledSat τ (u ∘ g) ((· ∘ g) '' 𝒱) ↔ CoupledSat (fibInf g τ) u 𝒱 := by
  constructor
  · rintro ⟨hsafe, hlive⟩
    refine ⟨le_fibInf_iff.mpr hsafe, fun v hv => ?_⟩
    exact dip_fibInf_iff.mpr (hlive (v ∘ g) ⟨v, hv, rfl⟩)
  · rintro ⟨hsafe, hlive⟩
    refine ⟨le_fibInf_iff.mp hsafe, ?_⟩
    rintro v' ⟨v, hv, rfl⟩
    exact dip_fibInf_iff.mp (hlive v hv)

/-- Along a surjective carrier map, the fibrewise infimum retracts
precomposition.  Surjectivity is consumed exactly here (the fibre of
each point must be inhabited), and nowhere else in this module. -/
theorem fibInf_precomp {g : K₁ → K₂} (hg : Function.Surjective g)
    (σ : K₂ → ℝ≥0∞) : fibInf g (σ ∘ g) = σ := by
  refine le_antisymm (fun y => ?_) (le_fibInf le_rfl)
  obtain ⟨x₀, rfl⟩ := hg y
  exact fibInf_le_of_eq rfl

/-- The landed surjective-stratum judgment invariance, re-derived from
the fibrewise-infimum dictionary: the dictionary strictly sharpens it. -/
theorem coupledSat_comp_iff_of_surjective {g : K₁ → K₂}
    (hg : Function.Surjective g) {σ u : K₂ → ℝ≥0∞}
    {𝒱 : Set (K₂ → ℝ≥0∞)} :
    CoupledSat (σ ∘ g) (u ∘ g) ((· ∘ g) '' 𝒱) ↔ CoupledSat σ u 𝒱 := by
  rw [coupledSat_comap_iff_fibInf, fibInf_precomp hg]

/-- The transported model class is a preimage, atom form: models of the
transported atom are exactly the systems whose reflection models the
original.  Arbitrary carrier maps. -/
theorem SpecAtom.comap_modelClass_eq_preimage {g : K₁ → K₂}
    (a : SpecAtom K₂) :
    (a.comap g).modelClass = fibInf g ⁻¹' a.modelClass := by
  ext τ
  show CoupledSat τ (a.floor ∘ g) ((· ∘ g) '' a.marks)
    ↔ CoupledSat (fibInf g τ) a.floor a.marks
  exact coupledSat_comap_iff_fibInf

/-- The transported model class is a preimage, presentation form. -/
theorem SpecDnf.comap_modelClass_eq_preimage {g : K₁ → K₂}
    (D : SpecDnf K₂) :
    (D.comap g).modelClass = fibInf g ⁻¹' D.modelClass := by
  rw [SpecDnf.modelClass, SpecDnf.modelClass, SpecDnf.comap_atoms,
    Set.biUnion_image, Set.preimage_iUnion₂]
  exact Set.iUnion₂_congr fun a _ =>
    SpecAtom.comap_modelClass_eq_preimage a

/-- **Spec-to-spec certificate transport is unconditionally monotone**:
inclusion of model classes is preserved by transport along every
carrier map — preimages are monotone.  The tight-seam composition law
of the certificate layer, with no surjectivity hypothesis. -/
theorem SpecDnf.comap_modelClass_mono {g : K₁ → K₂} {D E : SpecDnf K₂}
    (h : D.modelClass ⊆ E.modelClass) :
    (D.comap g).modelClass ⊆ (E.comap g).modelClass := by
  rw [SpecDnf.comap_modelClass_eq_preimage, SpecDnf.comap_modelClass_eq_preimage]
  exact Set.preimage_mono h

/-- System-point certificate transport, atom form: along a surjective
carrier map, a model of an atom transports to a model of the
transported atom.  (The fence below shows surjectivity is exact.) -/
theorem SpecAtom.comp_mem_modelClass_comap {g : K₁ → K₂}
    (hg : Function.Surjective g) {σ : K₂ → ℝ≥0∞} (a : SpecAtom K₂)
    (h : σ ∈ a.modelClass) : σ ∘ g ∈ (a.comap g).modelClass := by
  rw [SpecAtom.comap_modelClass_eq_preimage]
  show fibInf g (σ ∘ g) ∈ a.modelClass
  rw [fibInf_precomp hg]
  exact h

/-- System-point certificate transport, presentation form. -/
theorem SpecDnf.comp_mem_modelClass_comap {g : K₁ → K₂}
    (hg : Function.Surjective g) {σ : K₂ → ℝ≥0∞} (D : SpecDnf K₂)
    (h : σ ∈ D.modelClass) : σ ∘ g ∈ (D.comap g).modelClass := by
  rw [SpecDnf.comap_modelClass_eq_preimage]
  show fibInf g (σ ∘ g) ∈ D.modelClass
  rw [fibInf_precomp hg]
  exact h

/-- **System points are where surjectivity is load-bearing**: along a
non-surjective carrier map, a model of an atom need not transport to a
model of the transported atom — the point's off-range reflection reads
`⊤`, and the pulled mark degenerates to a penalty nothing dips under.
(The class-level face of the same geometry is the landed
`exists_image_modelClass_not_subset`.) -/
theorem exists_comp_notMem_modelClass_comap :
    ∃ (g : Unit → Bool) (a : SpecAtom Bool) (σ : Bool → ℝ≥0∞),
      σ ∈ a.modelClass ∧ σ ∘ g ∉ (a.comap g).modelClass := by
  classical
  set v : Bool → ℝ≥0∞ := fun b => if b then 0 else ⊤ with hv
  refine ⟨fun _ => true,
    ⟨0, {v, ⊤}, (Set.finite_singleton _).insert _, Or.inr rfl⟩, 0,
    ⟨le_rfl, ?_⟩, ?_⟩
  · rintro w (rfl | hw)
    · exact ⟨false, by simp [hv]⟩
    · rw [Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨true, by simp⟩
  · rintro ⟨-, hlive⟩
    obtain ⟨x, hx⟩ := hlive (v ∘ (fun _ : Unit => true)) ⟨v, Or.inl rfl, rfl⟩
    simp [hv] at hx

/-- Presentation-order monotonicity of transport: adding disjuncts
commutes with transport.  (The image of a larger atom family is
larger.) -/
theorem SpecDnf.comap_mono {g : K₁ → K₂} {D E : SpecDnf K₂}
    (h : D.atoms ⊆ E.atoms) :
    (D.comap g).atoms ⊆ (E.comap g).atoms := by
  rw [SpecDnf.comap_atoms, SpecDnf.comap_atoms]
  exact Set.image_mono h

end FibInf

/-! ## The composite certificate: safety faces compose, the liveness
family is re-witnessed -/

section Composite

variable {K K₁ K₂ : Type u}

/-- **The composite certificate, con-witness form**: two component
certificates compose to a certificate on the pairwise composite —
floors pulled and added, liveness families pulled and unioned — exactly
when the composite system's liveness family is re-witnessed.  The
safety faces compose unconditionally (`add_comp_safety_le`); the
demanded dip family `hcon` is the certificate data of the composite.
The component dip witnesses are deliberately unconsumed: the landed
`exists_coupledSat_add_fails` proves no composition law can consume
them (one component's dip is destroyed by the other's cost, already
along identity transports). -/
theorem coupledSat_comp_add_of_dips (g₁ : K → K₁) (g₂ : K → K₂)
    {σ₁ u₁ : K₁ → ℝ≥0∞} {σ₂ u₂ : K₂ → ℝ≥0∞}
    {𝒱₁ : Set (K₁ → ℝ≥0∞)} {𝒱₂ : Set (K₂ → ℝ≥0∞)}
    (h₁ : CoupledSat σ₁ u₁ 𝒱₁) (h₂ : CoupledSat σ₂ u₂ 𝒱₂)
    (hcon : ∀ w ∈ (· ∘ g₁) '' 𝒱₁ ∪ (· ∘ g₂) '' 𝒱₂,
      Dip ((σ₁ ∘ g₁) + (σ₂ ∘ g₂)) w) :
    CoupledSat ((σ₁ ∘ g₁) + (σ₂ ∘ g₂)) ((u₁ ∘ g₁) + (u₂ ∘ g₂))
      ((· ∘ g₁) '' 𝒱₁ ∪ (· ∘ g₂) '' 𝒱₂) :=
  ⟨add_comp_safety_le g₁ g₂ h₁.1 h₂.1, hcon⟩

/-- Dips over a one-point carrier are dips at the point. -/
theorem dip_unit_iff {σ w : Unit → ℝ≥0∞} : Dip σ w ↔ σ () < w () :=
  ⟨fun ⟨x, h⟩ => by cases x; exact h, fun h => ⟨(), h⟩⟩

/-- **The pairwise compositor does not descend to semantic classes**:
two presentations of the *same* model class — one atom `(0, {6, ⊤})`
against the two-atom split `(0, {2, ⊤})`, `(2, {6, ⊤})` — whose
pairwise composites with the fixed atom `(2, {⊤})` (floors added,
liveness families unioned) present genuinely different classes: the
model `3` satisfies the composite with the one-atom presentation and
satisfies neither composite with the split.  Splitting a spec into
finer disjuncts strengthens its composites, because each disjunct's
floor participates in the composite sum.  Composition of specs is an
operation on presentations, not on their semantic classes; the
certificate layer's horizontal composition is witness-gated per
presentation, and any bare-inclusion shortcut through the semantic
order is refuted. -/
theorem exists_boxplus_not_semantically_monotone :
    ∃ (a e e₁ e₂ : SpecAtom Unit) (τ : Unit → ℝ≥0∞),
      e.modelClass = e₁.modelClass ∪ e₂.modelClass ∧
      CoupledSat τ (a.floor + e.floor) (a.marks ∪ e.marks) ∧
      ¬ CoupledSat τ (a.floor + e₁.floor) (a.marks ∪ e₁.marks) ∧
      ¬ CoupledSat τ (a.floor + e₂.floor) (a.marks ∪ e₂.marks) := by
  classical
  set c : ℝ≥0∞ → Unit → ℝ≥0∞ := fun r _ => r with hc
  have h26 : (2 : ℝ≥0∞) ≤ 6 := by norm_num
  have h23 : (2 : ℝ≥0∞) ≤ 3 := by norm_num
  have h36 : (3 : ℝ≥0∞) < 6 := by norm_num
  have h32 : ¬ (3 : ℝ≥0∞) < 2 := by norm_num
  have h43 : ¬ (2 + 2 : ℝ≥0∞) ≤ 3 := by norm_num
  refine ⟨⟨c 2, {⊤}, Set.finite_singleton _, rfl⟩,
    ⟨c 0, {c 6, ⊤}, (Set.finite_singleton _).insert _, Or.inr rfl⟩,
    ⟨c 0, {c 2, ⊤}, (Set.finite_singleton _).insert _, Or.inr rfl⟩,
    ⟨c 2, {c 6, ⊤}, (Set.finite_singleton _).insert _, Or.inr rfl⟩,
    c 3, ?_, ?_, ?_, ?_⟩
  · -- the two presentations denote the same class
    ext σ
    have hmem : ∀ (u : Unit → ℝ≥0∞) (𝒱 : Set (Unit → ℝ≥0∞)),
        CoupledSat σ u 𝒱 ↔ u () ≤ σ () ∧ ∀ v ∈ 𝒱, σ () < v () := by
      intro u 𝒱
      constructor
      · rintro ⟨hsafe, hlive⟩
        exact ⟨hsafe (), fun v hv => dip_unit_iff.mp (hlive v hv)⟩
      · rintro ⟨hsafe, hlive⟩
        exact ⟨fun x => by cases x; exact hsafe,
          fun v hv => dip_unit_iff.mpr (hlive v hv)⟩
    show CoupledSat σ (c 0) {c 6, ⊤} ↔
      CoupledSat σ (c 0) {c 2, ⊤} ∨ CoupledSat σ (c 2) {c 6, ⊤}
    rw [hmem, hmem, hmem]
    constructor
    · rintro ⟨-, hlive⟩
      have h6 : σ () < 6 := hlive (c 6) (Or.inl rfl)
      rcases lt_trichotomy (σ ()) 2 with h2 | h2 | h2
      · refine Or.inl ⟨zero_le, ?_⟩
        rintro v (rfl | hv)
        · exact h2
        · rw [Set.mem_singleton_iff] at hv
          subst hv
          exact lt_of_lt_of_le h6 le_top
      · refine Or.inr ⟨le_of_eq h2.symm, ?_⟩
        rintro v (rfl | hv)
        · exact h6
        · rw [Set.mem_singleton_iff] at hv
          subst hv
          exact lt_of_lt_of_le h6 le_top
      · refine Or.inr ⟨le_of_lt h2, ?_⟩
        rintro v (rfl | hv)
        · exact h6
        · rw [Set.mem_singleton_iff] at hv
          subst hv
          exact lt_of_lt_of_le h6 le_top
    · rintro (⟨-, hlive⟩ | ⟨-, hlive⟩)
      · have h2 : σ () < 2 := hlive (c 2) (Or.inl rfl)
        refine ⟨zero_le, ?_⟩
        rintro v (rfl | hv)
        · exact lt_of_lt_of_le h2 h26
        · rw [Set.mem_singleton_iff] at hv
          subst hv
          exact lt_of_lt_of_le (lt_of_lt_of_le h2 h26) le_top
      · have h6 : σ () < 6 := hlive (c 6) (Or.inl rfl)
        refine ⟨zero_le, ?_⟩
        rintro v (rfl | hv)
        · exact h6
        · rw [Set.mem_singleton_iff] at hv
          subst hv
          exact lt_of_lt_of_le h6 le_top
  · -- the composite with the one-atom presentation is satisfied by 3
    refine ⟨fun x => by cases x; show (2 : ℝ≥0∞) + 0 ≤ 3; rwa [add_zero], ?_⟩
    intro w hw
    rcases hw with hw | hw
    · rw [Set.mem_singleton_iff] at hw
      subst hw
      exact dip_unit_iff.mpr (lt_of_lt_of_le h36 le_top)
    · rcases hw with rfl | hw
      · exact dip_unit_iff.mpr h36
      · rw [Set.mem_singleton_iff] at hw
        subst hw
        exact dip_unit_iff.mpr (lt_of_lt_of_le h36 le_top)
  · -- the composite with the split's first atom is refuted at its mark
    rintro ⟨-, hlive⟩
    have := dip_unit_iff.mp (hlive (c 2) (Or.inr (Or.inl rfl)))
    exact h32 this
  · -- the composite with the split's second atom is refuted at its floor
    rintro ⟨hsafe, -⟩
    exact h43 (hsafe ())

end Composite

end

end SuFunctor.Universe

/-! ## The wiring-level face: the fibre operations of the semantic
universe preserve fibrewise morphisms -/

namespace SuFunctor

noncomputable section

open CategoryTheory CategoryTheory.WireSpan PseudoDoubleCategoryStruct
open SuFunctor.Plain SuFunctor.Universe
open scoped ENNReal

universe u

variable {El : Type u}

/-- Presentation-order monotonicity of tight/cell transport at the
wiring base. -/
theorem dnfPull_mono {X Y : Type u} (h : X → Y)
    {D E : SpecDnf (Joint Y)} (hDE : D.atoms ⊆ E.atoms) :
    (dnfPull h D).atoms ⊆ (dnfPull h E).atoms := by
  rw [dnfPull_atoms, dnfPull_atoms]
  exact Set.image_mono hDE

/-- Presentation-order monotonicity of the compositor, in both
arguments. -/
theorem dnfBoxplus_mono {A B C : WireSpan El} {M : Pat A B} {N : Pat B C}
    {D₁ E₁ : DnfCpl M} {D₂ E₂ : DnfCpl N}
    (h₁ : D₁.atoms ⊆ E₁.atoms) (h₂ : D₂.atoms ⊆ E₂.atoms) :
    (dnfBoxplus D₁ D₂).atoms ⊆ (dnfBoxplus E₁ E₂).atoms :=
  Set.image2_subset h₁ h₂

/-- **The composite certificate at the wiring base**: component
certificates on atoms of the two decorations, together with the
composite liveness witness, certify the composite system against the
composite decoration.  The witness `hcon` is the certificate data of
the composite; the safety faces compose unconditionally. -/
theorem boxplus_mem_modelClass_dnfBoxplus {A B C : WireSpan El}
    {M : Pat A B} {N : Pat B C} {D₁ : DnfCpl M} {D₂ : DnfCpl N}
    {a₁ : SpecAtom (Joint (Pat.Tot M))} {a₂ : SpecAtom (Joint (Pat.Tot N))}
    {σ₁ : Pen (Pat.Tot M)} {σ₂ : Pen (Pat.Tot N)}
    (ha₁ : a₁ ∈ D₁.atoms) (ha₂ : a₂ ∈ D₂.atoms)
    (h₁ : CoupledSat σ₁ a₁.floor a₁.marks)
    (h₂ : CoupledSat σ₂ a₂.floor a₂.marks)
    (hcon : ∀ w ∈ (atomBoxplus a₁ a₂).marks, Dip (boxplus σ₁ σ₂) w) :
    boxplus σ₁ σ₂ ∈ (dnfBoxplus D₁ D₂).modelClass := by
  rw [SpecDnf.mem_modelClass_iff]
  refine ⟨atomBoxplus a₁ a₂, Set.mem_image2_of_mem ha₁ ha₂, ?_, hcon⟩
  intro ν
  exact add_le_add (h₁.1 _) (h₂.1 _)

end

end SuFunctor
