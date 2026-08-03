import Pointfree.Valuation.Basic

/-! # The subprobability promotion: the point-free dagger chart

The semantic universe reads missing mass as an explicit *dead state*:
`Δ≤1(X) ≅ Δ(X ⊔ {†})`.  Point-free, the frame of `X ⊔ {†}` is the
product frame `L × Prop` (the dagger point is isolated, so its frame of
opens is `Prop`), and the chart becomes a statement about valuations:

> subprobability valuations on `L` correspond exactly to probability
> valuations on `L × Prop`, by sending `μ` to
> `(a, p) ↦ μ a + (if p then 1 - μ ⊤ else 0)`.

Classically this promotion needs measure plumbing — pushforward along a
measurable embedding, `comap`, restriction, and a decomposition of the
ambient measure.  Here **modularity alone drives everything**: the two
identities the inverse needs are each one application of the modular
law at a complemented pair,

* `ν (a, True) = ν (a, False) + ν (⊥, True)`
  (modularity at `(a, False)`, `(⊥, True)`), and
* `ν (⊤, False) + ν (⊥, True) = ν ⊤`
  (modularity at `(⊤, False)`, `(⊥, True)`),

with no σ-algebra, no null sets, and no measurable-embedding API.
Scott continuity transports across the chart in both directions.

The topology module builds on this chart: the narrow topology of the
subprobability carrier *is* the plain lower (Scott) topology of the
promoted probability carrier, pulled back — the point-free explanation
of why total mass is a weakly continuous coordinate of the carrier.
-/

namespace Pointfree

open scoped ENNReal

variable {L : Type*} [Order.Frame L]

namespace Valuation

/-! ## `L × Prop` bookkeeping

Elements of the dagger frame `L × Prop` have a propositional second
component; the lattice operations act componentwise and are
definitionally `∨`/`∧`/`False`/`True` there.  The one genuinely
non-definitional step is rewriting a propositional component along a
logical equivalence, which `prodMk_eq` packages via `propext`. -/

omit [Order.Frame L] in
theorem prodMk_eq {a b : L} {p q : Prop} (h : a = b) (h' : p ↔ q) :
    ((a, p) : L × Prop) = (b, q) := by
  subst h
  exact congrArg _ (propext h')

theorem bot_prod_prop : (⊥ : L × Prop) = ((⊥ : L), False) := rfl

theorem top_prod_prop : (⊤ : L × Prop) = ((⊤ : L), True) := rfl

theorem sup_mk_prop (a b : L) (p q : Prop) :
    ((a, p) : L × Prop) ⊔ (b, q) = (a ⊔ b, p ∨ q) := rfl

theorem inf_mk_prop (a b : L) (p q : Prop) :
    ((a, p) : L × Prop) ⊓ (b, q) = (a ⊓ b, p ∧ q) := rfl

/-- The biSup–sum exchange on a directed family: the point-free face of
"suprema of monotone families add along directed sets". -/
theorem biSup_add_biSup {β : Type*} {d : Set β} (hd : d.Nonempty)
    {f g : β → ℝ≥0∞}
    (h : ∀ x ∈ d, ∀ y ∈ d, ∃ z ∈ d, f x + g y ≤ f z + g z) :
    (⨆ x ∈ d, f x) + (⨆ x ∈ d, g x) = ⨆ x ∈ d, (f x + g x) := by
  haveI : Nonempty ↥d := hd.to_subtype
  rw [← iSup_subtype'' d f, ← iSup_subtype'' d g,
    ← iSup_subtype'' d (fun x => f x + g x)]
  exact ENNReal.iSup_add_iSup fun i j => by
    obtain ⟨z, hz, hle⟩ := h i.1 i.2 j.1 j.2
    exact ⟨⟨z, hz⟩, hle⟩

open Classical in
/-- The **dagger indicator**: mass `m` exactly when the dagger-side
proposition holds.  The decidability instance is fixed inside the
definition once and for all, so statements about `daggerInd` never
suffer instance drift. -/
noncomputable def daggerInd (m : ℝ≥0∞) (p : Prop) : ℝ≥0∞ :=
  if p then m else 0

@[simp] theorem daggerInd_false (m : ℝ≥0∞) : daggerInd m False = 0 :=
  if_neg not_false

@[simp] theorem daggerInd_true (m : ℝ≥0∞) : daggerInd m True = m :=
  if_pos trivial

theorem daggerInd_of {m : ℝ≥0∞} {p : Prop} (h : p) : daggerInd m p = m :=
  if_pos h

theorem daggerInd_of_not {m : ℝ≥0∞} {p : Prop} (h : ¬p) : daggerInd m p = 0 :=
  if_neg h

theorem daggerInd_le (m : ℝ≥0∞) (p : Prop) : daggerInd m p ≤ m := by
  by_cases h : p
  · rw [daggerInd_of h]
  · rw [daggerInd_of_not h]
    exact zero_le

theorem daggerInd_mono (m : ℝ≥0∞) {p q : Prop} (h : p → q) :
    daggerInd m p ≤ daggerInd m q := by
  by_cases hp : p
  · rw [daggerInd_of hp, daggerInd_of (h hp)]
  · rw [daggerInd_of_not hp]
    exact zero_le

/-- The indicator is modular in its proposition — the `Prop`-component
face of the promotion's modularity. -/
theorem daggerInd_modular (m : ℝ≥0∞) (p q : Prop) :
    daggerInd m p + daggerInd m q
      = daggerInd m (p ∨ q) + daggerInd m (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;>
    simp [daggerInd, hp, hq, add_comm]

/-- The promotion of a valuation by a dagger weight `m`: the mass `m`
is deposited on the dagger point. -/
noncomputable def promoteVal (μ : Valuation L) (m : ℝ≥0∞) : Valuation (L × Prop) where
  toFun x := μ x.1 + daggerInd m x.2
  map_bot' := by
    rw [bot_prod_prop]
    show μ (⊥ : L) + daggerInd m False = 0
    rw [daggerInd_false, μ.map_bot, add_zero]
  monotone' := by
    rintro ⟨a, p⟩ ⟨b, q⟩ ⟨hab, hpq⟩
    show μ a + daggerInd m p ≤ μ b + daggerInd m q
    exact add_le_add (μ.mono hab) (daggerInd_mono m hpq)
  modular' := by
    rintro ⟨a, p⟩ ⟨b, q⟩
    rw [sup_mk_prop, inf_mk_prop]
    show μ a + daggerInd m p + (μ b + daggerInd m q)
      = μ (a ⊔ b) + daggerInd m (p ∨ q) + (μ (a ⊓ b) + daggerInd m (p ∧ q))
    calc μ a + daggerInd m p + (μ b + daggerInd m q)
        = μ a + μ b + (daggerInd m p + daggerInd m q) := by ring
      _ = μ (a ⊔ b) + μ (a ⊓ b)
            + (daggerInd m (p ∨ q) + daggerInd m (p ∧ q)) := by
          rw [μ.modular a b, daggerInd_modular]
      _ = μ (a ⊔ b) + daggerInd m (p ∨ q)
            + (μ (a ⊓ b) + daggerInd m (p ∧ q)) := by ring

theorem promoteVal_apply (μ : Valuation L) (m : ℝ≥0∞) (a : L) (p : Prop) :
    promoteVal μ m (a, p) = μ a + daggerInd m p := rfl

@[simp] theorem promoteVal_apply_false (μ : Valuation L) (m : ℝ≥0∞) (a : L) :
    promoteVal μ m (a, False) = μ a := by
  rw [promoteVal_apply, daggerInd_false, add_zero]

@[simp] theorem promoteVal_apply_true (μ : Valuation L) (m : ℝ≥0∞) (a : L) :
    promoteVal μ m (a, True) = μ a + m := by
  rw [promoteVal_apply, daggerInd_true]

/-- The restriction of a valuation on `L × Prop` to the `L`-slice: the
point-free "forget the dagger point". -/
def restrictVal (ν : Valuation (L × Prop)) : Valuation L where
  toFun a := ν (a, False)
  map_bot' := ν.map_bot
  monotone' := fun a b hab => ν.mono ⟨hab, le_refl _⟩
  modular' := fun a b => by
    have hsup : ((a, False) : L × Prop) ⊔ (b, False) = (a ⊔ b, False) :=
      prodMk_eq rfl or_self_iff
    have hinf : ((a, False) : L × Prop) ⊓ (b, False) = (a ⊓ b, False) :=
      prodMk_eq rfl and_self_iff
    have h := ν.modular (a, False) (b, False)
    rwa [hsup, hinf] at h

@[simp] theorem restrictVal_apply (ν : Valuation (L × Prop)) (a : L) :
    restrictVal ν a = ν (a, False) := rfl

/-! ## The two modular identities -/

/-- **First modular identity**: the dagger point's mass is a summand of
every `True`-slice value.  One application of modularity at the
complemented pair `(a, False)`, `(⊥, True)`. -/
theorem apply_true_eq_add (ν : Valuation (L × Prop)) (a : L) :
    ν (a, True) = ν (a, False) + ν (⊥, True) := by
  have hsup : ((a, False) : L × Prop) ⊔ (⊥, True) = (a, True) :=
    prodMk_eq (sup_bot_eq a) ⟨fun _ => trivial, fun _ => Or.inr trivial⟩
  have hinf : ((a, False) : L × Prop) ⊓ (⊥, True) = ⊥ :=
    prodMk_eq (inf_bot_eq a) ⟨fun h => h.1, False.elim⟩
  have h := ν.modular (a, False) (⊥, True)
  rw [hsup, hinf, ν.map_bot, add_zero] at h
  exact h.symm

/-- **Second modular identity**: the `L`-slice mass and the dagger mass
partition the total.  One application of modularity at the complemented
pair `(⊤, False)`, `(⊥, True)`. -/
theorem apply_top_false_add_bot_true (ν : Valuation (L × Prop)) :
    ν (⊤, False) + ν (⊥, True) = ν ⊤ := by
  have hsup : ((⊤, False) : L × Prop) ⊔ (⊥, True) = ⊤ :=
    prodMk_eq (sup_bot_eq (⊤ : L)) ⟨fun _ => trivial, fun _ => Or.inr trivial⟩
  have hinf : ((⊤, False) : L × Prop) ⊓ (⊥, True) = ⊥ :=
    prodMk_eq (inf_bot_eq (⊤ : L)) ⟨fun h => h.1, False.elim⟩
  have h := ν.modular (⊤, False) (⊥, True)
  rwa [hsup, hinf, ν.map_bot, add_zero] at h

end Valuation

namespace SubProb

open Valuation

/-- **The promotion**: a subprobability valuation on `L` becomes a
probability valuation on `L × Prop`, the missing mass deposited on the
dagger point. -/
noncomputable def promote (μ : SubProb L) : Prob (L × Prop) :=
  ⟨promoteVal μ.toValuation (1 - μ ⊤), by
    show promoteVal μ.toValuation (1 - μ ⊤) (⊤, True) = 1
    rw [promoteVal_apply_true]
    exact add_tsub_cancel_of_le μ.mass_le_one⟩

theorem promote_apply (μ : SubProb L) (a : L) (p : Prop) :
    promote μ (a, p) = μ a + Valuation.daggerInd (1 - μ ⊤) p := rfl

@[simp] theorem promote_apply_false (μ : SubProb L) (a : L) :
    promote μ (a, False) = μ a :=
  promoteVal_apply_false _ _ a

@[simp] theorem promote_apply_true (μ : SubProb L) (a : L) :
    promote μ (a, True) = μ a + (1 - μ ⊤) :=
  promoteVal_apply_true _ _ a

/-- The dagger point carries exactly the missing mass. -/
@[simp] theorem promote_dagger (μ : SubProb L) :
    promote μ (⊥, True) = 1 - μ ⊤ := by
  rw [promote_apply_true, SubProb.map_bot, zero_add]

end SubProb

namespace Prob

open Valuation

/-- **The restriction**: a probability valuation on `L × Prop` restricts
to a subprobability valuation on the `L`-slice. -/
def restrict (ν : Prob (L × Prop)) : SubProb L :=
  ⟨restrictVal ν.toValuation, by
    show ν.toValuation (⊤, False) ≤ 1
    calc ν.toValuation (⊤, False) ≤ ν.toValuation ⊤ := ν.mono le_top
      _ = 1 := ν.mass_eq_one⟩

@[simp] theorem restrict_apply (ν : Prob (L × Prop)) (a : L) :
    restrict ν a = ν (a, False) := rfl

/-- The first modular identity, at the probability face. -/
theorem apply_true_eq_add (ν : Prob (L × Prop)) (a : L) :
    ν (a, True) = ν (a, False) + ν (⊥, True) :=
  Valuation.apply_true_eq_add ν.1 a

/-- The dagger mass of a probability valuation is the complement of its
`L`-slice mass — the second modular identity, solved for the dagger. -/
theorem dagger_eq_one_sub (ν : Prob (L × Prop)) :
    ν (⊥, True) = 1 - ν (⊤, False) := by
  have h : ν (⊥, True) + ν (⊤, False) = 1 := by
    rw [add_comm, ← ν.mass_eq_one]
    exact Valuation.apply_top_false_add_bot_true ν.1
  exact ENNReal.eq_sub_of_add_eq (ν.apply_ne_top _) h

end Prob

namespace SubProb

open Valuation

@[simp] theorem restrict_promote (μ : SubProb L) : (promote μ).restrict = μ := by
  ext a
  rw [Prob.restrict_apply, promote_apply_false]

@[simp] theorem promote_restrict (ν : Prob (L × Prop)) : promote ν.restrict = ν := by
  ext x
  obtain ⟨a, p⟩ := x
  by_cases hp : p
  · rw [show ((a, p) : L × Prop) = (a, True) from prodMk_eq rfl (iff_true_intro hp)]
    rw [promote_apply_true]
    simp only [Prob.restrict_apply]
    rw [← Prob.dagger_eq_one_sub]
    exact (Prob.apply_true_eq_add ν a).symm
  · rw [show ((a, p) : L × Prop) = (a, False) from prodMk_eq rfl (iff_false_intro hp)]
    rw [promote_apply_false, Prob.restrict_apply]

/-- **The dagger chart**: subprobability valuations on `L` are exactly
probability valuations on `L × Prop`.  The forward map deposits the
missing mass on the dagger point; the inverse restricts to the
`L`-slice; both round trips are the modular identities. -/
noncomputable def promoteEquiv : SubProb L ≃ Prob (L × Prop) where
  toFun := promote
  invFun := Prob.restrict
  left_inv := restrict_promote
  right_inv := promote_restrict

@[simp] theorem promoteEquiv_apply (μ : SubProb L) :
    (promoteEquiv (L := L)) μ = promote μ := rfl

@[simp] theorem promoteEquiv_symm_apply (ν : Prob (L × Prop)) :
    (promoteEquiv (L := L)).symm ν = ν.restrict := rfl

/-! ## Scott continuity across the chart -/

/-- Restriction preserves Scott continuity: the `L`-slice embedding
preserves directed suprema. -/
theorem isScottContinuous_restrictVal {ν : Valuation (L × Prop)}
    (hν : ν.IsScottContinuous) : (restrictVal ν).IsScottContinuous := by
  intro d hd hdir
  have hkey : sSup ((fun a : L => ((a, False) : L × Prop)) '' d) = ((sSup d : L), False) := by
    have h1 : (sSup ((fun a : L => ((a, False) : L × Prop)) '' d)).1 = sSup d := by
      calc (sSup ((fun a : L => ((a, False) : L × Prop)) '' d)).1
          = sSup (Prod.fst '' ((fun a : L => ((a, False) : L × Prop)) '' d)) :=
            Prod.fst_sSup _
        _ = sSup ((fun a : L => a) '' d) := by rw [Set.image_image]
        _ = sSup d := by rw [Set.image_id']
    have h2 : (sSup ((fun a : L => ((a, False) : L × Prop)) '' d)).2 = False := by
      have hstep : (sSup ((fun a : L => ((a, False) : L × Prop)) '' d)).2
          = sSup (Prod.snd '' ((fun a : L => ((a, False) : L × Prop)) '' d)) :=
        Prod.snd_sSup _
      rw [hstep, Set.image_image]
      show sSup ((fun _ : L => False) '' d) = False
      rw [hd.image_const False, sSup_singleton]
    calc sSup ((fun a : L => ((a, False) : L × Prop)) '' d)
        = ((sSup ((fun a : L => ((a, False) : L × Prop)) '' d)).1,
           (sSup ((fun a : L => ((a, False) : L × Prop)) '' d)).2) := rfl
      _ = ((sSup d : L), False) := by rw [h1, h2]
  have himage : DirectedOn (· ≤ ·) ((fun a : L => ((a, False) : L × Prop)) '' d) :=
    hdir.mono_comp fun _ _ h => ⟨h, le_refl _⟩
  rw [restrictVal_apply, ← hkey,
    hν _ (hd.image _) himage, iSup_image]
  simp only [restrictVal_apply]

/-- Promotion preserves Scott continuity: on a directed family the
`L`-component supremum and the dagger-indicator supremum add. -/
theorem isScottContinuous_promoteVal {μ : SubProb L}
    (hμ : μ.toValuation.IsScottContinuous) :
    (promote μ).toValuation.IsScottContinuous := by
  classical
  intro d hd hdir
  have happly : ∀ x : L × Prop,
      (promote μ).toValuation x = μ x.1 + daggerInd (1 - μ ⊤) x.2 :=
    fun ⟨_, _⟩ => rfl
  -- componentwise decomposition of the supremum
  have hfst : (sSup d).1 = sSup (Prod.fst '' d) := Prod.fst_sSup d
  have hsnd : (sSup d).2 ↔ ∃ x ∈ d, x.2 := by
    rw [show ((sSup d).2 : Prop) = sSup (Prod.snd '' d) from Prod.snd_sSup d,
      sSup_Prop_eq]
    constructor
    · rintro ⟨q, ⟨x, hx, rfl⟩, hq⟩
      exact ⟨x, hx, hq⟩
    · rintro ⟨x, hx, hp⟩
      exact ⟨x.2, ⟨x, hx, rfl⟩, hp⟩
  -- the L-component: Scott continuity of μ on the directed image
  have hdfst : DirectedOn (· ≤ ·) (Prod.fst '' d) :=
    hdir.mono_comp fun _ _ h => h.1
  have hL : μ (sSup d).1 = ⨆ x ∈ d, μ x.1 := by
    rw [hfst]
    have hkey := hμ _ (hd.image Prod.fst) hdfst
    rw [iSup_image] at hkey
    exact hkey
  -- the dagger indicator: the indicator of an existential is the biSup
  have hInd : daggerInd (1 - μ ⊤) (sSup d).2
      = ⨆ x ∈ d, daggerInd (1 - μ ⊤) x.2 := by
    by_cases h : ∃ x ∈ d, x.2
    · obtain ⟨x, hx, hp⟩ := h
      rw [daggerInd_of (hsnd.mpr ⟨x, hx, hp⟩)]
      apply le_antisymm
      · calc (1 : ℝ≥0∞) - μ ⊤
            = daggerInd (1 - μ ⊤) x.2 := (daggerInd_of hp).symm
          _ ≤ ⨆ y ∈ d, daggerInd (1 - μ ⊤) y.2 :=
            le_iSup₂ (f := fun y (_ : y ∈ d) => daggerInd (1 - μ ⊤) y.2) x hx
      · exact iSup₂_le fun y _ => daggerInd_le _ _
    · rw [daggerInd_of_not (fun hs => h (hsnd.mp hs))]
      have h0 : ∀ y ∈ d, daggerInd (1 - μ ⊤) y.2 = 0 :=
        fun y hy => daggerInd_of_not (fun hp => h ⟨y, hy, hp⟩)
      exact (le_antisymm (iSup₂_le fun y hy => le_of_eq (h0 y hy))
        zero_le).symm
  rw [happly (sSup d), hL, hInd]
  -- suprema of monotone families add along a directed set
  have hexch := Valuation.biSup_add_biSup (d := d) hd
    (f := fun x => μ x.1) (g := fun x => daggerInd (1 - μ ⊤) x.2)
    (fun x hx y hy => by
      obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
      exact ⟨z, hz, add_le_add (μ.mono hxz.1) (daggerInd_mono _ hyz.2)⟩)
  rw [hexch]
  refine le_antisymm (iSup₂_le fun x hx => ?_) (iSup₂_le fun x hx => ?_)
  · rw [← happly x]
    exact le_iSup₂ (f := fun y (_ : y ∈ d) => (promote μ).toValuation y) x hx
  · rw [happly x]
    exact le_iSup₂ (f := fun y (_ : y ∈ d) =>
      μ y.1 + daggerInd (1 - μ ⊤) y.2) x hx

/-- Scott continuity transports across the dagger chart, in both
directions: the promotion is Scott continuous exactly when the
subprobability valuation is. -/
theorem isScottContinuous_promote_iff (μ : SubProb L) :
    (promote μ).toValuation.IsScottContinuous
      ↔ μ.toValuation.IsScottContinuous := by
  constructor
  · intro h
    have hr := isScottContinuous_restrictVal (ν := (promote μ).toValuation) h
    have : (promote μ).restrict = μ := restrict_promote μ
    rw [show μ.toValuation = ((promote μ).restrict).toValuation from by rw [this]]
    exact hr
  · exact isScottContinuous_promoteVal

end SubProb

end Pointfree
