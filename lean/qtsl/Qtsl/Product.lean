import Qtsl.QtslSoundness

/-!
# Product-rule soundness

Soundness of the Morse-product rule at witness level: orbits, limit
sets, and chains factor through the product (`lem:qmp-factor` shape),
witnesses transport componentwise, and the product of two Morse
witnesses is a Morse witness for the product semiflow.
-/

namespace PPLC
namespace Qtsl

open scoped NNReal

namespace Semiflow

variable {X₁ X₂ : Type*}

def prod (φ₁ : Semiflow X₁) (φ₂ : Semiflow X₂) : Semiflow (X₁ × X₂) where
  flow t p := (φ₁.flow t p.1, φ₂.flow t p.2)
  flow_zero p := by rw [φ₁.flow_zero, φ₂.flow_zero]
  flow_add s t p := by rw [φ₁.flow_add, φ₂.flow_add]

@[simp] theorem prod_flow (φ₁ : Semiflow X₁) (φ₂ : Semiflow X₂)
    (t : ℝ≥0) (p : X₁ × X₂) :
    (φ₁.prod φ₂).flow t p = (φ₁.flow t p.1, φ₂.flow t p.2) := rfl

variable {φ₁ : Semiflow X₁} {φ₂ : Semiflow X₂}

theorem CompleteOrbit.prodMk {γ₁ : ℝ → X₁} {γ₂ : ℝ → X₂}
    (h₁ : φ₁.CompleteOrbit γ₁) (h₂ : φ₂.CompleteOrbit γ₂) :
    (φ₁.prod φ₂).CompleteOrbit fun s => (γ₁ s, γ₂ s) := by
  intro s t
  show (γ₁ (s + t), γ₂ (s + t)) = ((φ₁.prod φ₂).flow t (γ₁ s, γ₂ s))
  rw [prod_flow, h₁ s t, h₂ s t]

theorem completeOrbit_prod_iff {γ : ℝ → X₁ × X₂} :
    (φ₁.prod φ₂).CompleteOrbit γ ↔
      φ₁.CompleteOrbit (fun s => (γ s).1) ∧
      φ₂.CompleteOrbit (fun s => (γ s).2) := by
  constructor
  · intro h
    exact ⟨fun s t => congrArg Prod.fst (h s t),
           fun s t => congrArg Prod.snd (h s t)⟩
  · rintro ⟨h₁, h₂⟩ s t
    have := CompleteOrbit.prodMk h₁ h₂ s t
    simpa using this

section LimitSets

variable [TopologicalSpace X₁] [TopologicalSpace X₂]

theorem omegaSet_prod_subset (γ : ℝ → X₁ × X₂) :
    omegaSet γ ⊆
      (omegaSet fun s => (γ s).1) ×ˢ (omegaSet fun s => (γ s).2) := by
  intro x hx
  simp only [omegaSet, Set.mem_iInter] at hx
  refine ⟨Set.mem_iInter.mpr fun T => ?_, Set.mem_iInter.mpr fun T => ?_⟩ <;>
  · have himg : γ '' Set.Ici T ⊆
        ((fun s => (γ s).1) '' Set.Ici T) ×ˢ
        ((fun s => (γ s).2) '' Set.Ici T) := by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs, rfl⟩, ⟨s, hs, rfl⟩⟩
    have hmem := closure_mono himg (hx T)
    rw [closure_prod_eq] at hmem
    first
      | exact hmem.1
      | exact hmem.2

theorem alphaSet_prod_subset (γ : ℝ → X₁ × X₂) :
    alphaSet γ ⊆
      (alphaSet fun s => (γ s).1) ×ˢ (alphaSet fun s => (γ s).2) := by
  intro x hx
  simp only [alphaSet, Set.mem_iInter] at hx
  refine ⟨Set.mem_iInter.mpr fun T => ?_, Set.mem_iInter.mpr fun T => ?_⟩ <;>
  · have himg : γ '' Set.Iic T ⊆
        ((fun s => (γ s).1) '' Set.Iic T) ×ˢ
        ((fun s => (γ s).2) '' Set.Iic T) := by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs, rfl⟩, ⟨s, hs, rfl⟩⟩
    have hmem := closure_mono himg (hx T)
    rw [closure_prod_eq] at hmem
    first
      | exact hmem.1
      | exact hmem.2

end LimitSets

section ClosureRange

variable {X : Type*} [TopologicalSpace X]

theorem omegaSet_subset_closure_range (γ : ℝ → X) :
    omegaSet γ ⊆ closure (Set.range γ) :=
  (Set.iInter_subset (fun T => closure (γ '' Set.Ici T)) 0).trans
    (closure_mono (Set.image_subset_range γ _))

theorem alphaSet_subset_closure_range (γ : ℝ → X) :
    alphaSet γ ⊆ closure (Set.range γ) :=
  (Set.iInter_subset (fun T => closure (γ '' Set.Iic T)) 0).trans
    (closure_mono (Set.image_subset_range γ _))

end ClosureRange

section Chains

variable [PseudoMetricSpace X₁] [PseudoMetricSpace X₂]

theorem EpsChainIn.fst {D₁ : Set X₁} {D₂ : Set X₂} {ε : ℝ} {T : ℝ≥0}
    {x y : X₁ × X₂}
    (h : EpsChainIn (φ₁.prod φ₂) (D₁ ×ˢ D₂) ε T x y) :
    EpsChainIn φ₁ D₁ ε T x.1 y.1 := by
  induction h with
  | step hx hy ht hjump =>
      refine .step hx.1 hy.1 ht (lt_of_le_of_lt ?_ hjump)
      rw [Prod.dist_eq]
      exact le_max_left _ _
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem EpsChainIn.snd {D₁ : Set X₁} {D₂ : Set X₂} {ε : ℝ} {T : ℝ≥0}
    {x y : X₁ × X₂}
    (h : EpsChainIn (φ₁.prod φ₂) (D₁ ×ˢ D₂) ε T x y) :
    EpsChainIn φ₂ D₂ ε T x.2 y.2 := by
  induction h with
  | step hx hy ht hjump =>
      refine .step hx.2 hy.2 ht (lt_of_le_of_lt ?_ hjump)
      rw [Prod.dist_eq]
      exact le_max_right _ _
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem ChainRecurrentIn.fst {D₁ : Set X₁} {D₂ : Set X₂} {x : X₁ × X₂}
    (h : ChainRecurrentIn (φ₁.prod φ₂) (D₁ ×ˢ D₂) x) :
    ChainRecurrentIn φ₁ D₁ x.1 :=
  fun ε hε T => (h ε hε T).fst

theorem ChainRecurrentIn.snd {D₁ : Set X₁} {D₂ : Set X₂} {x : X₁ × X₂}
    (h : ChainRecurrentIn (φ₁.prod φ₂) (D₁ ×ˢ D₂) x) :
    ChainRecurrentIn φ₂ D₂ x.2 :=
  fun ε hε T => (h ε hε T).snd

end Chains

section Transport

variable {Vtx₁ Vtx₂ : Type*}
variable [PseudoMetricSpace X₁] [PseudoMetricSpace X₂]
variable [T2Space X₁] [T2Space X₂]
variable [PartialOrder Vtx₁] [PartialOrder Vtx₂]
variable {D₁ : Set X₁} {D₂ : Set X₂}
variable {ρ₁ : Vtx₁ → Set X₁} {ρ₂ : Vtx₂ → Set X₂}

def MorseWitness.prod (W₁ : MorseWitness φ₁ D₁ ρ₁)
    (W₂ : MorseWitness φ₂ D₂ ρ₂) :
    MorseWitness (φ₁.prod φ₂) (D₁ ×ˢ D₂)
      (fun p : Vtx₁ × Vtx₂ => ρ₁ p.1 ×ˢ ρ₂ p.2) where
  M p := W₁.M p.1 ×ˢ W₂.M p.2
  isCompact p := (W₁.isCompact p.1).prod (W₂.isCompact p.2)
  invariant p := by
    constructor
    ·
      intro x hx t
      exact ⟨(W₁.invariant p.1).1 x.1 hx.1 t, (W₂.invariant p.2).1 x.2 hx.2 t⟩
    ·
      intro x hx
      obtain ⟨γ₁, horb₁, hγ₁, hr₁⟩ := (W₁.invariant p.1).2 hx.1
      obtain ⟨γ₂, horb₂, hγ₂, hr₂⟩ := (W₂.invariant p.2).2 hx.2
      refine ⟨fun s => (γ₁ s, γ₂ s), horb₁.prodMk horb₂, ?_, ?_⟩
      · show (γ₁ 0, γ₂ 0) = x
        rw [hγ₁, hγ₂]
      · rintro _ ⟨s, rfl⟩
        exact ⟨hr₁ ⟨s, rfl⟩, hr₂ ⟨s, rfl⟩⟩
  located p := Set.prod_mono (W₁.located p.1) (W₂.located p.2)
  disjoint p q hne := by
    obtain ⟨v, w⟩ := p
    obtain ⟨v', w'⟩ := q
    have hcoord : v ≠ v' ∨ w ≠ w' := by
      by_contra hc
      push Not at hc
      exact hne (by rw [hc.1, hc.2])
    rw [Set.disjoint_left]
    rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨ha', hb'⟩
    rcases hcoord with h | h
    · exact Set.disjoint_left.mp (W₁.disjoint v v' h) ha ha'
    · exact Set.disjoint_left.mp (W₂.disjoint w w' h) hb hb'
  crCover x hx hcr := by
    obtain ⟨v, hv⟩ := W₁.crCover x.1 hx.1 hcr.fst
    obtain ⟨w, hw⟩ := W₂.crCover x.2 hx.2 hcr.snd
    exact ⟨(v, w), hv, hw⟩
  order γ horb hrange hnot := by
    obtain ⟨horb₁, horb₂⟩ := completeOrbit_prod_iff.mp horb
    have hr₁ : Set.range (fun s => (γ s).1) ⊆ D₁ := by
      rintro _ ⟨s, rfl⟩; exact (hrange ⟨s, rfl⟩).1
    have hr₂ : Set.range (fun s => (γ s).2) ⊆ D₂ := by
      rintro _ ⟨s, rfl⟩; exact (hrange ⟨s, rfl⟩).2
    by_cases hc₁ : ∃ v, Set.range (fun s => (γ s).1) ⊆ W₁.M v
    ·
      obtain ⟨v₀, hv₀⟩ := hc₁
      have hc₂ : ∀ w, ¬ Set.range (fun s => (γ s).2) ⊆ W₂.M w := by
        intro w hw
        refine hnot (v₀, w) ?_
        rintro _ ⟨s, rfl⟩
        exact ⟨hv₀ ⟨s, rfl⟩, hw ⟨s, rfl⟩⟩
      obtain ⟨w, w', hww', hα₂, hω₂⟩ := W₂.order _ horb₂ hr₂ hc₂
      have hcl : closure (Set.range fun s => (γ s).1) ⊆ W₁.M v₀ :=
        closure_minimal hv₀ (W₁.isCompact v₀).isClosed
      refine ⟨(v₀, w), (v₀, w'), Prod.mk_lt_mk.mpr (Or.inr ⟨le_refl _, hww'⟩),
        ?_, ?_⟩
      · exact (alphaSet_prod_subset γ).trans
          (Set.prod_mono ((alphaSet_subset_closure_range _).trans hcl) hα₂)
      · exact (omegaSet_prod_subset γ).trans
          (Set.prod_mono ((omegaSet_subset_closure_range _).trans hcl) hω₂)
    · push Not at hc₁
      obtain ⟨v, v', hvv', hα₁, hω₁⟩ := W₁.order _ horb₁ hr₁ hc₁
      by_cases hc₂ : ∃ w, Set.range (fun s => (γ s).2) ⊆ W₂.M w
      ·
        obtain ⟨w₀, hw₀⟩ := hc₂
        have hcl : closure (Set.range fun s => (γ s).2) ⊆ W₂.M w₀ :=
          closure_minimal hw₀ (W₂.isCompact w₀).isClosed
        refine ⟨(v, w₀), (v', w₀),
          Prod.mk_lt_mk.mpr (Or.inl ⟨hvv', le_refl _⟩), ?_, ?_⟩
        · exact (alphaSet_prod_subset γ).trans
            (Set.prod_mono hα₁ ((alphaSet_subset_closure_range _).trans hcl))
        · exact (omegaSet_prod_subset γ).trans
            (Set.prod_mono hω₁ ((omegaSet_subset_closure_range _).trans hcl))
      ·
        push Not at hc₂
        obtain ⟨w, w', hww', hα₂, hω₂⟩ := W₂.order _ horb₂ hr₂ hc₂
        exact ⟨(v, w), (v', w'),
          Prod.mk_lt_mk.mpr (Or.inl ⟨hvv', hww'.le⟩),
          (alphaSet_prod_subset γ).trans (Set.prod_mono hα₁ hα₂),
          (omegaSet_prod_subset γ).trans (Set.prod_mono hω₁ hω₂)⟩

theorem qMorseProduct_sound
    (h₁ : MorseSat φ₁ D₁ ρ₁) (h₂ : MorseSat φ₂ D₂ ρ₂) :
    MorseSat (φ₁.prod φ₂) (D₁ ×ˢ D₂)
      (fun p : Vtx₁ × Vtx₂ => ρ₁ p.1 ×ˢ ρ₂ p.2) := by
  obtain ⟨W₁⟩ := h₁
  obtain ⟨W₂⟩ := h₂
  exact ⟨W₁.prod W₂⟩

end Transport

end Semiflow
end Qtsl

#print axioms Qtsl.Semiflow.completeOrbit_prod_iff
#print axioms Qtsl.Semiflow.omegaSet_prod_subset
#print axioms Qtsl.Semiflow.alphaSet_prod_subset
#print axioms Qtsl.Semiflow.omegaSet_subset_closure_range
#print axioms Qtsl.Semiflow.alphaSet_subset_closure_range
#print axioms Qtsl.Semiflow.EpsChainIn.fst
#print axioms Qtsl.Semiflow.EpsChainIn.snd
#print axioms Qtsl.Semiflow.ChainRecurrentIn.fst
#print axioms Qtsl.Semiflow.ChainRecurrentIn.snd
#print axioms Qtsl.Semiflow.MorseWitness.prod
#print axioms Qtsl.Semiflow.qMorseProduct_sound

end PPLC
