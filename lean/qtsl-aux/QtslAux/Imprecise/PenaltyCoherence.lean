import QtslAux.Imprecise.MarginalCompatGeneral

/-! # Penalty functionals: pushforward coherence

The pushforward of a penalty functional along a map of index types
(`pushPenaltyG`) and the lax two-marginal penalty (`laxPenaltyG`), with
the coherence laws — functoriality, additivity, monotonicity, and the
interaction of pushforward with the lax construction — needed to compose
imprecise-probability penalties across marginalization. -/

namespace Qtsl.Imprecise

open scoped NNRat

section Push

variable {J K M : Type*}

def pushPenaltyG (m : J → M) (f : M → ENNRat) : J → ENNRat :=
  fun ν => f (m ν)

@[simp] theorem pushPenaltyG_id (f : J → ENNRat) :
    pushPenaltyG (id : J → J) f = f := rfl

theorem pushPenaltyG_comp (m₁ : J → K) (m₂ : K → M) (f : M → ENNRat) :
    pushPenaltyG (m₂ ∘ m₁) f = pushPenaltyG m₁ (pushPenaltyG m₂ f) := rfl

theorem pushPenaltyG_add (m : J → M) (f g : M → ENNRat) :
    pushPenaltyG m (f + g) = pushPenaltyG m f + pushPenaltyG m g := rfl

@[simp] theorem pushPenaltyG_zero (m : J → M) :
    pushPenaltyG m (0 : M → ENNRat) = 0 := rfl

theorem pushPenaltyG_mono (m : J → M) {f g : M → ENNRat} (h : f ≤ g) :
    pushPenaltyG m f ≤ pushPenaltyG m g :=
  fun ν => h (m ν)

theorem pushPenaltyG_unique [Unique M] (m : J → M) (g : M → ENNRat) :
    pushPenaltyG m g = fun _ => g default := by
  funext ν
  simp [pushPenaltyG, Unique.eq_default (m ν)]

end Push

section Lax

variable {J J' A A' B B' : Type*}

def laxPenaltyG (ma : J → A) (mb : J → B)
    (f : A → ENNRat) (g : B → ENNRat) : J → ENNRat :=
  fun ν => f (ma ν) + g (mb ν)

theorem laxPenaltyG_eq_add (ma : J → A) (mb : J → B)
    (f : A → ENNRat) (g : B → ENNRat) :
    laxPenaltyG ma mb f g = pushPenaltyG ma f + pushPenaltyG mb g := rfl

theorem pushPenaltyG_laxPenaltyG (k : J' → J) (ma : J → A) (mb : J → B)
    (f : A → ENNRat) (g : B → ENNRat) :
    pushPenaltyG k (laxPenaltyG ma mb f g)
      = laxPenaltyG (ma ∘ k) (mb ∘ k) f g := rfl

theorem laxPenaltyG_natural (k : J' → J) (u : A' → A) (v : B' → B)
    {ma : J → A} {mb : J → B} {ma' : J' → A'} {mb' : J' → B'}
    (hA : ∀ ν, ma (k ν) = u (ma' ν)) (hB : ∀ ν, mb (k ν) = v (mb' ν))
    (f : A → ENNRat) (g : B → ENNRat) :
    pushPenaltyG k (laxPenaltyG ma mb f g)
      = laxPenaltyG ma' mb' (pushPenaltyG u f) (pushPenaltyG v g) := by
  funext ν
  simp only [pushPenaltyG, laxPenaltyG, hA, hB]

theorem laxPenaltyG_assoc {AB BC C : Type*}
    {pab : J → AB} {pc : J → C} {pa : J → A} {pbc : J → BC}
    {qa : AB → A} {qb : AB → B} {rb : BC → B} {rc : BC → C}
    (hA : ∀ ν, qa (pab ν) = pa ν)
    (hB : ∀ ν, qb (pab ν) = rb (pbc ν))
    (hC : ∀ ν, pc ν = rc (pbc ν))
    (f : A → ENNRat) (g : B → ENNRat) (h : C → ENNRat) :
    laxPenaltyG pab pc (laxPenaltyG qa qb f g) h
      = laxPenaltyG pa pbc f (laxPenaltyG rb rc g h) := by
  funext ν
  simp only [laxPenaltyG, hA, hB, hC, add_assoc]

@[simp] theorem laxPenaltyG_zero_left (ma : J → A) (mb : J → B)
    (g : B → ENNRat) :
    laxPenaltyG ma mb (0 : A → ENNRat) g = pushPenaltyG mb g := by
  funext ν
  simp [laxPenaltyG, pushPenaltyG]

@[simp] theorem laxPenaltyG_zero_right (ma : J → A) (mb : J → B)
    (f : A → ENNRat) :
    laxPenaltyG ma mb f (0 : B → ENNRat) = pushPenaltyG ma f := by
  funext ν
  simp [laxPenaltyG, pushPenaltyG]

theorem laxPenaltyG_unit_left {U : Type*} (mu : J → U) (f : J → ENNRat) :
    laxPenaltyG mu (id : J → J) (0 : U → ENNRat) f = f := by
  simp

theorem laxPenaltyG_unit_right {U : Type*} (mu : J → U) (f : J → ENNRat) :
    laxPenaltyG (id : J → J) mu f (0 : U → ENNRat) = f := by
  simp

theorem laxPenaltyG_unique_right {U : Type*} [Unique U]
    (ma : J → A) (mu : J → U) (f : A → ENNRat) (g : U → ENNRat) :
    laxPenaltyG ma mu f g = fun ν => f (ma ν) + g default := by
  funext ν
  simp [laxPenaltyG, Unique.eq_default (mu ν)]

theorem laxPenaltyG_comm (ma : J → A) (mb : J → B)
    (f : A → ENNRat) (g : B → ENNRat) :
    laxPenaltyG ma mb f g = laxPenaltyG mb ma g f := by
  funext ν
  exact add_comm _ _

theorem laxPenaltyG_mono (ma : J → A) (mb : J → B)
    {f f' : A → ENNRat} {g g' : B → ENNRat}
    (hf : f ≤ f') (hg : g ≤ g') :
    laxPenaltyG ma mb f g ≤ laxPenaltyG ma mb f' g' :=
  fun ν => add_le_add (hf (ma ν)) (hg (mb ν))

theorem le_laxPenaltyG_left (ma : J → A) (mb : J → B)
    (f : A → ENNRat) (g : B → ENNRat) :
    pushPenaltyG ma f ≤ laxPenaltyG ma mb f g :=
  fun _ => le_self_add

theorem le_laxPenaltyG_right (ma : J → A) (mb : J → B)
    (f : A → ENNRat) (g : B → ENNRat) :
    pushPenaltyG mb g ≤ laxPenaltyG ma mb f g :=
  fun _ => le_add_self

theorem laxPenaltyG_indicator (ma : J → A) (mb : J → B)
    (PA : A → Prop) (PB : B → Prop)
    [DecidablePred PA] [DecidablePred PB] :
    laxPenaltyG ma mb (fun a => if PA a then 0 else ⊤)
        (fun b => if PB b then 0 else ⊤)
      = fun ν => if PA (ma ν) ∧ PB (mb ν) then 0 else ⊤ := by
  funext ν
  by_cases hA : PA (ma ν) <;> by_cases hB : PB (mb ν) <;>
    simp [laxPenaltyG, hA, hB]

end Lax

section Bridges

variable {J : Type*}

universe u

theorem laxPenaltyG_eq_compositePenaltyG_bool {A B : Type u}
    (ma : J → A) (mb : J → B) (f : A → ENNRat) (g : B → ENNRat) :
    laxPenaltyG ma mb f g
      = fun ν => compositePenaltyG (Mi := fun b => cond b A B)
          (fun b => match b with | true => ma | false => mb)
          (fun b => match b with | true => f | false => g) ν := by
  funext ν
  simp [laxPenaltyG, compositePenaltyG]

theorem compositePenaltyG_sum_type {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Mi : ι ⊕ κ → Type*}
    (m : ∀ i, J → Mi i) (f : ∀ i, Mi i → ENNRat) (ν : J) :
    compositePenaltyG m f ν
      = compositePenaltyG (fun i => m (.inl i)) (fun i => f (.inl i)) ν
        + compositePenaltyG (fun k => m (.inr k)) (fun k => f (.inr k)) ν := by
  unfold compositePenaltyG
  exact Fintype.sum_sum_type _

theorem compositePenaltyG_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) {Mi : ι → Type*}
    (m : ∀ i, J → Mi i) (f : ∀ i, Mi i → ENNRat) (ν : J) :
    compositePenaltyG (fun k => m (e k)) (fun k => f (e k)) ν
      = compositePenaltyG m f ν := by
  unfold compositePenaltyG
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem compositePenaltyG_sumAssoc {ι κ μ : Type*}
    [Fintype ι] [Fintype κ] [Fintype μ]
    {Mi : ι ⊕ (κ ⊕ μ) → Type*}
    (m : ∀ i, J → Mi i) (f : ∀ i, Mi i → ENNRat) (ν : J) :
    compositePenaltyG (fun j => m (Equiv.sumAssoc ι κ μ j))
        (fun j => f (Equiv.sumAssoc ι κ μ j)) ν
      = compositePenaltyG m f ν :=
  compositePenaltyG_reindex (Equiv.sumAssoc ι κ μ) m f ν

end Bridges

section Mutants

def doublingLax {J A B : Type*} (ma : J → A) (mb : J → B)
    (f : A → ENNRat) (g : B → ENNRat) : J → ENNRat :=
  fun ν => f (ma ν) + (g (mb ν) + g (mb ν))

def offsetLax {J A B : Type*} (ma : J → A) (mb : J → B)
    (f : A → ENNRat) (g : B → ENNRat) : J → ENNRat :=
  fun ν => f (ma ν) + g (mb ν) + 1

def pointLax {A B : Type*} (ma : Bool → A) (mb : Bool → B)
    (f : A → ENNRat) (g : B → ENNRat) : Bool → ENNRat :=
  fun ν => bif ν then f (ma ν) + g (mb ν) else 0

private theorem one_add_one_ne_one : (1 : ENNRat) + 1 ≠ 1 := by
  have h : (1 : ℚ≥0) + 1 ≠ 1 := by norm_num
  exact_mod_cast h

private theorem one_add_one_ne_zero : (1 : ENNRat) + 1 ≠ 0 := by
  have h : (1 : ℚ≥0) + 1 ≠ 0 := by norm_num
  exact_mod_cast h

private theorem two_ne_four :
    (1 : ENNRat) + 1 ≠ (1 + 1) + (1 + 1) := by
  have h : (1 : ℚ≥0) + 1 ≠ (1 + 1) + (1 + 1) := by norm_num
  exact_mod_cast h

private theorem one_ne_zero' : (1 : ENNRat) ≠ 0 := by
  have h : (1 : ℚ≥0) ≠ 0 := one_ne_zero
  exact_mod_cast h

theorem doublingLax_not_comm :
    doublingLax (id : PUnit → PUnit) id (fun _ => 0) (fun _ => 1)
      ≠ doublingLax (id : PUnit → PUnit) id (fun _ => 1) (fun _ => 0) := by
  intro hcontra
  have h := congrFun hcontra PUnit.unit
  simp only [doublingLax, zero_add, add_zero] at h
  exact one_add_one_ne_one h

theorem doublingLax_not_assoc :
    doublingLax (id : PUnit → PUnit) id
        (doublingLax (id : PUnit → PUnit) id (fun _ => 0) (fun _ => 0))
        (fun _ => 1)
      ≠ doublingLax (id : PUnit → PUnit) id (fun _ => 0)
          (doublingLax (id : PUnit → PUnit) id (fun _ => 0) (fun _ => 1)) := by
  intro hcontra
  have h := congrFun hcontra PUnit.unit
  simp only [doublingLax, zero_add, add_zero] at h
  exact two_ne_four h

theorem laxPenaltyG_assoc_instancePUnit :
    laxPenaltyG (id : PUnit → PUnit) id
        (laxPenaltyG (id : PUnit → PUnit) id
          (fun _ => (0 : ENNRat)) (fun _ => 0))
        (fun _ => 1)
      = laxPenaltyG (id : PUnit → PUnit) id (fun _ => 0)
          (laxPenaltyG (id : PUnit → PUnit) id (fun _ => 0) (fun _ => 1)) :=
  laxPenaltyG_assoc (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) _ _ _

theorem offsetLax_not_unital :
    offsetLax (id : PUnit → PUnit) id (fun _ => (0 : ENNRat)) (fun _ => 0)
      ≠ (fun _ => (0 : ENNRat)) := by
  intro hcontra
  have h := congrFun hcontra PUnit.unit
  simp only [offsetLax, zero_add] at h
  exact one_ne_zero' h

theorem pointLax_not_natural :
    pushPenaltyG Bool.not
        (pointLax (id : Bool → Bool) id (fun _ => 1) (fun _ => 1))
      ≠ pointLax (Bool.not : Bool → Bool) Bool.not
          (fun _ => 1) (fun _ => 1) :=
  fun hcontra => one_add_one_ne_zero (congrFun hcontra false)

end Mutants

end Qtsl.Imprecise
