import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Dynamical rule soundness over semiflows

The semiflow stratum and the Morse-family soundness lemmas:

* `Semiflow`, invariance, complete orbits, and the maximal invariant
  set `MaxInv` with its calculus;
* `qBlockInv_sound` — an isolating-block invariance rule: forward
  confinement plus initial containment yields invariant-scope
  satisfaction;
* `qBasin_sound` and `qBasin_batch` — basin/safety rules;
* ω/α-limit sets, ε-chains, chain recurrence, `MorseWitness`/`MorseSat`,
  and `qMorseDischarge_sound` — soundness of the Morse-decomposition
  discharge, with the analytic clauses as interface hypotheses
  discharged in `Qtsl.Discharge` and its companions.
-/

namespace PPLC
namespace Qtsl

open scoped NNReal

variable {X : Type*}

structure Semiflow (X : Type*) where
  flow : ℝ≥0 → X → X
  flow_zero : ∀ x, flow 0 x = x
  flow_add : ∀ (s t : ℝ≥0) (x : X), flow (s + t) x = flow t (flow s x)

namespace Semiflow

def Invariant (φ : Semiflow X) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ t : ℝ≥0, φ.flow t x ∈ S

def CompleteOrbit (φ : Semiflow X) (γ : ℝ → X) : Prop :=
  ∀ (s : ℝ) (t : ℝ≥0), γ (s + t) = φ.flow t (γ s)

def MaxInv (φ : Semiflow X) (C : Set X) : Set X :=
  {x | ∃ γ : ℝ → X, φ.CompleteOrbit γ ∧ γ 0 = x ∧ Set.range γ ⊆ C}

theorem maxInv_subset (φ : Semiflow X) (C : Set X) : φ.MaxInv C ⊆ C := by
  rintro x ⟨γ, -, rfl, hr⟩
  exact hr (Set.mem_range_self 0)

theorem CompleteOrbit.shift {φ : Semiflow X} {γ : ℝ → X}
    (h : φ.CompleteOrbit γ) (s : ℝ) : φ.CompleteOrbit fun u => γ (u + s) := by
  intro u t
  show γ (u + ↑t + s) = φ.flow t (γ (u + s))
  have hre : u + ↑t + s = (u + s) + ↑t := by ring
  rw [hre, h (u + s) t]

theorem mem_maxInv_of_orbit {φ : Semiflow X} {γ : ℝ → X} {C : Set X}
    (horb : φ.CompleteOrbit γ) (hr : Set.range γ ⊆ C) (s : ℝ) :
    γ s ∈ φ.MaxInv C := by
  refine ⟨fun u => γ (u + s), horb.shift s, by simp, ?_⟩
  rintro y ⟨u, rfl⟩
  exact hr ⟨u + s, rfl⟩

theorem maxInv_invariant (φ : Semiflow X) (C : Set X) :
    φ.Invariant (φ.MaxInv C) := by
  rintro x ⟨γ, horb, rfl, hr⟩ t
  have h0 : φ.flow t (γ 0) = γ ((0 : ℝ) + t) := (horb 0 t).symm
  rw [h0]
  exact mem_maxInv_of_orbit horb hr _

theorem maxInv_subset_maxInv_maxInv (φ : Semiflow X) (C : Set X) :
    φ.MaxInv C ⊆ φ.MaxInv (φ.MaxInv C) := by
  rintro x ⟨γ, horb, rfl, hr⟩
  refine ⟨γ, horb, rfl, ?_⟩
  rintro y ⟨s, rfl⟩
  exact mem_maxInv_of_orbit horb hr s

def IsInvariantIn (φ : Semiflow X) (S : Set X) : Prop :=
  φ.Invariant S ∧ S ⊆ φ.MaxInv S

theorem maxInv_isInvariant (φ : Semiflow X) (C : Set X) :
    φ.IsInvariantIn (φ.MaxInv C) :=
  ⟨φ.maxInv_invariant C, φ.maxInv_subset_maxInv_maxInv C⟩

def InvScopeSat (φ : Semiflow X) (S X0 : Set X) : Prop :=
  φ.Invariant S ∧ X0 ⊆ S

def SafetySat (φ : Semiflow X) (X0 B : Set X) : Prop :=
  ∀ x ∈ X0, ∀ t : ℝ≥0, φ.flow t x ∉ B

/-- Soundness of the block-invariance rule: an invariant scope containing
the initial set satisfies the invariant-scope judgement. -/
theorem qBlockInv_sound {φ : Semiflow X} {N X0 : Set X}
    (hInv : φ.Invariant N) (hInit : X0 ⊆ N) :
    φ.InvScopeSat N X0 :=
  ⟨hInv, hInit⟩

theorem qBasin_sound {φ : Semiflow X} {S X0 B : Set X}
    (hscope : φ.InvScopeSat S X0) (hAvoid : S ∩ B = ∅) :
    φ.SafetySat X0 B := by
  intro x hx t hB
  have hS : φ.flow t x ∈ S := hscope.1 x (hscope.2 hx) t
  have hmem : φ.flow t x ∈ S ∩ B := ⟨hS, hB⟩
  rw [hAvoid] at hmem
  exact hmem

theorem qBasin_batch {φ : Semiflow X} {S X0 : Set X} {J : Type*}
    {B : J → Set X} (hscope : φ.InvScopeSat S X0)
    (hAvoid : ∀ j, S ∩ B j = ∅) :
    φ.SafetySat X0 (⋃ j, B j) := by
  intro x hx t hB
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hB
  exact qBasin_sound hscope (hAvoid j) x hx t hj

theorem transit_maxInv_empty {φ : Semiflow X} {C : Set X} {V : X → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hBdd : BddBelow (V '' C))
    (hDec : ∀ x ∈ C, ∀ t : ℝ≥0,
      (∀ s : ℝ≥0, s ≤ t → φ.flow s x ∈ C) → V (φ.flow t x) ≤ V x - ε * t) :
    φ.MaxInv C = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨γ, horb, rfl, hr⟩ := hx
  obtain ⟨m, hm⟩ := hBdd

  have hCseg : ∀ s : ℝ≥0, φ.flow s (γ 0) ∈ C := by
    intro s
    rw [← horb 0 s]
    exact hr (Set.mem_range_self _)

  obtain ⟨n, hAr⟩ := Archimedean.arch (V (γ 0) - m) hε
  rw [nsmul_eq_mul] at hAr
  have hdec := hDec (γ 0) (hr (Set.mem_range_self 0)) ((n + 1 : ℕ) : ℝ≥0)
    (fun s _ => hCseg s)
  have hlow : m ≤ V (φ.flow ((n + 1 : ℕ) : ℝ≥0) (γ 0)) :=
    hm ⟨_, hCseg _, rfl⟩
  have hcoe : (((n + 1 : ℕ) : ℝ≥0) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcoe] at hdec
  have hexp : ε * ((n : ℝ) + 1) = ε * n + ε := by ring
  linarith

section Judgment

def omegaSet [TopologicalSpace X] (γ : ℝ → X) : Set X :=
  ⋂ T : ℝ, closure (γ '' Set.Ici T)

def alphaSet [TopologicalSpace X] (γ : ℝ → X) : Set X :=
  ⋂ T : ℝ, closure (γ '' Set.Iic T)

variable [PseudoMetricSpace X]

inductive EpsChainIn (φ : Semiflow X) (D : Set X) (ε : ℝ) (T : ℝ≥0) :
    X → X → Prop
  | step {x y : X} {t : ℝ≥0} (hx : x ∈ D) (hy : y ∈ D) (ht : T ≤ t)
      (hjump : dist (φ.flow t x) y < ε) : EpsChainIn φ D ε T x y
  | trans {x y z : X} (h1 : EpsChainIn φ D ε T x y)
      (h2 : EpsChainIn φ D ε T y z) : EpsChainIn φ D ε T x z

def ChainRecurrentIn (φ : Semiflow X) (D : Set X) (x : X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ T : ℝ≥0, EpsChainIn φ D ε T x x

variable {Vtx : Type*}

structure MorseWitness (φ : Semiflow X) (D : Set X) [PartialOrder Vtx]
    (ρ : Vtx → Set X) where

  M : Vtx → Set X

  isCompact : ∀ v, IsCompact (M v)

  invariant : ∀ v, φ.IsInvariantIn (M v)

  located : ∀ v, M v ⊆ ρ v

  disjoint : ∀ v w, v ≠ w → Disjoint (M v) (M w)

  crCover : ∀ x ∈ D, ChainRecurrentIn φ D x → ∃ v, x ∈ M v

  order : ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
    (∀ v, ¬ Set.range γ ⊆ M v) →
    ∃ v w, w < v ∧ alphaSet γ ⊆ M v ∧ omegaSet γ ⊆ M w

def MorseSat (φ : Semiflow X) (D : Set X) [PartialOrder Vtx]
    (ρ : Vtx → Set X) : Prop :=
  Nonempty (MorseWitness φ D ρ)

end Judgment

section Discharge

variable {Vtx ι : Type*}

def fiberUnion (cells : ι → Set X) (hmap : ι → Option Vtx) (v : Vtx) :
    Set X :=
  ⋃ i ∈ {i | hmap i = some v}, cells i

theorem fiberUnion_subset {cells : ι → Set X} {hmap : ι → Option Vtx}
    {ρ : Vtx → Set X} (hContain : ∀ i v, hmap i = some v → cells i ⊆ ρ v)
    (v : Vtx) : fiberUnion cells hmap v ⊆ ρ v :=
  Set.iUnion₂_subset fun i hi => hContain i v hi

variable [PseudoMetricSpace X] [PartialOrder Vtx]

/-- Soundness of the Morse-decomposition discharge rule, with the analytic
clauses as interface hypotheses. -/
theorem qMorseDischarge_sound (φ : Semiflow X) (D : Set X)
    (ρ : Vtx → Set X) (cells : ι → Set X) (hmap : ι → Option Vtx)
    (hContain : ∀ i v, hmap i = some v → cells i ⊆ ρ v)
    (hCompact : ∀ v, IsCompact (φ.MaxInv (fiberUnion cells hmap v)))
    (hDisj : ∀ v w, v ≠ w →
      Disjoint (φ.MaxInv (fiberUnion cells hmap v))
        (φ.MaxInv (fiberUnion cells hmap w)))
    (hCR : ∀ x ∈ D, ChainRecurrentIn φ D x →
      ∃ v, x ∈ φ.MaxInv (fiberUnion cells hmap v))
    (hOrder : ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
      (∀ v, ¬ Set.range γ ⊆ φ.MaxInv (fiberUnion cells hmap v)) →
      ∃ v w, w < v ∧ alphaSet γ ⊆ φ.MaxInv (fiberUnion cells hmap v) ∧
        omegaSet γ ⊆ φ.MaxInv (fiberUnion cells hmap w)) :
    MorseSat φ D ρ :=
  ⟨{ M := fun v => φ.MaxInv (fiberUnion cells hmap v)
     isCompact := hCompact
     invariant := fun _ => φ.maxInv_isInvariant _
     located := fun v => (φ.maxInv_subset _).trans (fiberUnion_subset hContain v)
     disjoint := hDisj
     crCover := hCR
     order := hOrder }⟩

end Discharge

end Semiflow
end Qtsl

#print axioms Qtsl.Semiflow.maxInv_subset
#print axioms Qtsl.Semiflow.maxInv_invariant
#print axioms Qtsl.Semiflow.maxInv_isInvariant
#print axioms Qtsl.Semiflow.qBlockInv_sound
#print axioms Qtsl.Semiflow.qBasin_sound
#print axioms Qtsl.Semiflow.qBasin_batch
#print axioms Qtsl.Semiflow.transit_maxInv_empty
#print axioms Qtsl.Semiflow.qMorseDischarge_sound

end PPLC
