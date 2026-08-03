import Qtsl.Behavioral

/-!
# The switch composite

Switched systems at the behavioural floor: locations are whole systems,
each with its own carrier and its own solution-set behaviour, and switch
edges form a quiver family `Edge : ι → ι → Type*` — cycles welcome by
construction. No acyclicity hypothesis appears in any statement, and
none could bind: runs are proof-relevant paths in the quiver.
-/

namespace PPLC
namespace Qtsl

open scoped NNReal
open Set

universe u v w

structure SwitchSys (ι : Type u) (X : ι → Type v) where

  B : ∀ i, Behavior (X i)

  Edge : ι → ι → Type w

  guard : ∀ {i j}, Edge i j → Set (X i)

  reset : ∀ {i j}, Edge i j → X i → X j

  forced : ∀ {i j}, Edge i j → Bool

variable {ι : Type u} {X : ι → Type v}

structure FinExec (S : SwitchSys ι X) where

  n : ℕ

  loc : Fin (n + 1) → ι

  seg : ∀ k : Fin (n + 1), ℝ≥0 → X (loc k)

  seg_mem : ∀ k, seg k ∈ (S.B (loc k)).fwd

  dwell : Fin n → ℝ≥0

  edge : ∀ k : Fin n, S.Edge (loc k.castSucc) (loc k.succ)

  guard_mem : ∀ k : Fin n,
    seg k.castSucc (dwell k) ∈ S.guard (edge k)

  link : ∀ k : Fin n,
    seg k.succ 0 = S.reset (edge k) (seg k.castSucc (dwell k))

def BoundaryContain (S : SwitchSys ι X) (R : ∀ i, Set (X i)) : Prop :=
  ∀ {i j} (e : S.Edge i j), ∀ x ∈ S.guard e, x ∈ R i → S.reset e x ∈ R j

def BoundaryRows (S : SwitchSys ι X) (V : ∀ i, X i → ℝ) : Prop :=
  ∀ {i j} (e : S.Edge i j), ∀ x ∈ S.guard e, V j (S.reset e x) ≤ V i x

theorem BoundaryRows.contain {S : SwitchSys ι X} {V : ∀ i, X i → ℝ}
    (h : BoundaryRows S V) (c : ℝ) :
    BoundaryContain S (fun i => {x | V i x ≤ c}) := by
  intro i j e x hg hx
  exact le_trans (h e x hg) hx

namespace FinExec

variable {S : SwitchSys ι X}

theorem start_mem {R : ∀ i, Set (X i)}
    (hloc : ∀ i, (S.B i).Invariant (R i))
    (hbnd : BoundaryContain S R)
    (E : FinExec S) (h0 : E.seg 0 0 ∈ R (E.loc 0)) :
    ∀ k, E.seg k 0 ∈ R (E.loc k) := by
  intro k
  induction k using Fin.induction with
  | zero => exact h0
  | succ i ih =>
      have hdwell : E.seg i.castSucc (E.dwell i) ∈ R (E.loc i.castSucc) :=
        hloc _ _ (E.seg_mem i.castSucc) ih (E.dwell i)
      have := hbnd (E.edge i) _ (E.guard_mem i) hdwell
      rw [E.link i]
      exact this

theorem mem {R : ∀ i, Set (X i)}
    (hloc : ∀ i, (S.B i).Invariant (R i))
    (hbnd : BoundaryContain S R)
    (E : FinExec S) (h0 : E.seg 0 0 ∈ R (E.loc 0))
    (k : Fin (E.n + 1)) (t : ℝ≥0) : E.seg k t ∈ R (E.loc k) :=
  hloc _ _ (E.seg_mem k) (E.start_mem hloc hbnd h0 k) t

theorem value_le {V : ∀ i, X i → ℝ}
    (hloc : ∀ i, ∀ γ ∈ (S.B i).fwd, ∀ t : ℝ≥0, V i (γ t) ≤ V i (γ 0))
    (hrow : BoundaryRows S V)
    (E : FinExec S) :
    ∀ k, ∀ t : ℝ≥0,
      V (E.loc k) (E.seg k t) ≤ V (E.loc 0) (E.seg 0 0) := by
  have hstart : ∀ k, V (E.loc k) (E.seg k 0) ≤ V (E.loc 0) (E.seg 0 0) := by
    intro k
    induction k using Fin.induction with
    | zero => exact le_rfl
    | succ i ih =>
        have hdwell :
            V (E.loc i.castSucc) (E.seg i.castSucc (E.dwell i))
              ≤ V (E.loc i.castSucc) (E.seg i.castSucc 0) :=
          hloc _ _ (E.seg_mem i.castSucc) (E.dwell i)
        have hjump := hrow (E.edge i) _ (E.guard_mem i)
        rw [E.link i]
        exact le_trans (le_trans hjump hdwell) ih
  intro k t
  exact le_trans (hloc _ _ (E.seg_mem k) t) (hstart k)

def InWindow (E : FinExec S) (k : Fin (E.n + 1)) (t : ℝ≥0) : Prop :=
  ∀ h : (k : ℕ) < E.n, t ≤ E.dwell ⟨(k : ℕ), h⟩

end FinExec

def SwitchSafetySat (S : SwitchSys ι X) (X0 Bad : ∀ i, Set (X i)) : Prop :=
  ∀ E : FinExec S, E.seg 0 0 ∈ X0 (E.loc 0) →
    ∀ k t, E.InWindow k t → E.seg k t ∉ Bad (E.loc k)

theorem qSwitchCompose_sound_regions {S : SwitchSys ι X}
    {X0 Bad : ∀ i, Set (X i)} (R : ∀ i, Set (X i))
    (hloc : ∀ i, (S.B i).Invariant (R i))
    (hbnd : BoundaryContain S R)
    (hX0 : ∀ i, X0 i ⊆ R i)
    (hBad : ∀ i, Disjoint (R i) (Bad i)) :
    SwitchSafetySat S X0 Bad := by
  intro E h0 k t _ hbad
  have hmem : E.seg k t ∈ R (E.loc k) :=
    E.mem hloc hbnd (hX0 _ h0) k t
  exact (hBad (E.loc k)).ne_of_mem hmem hbad rfl

theorem qSwitchCompose_sound {S : SwitchSys ι X}
    {X0 Bad : ∀ i, Set (X i)} (V : ∀ i, X i → ℝ) (c : ℝ)
    (hloc : ∀ i, (S.B i).Invariant {x | V i x ≤ c})
    (hrow : BoundaryRows S V)
    (hX0 : ∀ i, X0 i ⊆ {x | V i x ≤ c})
    (hBad : ∀ i x, x ∈ Bad i → c < V i x) :
    SwitchSafetySat S X0 Bad := by
  refine qSwitchCompose_sound_regions (fun i => {x | V i x ≤ c})
    hloc (hrow.contain c) hX0 (fun i => ?_)
  rw [Set.disjoint_left]
  intro x hx hbad
  exact absurd (hBad _ _ hbad) (not_lt.mpr hx)

def ofShared {X' : Type v} (B : ι → Behavior X') (Edge : ι → ι → Type w)
    (guard : ∀ i j, Edge i j → Set X')
    (reset : ∀ i j, Edge i j → X' → X')
    (forced : ∀ i j, Edge i j → Bool) :
    SwitchSys ι (fun _ => X') where
  B := B
  Edge := Edge
  guard := fun {i j} e => guard i j e
  reset := fun {i j} e => reset i j e
  forced := fun {i j} e => forced i j e

section OfSharedReceipts

variable {X' : Type v} {B : ι → Behavior X'} {Edge : ι → ι → Type w}
  {guard : ∀ i j, Edge i j → Set X'}
  {reset : ∀ i j, Edge i j → X' → X'}
  {forced : ∀ i j, Edge i j → Bool}

@[simp] theorem ofShared_B (i : ι) :
    (ofShared B Edge guard reset forced).B i = B i := rfl

@[simp] theorem ofShared_guard {i j : ι} (e : Edge i j) :
    (ofShared B Edge guard reset forced).guard e = guard i j e := rfl

@[simp] theorem ofShared_reset {i j : ι} (e : Edge i j) :
    (ofShared B Edge guard reset forced).reset e = reset i j e := rfl

@[simp] theorem ofShared_forced {i j : ι} (e : Edge i j) :
    (ofShared B Edge guard reset forced).forced e = forced i j e := rfl

end OfSharedReceipts

end Qtsl
end PPLC

#print axioms PPLC.Qtsl.FinExec.start_mem
#print axioms PPLC.Qtsl.FinExec.mem
#print axioms PPLC.Qtsl.FinExec.value_le
#print axioms PPLC.Qtsl.qSwitchCompose_sound_regions
#print axioms PPLC.Qtsl.qSwitchCompose_sound
#print axioms PPLC.Qtsl.BoundaryRows.contain
