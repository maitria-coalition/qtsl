import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Data.Fintype.BigOperators

/-! # Certified lower bounds on fixed points, and POMDP value lower bounds

This module proves the soundness of a simple certificate scheme for lower
bounds on the fixed point of a monotone contraction, and instantiates the
underlying idea for point-based value iteration on finite POMDPs.

Principal declarations:

* `le_fixedPoint_of_le_map`, `certificate_sound`: for a contraction `B` that
  is also monotone, any `VΓ` with `VΓ ≤ B VΓ` (and `{x | VΓ ≤ x}` closed)
  satisfies `VΓ ≤ Vstar` for the (unique, `eq_of_isFixedPt`) fixed point
  `Vstar` — so a one-step self-support check certifies a global lower bound.
* `FinPomdp S O A`: a finite POMDP given by transition weights `T`, observation
  weights `Z`, rewards `r`, and a nonnegative discount, all entrywise
  nonnegative.
* `gVec`, `backupVec`, `valueAt`: the observation-conditioned α-vector
  transport, the point-based Bellman backup of a family of successor
  α-vectors, and evaluation of an α-vector against a belief.
* `bellmanPWLC`: the piecewise-linear-convex Bellman operator applied to a
  finite set `Γ` of α-vectors, as a function of the belief.
* `witness_le_bellmanPWLC`: soundness of an α-vector witness set. If every
  `α ∈ Γ` is dominated by the backup of successors chosen inside `Γ`, then on
  every nonnegative belief the value of `Γ` is at most `bellmanPWLC M Γ` —
  the finite-dimensional self-support inequality feeding the abstract
  certificate above.
-/

namespace Qtsl

namespace QBeliefLowerBound

open Function Filter
open scoped NNReal

section Abstract

variable {X : Type*} [MetricSpace X] {f : X → X} {K : ℝ≥0}

omit [MetricSpace X] in

theorem le_iterate_of_le_map [Preorder X] (hmono : Monotone f) {v : X}
    (hv : v ≤ f v) : ∀ n, v ≤ f^[n] v := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hv.trans (hmono ih)

theorem eq_of_isFixedPt (hf : ContractingWith K f) {y z : X}
    (hy : IsFixedPt f y) (hz : IsFixedPt f z) : y = z := by
  have hstep : dist (f y) (f z) ≤ K * dist y z := hf.2.dist_le_mul y z
  rw [hy.eq, hz.eq] at hstep
  have h1K : (K : ℝ) < 1 := by exact_mod_cast hf.1
  have h0 : dist y z ≤ 0 := by nlinarith [dist_nonneg (x := y) (y := z)]
  exact eq_of_dist_eq_zero (le_antisymm h0 dist_nonneg)

theorem le_fixedPoint_of_le_map [Nonempty X] [CompleteSpace X] [Preorder X]
    (hf : ContractingWith K f) (hmono : Monotone f) {v : X}
    (hclosed : IsClosed {x | v ≤ x}) (hv : v ≤ f v) :
    v ≤ ContractingWith.fixedPoint f hf :=
  hclosed.mem_of_tendsto (hf.tendsto_iterate_fixedPoint v)
    (Eventually.of_forall (le_iterate_of_le_map hmono hv))

theorem le_isFixedPt_of_le_map [Nonempty X] [CompleteSpace X] [Preorder X]
    (hf : ContractingWith K f) (hmono : Monotone f) {v w : X}
    (hclosed : IsClosed {x | v ≤ x}) (hv : v ≤ f v) (hw : IsFixedPt f w) :
    v ≤ w := by
  have := eq_of_isFixedPt hf hw (hf.fixedPoint_isFixedPt (f := f))
  exact this ▸ le_fixedPoint_of_le_map hf hmono hclosed hv

theorem certificate_sound [Nonempty X] [CompleteSpace X] [Preorder X]
    (B : X → X) (hB : ContractingWith K B) (hmono : Monotone B)
    {VΓ Vstar : X} (hclosed : IsClosed {x | VΓ ≤ x})
    (hsub : VΓ ≤ B VΓ) (hfix : IsFixedPt B Vstar) :
    VΓ ≤ Vstar :=
  le_isFixedPt_of_le_map hB hmono hclosed hsub hfix

end Abstract

section Finite

variable {S O A : Type*} [Fintype S] [Fintype O] [Fintype A] [Nonempty A]

open Finset

structure FinPomdp (S O A : Type*) where

  T : A → S → S → ℝ

  Z : A → S → O → ℝ

  r : A → S → ℝ

  disc : ℝ
  T_nonneg : ∀ a s s', 0 ≤ T a s s'
  Z_nonneg : ∀ a s' o, 0 ≤ Z a s' o
  disc_nonneg : 0 ≤ disc

variable (M : FinPomdp S O A)

def gVec (a : A) (o : O) (α : S → ℝ) : S → ℝ :=
  fun s => ∑ s', M.T a s s' * M.Z a s' o * α s'

def backupVec (a : A) (succ : O → S → ℝ) : S → ℝ :=
  fun s => M.r a s + M.disc * ∑ o, gVec M a o (succ o) s

def valueAt (b α : S → ℝ) : ℝ := ∑ s, b s * α s

noncomputable def bellmanPWLC (Γ : Finset (S → ℝ)) (hne : Γ.Nonempty)
    (b : S → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun a : A =>
    (∑ s, b s * M.r a s) + M.disc * ∑ o, Γ.sup' hne fun α' => valueAt b (gVec M a o α')

omit [Fintype A] [Nonempty A] in

theorem valueAt_backupVec (a : A) (succ : O → S → ℝ) (b : S → ℝ) :
    valueAt b (backupVec M a succ)
      = (∑ s, b s * M.r a s) + M.disc * ∑ o, valueAt b (gVec M a o (succ o)) := by
  unfold valueAt backupVec
  have h : ∀ s : S, b s * (M.r a s + M.disc * ∑ o, gVec M a o (succ o) s)
      = b s * M.r a s + M.disc * ∑ o, b s * gVec M a o (succ o) s := by
    intro s
    rw [mul_add]
    congr 1
    rw [mul_left_comm, Finset.mul_sum]
  calc ∑ s, b s * (M.r a s + M.disc * ∑ o, gVec M a o (succ o) s)
      = ∑ s, (b s * M.r a s + M.disc * ∑ o, b s * gVec M a o (succ o) s) := by
        exact Finset.sum_congr rfl fun s _ => h s
    _ = (∑ s, b s * M.r a s) + ∑ s, M.disc * ∑ o, b s * gVec M a o (succ o) s :=
        Finset.sum_add_distrib
    _ = (∑ s, b s * M.r a s) + M.disc * ∑ s, ∑ o, b s * gVec M a o (succ o) s := by
        rw [← Finset.mul_sum]
    _ = (∑ s, b s * M.r a s) + M.disc * ∑ o, ∑ s, b s * gVec M a o (succ o) s := by
        rw [Finset.sum_comm]

theorem witness_le_bellmanPWLC (Γ : Finset (S → ℝ)) (hne : Γ.Nonempty)
    (act : (S → ℝ) → A) (succ : (S → ℝ) → O → (S → ℝ))
    (hsucc : ∀ α ∈ Γ, ∀ o, succ α o ∈ Γ)
    (hdom : ∀ α ∈ Γ, ∀ s, α s ≤ backupVec M (act α) (succ α) s)
    (b : S → ℝ) (hb : ∀ s, 0 ≤ b s) :
    (Γ.sup' hne fun α => valueAt b α) ≤ bellmanPWLC M Γ hne b := by
  apply Finset.sup'_le
  intro α hα
  have h1 : valueAt b α ≤ valueAt b (backupVec M (act α) (succ α)) :=
    Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hdom α hα s) (hb s)
  have h2 : (∑ o, valueAt b (gVec M (act α) o (succ α o)))
      ≤ ∑ o, Γ.sup' hne fun α' => valueAt b (gVec M (act α) o α') :=
    Finset.sum_le_sum fun o _ =>
      Finset.le_sup' (fun α' => valueAt b (gVec M (act α) o α')) (hsucc α hα o)
  have h3 : valueAt b (backupVec M (act α) (succ α))
      ≤ (∑ s, b s * M.r (act α) s)
        + M.disc * ∑ o, Γ.sup' hne fun α' => valueAt b (gVec M (act α) o α') := by
    rw [valueAt_backupVec]
    have hmul := mul_le_mul_of_nonneg_left h2 M.disc_nonneg
    linarith
  exact (h1.trans h3).trans
    (Finset.le_sup'
      (fun a : A =>
        (∑ s, b s * M.r a s)
          + M.disc * ∑ o, Γ.sup' hne fun α' => valueAt b (gVec M a o α'))
      (Finset.mem_univ (act α)))

end Finite

end QBeliefLowerBound

end Qtsl

