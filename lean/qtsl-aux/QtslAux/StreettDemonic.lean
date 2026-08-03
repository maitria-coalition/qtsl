import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith

/-! # Streett response under demonic input via ranking functions

This module proves the deterministic (nonprobabilistic) counterpart of the
Streett soundness theorems: for a transition function `f : S → W → S` driven
by an arbitrary ("demonic") input sequence, a rational-valued ranking function
forces responses to recur whenever requests do.

Principal declarations:

* `ranking_antitone_on_tail`: once no response occurs from time `N` onward,
  the ranking value is non-increasing along the run.
* `frequently_response_of_ranking`: the main theorem. If the rank `R` never
  increases while the response `G` fails, strictly decreases by at least
  `ε₀ > 0` at every request that is not a response, and stays nonnegative
  while responses fail, then a run with infinitely many requests has
  infinitely many responses — otherwise the rank would descend below `0` in
  finitely many `ε₀`-steps (Archimedean property of `ℚ`).
* `frequently_target_of_ranking`: the degenerate case with every step counted
  as a request, forcing the target `γ` to recur.
* `frequently_all_responses`: the indexed bundle — one ranking function per
  Streett pair yields all responses simultaneously.
-/

namespace Qtsl.StreettDemonic

variable {S W : Type*}

theorem ranking_antitone_on_tail
    {f : S → W → S} {G : S → W → Prop} {R : S → ℚ}
    {run : ℕ → S} {inp : ℕ → W}
    (hstep : ∀ n, run (n + 1) = f (run n) (inp n))
    (hmono : ∀ x w, ¬G x w → R (f x w) ≤ R x)
    {N : ℕ} (hno : ∀ n, N ≤ n → ¬G (run n) (inp n)) :
    ∀ a, N ≤ a → ∀ b, a ≤ b → R (run b) ≤ R (run a) := by
  intro a hNa
  refine Nat.le_induction ?_ ?_
  · exact le_rfl
  · intro b hab ih
    have hb : R (run (b + 1)) ≤ R (run b) := by
      rw [hstep b]
      exact hmono _ _ (hno b (hNa.trans hab))
    exact hb.trans ih

theorem frequently_response_of_ranking
    {f : S → W → S} {Rq G : S → W → Prop} {R : S → ℚ} {ε₀ : ℚ}
    {run : ℕ → S} {inp : ℕ → W}
    (hε : 0 < ε₀)
    (hstep : ∀ n, run (n + 1) = f (run n) (inp n))
    (hmono : ∀ x w, ¬G x w → R (f x w) ≤ R x)
    (hdec : ∀ x w, Rq x w → ¬G x w → R (f x w) ≤ R x - ε₀)
    (hnonneg : ∀ x w, ¬G x w → 0 ≤ R (f x w))
    (hreq : ∀ N, ∃ n, N ≤ n ∧ Rq (run n) (inp n)) :
    ∀ N, ∃ n, N ≤ n ∧ G (run n) (inp n) := by
  intro N
  by_contra hcon
  have hno : ∀ n, N ≤ n → ¬G (run n) (inp n) := fun n hn hG => hcon ⟨n, hn, hG⟩

  have hpos : ∀ m, N + 1 ≤ m → 0 ≤ R (run m) := by
    intro m hm
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [hstep j]
    exact hnonneg _ _ (hno j (by omega))

  have hdrop : ∀ k : ℕ, ∃ m, N + 1 ≤ m ∧ R (run m) ≤ R (run (N + 1)) - k • ε₀ := by
    intro k
    induction k with
    | zero => exact ⟨N + 1, le_rfl, by simp⟩
    | succ k ih =>
      obtain ⟨m, hm, hRm⟩ := ih
      obtain ⟨n, hn, hRq⟩ := hreq m
      have hGn : ¬G (run n) (inp n) := hno n (by omega)
      have h1 : R (run n) ≤ R (run m) :=
        ranking_antitone_on_tail hstep hmono hno m (by omega) n hn
      have h2 : R (run (n + 1)) ≤ R (run n) - ε₀ := by
        rw [hstep n]
        exact hdec _ _ hRq hGn
      refine ⟨n + 1, by omega, ?_⟩
      have hsucc : (k + 1) • ε₀ = k • ε₀ + ε₀ := by rw [add_nsmul, one_nsmul]
      rw [hsucc]
      linarith

  obtain ⟨c, hc⟩ := Archimedean.arch (R (run (N + 1))) hε
  obtain ⟨m, hm, hRm⟩ := hdrop (c + 1)
  have h0 : 0 ≤ R (run m) := hpos m hm
  have hsucc : (c + 1) • ε₀ = c • ε₀ + ε₀ := by rw [add_nsmul, one_nsmul]
  rw [hsucc] at hRm
  linarith

theorem frequently_target_of_ranking
    {f : S → W → S} {γ : S → W → Prop} {R : S → ℚ} {ε₀ : ℚ}
    {run : ℕ → S} {inp : ℕ → W}
    (hε : 0 < ε₀)
    (hstep : ∀ n, run (n + 1) = f (run n) (inp n))
    (hR1 : ∀ x w, ¬γ x w → R (f x w) ≤ R x - ε₀)
    (hR2 : ∀ x w, ¬γ x w → 0 ≤ R (f x w)) :
    ∀ N, ∃ n, N ≤ n ∧ γ (run n) (inp n) :=
  frequently_response_of_ranking (Rq := fun _ _ => True) hε hstep
    (fun x w h => (hR1 x w h).trans (by linarith))
    (fun x w _ h => hR1 x w h) hR2
    (fun N => ⟨N, le_rfl, trivial⟩)

theorem frequently_all_responses {I : Type*}
    {f : S → W → S} {Rq G : I → S → W → Prop} {R : I → S → ℚ} {ε : I → ℚ}
    {run : ℕ → S} {inp : ℕ → W}
    (hε : ∀ i, 0 < ε i)
    (hstep : ∀ n, run (n + 1) = f (run n) (inp n))
    (hmono : ∀ i x w, ¬G i x w → R i (f x w) ≤ R i x)
    (hdec : ∀ i x w, Rq i x w → ¬G i x w → R i (f x w) ≤ R i x - ε i)
    (hnonneg : ∀ i x w, ¬G i x w → 0 ≤ R i (f x w))
    (hreq : ∀ i N, ∃ n, N ≤ n ∧ Rq i (run n) (inp n)) :
    ∀ i N, ∃ n, N ≤ n ∧ G i (run n) (inp n) :=
  fun i => frequently_response_of_ranking (hε i) hstep (hmono i) (hdec i)
    (hnonneg i) (hreq i)

end Qtsl.StreettDemonic
