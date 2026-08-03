import QtslAux.Imprecise.PenaltyEnvelope
import QtslAux.Imprecise.Compose
import Mathlib.Data.Fintype.BigOperators

/-! # Mixed contraction: sum-product inside, max-plus outside

The judgment-level quantity of a kernel with a noise block and a gated
imprecise block is a **mixed contraction**: an ordinary sum-product
contraction over the noise indices nested inside a max-plus contraction over
the imprecise indices, with the penalty gate as the tropical density.  This
module mechanizes that identity and the exchange laws that govern the two
semirings' interaction:

* `penUpperE_mixedFam` — **the mixed-contraction identity**: the penalty
  kernel whose members pair the noise reference with a point of the
  imprecise block at the gate's cost prices a gamble as
  `max_m (Σ_u p(u)·g(u,m) − w(m))`.  The affinity theorem of
  `Imprecise.PenaltyEnvelope` (`exp_sub_exp_le_sup_sub` + Dirac attainment)
  is why the Dirac family loses nothing: the sup over all laws of the
  affine objective sits at the points.
* `sup_exp_le_exp_sup` — **the exchange inequality**: contracting max-plus
  before sum-product under-prices contracting after; the two semirings do
  *not* satisfy a Fubini law, and `Mutants.exchange_strict` pins the gap on
  a fair coin (the value-of-information/dilation gap: choosing before
  seeing the draw is worth strictly less than choosing after).
* `exchange_of_separated` — exchange *is* an equality when the objective
  separates additively across the two blocks: the gap is an interaction
  term, not an artifact of the ordering.
-/

namespace Qtsl.Imprecise

open Finset

section SupHelpers

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem sup'_const_add (a : ℚ) (f : ι → ℚ) :
    univ.sup' univ_nonempty (fun i => a + f i)
      = a + univ.sup' univ_nonempty f := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun i _ => ?_
    have := Finset.le_sup' f (mem_univ i)
    linarith
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (univ_nonempty) f
    rw [hi]
    exact Finset.le_sup' (fun j => a + f j) (mem_univ i)

end SupHelpers

section Mixed

variable {U M : Type*} [Fintype U] [Fintype M] [Nonempty M] [DecidableEq M]

/-- The noise-with-gated-point family: member `m` pairs the noise reference
`p` with the point `m` of the imprecise block, at the gate's cost `w m`. -/
def mixedFam (p : FinPMF U) : M → FinPMF (U × M) :=
  fun m => p.compProd fun _ => FinPMF.dirac m

/-- **The mixed-contraction identity**: sum-product over the noise index
nested inside max-plus over the imprecise index, penalty gate as tropical
density.  The demonic seat's sup and kernel-level imprecision land in the
same algebra. -/
theorem penUpperE_mixedFam (p : FinPMF U) (w : M → ℚ) (g : U × M → ℚ) :
    penUpperE (mixedFam p) w g
      = univ.sup' univ_nonempty fun m => p.exp (fun u => g (u, m)) - w m := by
  unfold penUpperE mixedFam
  refine Finset.sup'_congr _ rfl fun m _ => ?_
  rw [FinPMF.exp_compProd]
  congr 1
  exact p.exp_congr fun u => FinPMF.exp_dirac m fun y => g (u, y)

omit [DecidableEq M] in
/-- **The exchange inequality**: max-plus-then-sum-product is dominated by
sum-product-then-max-plus.  The two semirings satisfy no Fubini law; the
strict gap (`Mutants.exchange_strict`) is the value of seeing the draw
before choosing. -/
theorem sup_exp_le_exp_sup (p : FinPMF U) (F : U → M → ℚ) :
    univ.sup' univ_nonempty (fun m => p.exp fun u => F u m)
      ≤ p.exp fun u => univ.sup' univ_nonempty fun m => F u m := by
  refine Finset.sup'_le _ _ fun m _ => ?_
  exact p.exp_mono fun u => Finset.le_sup' (fun m' => F u m') (mem_univ m)

omit [DecidableEq M] in
/-- Exchange is an **equality** when the objective separates additively
across the two blocks: the exchange gap is an interaction term. -/
theorem exchange_of_separated (p : FinPMF U) (A : U → ℚ) (B : M → ℚ) :
    univ.sup' univ_nonempty (fun m => p.exp fun u => A u + B m)
      = p.exp fun u => univ.sup' univ_nonempty fun m => A u + B m := by
  have hL : ∀ m : M, p.exp (fun u => A u + B m) = p.exp A + B m := fun m => by
    rw [show (fun u => A u + B m) = fun u => A u + (fun _ : U => B m) u from rfl,
      p.exp_add A fun _ => B m, p.exp_const]
  have hR : ∀ u : U,
      univ.sup' univ_nonempty (fun m => A u + B m)
        = A u + univ.sup' univ_nonempty B := fun u => sup'_const_add (A u) B
  calc univ.sup' univ_nonempty (fun m => p.exp fun u => A u + B m)
      = univ.sup' univ_nonempty (fun m => p.exp A + B m) :=
        Finset.sup'_congr _ rfl fun m _ => hL m
    _ = p.exp A + univ.sup' univ_nonempty B := sup'_const_add _ B
    _ = p.exp fun u => A u + univ.sup' univ_nonempty B := by
        rw [p.exp_add A fun _ => univ.sup' univ_nonempty B, p.exp_const]
    _ = p.exp fun u => univ.sup' univ_nonempty fun m => A u + B m :=
        p.exp_congr fun u => (hR u).symm

end Mixed

namespace Mutants

open FinPMF

private def coin : FinPMF Bool where
  prob := fun _ => 1 / 2
  nonneg := fun _ => by norm_num
  total := by rw [Fintype.sum_bool]; norm_num

/-- The matching objective: reward `1` for guessing the draw. -/
private def matchF : Bool → Bool → ℚ := fun u m => if u = m then 1 else 0

private theorem coin_exp_matchF (m : Bool) :
    coin.exp (fun u => matchF u m) = 1 / 2 := by
  unfold FinPMF.exp
  rw [Fintype.sum_bool]
  cases m <;> norm_num [coin, matchF]

private theorem sup_matchF (u : Bool) :
    univ.sup' univ_nonempty (fun m => matchF u m) = 1 := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun m _ => ?_
    unfold matchF
    by_cases h : u = m <;> norm_num [h]
  · have := Finset.le_sup' (fun m => matchF u m) (mem_univ u)
    simpa [matchF] using this

/-- **M4 (exchange locus)**: the exchange inequality is strict on the
guessing game — committing to a guess before the coin is tossed is worth
`1/2`; guessing after seeing it is worth `1`.  Max-plus and sum-product do
not commute, and the gap is exactly the value of information. -/
theorem exchange_strict :
    univ.sup' univ_nonempty (fun m => coin.exp fun u => matchF u m)
      < coin.exp fun u => univ.sup' univ_nonempty fun m => matchF u m := by
  have hL : univ.sup' univ_nonempty (fun m => coin.exp fun u => matchF u m)
      = 1 / 2 := by
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun m _ => ?_
      rw [coin_exp_matchF]
    · have := Finset.le_sup' (fun m => coin.exp fun u => matchF u m)
        (mem_univ true)
      rw [coin_exp_matchF] at this
      exact this
  have hR : (coin.exp fun u => univ.sup' univ_nonempty fun m => matchF u m)
      = 1 := by
    rw [coin.exp_congr fun u => sup_matchF u, coin.exp_const]
  rw [hL, hR]
  norm_num

end Mutants

end Qtsl.Imprecise
