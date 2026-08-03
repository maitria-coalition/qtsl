import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Data.Real.Pointwise
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.LinearPMap
import QtslAux.Imprecise.Credal

/-! # Natural extension and the finite envelope theorem

Coherent lower previsions over a finite state space, their envelope
theorem, and the natural extension of a finite assessment with its
universal property and linear-programming duality (Walley, *Statistical
Reasoning with Imprecise Probabilities*, 1991, §2–3).

* `IsCoherent` — (W1) dominating the infimum, (W2) positive homogeneity,
  (W3) superadditivity — with the standard consequences as lemmas
  (`const_eval`, `add_const`, `mono`, `le_sup'`, `sum_smul_le`).
* *Envelopes are coherent*: `envelope_coherent` — the lower envelope of
  an arbitrary nonempty family of pmfs satisfies (W1)–(W3);
  one-line-per-axiom shape, no convexity or closure of the family used.
* *Coherent previsions are envelopes* (`[Fintype X]`, exact):
  `IsCoherent.exists_dominating_exp_eq` (attained form: a dominating
  precise expectation touching any prescribed gamble) and
  `IsCoherent.eq_sInf_credal` (the envelope display over the credal set
  `M(P)` = `Dominates P`).
* Natural extension: assessments `(h, c)` with finitely many gambles
  over `[Fintype X]`; `Compatible`/`compatibleSet` (= `M(K,c)`),
  `AvoidsSureLoss` (= `M(K,c) ≠ ∅`), `natExt` (the envelope over the
  compatible set), and the universal property:
  - NE1 `natExt_coherent`,
  - NE2 `assessment_le_natExt`,
  - NE3 `natExt_le_coherent` (pointwise-smallest coherent functional
    dominating the assessment),
  - the sup-of-deficit-combinations display (exact for finite `X`, by
    linear-programming duality): `natExt_eq_dualVal`,
  - the largest-credal-set dual `dominates_natExt_iff`
    (`M(E_{K,c}) = M(K,c)`),
  - the sure-loss alternative `avoidsSureLoss_iff_noSureLoss`
    (compatible model exists ↔ no positive deficit combination is
    uniformly negative).

## Route note

The mathlib pin carries no matrix Farkas lemma; the separating-hyperplane
engine used instead is `exists_extension_of_le_sublinear` (M. Riesz
extension / Hahn–Banach for sublinear functionals) — the textbook engine
for the lower envelope theorem (Walley 1991, §3.3.3): the conjugate upper
prevision is the sublinear majorant, and the extension of `t • g ↦ t • P g`
from the span of the target gamble is the touching expectation. Strong LP
duality and the sure-loss alternative are then *derived* from the envelope
theorem applied to the dual functional `dualVal` (coherent whenever no
sure loss is exposed), so one Hahn–Banach invocation powers the whole
package.

Scalar field: `ℝ`. The `ℚ`-valued `FinPMF` face of `Imprecise.Credal`
remains the computable/`decide` stratum; `FinPMF.toReal` bridges.

Mutants (teeth for the statements) live in the `Mutants` namespace at the
bottom: a two-sided exact evaluation of a concrete natural extension
(primal witness pmf and dual deficit certificate, both tight at `1/2`), a
forged envelope refuted through `dominates_natExt_iff`, a non-coherent
would-be extension (the upper envelope) refused by W3, and the vacuous
prevision strictly below the natural extension on the assessed gamble
(NE2's content).
-/

namespace Qtsl.Imprecise

open Finset Pointwise

/-! ## Real-valued pmfs -/

/-- A real-valued probability mass function on a finite type. The real face of
`FinPMF` (which stays `ℚ`-valued for the computable/`decide` stratum). -/
structure RealPMF (X : Type*) [Fintype X] where
  /-- Pointwise probability mass. -/
  prob : X → ℝ
  /-- All masses are nonnegative. -/
  nonneg : ∀ x, 0 ≤ prob x
  /-- Total mass one. -/
  total : ∑ x, prob x = 1

namespace RealPMF

variable {X : Type*} [Fintype X]

/-- Expectation (precise prevision) of `f` under `p`. -/
def exp (p : RealPMF X) (f : X → ℝ) : ℝ := ∑ x, p.prob x * f x

theorem exp_add (p : RealPMF X) (f g : X → ℝ) :
    p.exp (fun x => f x + g x) = p.exp f + p.exp g := by
  simp [exp, mul_add, Finset.sum_add_distrib]

theorem exp_smul (p : RealPMF X) (c : ℝ) (f : X → ℝ) :
    p.exp (fun x => c * f x) = c * p.exp f := by
  rw [exp, exp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => mul_left_comm _ _ _

theorem exp_const (p : RealPMF X) (c : ℝ) : p.exp (fun _ => c) = c := by
  rw [exp, ← Finset.sum_mul, p.total, one_mul]

theorem exp_const_add (p : RealPMF X) (a : ℝ) (f : X → ℝ) :
    p.exp (fun x => a + f x) = a + p.exp f := by
  calc p.exp (fun x => a + f x) = ∑ x, (p.prob x * a + p.prob x * f x) := by
        simp [exp, mul_add]
    _ = (∑ x, p.prob x * a) + ∑ x, p.prob x * f x := Finset.sum_add_distrib
    _ = a + p.exp f := by rw [← Finset.sum_mul, p.total, one_mul]; rfl

theorem exp_mono (p : RealPMF X) {f g : X → ℝ} (h : ∀ x, f x ≤ g x) :
    p.exp f ≤ p.exp g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (p.nonneg x)

section NonemptyX

variable [Nonempty X]

theorem inf'_le_exp (p : RealPMF X) (f : X → ℝ) :
    univ.inf' univ_nonempty f ≤ p.exp f :=
  calc univ.inf' univ_nonempty f
      = p.exp (fun _ => univ.inf' univ_nonempty f) := (p.exp_const _).symm
    _ ≤ p.exp f := p.exp_mono fun x => Finset.inf'_le _ (mem_univ x)

theorem exp_le_sup' (p : RealPMF X) (f : X → ℝ) :
    p.exp f ≤ univ.sup' univ_nonempty f :=
  calc p.exp f
      ≤ p.exp (fun _ => univ.sup' univ_nonempty f) :=
        p.exp_mono fun x => Finset.le_sup' f (mem_univ x)
    _ = univ.sup' univ_nonempty f := p.exp_const _

end NonemptyX

end RealPMF

/-- Cast the `ℚ`-valued pmf face into the real-valued face. -/
def FinPMF.toReal {X : Type*} [Fintype X] (p : FinPMF X) : RealPMF X where
  prob x := (p.prob x : ℝ)
  nonneg x := by exact_mod_cast p.nonneg x
  total := by exact_mod_cast p.total

theorem FinPMF.exp_toReal {X : Type*} [Fintype X] (p : FinPMF X) (f : X → ℚ) :
    p.toReal.exp (fun x => (f x : ℝ)) = (p.exp f : ℝ) := by
  simp only [RealPMF.exp, FinPMF.exp, FinPMF.toReal]
  push_cast
  rfl

/-! ## Coherent lower previsions -/

section Coherence

variable {X : Type*} [Fintype X] [Nonempty X]

/-- A coherent lower prevision on the gambles `X → ℝ` — (W1) dominates the
infimum, (W2) positive homogeneity, (W3) superadditivity. Stated on the
full-mass stratum, where the classical theory is recovered exactly. -/
structure IsCoherent (P : (X → ℝ) → ℝ) : Prop where
  /-- (W1) dominating the infimum. -/
  inf_le : ∀ f, univ.inf' univ_nonempty f ≤ P f
  /-- (W2) positive homogeneity. -/
  homog : ∀ l : ℝ, 0 ≤ l → ∀ f, P (fun x => l * f x) = l * P f
  /-- (W3) superadditivity. -/
  superadd : ∀ f g, P f + P g ≤ P (fun x => f x + g x)

namespace IsCoherent

variable {P : (X → ℝ) → ℝ} (hP : IsCoherent P)

include hP

theorem const_zero : P (fun _ => (0 : ℝ)) = 0 := by
  have h := hP.homog 0 le_rfl (fun _ => (0 : ℝ))
  have h2 : (fun _ : X => (0 : ℝ) * 0) = (fun _ : X => (0 : ℝ)) := by
    funext x; ring
  rw [h2, zero_mul] at h
  exact h

/-- Standard consequence: `P f ≤ sup f` (with W1, `inf h ≤ P h ≤ sup h`). -/
theorem le_sup' (f : X → ℝ) : P f ≤ univ.sup' univ_nonempty f := by
  have h1 := hP.superadd f (fun x => -f x)
  have h0 : (fun x => f x + -f x) = (fun _ : X => (0 : ℝ)) := by
    funext x; ring
  rw [h0, hP.const_zero] at h1
  have h2 := hP.inf_le (fun x => -f x)
  have h3 : univ.inf' univ_nonempty (fun x => -f x) =
      -univ.sup' univ_nonempty f := by
    apply le_antisymm
    · obtain ⟨x, _, hval⟩ := Finset.exists_mem_eq_sup' univ_nonempty f
      calc univ.inf' univ_nonempty (fun y => -f y) ≤ -f x :=
            Finset.inf'_le _ (mem_univ x)
        _ = -univ.sup' univ_nonempty f := by rw [hval]
    · exact Finset.le_inf' _ _ fun x hx => neg_le_neg (Finset.le_sup' f hx)
  linarith

theorem const_eval (c : ℝ) : P (fun _ => c) = c := by
  apply le_antisymm
  · have h := hP.le_sup' (fun _ => c)
    simpa [Finset.sup'_const] using h
  · have h := hP.inf_le (fun _ => c)
    simpa [Finset.inf'_const] using h

/-- Standard consequence: constant additivity. -/
theorem add_const (f : X → ℝ) (c : ℝ) : P (fun x => f x + c) = P f + c := by
  apply le_antisymm
  · have h := hP.superadd (fun x => f x + c) (fun _ => -c)
    rw [hP.const_eval (-c)] at h
    rw [show (fun x => (f x + c) + -c) = f from by funext x; ring] at h
    linarith
  · have h := hP.superadd f (fun _ => c)
    rw [hP.const_eval c] at h
    exact h

/-- Standard consequence: monotonicity. -/
theorem mono {f g : X → ℝ} (h : ∀ x, f x ≤ g x) : P f ≤ P g := by
  have hs := hP.superadd f (fun x => g x - f x)
  have h0 : (fun x => f x + (g x - f x)) = g := by funext x; ring
  rw [h0] at hs
  have hpos : (0 : ℝ) ≤ P (fun x => g x - f x) := by
    have h1 := hP.inf_le (fun x => g x - f x)
    have h2 : (0 : ℝ) ≤ univ.inf' univ_nonempty (fun x => g x - f x) :=
      Finset.le_inf' _ _ fun x _ => by linarith [h x]
    linarith
  linarith

/-- Finite nonnegative combinations: iterated (W2)+(W3). The workhorse behind
NE3 (finite positive combinations of assessment deficits). -/
theorem sum_smul_le {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (F : ι → X → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) :
    ∑ i ∈ s, lam i * P (F i) ≤ P (fun x => ∑ i ∈ s, lam i * F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [Finset.sum_empty, hP.const_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hstep := hP.superadd (fun x => lam a * F a x)
      (fun x => ∑ i ∈ s, lam i * F i x)
    have hfun : (fun x => lam a * F a x + ∑ i ∈ s, lam i * F i x) =
        (fun x => ∑ i ∈ insert a s, lam i * F i x) := by
      funext x
      rw [Finset.sum_insert ha]
    rw [hfun] at hstep
    have hsmul := hP.homog (lam a) (hlam a) (F a)
    linarith

end IsCoherent

/-! ## Envelopes and the credal set -/

/-- `p` lies in the credal set `M(P)` of the functional `P`: its expectation
dominates `P` on every gamble. -/
def Dominates (P : (X → ℝ) → ℝ) (p : RealPMF X) : Prop := ∀ f, P f ≤ p.exp f

theorem bddBelow_exp_image (S : Set (RealPMF X)) (f : X → ℝ) :
    BddBelow ((fun p => p.exp f) '' S) :=
  ⟨univ.inf' univ_nonempty f, by rintro r ⟨p, _, rfl⟩; exact p.inf'_le_exp f⟩

/-- *Envelopes are coherent*: the lower envelope of any nonempty family of
pmfs satisfies (W1)–(W3); no convexity or closure of the family is used. -/
theorem envelope_coherent (S : Set (RealPMF X)) (hS : S.Nonempty) :
    IsCoherent (fun g => sInf ((fun p => p.exp g) '' S)) where
  inf_le f :=
    le_csInf (hS.image _) (by rintro r ⟨p, _, rfl⟩; exact p.inf'_le_exp f)
  homog l hl f := by
    show sInf ((fun p : RealPMF X => p.exp (fun x => l * f x)) '' S)
        = l * sInf ((fun p : RealPMF X => p.exp f) '' S)
    rcases hl.eq_or_lt with heq | hpos
    · have h0 : (fun x : X => l * f x) = (fun _ : X => (0 : ℝ)) := by
        funext x
        rw [← heq, zero_mul]
      have himg : (fun p : RealPMF X => p.exp (fun _ => (0 : ℝ))) '' S
          = {0} := by
        have hc : ∀ p ∈ S, p.exp (fun _ => (0 : ℝ)) = 0 :=
          fun p _ => p.exp_const 0
        rw [Set.image_congr hc]
        exact hS.image_const 0
      rw [h0, himg, csInf_singleton, ← heq, zero_mul]
    · have key : (fun p : RealPMF X => p.exp (fun x => l * f x)) '' S =
          l • ((fun p : RealPMF X => p.exp f) '' S) := by
        ext r
        simp only [Set.mem_image, Set.mem_smul_set]
        constructor
        · rintro ⟨p, hp, rfl⟩
          exact ⟨p.exp f, ⟨p, hp, rfl⟩, by
            rw [smul_eq_mul]; exact (p.exp_smul l f).symm⟩
        · rintro ⟨r', ⟨p, hp, rfl⟩, rfl⟩
          exact ⟨p, hp, by rw [smul_eq_mul]; exact p.exp_smul l f⟩
      rw [key, Real.sInf_smul_of_nonneg hl, smul_eq_mul]
  superadd f g := by
    show sInf ((fun p : RealPMF X => p.exp f) '' S)
        + sInf ((fun p : RealPMF X => p.exp g) '' S)
        ≤ sInf ((fun p : RealPMF X => p.exp (fun x => f x + g x)) '' S)
    apply le_csInf (hS.image _)
    rintro r ⟨p, hp, rfl⟩
    show sInf ((fun p : RealPMF X => p.exp f) '' S)
        + sInf ((fun p : RealPMF X => p.exp g) '' S) ≤ p.exp (fun x => f x + g x)
    have h1 : sInf ((fun p : RealPMF X => p.exp f) '' S) ≤ p.exp f :=
      csInf_le (bddBelow_exp_image S f) ⟨p, hp, rfl⟩
    have h2 : sInf ((fun p : RealPMF X => p.exp g) '' S) ≤ p.exp g :=
      csInf_le (bddBelow_exp_image S g) ⟨p, hp, rfl⟩
    rw [p.exp_add]
    linarith

/-- The envelope theorem, attained form: over a finite state space, a
coherent lower prevision is dominated by a precise expectation that
touches it at any prescribed gamble. The separating-hyperplane step is
mathlib's sublinear Hahn–Banach (`exists_extension_of_le_sublinear`), applied
to the conjugate upper prevision `N f = -P (-f)` and the partial map
`t • g ↦ t • P g` on `span {g}`. -- [classical] -/
theorem IsCoherent.exists_dominating_exp_eq {P : (X → ℝ) → ℝ}
    (hP : IsCoherent P) (g : X → ℝ) :
    ∃ p : RealPMF X, Dominates P p ∧ p.exp g = P g := by
  classical
  -- the conjugate upper prevision, as the sublinear majorant
  set N : (X → ℝ) → ℝ := fun f => -P (fun x => -f x) with hNdef
  have hNval : ∀ f : X → ℝ, N f = -P (fun x => -f x) := fun _ => rfl
  have hP0 : P (fun _ : X => (0 : ℝ)) = 0 := hP.const_zero
  have hNhom : ∀ c : ℝ, 0 < c → ∀ f : X → ℝ, N (c • f) = c * N f := by
    intro c hc f
    have h1 : (fun x => -(c • f) x) = (fun x => c * -f x) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hNval (c • f), h1, hP.homog c hc.le (fun x => -f x), hNval f]
    ring
  have hNadd : ∀ f h : X → ℝ, N (f + h) ≤ N f + N h := by
    intro f h
    have h1 : (fun x => -(f + h) x) = (fun x => -f x + -h x) := by
      funext x
      simp only [Pi.add_apply]
      ring
    have h2 := hP.superadd (fun x => -f x) (fun x => -h x)
    rw [hNval (f + h), h1, hNval f, hNval h]
    linarith
  -- P is below its conjugate upper prevision
  have hPleN : ∀ f : X → ℝ, P f ≤ N f := by
    intro f
    have h1 := hP.superadd f (fun x => -f x)
    have h0 : (fun x => f x + -f x) = (fun _ : X => (0 : ℝ)) := by
      funext x; ring
    rw [h0, hP0] at h1
    rw [hNval f]
    linarith
  -- the partial linear map on span {g}
  have hH : ∀ c : ℝ, c • g = 0 → c • P g = 0 := by
    intro c hc
    rcases smul_eq_zero.mp hc with rfl | hg0
    · simp
    · have hg' : P g = 0 := by
        rw [hg0, show (0 : X → ℝ) = (fun _ : X => (0 : ℝ)) from rfl, hP0]
      rw [hg', smul_zero]
  let fpm : (X → ℝ) →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' g (P g) hH
  have hf : ∀ x : fpm.domain, fpm x ≤ N x := by
    rintro ⟨xv, hxv⟩
    have hxv' : xv ∈ (Submodule.span ℝ {g} : Submodule ℝ (X → ℝ)) := hxv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxv'
    have happ : fpm ⟨c • g, hxv⟩ = c • P g := by
      show LinearPMap.mkSpanSingleton' g (P g) hH ⟨c • g, hxv⟩ = c • P g
      have happ' := LinearPMap.mkSpanSingleton'_apply g (P g) hH c hxv
      simpa using happ'
    rw [happ]
    show c • P g ≤ N (c • g)
    rcases lt_trichotomy c 0 with hneg | hzero | hpos
    · -- c < 0: equality, via homogeneity at -c > 0
      have hgg : c • g = (-c) • (fun x => -g x) := by
        funext x
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      have hNg : N (fun x => -g x) = -P g := by
        rw [hNval (fun x => -g x)]
        have h1 : (fun x => -(fun y => -g y) x) = g := by
          funext x
          simp
        rw [h1]
      rw [hgg, hNhom (-c) (by linarith) (fun x => -g x), hNg, smul_eq_mul]
      exact le_of_eq (by ring)
    · subst hzero
      rw [zero_smul, zero_smul]
      have hN0 : N 0 = 0 := by
        rw [hNval 0]
        have h1 : (fun x : X => -(0 : X → ℝ) x) = (fun _ : X => (0 : ℝ)) := by
          funext x
          simp
        rw [h1, hP0, neg_zero]
      rw [hN0]
    · rw [hNhom c hpos g, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (hPleN g) hpos.le
  obtain ⟨T, hTeq, hTle⟩ := exists_extension_of_le_sublinear fpm N hNhom hNadd hf
  -- T dominates P …
  have hTP : ∀ f : X → ℝ, P f ≤ T f := by
    intro f
    have h1 := hTle (-f)
    have h2 : N (-f) = -P f := by
      rw [hNval (-f)]
      have h3 : (fun x => -(-f) x) = f := by
        funext x
        simp
      rw [h3]
    rw [map_neg, h2] at h1
    linarith
  -- … and touches at g
  have hTg : T g = P g := by
    have hmem : g ∈ fpm.domain := Submodule.mem_span_singleton_self g
    have h1 := hTeq ⟨g, hmem⟩
    have h2 : fpm ⟨g, hmem⟩ = P g :=
      LinearPMap.mkSpanSingleton'_apply_self g (P g) hH hmem
    exact h1.trans h2
  -- extract the pmf carried by T
  have hdecomp : ∀ f : X → ℝ, T f = ∑ x, f x * T (Pi.single x 1) := by
    intro f
    have h2 : ∀ x : X, f x • Pi.single x (1 : ℝ) = Pi.single x (f x) := by
      intro x
      rw [← Pi.single_smul' x (f x) (1 : ℝ), smul_eq_mul, mul_one]
    have h1 : (∑ x, f x • Pi.single x (1 : ℝ)) = f := by
      rw [Finset.sum_congr rfl fun x _ => h2 x, Finset.univ_sum_single]
    calc T f = T (∑ x, f x • Pi.single x (1 : ℝ)) := by rw [h1]
      _ = ∑ x, f x * T (Pi.single x 1) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun x _ => by rw [map_smul, smul_eq_mul]
  have hT1 : T (fun _ => (1 : ℝ)) = 1 := by
    have hlow : (1 : ℝ) ≤ T (fun _ => 1) := by
      have h1 := hTP (fun _ => (1 : ℝ))
      rw [hP.const_eval 1] at h1
      exact h1
    have hup : T (fun _ => (1 : ℝ)) ≤ 1 := by
      have h1 := hTle (fun _ => (1 : ℝ))
      have h2 : N (fun _ => (1 : ℝ)) = 1 := by
        rw [hNval (fun _ => (1 : ℝ))]
        have h3 : (fun x : X => -(fun _ : X => (1 : ℝ)) x) =
            (fun _ : X => (-1 : ℝ)) := by
          funext x
          simp
        rw [h3, hP.const_eval (-1)]
        ring
      rw [h2] at h1
      exact h1
    linarith
  have hpnonneg : ∀ x, (0 : ℝ) ≤ T (Pi.single x 1) := by
    intro x
    have h1 : P (Pi.single x 1) ≤ T (Pi.single x 1) := hTP _
    have h2 : (0 : ℝ) ≤ P (Pi.single x 1) := by
      have h3 := hP.inf_le (Pi.single x 1)
      have h4 : (0 : ℝ) ≤ univ.inf' univ_nonempty (Pi.single x 1) :=
        Finset.le_inf' _ _ fun y _ => by
          rcases eq_or_ne y x with rfl | hy
          · simp
          · simp [hy]
      linarith
    linarith
  have htotal : ∑ x, T (Pi.single x (1 : ℝ)) = 1 := by
    have h1 := hdecomp (fun _ => (1 : ℝ))
    rw [hT1] at h1
    simp only [one_mul] at h1
    exact h1.symm
  set p : RealPMF X := ⟨fun x => T (Pi.single x 1), hpnonneg, htotal⟩ with hpdef
  have hexp : ∀ f : X → ℝ, p.exp f = T f := by
    intro f
    rw [hdecomp f]
    show (∑ x, T (Pi.single x 1) * f x) = ∑ x, f x * T (Pi.single x 1)
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  refine ⟨p, fun f => ?_, ?_⟩
  · rw [hexp f]
    exact hTP f
  · rw [hexp g]
    exact hTg

/-- The credal set of a coherent lower prevision is nonempty. -/
theorem IsCoherent.credal_nonempty {P : (X → ℝ) → ℝ} (hP : IsCoherent P) :
    {p : RealPMF X | Dominates P p}.Nonempty := by
  obtain ⟨p, hp, -⟩ := hP.exists_dominating_exp_eq (fun _ => 0)
  exact ⟨p, hp⟩

/-- The envelope theorem, envelope display: over a finite state space, every
coherent lower prevision *is* the lower envelope of its credal set
`M(P)` — exactly. -/
theorem IsCoherent.eq_sInf_credal {P : (X → ℝ) → ℝ} (hP : IsCoherent P)
    (g : X → ℝ) :
    P g = sInf ((fun p => p.exp g) '' {p : RealPMF X | Dominates P p}) := by
  obtain ⟨p₀, hp₀, hp₀g⟩ := hP.exists_dominating_exp_eq g
  apply le_antisymm
  · exact le_csInf ⟨_, ⟨p₀, hp₀, rfl⟩⟩
      (by rintro r ⟨p, hp, rfl⟩; exact hp g)
  · calc sInf ((fun p => p.exp g) '' {p : RealPMF X | Dominates P p})
        ≤ p₀.exp g := csInf_le (bddBelow_exp_image _ _) ⟨p₀, hp₀, rfl⟩
      _ = P g := hp₀g

end Coherence

/-! ## The natural extension -/

section NaturalExtension

variable {X : Type*} [Fintype X] [Nonempty X] {ι : Type*}
variable (h : ι → X → ℝ) (c : ι → ℝ)

/-- `p` is compatible with the assessment `(h, c)`: every claimed lower bound
holds under `p`'s expectation. (The assessment `(K, c)` is presented as a
finitely indexed family of gambles with claimed bounds.) -/
def Compatible (p : RealPMF X) : Prop := ∀ i, c i ≤ p.exp (h i)

/-- The compatible set `M(K, c)`. -/
def compatibleSet : Set (RealPMF X) := {p | Compatible h c p}

/-- `(K, c)` avoids sure loss when `M(K, c) ≠ ∅` (the betting
characterization is `avoidsSureLoss_iff_noSureLoss`). -/
def AvoidsSureLoss : Prop := (compatibleSet h c).Nonempty

/-- The natural extension of the assessment `(h, c)` — the lower envelope of
its compatible set. -/
noncomputable def natExt (g : X → ℝ) : ℝ :=
  sInf ((fun p => p.exp g) '' compatibleSet h c)

/-- NE1: the natural extension of an assessment avoiding sure loss is a
coherent lower prevision. -/
theorem natExt_coherent (hASL : AvoidsSureLoss h c) :
    IsCoherent (natExt h c) :=
  envelope_coherent (compatibleSet h c) hASL

omit [Nonempty X] in
/-- NE2: the natural extension dominates the assessment. -/
theorem assessment_le_natExt (hASL : AvoidsSureLoss h c) (i : ι) :
    c i ≤ natExt h c (h i) :=
  le_csInf (Set.Nonempty.image _ hASL) (by rintro r ⟨p, hp, rfl⟩; exact hp i)

/-- The largest-credal-set dual of NE3: `M(E_{K,c}) = M(K, c)` — a pmf's
expectation dominates the natural extension iff the pmf is compatible with
the assessment. -/
theorem dominates_natExt_iff (hASL : AvoidsSureLoss h c) (p : RealPMF X) :
    Dominates (natExt h c) p ↔ Compatible h c p := by
  constructor
  · intro hd i
    exact (assessment_le_natExt h c hASL i).trans (hd (h i))
  · intro hp f
    exact csInf_le (bddBelow_exp_image _ _) ⟨p, hp, rfl⟩

/-! ### The dual display: finite positive combinations of deficits -/

variable [Fintype ι]

/-- A finite nonnegative combination of assessment deficits,
`x ↦ ∑ i, λ i · (h i x − c i)`. -/
def deficit (lam : ι → ℝ) : X → ℝ := fun x => ∑ i, lam i * (h i x - c i)

/-- `α` is dual-feasible for `g`: some nonnegative deficit combination
certifies `g − α ≥ ∑ λᵢ (hᵢ − c hᵢ)` pointwise. -/
def DualFeasible (g : X → ℝ) (α : ℝ) : Prop :=
  ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ ∀ x, α + deficit h c lam x ≤ g x

/-- The sup of the dual-feasible values — the sup of finite positive
combinations of assessment deficits. -/
noncomputable def dualVal (g : X → ℝ) : ℝ := sSup {α | DualFeasible h c g α}

/-- No nonnegative combination of deficits is uniformly negative — the
betting face of avoiding sure loss. -/
def NoSureLoss : Prop :=
  ∀ lam : ι → ℝ, (∀ i, 0 ≤ lam i) →
    0 ≤ univ.sup' univ_nonempty (deficit h c lam)

theorem dualFeasible_inf' (g : X → ℝ) :
    DualFeasible h c g (univ.inf' univ_nonempty g) := by
  refine ⟨fun _ => 0, fun _ => le_rfl, fun x => ?_⟩
  have h0 : deficit h c (fun _ => 0) x = 0 := by
    simp [deficit]
  rw [h0, add_zero]
  exact Finset.inf'_le _ (mem_univ x)

omit [Nonempty X] in
theorem exp_deficit (p : RealPMF X) (lam : ι → ℝ) :
    p.exp (deficit h c lam) = ∑ i, lam i * (p.exp (h i) - c i) := by
  simp only [RealPMF.exp, deficit, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hterm : ∀ x, p.prob x * (lam i * (h i x - c i)) =
      lam i * (p.prob x * h i x - c i * p.prob x) := fun x => by ring
  rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, p.total, mul_one]

omit [Nonempty X] in
/-- Weak duality: every dual-feasible value bounds every compatible
expectation from below. -/
theorem DualFeasible.le_exp {g : X → ℝ} {α : ℝ} (hα : DualFeasible h c g α)
    {p : RealPMF X} (hp : Compatible h c p) : α ≤ p.exp g := by
  obtain ⟨lam, hlam, hpt⟩ := hα
  have h1 : p.exp (fun x => α + deficit h c lam x) ≤ p.exp g :=
    p.exp_mono hpt
  have h2 : p.exp (fun x => α + deficit h c lam x)
      = α + ∑ i, lam i * (p.exp (h i) - c i) := by
    rw [p.exp_const_add α (deficit h c lam), exp_deficit]
  have h3 : (0 : ℝ) ≤ ∑ i, lam i * (p.exp (h i) - c i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (by linarith [hp i])
  linarith

theorem dualFeasible_le_sup' (hNSL : NoSureLoss h c) {g : X → ℝ} {α : ℝ}
    (hα : DualFeasible h c g α) : α ≤ univ.sup' univ_nonempty g := by
  obtain ⟨lam, hlam, hpt⟩ := hα
  obtain ⟨x₀, _, hval⟩ :=
    Finset.exists_mem_eq_sup' univ_nonempty (deficit h c lam)
  have h1 : (0 : ℝ) ≤ deficit h c lam x₀ := by
    have h2 := hNSL lam hlam
    rw [hval] at h2
    exact h2
  have h3 := hpt x₀
  have h4 : g x₀ ≤ univ.sup' univ_nonempty g := Finset.le_sup' g (mem_univ x₀)
  linarith

theorem dualVal_bddAbove (hNSL : NoSureLoss h c) (g : X → ℝ) :
    BddAbove {α | DualFeasible h c g α} :=
  ⟨univ.sup' univ_nonempty g, fun _ hα => dualFeasible_le_sup' h c hNSL hα⟩

theorem le_dualVal (hNSL : NoSureLoss h c) (g : X → ℝ) :
    univ.inf' univ_nonempty g ≤ dualVal h c g :=
  le_csSup (dualVal_bddAbove h c hNSL g) (dualFeasible_inf' h c g)

theorem dualVal_le_sup' (hNSL : NoSureLoss h c) (g : X → ℝ) :
    dualVal h c g ≤ univ.sup' univ_nonempty g :=
  csSup_le ⟨_, dualFeasible_inf' h c g⟩
    fun _ hα => dualFeasible_le_sup' h c hNSL hα

/-- If a compatible model exists, no sure loss is exposed (the easy direction
of the alternative). -/
theorem AvoidsSureLoss.noSureLoss (hASL : AvoidsSureLoss h c) :
    NoSureLoss h c := by
  obtain ⟨p, hp⟩ := hASL
  intro lam hlam
  have h1 : (0 : ℝ) ≤ p.exp (deficit h c lam) := by
    rw [exp_deficit]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (by linarith [hp i])
  linarith [p.exp_le_sup' (deficit h c lam)]

omit [Fintype X] [Nonempty X] in
theorem deficit_add (lama lamb : ι → ℝ) (x : X) :
    deficit h c (fun i => lama i + lamb i) x
      = deficit h c lama x + deficit h c lamb x := by
  simp [deficit, add_mul, Finset.sum_add_distrib]

/-- The dual functional is itself a coherent lower prevision whenever no sure
loss is exposed — the keystone that lets the envelope theorem discharge both
strong duality and the sure-loss alternative. -/
theorem dualVal_coherent (hNSL : NoSureLoss h c) :
    IsCoherent (dualVal h c) where
  inf_le g := le_dualVal h c hNSL g
  homog l hl g := by
    rcases hl.eq_or_lt with heq | hpos
    · have h0 : (fun x : X => l * g x) = (fun _ : X => (0 : ℝ)) := by
        funext x
        rw [← heq, zero_mul]
      rw [h0, ← heq, zero_mul]
      apply le_antisymm
      · have h1 := dualVal_le_sup' h c hNSL (fun _ : X => (0 : ℝ))
        simpa [Finset.sup'_const] using h1
      · have h1 := le_dualVal h c hNSL (fun _ : X => (0 : ℝ))
        simpa [Finset.inf'_const] using h1
    · have key : {α | DualFeasible h c (fun x => l * g x) α}
          = l • {α | DualFeasible h c g α} := by
        ext α
        simp only [Set.mem_setOf_eq, Set.mem_smul_set]
        constructor
        · rintro ⟨lam, hlam, hpt⟩
          have hl0 : l ≠ 0 := hpos.ne'
          refine ⟨α / l, ⟨fun i => lam i / l, fun i =>
            div_nonneg (hlam i) hpos.le, fun x => ?_⟩, by
              rw [smul_eq_mul]
              field_simp⟩
          have hd : deficit h c (fun i => lam i / l) x
              = deficit h c lam x / l := by
            simp only [deficit, Finset.sum_div]
            exact Finset.sum_congr rfl fun i _ => by ring
          have h1 := hpt x
          rw [hd, ← add_div, div_le_iff₀ hpos]
          linarith
        · rintro ⟨α', ⟨lam, hlam, hpt⟩, rfl⟩
          refine ⟨fun i => l * lam i, fun i =>
            mul_nonneg hpos.le (hlam i), fun x => ?_⟩
          have hd : deficit h c (fun i => l * lam i) x
              = l * deficit h c lam x := by
            simp only [deficit, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
          have h1 := hpt x
          rw [hd, smul_eq_mul]
          linarith [mul_le_mul_of_nonneg_left h1 hpos.le]
      show sSup {α | DualFeasible h c (fun x => l * g x) α}
          = l * sSup {α | DualFeasible h c g α}
      rw [key, Real.sSup_smul_of_nonneg hl, smul_eq_mul]
  superadd f g := by
    have hAne : {α | DualFeasible h c f α}.Nonempty :=
      ⟨_, dualFeasible_inf' h c f⟩
    have hBne : {α | DualFeasible h c g α}.Nonempty :=
      ⟨_, dualFeasible_inf' h c g⟩
    have hCbdd := dualVal_bddAbove h c hNSL (fun x => f x + g x)
    have hsub : ∀ a, DualFeasible h c f a → ∀ b, DualFeasible h c g b →
        DualFeasible h c (fun x => f x + g x) (a + b) := by
      rintro a ⟨lama, hla, hpa⟩ b ⟨lamb, hlb, hpb⟩
      refine ⟨fun i => lama i + lamb i, fun i => add_nonneg (hla i) (hlb i),
        fun x => ?_⟩
      have h1 := hpa x
      have h2 := hpb x
      rw [deficit_add]
      linarith
    have step1 : ∀ a ∈ {α | DualFeasible h c f α},
        a ≤ dualVal h c (fun x => f x + g x) - dualVal h c g := by
      intro a ha
      have step2 : ∀ b ∈ {α | DualFeasible h c g α},
          b ≤ dualVal h c (fun x => f x + g x) - a := by
        intro b hb
        have h1 : a + b ≤ dualVal h c (fun x => f x + g x) :=
          le_csSup hCbdd (hsub a ha b hb)
        linarith
      have h2 : dualVal h c g ≤ dualVal h c (fun x => f x + g x) - a :=
        csSup_le hBne step2
      linarith
    have h3 : dualVal h c f
        ≤ dualVal h c (fun x => f x + g x) - dualVal h c g :=
      csSup_le hAne step1
    linarith

/-- The dual functional dominates the assessment (certificate: the `i`-th
unit deficit, tight at `α = c i`). -/
theorem assessment_le_dualVal (hNSL : NoSureLoss h c) (i : ι) :
    c i ≤ dualVal h c (h i) := by
  classical
  apply le_csSup (dualVal_bddAbove h c hNSL (h i))
  refine ⟨Pi.single i 1, fun j => ?_, fun x => ?_⟩
  · rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [hj]
  · have hd : deficit h c (Pi.single i 1) x = h i x - c i := by
      simp only [deficit, Pi.single_apply, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq' univ i (fun j => h j x - c j)]
      simp
    rw [hd]
    linarith

/-- Strong linear-programming duality (exact, for finite `X`): the natural
extension equals the sup of the values certified by finite positive
combinations of assessment deficits. Weak duality is elementary; strong
duality is the envelope theorem applied to the coherent dual functional. -/
theorem natExt_eq_dualVal (hASL : AvoidsSureLoss h c) (g : X → ℝ) :
    natExt h c g = dualVal h c g := by
  have hNSL := hASL.noSureLoss
  apply le_antisymm
  · -- strong direction, via the envelope theorem on `dualVal`
    obtain ⟨p, hpd, hpg⟩ :=
      (dualVal_coherent h c hNSL).exists_dominating_exp_eq g
    have hpc : Compatible h c p := fun i =>
      (assessment_le_dualVal h c hNSL i).trans (hpd (h i))
    calc natExt h c g ≤ p.exp g :=
          csInf_le (bddBelow_exp_image _ _) ⟨p, hpc, rfl⟩
      _ = dualVal h c g := hpg
  · -- weak duality
    have hne : {α | DualFeasible h c g α}.Nonempty :=
      ⟨_, dualFeasible_inf' h c g⟩
    apply csSup_le hne
    intro α hα
    exact le_csInf (Set.Nonempty.image _ hASL)
      (by rintro r ⟨p, hp, rfl⟩; exact DualFeasible.le_exp h c hα hp)

/-- The sure-loss alternative (Farkas-shaped): a compatible model exists iff
no nonnegative deficit combination is uniformly negative. -/
theorem avoidsSureLoss_iff_noSureLoss :
    AvoidsSureLoss h c ↔ NoSureLoss h c := by
  constructor
  · exact fun hASL => hASL.noSureLoss
  · intro hNSL
    obtain ⟨p, hpd, -⟩ :=
      (dualVal_coherent h c hNSL).exists_dominating_exp_eq (fun _ => 0)
    exact ⟨p, fun i => (assessment_le_dualVal h c hNSL i).trans (hpd (h i))⟩

/-- NE3: the natural extension is the pointwise-*smallest* coherent lower
prevision dominating the assessment. -/
theorem natExt_le_coherent (hASL : AvoidsSureLoss h c) {Q : (X → ℝ) → ℝ}
    (hQ : IsCoherent Q) (hdom : ∀ i, c i ≤ Q (h i)) (g : X → ℝ) :
    natExt h c g ≤ Q g := by
  rw [natExt_eq_dualVal h c hASL]
  have hne : {α | DualFeasible h c g α}.Nonempty :=
    ⟨_, dualFeasible_inf' h c g⟩
  apply csSup_le hne
  rintro α ⟨lam, hlam, hpt⟩
  have h1 : Q (fun x => α + deficit h c lam x) ≤ Q g := hQ.mono hpt
  have h2 : Q (fun x => α + deficit h c lam x)
      = Q (deficit h c lam) + α := by
    rw [show (fun x => α + deficit h c lam x)
        = (fun x => deficit h c lam x + α) from by funext x; ring]
    exact hQ.add_const (deficit h c lam) α
  have hFi : ∀ i, Q (fun x => h i x - c i) = Q (h i) - c i := by
    intro i
    rw [show (fun x => h i x - c i) = (fun x => h i x + -c i) from by
      funext x; ring]
    rw [hQ.add_const (h i) (-c i)]
    ring
  have h3 : ∑ i, lam i * (Q (h i) - c i) ≤ Q (deficit h c lam) := by
    calc ∑ i, lam i * (Q (h i) - c i)
        = ∑ i, lam i * Q (fun x => h i x - c i) :=
          Finset.sum_congr rfl fun i _ => by rw [hFi i]
      _ ≤ Q (fun x => ∑ i, lam i * (h i x - c i)) :=
          hQ.sum_smul_le univ lam (fun i x => h i x - c i) hlam
      _ = Q (deficit h c lam) := rfl
  have h4 : (0 : ℝ) ≤ ∑ i, lam i * (Q (h i) - c i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (by linarith [hdom i])
  linarith

end NaturalExtension

/-! ## Mutants: teeth for the statements

A concrete assessment over `Bool`: one gamble (the indicator of `true`) with
claimed lower bound `1/2`, evaluated at the gamble `g = (2 on true, −1 on
false)`. Exact value of the natural extension: `1/2`, witnessed on both sides
of the duality (primal: the uniform pmf; dual: the deficit certificate
`λ = 3`). -/

namespace Mutants

noncomputable section

def hA : Unit → Bool → ℝ := fun _ b => cond b 1 0

def cA : Unit → ℝ := fun _ => 1 / 2

def gA : Bool → ℝ := fun b => cond b 2 (-1)

/-- The uniform pmf on `Bool` — the primal witness. -/
def pHalf : RealPMF Bool where
  prob := fun _ => 1 / 2
  nonneg := fun _ => by norm_num
  total := by rw [Fintype.sum_bool]; norm_num

theorem pHalf_compatible : Compatible hA cA pHalf := by
  intro i
  norm_num [RealPMF.exp, Fintype.sum_bool, pHalf, hA, cA]

theorem aslA : AvoidsSureLoss hA cA := ⟨pHalf, pHalf_compatible⟩

theorem pHalf_exp_gA : pHalf.exp gA = 1 / 2 := by
  norm_num [RealPMF.exp, Fintype.sum_bool, pHalf, gA]

/-- The natural extension of the assessment at `gA`, evaluated exactly. -/
theorem natExt_val : natExt hA cA gA = 1 / 2 := by
  apply le_antisymm
  · calc natExt hA cA gA ≤ pHalf.exp gA :=
        csInf_le (bddBelow_exp_image _ _) ⟨pHalf, pHalf_compatible, rfl⟩
      _ = 1 / 2 := pHalf_exp_gA
  · apply le_csInf (Set.Nonempty.image _ aslA)
    rintro r ⟨p, hp, rfl⟩
    have h1 := hp ()
    have h2 := p.total
    have h3 := p.nonneg false
    rw [Fintype.sum_bool] at h2
    norm_num [RealPMF.exp, Fintype.sum_bool, hA, cA] at h1
    norm_num [RealPMF.exp, Fintype.sum_bool, gA]
    linarith

/-- The dual certificate `λ = 3` is feasible at `α = 1/2`: the deficit
display touches the same value from below — both duality directions are
tight on this instance. -/
theorem dual_certificate_tight : DualFeasible hA cA gA (1 / 2) := by
  refine ⟨fun _ => 3, fun _ => by norm_num, fun x => ?_⟩
  cases x <;> norm_num [deficit, hA, cA, gA, Fintype.sum_unique]

theorem half_le_dualVal : 1 / 2 ≤ dualVal hA cA gA :=
  le_csSup (dualVal_bddAbove hA cA aslA.noSureLoss gA) dual_certificate_tight

/-- The forged envelope: `pBad` puts only `1/4` on `true`. -/
def pBad : RealPMF Bool where
  prob := fun b => cond b (1 / 4) (3 / 4)
  nonneg := fun b => by cases b <;> norm_num
  total := by rw [Fintype.sum_bool]; norm_num

theorem pBad_not_compatible : ¬Compatible hA cA pBad := by
  intro hcon
  have h1 := hcon ()
  norm_num [RealPMF.exp, Fintype.sum_bool, pBad, hA, cA] at h1

/-- Mutant 1a: the forged envelope's value sits strictly below the natural
extension — the envelope bound has teeth. -/
theorem forged_envelope_violates : pBad.exp gA < natExt hA cA gA := by
  rw [natExt_val]
  norm_num [RealPMF.exp, Fintype.sum_bool, pBad, gA]

/-- Mutant 1b: the forgery is refused through the largest-credal-set dual —
`pBad` does not dominate the natural extension. -/
theorem pBad_not_dominating : ¬Dominates (natExt hA cA) pBad := fun hd =>
  pBad_not_compatible ((dominates_natExt_iff hA cA aslA pBad).mp hd)

/-- The would-be "extension" by upper envelope. -/
def QSup : (Bool → ℝ) → ℝ := fun f => univ.sup' univ_nonempty f

theorem QSup_dominates : ∀ i : Unit, cA i ≤ QSup (hA i) := by
  intro _
  have h1 : hA () true ≤ QSup (hA ()) := Finset.le_sup' (hA ()) (mem_univ true)
  have h2 : hA () true = 1 := rfl
  have h3 : cA () = 1 / 2 := rfl
  rw [h2] at h1
  rw [h3]
  linarith

/-- Mutant 2: the upper envelope dominates the assessment but is refused as
an extension — it violates (W3) superadditivity, so NE3's coherence
hypothesis has content. -/
theorem QSup_not_coherent : ¬IsCoherent QSup := by
  intro hQ
  have hsum := hQ.superadd (fun b => cond b (1 : ℝ) 0)
    (fun b => cond b (0 : ℝ) 1)
  have h1 : (1 : ℝ) ≤ QSup (fun b => cond b (1 : ℝ) 0) :=
    Finset.le_sup' (fun b : Bool => cond b (1 : ℝ) 0) (mem_univ true)
  have h2 : (1 : ℝ) ≤ QSup (fun b => cond b (0 : ℝ) 1) :=
    Finset.le_sup' (fun b : Bool => cond b (0 : ℝ) 1) (mem_univ false)
  have h3 : QSup (fun b => cond b (1 : ℝ) 0 + cond b (0 : ℝ) 1) ≤ 1 := by
    apply Finset.sup'_le
    intro b _
    cases b <;> norm_num
  linarith

/-- The vacuous lower prevision (no assessment content at all). -/
def QInf : (Bool → ℝ) → ℝ := fun f => univ.inf' univ_nonempty f

/-- Mutant 3: NE2 has content — on the assessed gamble, the natural extension
sits strictly above the vacuous prevision (the assessment genuinely
constrains). -/
theorem natExt_gt_vacuous : QInf (hA ()) < natExt hA cA (hA ()) := by
  have h1 : QInf (hA ()) ≤ hA () false :=
    Finset.inf'_le (hA ()) (mem_univ false)
  have h1' : hA () false = 0 := rfl
  have h2 : (1 : ℝ) / 2 ≤ natExt hA cA (hA ()) :=
    assessment_le_natExt hA cA aslA ()
  rw [h1'] at h1
  linarith

end

end Mutants

end Qtsl.Imprecise
