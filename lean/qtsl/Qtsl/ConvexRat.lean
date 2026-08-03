import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Fintype.BigOperators

/-!
# Rational feasibility of rational linear systems

If a finite system of linear equations with rational coefficients
admits a nonnegative real solution, it admits a nonnegative rational
one (`exists_nonneg_rat_solution`). Downstream this hands the
multivariate Bernstein-cone bridge rational barycentric weights: a
rational point in the real convex hull of rational vertices is a
rational convex combination of them.
-/

namespace PPLC.ConvexRat

open Finset

variable {k m : ℕ}

private def famQ (A : Fin k → Fin m → ℚ) (T : Finset (Fin k)) :
    {i // i ∈ T} → (Fin m → ℚ) :=
  fun i => A i.val

private def famR (A : Fin k → Fin m → ℚ) (T : Finset (Fin k)) :
    {i // i ∈ T} → (Fin m → ℝ) :=
  fun i j => ((A i.val j : ℚ) : ℝ)

private theorem famR_eq_cast_comp (A : Fin k → Fin m → ℚ)
    (T : Finset (Fin k)) :
    famR A T = fun i => algebraMap ℚ ℝ ∘ famQ A T i := by
  funext i j
  simp [famR, famQ]

private theorem famR_linearIndependent_iff (A : Fin k → Fin m → ℚ)
    (T : Finset (Fin k)) :
    LinearIndependent ℝ (famR A T) ↔ LinearIndependent ℚ (famQ A T) := by
  rw [famR_eq_cast_comp]
  exact linearIndependent_algebraMap_comp_iff

private theorem sum_support_collapse {M : Type*} [AddCommMonoid M]
    {T : Finset (Fin k)} (F : Fin k → M)
    (hz : ∀ i, i ∉ T → F i = 0) :
    (∑ i, F i) = ∑ i : {i // i ∈ T}, F i.val := by
  rw [Finset.sum_coe_sort T F]
  exact (Finset.sum_subset (Finset.subset_univ T)
    (fun i _ hi => hz i hi)).symm

private theorem aux (A : Fin k → Fin m → ℚ) (b : Fin m → ℚ)
    (T : Finset (Fin k)) :
    ∀ (c : Fin k → ℝ), (∀ i, 0 ≤ c i) → (∀ i, c i ≠ 0 → i ∈ T) →
    (∀ j, (∑ i, c i * (A i j : ℝ)) = (b j : ℝ)) →
    ∃ q : Fin k → ℚ, (∀ i, 0 ≤ q i) ∧ ∀ j, (∑ i, q i * A i j) = b j := by
  induction T using Finset.strongInduction with
  | _ T ih =>
  intro c hc0 hsupp hcsol

  have hsubsol : ∀ j, (∑ i : {i // i ∈ T}, c i.val * (A i.val j : ℝ))
      = (b j : ℝ) := by
    intro j
    rw [← sum_support_collapse (fun i => c i * (A i j : ℝ))
      (fun i hi => by
        have hci : c i = 0 := by
          by_contra hne
          exact hi (hsupp i hne)
        rw [hci, zero_mul])]
    exact hcsol j
  by_cases hind : LinearIndependent ℝ (famR A T)
  ·

    have hbmem : b ∈ Submodule.span ℚ (Set.range (famQ A T)) := by
      by_contra hbnot

      have hQind : LinearIndependent ℚ (famQ A T) :=
        (famR_linearIndependent_iff A T).mp hind
      have hext : LinearIndependent ℚ
          (fun o : Option {i // i ∈ T} => o.elim b (famQ A T)) := by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        have hsplit : g none • b + ∑ i : {i // i ∈ T},
            g (some i) • famQ A T i = 0 := by
          have h := hg
          rw [Fintype.sum_option (f := fun o => g o • (o.elim b (famQ A T)))]
            at h
          simpa using h
        have hgnone : g none = 0 := by
          by_contra hne
          apply hbnot
          have hb' : b = (-(g none)⁻¹) •
              ∑ i : {i // i ∈ T}, g (some i) • famQ A T i := by
            have h1 : g none • b
                = -∑ i : {i // i ∈ T}, g (some i) • famQ A T i := by
              rw [eq_neg_iff_add_eq_zero]
              exact hsplit
            calc b = (g none)⁻¹ • (g none • b) := by
                  rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
              _ = (-(g none)⁻¹) •
                  ∑ i : {i // i ∈ T}, g (some i) • famQ A T i := by
                  rw [h1, smul_neg, ← neg_smul]
          rw [hb']
          exact Submodule.smul_mem _ _ (Submodule.sum_mem _
            (fun i _ => Submodule.smul_mem _ _
              (Submodule.subset_span ⟨i, rfl⟩)))
        have hrest : ∑ i : {i // i ∈ T}, g (some i) • famQ A T i = 0 := by
          rw [hgnone, zero_smul, zero_add] at hsplit
          exact hsplit
        intro o
        cases o with
        | none => exact hgnone
        | some i => exact Fintype.linearIndependent_iff.mp hQind _ hrest i

      have hextR : LinearIndependent ℝ
          (fun o : Option {i // i ∈ T} =>
            algebraMap ℚ ℝ ∘ (o.elim b (famQ A T))) :=
        linearIndependent_algebraMap_comp_iff.mpr hext

      have hdep : ∑ o : Option {i // i ∈ T},
          (Option.elim o (-1 : ℝ) fun i => c i.val) •
            (algebraMap ℚ ℝ ∘ (Option.elim o b (famQ A T))) = 0 := by
        rw [Fintype.sum_option]
        funext j
        simp only [Option.elim, Pi.add_apply, Finset.sum_apply,
          Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply,
          eq_ratCast, famQ]
        have h1 := hsubsol j
        linarith [h1]
      have := Fintype.linearIndependent_iff.mp hextR _ hdep none
      norm_num at this

    obtain ⟨cT, hcT⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hbmem
    have hcTj : ∀ j, (∑ i : {i // i ∈ T}, cT i * A i.val j) = b j := by
      intro j
      have := congrFun hcT j
      simpa [Finset.sum_apply, famQ] using this

    have hcast : ∀ i : {i // i ∈ T}, ((cT i : ℚ) : ℝ) = c i.val := by
      have hdiff : ∑ i : {i // i ∈ T},
          (((cT i : ℚ) : ℝ) - c i.val) • famR A T i = 0 := by
        funext j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply, famR, sub_mul, Finset.sum_sub_distrib]
        have h1 : (∑ i : {i // i ∈ T}, ((cT i : ℚ) : ℝ) * ((A i.val j : ℚ) : ℝ))
            = ((b j : ℚ) : ℝ) := by
          exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) (hcTj j)
        rw [h1, hsubsol j, sub_self]
      intro i
      have := Fintype.linearIndependent_iff.mp hind _ hdiff i
      have h0 : ((cT i : ℚ) : ℝ) - c i.val = 0 := this
      linarith [h0]

    refine ⟨fun i => if h : i ∈ T then cT ⟨i, h⟩ else 0, ?_, ?_⟩
    · intro i
      show (0:ℚ) ≤ if h : i ∈ T then cT ⟨i, h⟩ else 0
      split
      · next h =>
        have hge : (0 : ℝ) ≤ ((cT ⟨i, h⟩ : ℚ) : ℝ) := by
          rw [hcast ⟨i, h⟩]
          exact hc0 i
        exact_mod_cast hge
      · exact le_refl 0
    · intro j
      rw [sum_support_collapse
        (fun i => (if h : i ∈ T then cT ⟨i, h⟩ else 0) * A i j)
        (fun i hi => by
          show (if h : i ∈ T then cT ⟨i, h⟩ else 0) * A i j = 0
          split
          · next h => exact absurd h hi
          · exact zero_mul _)]
      rw [← hcTj j]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      show (if h : i.val ∈ T then cT ⟨i.val, h⟩ else 0) * A i.val j
        = cT i * A i.val j
      split
      · next h => rw [Subtype.coe_eta]
      · next h => exact absurd i.property h
  ·
    obtain ⟨g₀, hg₀, i₀, hgi₀⟩ := Fintype.not_linearIndependent_iff.mp hind

    obtain ⟨g, hg, i₁, hgpos⟩ :
        ∃ g : {i // i ∈ T} → ℝ, (∑ i, g i • famR A T i = 0) ∧
          ∃ i, 0 < g i := by
      rcases lt_or_gt_of_ne hgi₀ with hneg | hpos
      · refine ⟨-g₀, ?_, i₀, by simpa using hneg⟩
        rw [← neg_zero, ← hg₀, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by rw [Pi.neg_apply, neg_smul])
      · exact ⟨g₀, hg₀, i₀, hpos⟩

    obtain ⟨gext, hgmem, hgnmem⟩ :
        ∃ gext : Fin k → ℝ, (∀ (i : Fin k) (h : i ∈ T), gext i = g ⟨i, h⟩) ∧
          ∀ i ∉ T, gext i = 0 := by
      refine ⟨fun i => if h : i ∈ T then g ⟨i, h⟩ else 0, ?_, ?_⟩
      · intro i h
        show (if h' : i ∈ T then g ⟨i, h'⟩ else 0) = g ⟨i, h⟩
        split
        · rfl
        · next h' => exact absurd h h'
      · intro i hi
        show (if h' : i ∈ T then g ⟨i, h'⟩ else 0) = 0
        split
        · next h' => exact absurd h' hi
        · rfl
    have hgsum : ∀ j, (∑ i, gext i * (A i j : ℝ)) = 0 := by
      intro j
      rw [sum_support_collapse (fun i => gext i * (A i j : ℝ))
        (fun i hi => by rw [hgnmem i hi, zero_mul])]
      have hdep := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, famR,
        Pi.zero_apply] at hdep
      rw [← hdep]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hgmem i.val i.property, Subtype.coe_eta]

    set S : Finset {i // i ∈ T} :=
      Finset.univ.filter (fun i => 0 < g i) with hSdef
    have hSne : S.Nonempty := ⟨i₁, by simp [hSdef, hgpos]⟩
    obtain ⟨istar, histar, hmin⟩ :=
      Finset.exists_min_image S (fun i => c i.val / g i) hSne
    have hgstar : 0 < g istar := by
      have := Finset.mem_filter.mp histar
      exact this.2
    set t : ℝ := c istar.val / g istar with htdef
    have ht0 : 0 ≤ t := div_nonneg (hc0 _) hgstar.le
    set c' : Fin k → ℝ := fun i => c i - t * gext i with hc'def
    have hc'0 : ∀ i, 0 ≤ c' i := by
      intro i
      show (0:ℝ) ≤ c i - t * gext i
      by_cases h : i ∈ T
      · rw [hgmem i h]
        rcases le_or_gt (g ⟨i, h⟩) 0 with hgle | hgpos'
        · have : t * g ⟨i, h⟩ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hgle
          linarith [hc0 i]
        · have hmem : (⟨i, h⟩ : {i // i ∈ T}) ∈ S := by
            simp [hSdef, hgpos']
          have hle : t ≤ c i / g ⟨i, h⟩ := hmin _ hmem
          rw [le_div_iff₀ hgpos'] at hle
          linarith
      · rw [hgnmem i h, mul_zero, sub_zero]
        exact hc0 i
    have hc'sol : ∀ j, (∑ i, c' i * (A i j : ℝ)) = (b j : ℝ) := by
      intro j
      show (∑ i, (c i - t * gext i) * (A i j : ℝ)) = (b j : ℝ)
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc]
      rw [← Finset.mul_sum, hgsum j, mul_zero, sub_zero]
      exact hcsol j
    have hstar0 : c' istar.val = 0 := by
      show c istar.val - t * gext istar.val = 0
      rw [hgmem istar.val istar.property, Subtype.coe_eta, htdef,
        div_mul_cancel₀ _ (ne_of_gt hgstar)]
      ring
    have hsupp' : ∀ i, c' i ≠ 0 → i ∈ T.erase istar.val := by
      intro i hne
      rw [Finset.mem_erase]
      refine ⟨fun heq => hne (heq ▸ hstar0), ?_⟩
      by_contra hiT
      apply hne
      show c i - t * gext i = 0
      rw [hgnmem i hiT, mul_zero, sub_zero]
      by_contra hci
      exact hiT (hsupp i hci)
    exact ih (T.erase istar.val) (Finset.erase_ssubset istar.property)
      c' hc'0 hsupp' hc'sol

/-- A finite rational linear system admitting a nonnegative real solution
admits a nonnegative rational one. -/
theorem exists_nonneg_rat_solution (A : Fin k → Fin m → ℚ)
    (b : Fin m → ℚ) (c : Fin k → ℝ) (hc0 : ∀ i, 0 ≤ c i)
    (hcsol : ∀ j, (∑ i, c i * (A i j : ℝ)) = (b j : ℝ)) :
    ∃ q : Fin k → ℚ, (∀ i, 0 ≤ q i) ∧ ∀ j, (∑ i, q i * A i j) = b j :=
  aux A b Finset.univ c hc0 (fun i _ => Finset.mem_univ i) hcsol

end PPLC.ConvexRat
