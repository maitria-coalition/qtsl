import QtslAux.QRelChain
import QtslAux.Battery

/-! # Tabular tier: solve/table certificate soundness

For a finite discrete-time Markov chain presented by a row-stochastic
rational matrix, nested probability operators collapse to exact rational
linear algebra. This module defines the bounded-until value `uBdd` by
backward induction and its monotone limit `uStar` (unbounded until), and
proves the two tabular certificate shapes sound against that semantics:
`solve_cert_exact_rat` (a solved linear system certifies the unbounded-until
value on the transient block) and `satSet_exact_rat` (a certified
satisfaction set for a threshold query). The bridge theorem
`uBdd_eq_absorbedMass` identifies `uBdd` with absorbed mass under the
frozen forward chain, connecting the tier to the finite-chain semantics
used by the checker's arithmetic. No measure theory is required at this
tier. -/

namespace Qtsl

namespace Tabular

open Finset Filter Topology

open QRelChain (IsMarkov pointMass law step step_pointMass law_add
  law_eq_sum_pointMass)

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def uBdd (K : α → α → ℝ) (A B : Finset α) : ℕ → α → ℝ
  | 0 => fun s => if s ∈ B then 1 else 0
  | k + 1 => fun s =>
      if s ∈ B then 1
      else if s ∈ A then ∑ t, K s t * uBdd K A B k t
      else 0

variable {K : α → α → ℝ} {A B : Finset α}

@[simp] theorem uBdd_zero (s : α) :
    uBdd K A B 0 s = if s ∈ B then 1 else 0 := rfl

theorem uBdd_succ (k : ℕ) (s : α) :
    uBdd K A B (k + 1) s =
      if s ∈ B then 1
      else if s ∈ A then ∑ t, K s t * uBdd K A B k t
      else 0 := rfl

theorem uBdd_of_mem {s : α} (hs : s ∈ B) (k : ℕ) : uBdd K A B k s = 1 := by
  cases k <;> simp [uBdd, hs]

theorem uBdd_dead {s : α} (hsB : s ∉ B) (hsA : s ∉ A) (k : ℕ) :
    uBdd K A B k s = 0 := by
  cases k <;> simp [uBdd, hsB, hsA]

theorem uBdd_step {s : α} (hsB : s ∉ B) (hsA : s ∈ A) (k : ℕ) :
    uBdd K A B (k + 1) s = ∑ t, K s t * uBdd K A B k t := by
  simp [uBdd, hsB, hsA]

theorem uBdd_nonneg (hK : ∀ s t, 0 ≤ K s t) :
    ∀ (k : ℕ) (s : α), 0 ≤ uBdd K A B k s := by
  intro k
  induction k with
  | zero => intro s; rw [uBdd_zero]; split_ifs <;> norm_num
  | succ k ih =>
    intro s
    rw [uBdd_succ]
    split_ifs
    · norm_num
    · exact sum_nonneg fun t _ => mul_nonneg (hK s t) (ih t)
    · exact le_refl 0

theorem uBdd_le_one (hK : IsMarkov K) :
    ∀ (k : ℕ) (s : α), uBdd K A B k s ≤ 1 := by
  intro k
  induction k with
  | zero => intro s; rw [uBdd_zero]; split_ifs <;> norm_num
  | succ k ih =>
    intro s
    rw [uBdd_succ]
    split_ifs
    · exact le_refl 1
    · calc ∑ t, K s t * uBdd K A B k t
          ≤ ∑ t, K s t * 1 :=
            sum_le_sum fun t _ =>
              mul_le_mul_of_nonneg_left (ih t) (hK.nonneg s t)
        _ = 1 := by simp [hK.rowSum s]
    · norm_num

theorem uBdd_le_succ (hK : ∀ s t, 0 ≤ K s t) :
    ∀ (k : ℕ) (s : α), uBdd K A B k s ≤ uBdd K A B (k + 1) s := by
  intro k
  induction k with
  | zero =>
    intro s
    rw [uBdd_zero, uBdd_succ]
    split_ifs with h1 h2
    · exact le_refl 1
    · exact sum_nonneg fun t _ => mul_nonneg (hK s t) (uBdd_nonneg hK 0 t)
    · exact le_refl 0
  | succ k ih =>
    intro s
    rw [uBdd_succ, uBdd_succ (k + 1)]
    split_ifs
    · exact le_refl 1
    · exact sum_le_sum fun t _ =>
        mul_le_mul_of_nonneg_left (ih t) (hK s t)
    · exact le_refl 0

theorem uBdd_mono (hK : ∀ s t, 0 ≤ K s t) (s : α) :
    Monotone fun k => uBdd K A B k s :=
  monotone_nat_of_le_succ fun k => uBdd_le_succ hK k s

def uStar (K : α → α → ℝ) (A B : Finset α) (s : α) : ℝ :=
  ⨆ k, uBdd K A B k s

theorem bddAbove_uBdd (hK : IsMarkov K) (s : α) :
    BddAbove (Set.range fun k => uBdd K A B k s) := by
  refine ⟨1, ?_⟩
  rintro x ⟨k, rfl⟩
  exact uBdd_le_one hK k s

theorem tendsto_uBdd (hK : IsMarkov K) (s : α) :
    Tendsto (fun k => uBdd K A B k s) atTop (𝓝 (uStar K A B s)) :=
  tendsto_atTop_ciSup (uBdd_mono hK.nonneg s) (bddAbove_uBdd hK s)

theorem uBdd_le_uStar (hK : IsMarkov K) (k : ℕ) (s : α) :
    uBdd K A B k s ≤ uStar K A B s :=
  le_ciSup (bddAbove_uBdd hK s) k

theorem uStar_nonneg (hK : IsMarkov K) (s : α) : 0 ≤ uStar K A B s :=
  (uBdd_nonneg hK.nonneg 0 s).trans (uBdd_le_uStar hK 0 s)

theorem uStar_le_one (hK : IsMarkov K) (s : α) : uStar K A B s ≤ 1 :=
  ciSup_le fun k => uBdd_le_one hK k s

theorem uStar_of_mem {s : α} (hs : s ∈ B) : uStar K A B s = 1 := by
  have h : ∀ k : ℕ, uBdd K A B k s = 1 := fun k => uBdd_of_mem hs k
  simp only [uStar, h]
  exact ciSup_const

theorem uStar_dead {s : α} (hsB : s ∉ B) (hsA : s ∉ A) :
    uStar K A B s = 0 := by
  have h : ∀ k : ℕ, uBdd K A B k s = 0 := fun k => uBdd_dead hsB hsA k
  simp only [uStar, h]
  exact ciSup_const

theorem uStar_step (hK : IsMarkov K) {s : α} (hsB : s ∉ B) (hsA : s ∈ A) :
    uStar K A B s = ∑ t, K s t * uStar K A B t := by
  have h1 : Tendsto (fun k => uBdd K A B (k + 1) s) atTop
      (𝓝 (uStar K A B s)) := by
    have hcomp := (tendsto_uBdd (A := A) (B := B) hK s).comp
      (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using hcomp
  have h2 : Tendsto (fun k => ∑ t, K s t * uBdd K A B k t) atTop
      (𝓝 (∑ t, K s t * uStar K A B t)) :=
    tendsto_finsetSum _ fun t _ => (tendsto_uBdd hK t).const_mul (K s t)
  have h3 : (fun k => uBdd K A B (k + 1) s)
      = fun k => ∑ t, K s t * uBdd K A B k t :=
    funext fun k => uBdd_step hsB hsA k
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

theorem uBdd_zero_on_closed (hK : ∀ s t, 0 ≤ K s t) {D : Finset α}
    (hDB : ∀ s ∈ D, s ∉ B)
    (hDcl : ∀ s ∈ D, s ∈ A → ∀ t, 0 < K s t → t ∈ D) :
    ∀ (k : ℕ), ∀ s ∈ D, uBdd K A B k s = 0 := by
  intro k
  induction k with
  | zero => intro s hs; simp [uBdd_zero, hDB s hs]
  | succ k ih =>
    intro s hs
    by_cases hsA : s ∈ A
    · rw [uBdd_step (hDB s hs) hsA]
      refine Finset.sum_eq_zero fun t _ => ?_
      by_cases htD : t ∈ D
      · rw [ih t htD, mul_zero]
      · rcases (hK s t).lt_or_eq with hpos | hzero
        · exact absurd (hDcl s hs hsA t hpos) htD
        · rw [← hzero, zero_mul]
    · exact uBdd_dead (hDB s hs) hsA (k + 1)

theorem uStar_zero_on_closed (hK : ∀ s t, 0 ≤ K s t) {D : Finset α}
    (hDB : ∀ s ∈ D, s ∉ B)
    (hDcl : ∀ s ∈ D, s ∈ A → ∀ t, 0 < K s t → t ∈ D)
    {s : α} (hs : s ∈ D) : uStar K A B s = 0 := by
  have h : ∀ k : ℕ, uBdd K A B k s = 0 := fun k =>
    uBdd_zero_on_closed hK hDB hDcl k s hs
  simp only [uStar, h]
  exact ciSup_const

theorem harmonic_eq_zero_of_exitWitness (hK : IsMarkov K) {Q : Finset α}
    {rank : α → ℕ} {wit : α → α}
    (hwit : ∀ s ∈ Q, 0 < K s (wit s) ∧ (wit s ∉ Q ∨ rank (wit s) < rank s))
    {d : α → ℝ}
    (hd0 : ∀ s, s ∉ Q → d s = 0)
    (hharm : ∀ s ∈ Q, d s = ∑ t, K s t * d t) :
    ∀ s, d s = 0 := by
  rcases Q.eq_empty_or_nonempty with hQ | hQ
  · intro s
    exact hd0 s (by simp [hQ])

  have hQim : (Q.image fun s => |d s|).Nonempty := hQ.image _
  set m := (Q.image fun s => |d s|).max' hQim with hm
  have hle : ∀ s ∈ Q, |d s| ≤ m := fun s hs =>
    Finset.le_max' _ _ (Finset.mem_image_of_mem (fun t => |d t|) hs)
  rcases le_or_gt m 0 with hm0 | hm0
  ·
    intro s
    by_cases hs : s ∈ Q
    · exact abs_eq_zero.mp (le_antisymm ((hle s hs).trans hm0) (abs_nonneg _))
    · exact hd0 s hs
  ·
    exfalso
    have hmmem : m ∈ Q.image fun s => |d s| := Finset.max'_mem _ _
    obtain ⟨s₀, hs₀Q, hs₀⟩ := Finset.mem_image.mp hmmem
    have hBne : (Q.filter fun s => |d s| = m).Nonempty :=
      ⟨s₀, Finset.mem_filter.mpr ⟨hs₀Q, hs₀⟩⟩
    obtain ⟨s, hsB, hsmin⟩ :=
      Finset.exists_min_image (Q.filter fun s => |d s| = m) rank hBne
    obtain ⟨hsQ, hsd⟩ := Finset.mem_filter.mp hsB

    have hsum : ∑ t, K s t * d t = ∑ t ∈ Q, K s t * d t := by
      symm
      refine Finset.sum_subset (Finset.subset_univ Q) fun t _ ht => ?_
      rw [hd0 t ht, mul_zero]

    have h1 : m ≤ ∑ t ∈ Q, K s t * |d t| := by
      calc m = |d s| := hsd.symm
        _ = |∑ t ∈ Q, K s t * d t| := by rw [hharm s hsQ, hsum]
        _ ≤ ∑ t ∈ Q, |K s t * d t| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ t ∈ Q, K s t * |d t| := by
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [abs_mul, abs_of_nonneg (hK.nonneg s t)]
    have h2 : ∑ t ∈ Q, K s t * |d t| ≤ (∑ t ∈ Q, K s t) * m := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun t ht =>
        mul_le_mul_of_nonneg_left (hle t ht) (hK.nonneg s t)
    have hQrow : ∑ t ∈ Q, K s t ≤ 1 := by
      calc ∑ t ∈ Q, K s t
          ≤ ∑ t, K s t :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Q)
              fun t _ _ => hK.nonneg s t
        _ = 1 := hK.rowSum s
    have h3 : (∑ t ∈ Q, K s t) * m ≤ m := by
      calc (∑ t ∈ Q, K s t) * m ≤ 1 * m :=
            mul_le_mul_of_nonneg_right hQrow hm0.le
        _ = m := one_mul m

    have hS2 : (∑ t ∈ Q, K s t) * m = m := le_antisymm h3 (h1.trans h2)
    have hrow1 : ∑ t ∈ Q, K s t = 1 := by
      have hfac : (∑ t ∈ Q, K s t - 1) * m = 0 := by linarith
      rcases mul_eq_zero.mp hfac with h | h
      · linarith
      · exact absurd h hm0.ne'
    have hoff : ∀ t, t ∉ Q → K s t = 0 := by
      intro t ht
      have hsplit : (∑ t ∈ Q, K s t) + ∑ t ∈ Qᶜ, K s t = 1 := by
        rw [Finset.sum_add_sum_compl]
        exact hK.rowSum s
      have hcompl : ∑ t ∈ Qᶜ, K s t = 0 := by linarith
      exact (Finset.sum_eq_zero_iff_of_nonneg
        fun t' _ => hK.nonneg s t').mp hcompl t (Finset.mem_compl.mpr ht)

    have hS1 : ∑ t ∈ Q, K s t * |d t| = (∑ t ∈ Q, K s t) * m :=
      le_antisymm h2 (by rw [hrow1, one_mul]; exact h1)
    have hterm : ∀ t ∈ Q, K s t * (m - |d t|) = 0 := by
      have hz : ∑ t ∈ Q, K s t * (m - |d t|) = 0 := by
        have hexp : ∑ t ∈ Q, K s t * (m - |d t|)
            = (∑ t ∈ Q, K s t) * m - ∑ t ∈ Q, K s t * |d t| := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun t _ => by ring
        rw [hexp, hS1]
        ring
      intro t ht
      exact (Finset.sum_eq_zero_iff_of_nonneg fun t' ht' =>
        mul_nonneg (hK.nonneg s t') (sub_nonneg.mpr (hle t' ht'))).mp hz t ht

    obtain ⟨hwpos, hwalt⟩ := hwit s hsQ
    have hwQ : wit s ∈ Q := by
      by_contra hw
      exact absurd (hoff _ hw) hwpos.ne'
    have hwrank : rank (wit s) < rank s :=
      hwalt.resolve_left fun h => h hwQ
    have hwm : |d (wit s)| = m := by
      rcases mul_eq_zero.mp (hterm _ hwQ) with h | h
      · exact absurd h hwpos.ne'
      · linarith [sub_eq_zero.mp h]
    exact absurd (hsmin _ (Finset.mem_filter.mpr ⟨hwQ, hwm⟩))
      (not_le.mpr hwrank)

theorem solve_cert_exact (hK : IsMarkov K) {Q : Finset α} {x : α → ℝ}
    {rank : α → ℕ} {wit : α → α}
    (hQA : Q ⊆ A) (hQB : ∀ s ∈ Q, s ∉ B)
    (hxB : ∀ s ∈ B, x s = 1)
    (hxD : ∀ s, s ∉ B → s ∉ Q → x s = 0)
    (hres : ∀ s ∈ Q, x s = ∑ t, K s t * x t)
    (hcl : ∀ s, s ∉ B → s ∉ Q → s ∈ A → ∀ t, 0 < K s t → t ∉ B ∧ t ∉ Q)
    (hwit : ∀ s ∈ Q, 0 < K s (wit s) ∧ (wit s ∉ Q ∨ rank (wit s) < rank s)) :
    ∀ s, x s = uStar K A B s := by

  set D : Finset α := Finset.univ \ (B ∪ Q) with hD
  have hDmem : ∀ s, s ∈ D ↔ s ∉ B ∧ s ∉ Q := by
    intro s
    simp [hD, Finset.mem_sdiff, Finset.mem_union, not_or]
  have hDB : ∀ s ∈ D, s ∉ B := fun s hs => ((hDmem s).mp hs).1
  have hDcl : ∀ s ∈ D, s ∈ A → ∀ t, 0 < K s t → t ∈ D := by
    intro s hs hsA t hpos
    obtain ⟨h1, h2⟩ := (hDmem s).mp hs
    obtain ⟨h3, h4⟩ := hcl s h1 h2 hsA t hpos
    exact (hDmem t).mpr ⟨h3, h4⟩

  have huB : ∀ s ∈ B, uStar K A B s = 1 := fun s hs => uStar_of_mem hs
  have huD : ∀ s ∈ D, uStar K A B s = 0 := fun s hs =>
    uStar_zero_on_closed hK.nonneg hDB hDcl hs
  have hustep : ∀ s ∈ Q, uStar K A B s = ∑ t, K s t * uStar K A B t :=
    fun s hs => uStar_step hK (hQB s hs) (hQA hs)

  set d : α → ℝ := fun s => x s - uStar K A B s with hd
  have hd0 : ∀ s, s ∉ Q → d s = 0 := by
    intro s hs
    by_cases hsB : s ∈ B
    · simp [hd, hxB s hsB, huB s hsB]
    · have hsD : s ∈ D := (hDmem s).mpr ⟨hsB, hs⟩
      simp [hd, hxD s hsB hs, huD s hsD]
  have hharm : ∀ s ∈ Q, d s = ∑ t, K s t * d t := by
    intro s hs
    have hsplit : ∑ t, K s t * d t
        = (∑ t, K s t * x t) - ∑ t, K s t * uStar K A B t := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ => by simp [hd]; ring
    rw [hsplit, ← hres s hs, ← hustep s hs]
  have hzero := harmonic_eq_zero_of_exitWitness hK hwit hd0 hharm
  intro s
  have hs := hzero s
  simp only [hd] at hs
  linarith

theorem table_exact {V : ℕ → α → ℝ} {T : ℕ}
    (h0 : ∀ s, V 0 s = if s ∈ B then 1 else 0)
    (hstep : ∀ k < T, ∀ s, V (k + 1) s =
      if s ∈ B then 1
      else if s ∈ A then ∑ t, K s t * V k t
      else 0) :
    ∀ k ≤ T, ∀ s, V k s = uBdd K A B k s := by
  intro k
  induction k with
  | zero => intro _ s; rw [h0 s, uBdd_zero]
  | succ k ih =>
    intro hk s
    have hk' : k < T := Nat.lt_of_succ_le hk
    have hV : ∀ t, V k t = uBdd K A B k t := ih hk'.le
    rw [hstep k hk' s, uBdd_succ]
    simp only [hV]

theorem table_le (hK : ∀ s t, 0 ≤ K s t) {V : ℕ → α → ℝ} {T : ℕ}
    (h0 : ∀ s, V 0 s ≤ if s ∈ B then 1 else 0)
    (hstep : ∀ k < T, ∀ s, V (k + 1) s ≤
      if s ∈ B then 1
      else if s ∈ A then ∑ t, K s t * V k t
      else 0) :
    ∀ k ≤ T, ∀ s, V k s ≤ uBdd K A B k s := by
  intro k
  induction k with
  | zero => intro _ s; rw [uBdd_zero]; exact h0 s
  | succ k ih =>
    intro hk s
    have hk' : k < T := Nat.lt_of_succ_le hk
    refine (hstep k hk' s).trans ?_
    rw [uBdd_succ]
    split_ifs
    · exact le_refl 1
    · exact Finset.sum_le_sum fun t _ =>
        mul_le_mul_of_nonneg_left (ih hk'.le t) (hK s t)
    · exact le_refl 0

def nextVec (K : α → α → ℝ) (B : Finset α) (s : α) : ℝ := ∑ t ∈ B, K s t

theorem nextVec_eq_law_one (s : α) :
    nextVec K B s = ∑ a ∈ B, law K (pointMass s) 1 a := by
  have h : ∀ a : α, law K (pointMass s) 1 a = K s a := by
    intro a
    show step K (law K (pointMass s) 0) a = K s a
    rw [show law K (pointMass s) 0 = pointMass s from rfl, step_pointMass]
  simp only [h, nextVec]

def frozen (K : α → α → ℝ) (A B : Finset α) : α → α → ℝ :=
  fun s t => if s ∈ A ∧ s ∉ B then K s t else if t = s then 1 else 0

theorem isMarkov_frozen (hK : IsMarkov K) : IsMarkov (frozen K A B) := by
  constructor
  · intro s t
    unfold frozen
    split_ifs
    · exact hK.nonneg s t
    · exact zero_le_one
    · exact le_refl 0
  · intro s
    unfold frozen
    by_cases h : s ∈ A ∧ s ∉ B
    · simp only [h]
      exact hK.rowSum s
    · simp [h]

theorem uBdd_eq_absorbedMass :
    ∀ (k : ℕ) (s : α),
      uBdd K A B k s = ∑ a ∈ B, law (frozen K A B) (pointMass s) k a := by
  intro k
  induction k with
  | zero =>
    intro s
    show uBdd K A B 0 s = ∑ a ∈ B, pointMass s a
    rw [uBdd_zero]
    unfold pointMass
    rw [Finset.sum_ite_eq' B s fun _ => (1 : ℝ)]
  | succ k ih =>
    intro s

    have hpeel : ∀ a : α, law (frozen K A B) (pointMass s) (k + 1) a
        = law (frozen K A B) (frozen K A B s) k a := by
      intro a
      have h1 : law (frozen K A B) (pointMass s) (1 + k)
          = law (frozen K A B) (law (frozen K A B) (pointMass s) 1) k :=
        law_add (frozen K A B) (pointMass s) 1 k
      have h2 : law (frozen K A B) (pointMass s) 1 = frozen K A B s := by
        show step (frozen K A B) (law (frozen K A B) (pointMass s) 0)
            = frozen K A B s
        rw [show law (frozen K A B) (pointMass s) 0 = pointMass s from rfl,
          step_pointMass]
      rw [Nat.add_comm k 1, h1, h2]

    have hlin : ∑ a ∈ B, law (frozen K A B) (pointMass s) (k + 1) a
        = ∑ t, frozen K A B s t * uBdd K A B k t := by
      calc ∑ a ∈ B, law (frozen K A B) (pointMass s) (k + 1) a
          = ∑ a ∈ B, law (frozen K A B) (frozen K A B s) k a := by
            exact Finset.sum_congr rfl fun a _ => hpeel a
        _ = ∑ a ∈ B, ∑ t, frozen K A B s t
              * law (frozen K A B) (pointMass t) k a := by
            exact Finset.sum_congr rfl fun a _ =>
              law_eq_sum_pointMass k a
        _ = ∑ t, frozen K A B s t
              * ∑ a ∈ B, law (frozen K A B) (pointMass t) k a := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun t _ => by
              rw [Finset.mul_sum]
        _ = ∑ t, frozen K A B s t * uBdd K A B k t := by
            exact Finset.sum_congr rfl fun t _ => by rw [← ih t]
    rw [hlin]

    by_cases hlive : s ∈ A ∧ s ∉ B
    · have hfr : ∀ t, frozen K A B s t = K s t := by
        intro t
        unfold frozen
        rw [if_pos hlive]
      simp only [hfr]
      rw [uBdd_step hlive.2 hlive.1]
    · have hfr : ∀ t, frozen K A B s t = if t = s then 1 else 0 := by
        intro t
        unfold frozen
        rw [if_neg hlive]
      simp only [hfr, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ s fun t => uBdd K A B k t]
      simp only [Finset.mem_univ, if_true]

      by_cases hsB : s ∈ B
      · rw [uBdd_of_mem hsB, uBdd_of_mem hsB]
      · have hsA : s ∉ A := fun hsA => hlive ⟨hsA, hsB⟩
        rw [uBdd_dead hsB hsA, uBdd_dead hsB hsA]

theorem tendsto_absorbedMass_uStar (hK : IsMarkov K) (s : α) :
    Tendsto (fun k => ∑ a ∈ B, law (frozen K A B) (pointMass s) k a)
      atTop (𝓝 (uStar K A B s)) := by
  have h := tendsto_uBdd (A := A) (B := B) hK s
  have heq : (fun k => uBdd K A B k s)
      = fun k => ∑ a ∈ B, law (frozen K A B) (pointMass s) k a :=
    funext fun k => uBdd_eq_absorbedMass k s
  rwa [heq] at h

section RatCert

variable {P : α → α → ℚ} {xq : α → ℚ}

omit [DecidableEq α] in

theorem isMarkov_cast (hP : ∀ s t, 0 ≤ P s t) (hrow : ∀ s, ∑ t, P s t = 1) :
    IsMarkov fun s t => ((P s t : ℚ) : ℝ) := by
  constructor
  · intro s t
    exact_mod_cast hP s t
  · intro s
    exact_mod_cast hrow s

theorem solve_cert_exact_rat
    (hP : ∀ s t, 0 ≤ P s t) (hrow : ∀ s, ∑ t, P s t = 1)
    {Q : Finset α} {rank : α → ℕ} {wit : α → α}
    (hQA : Q ⊆ A) (hQB : ∀ s ∈ Q, s ∉ B)
    (hxB : ∀ s ∈ B, xq s = 1)
    (hxD : ∀ s, s ∉ B → s ∉ Q → xq s = 0)
    (hres : ∀ s ∈ Q, xq s = ∑ t, P s t * xq t)
    (hcl : ∀ s, s ∉ B → s ∉ Q → s ∈ A → ∀ t, 0 < P s t → t ∉ B ∧ t ∉ Q)
    (hwit : ∀ s ∈ Q, 0 < P s (wit s) ∧ (wit s ∉ Q ∨ rank (wit s) < rank s)) :
    ∀ s, (xq s : ℝ) = uStar (fun s t => ((P s t : ℚ) : ℝ)) A B s := by
  refine solve_cert_exact (rank := rank) (wit := wit)
    (isMarkov_cast hP hrow) hQA hQB ?_ ?_ ?_ ?_ ?_
  · intro s hs
    exact_mod_cast hxB s hs
  · intro s hsB hsQ
    exact_mod_cast hxD s hsB hsQ
  · intro s hs
    exact_mod_cast hres s hs
  · intro s hsB hsQ hsA t hpos
    exact hcl s hsB hsQ hsA t (by exact_mod_cast hpos)
  · intro s hs
    obtain ⟨hpos, halt⟩ := hwit s hs
    exact ⟨by exact_mod_cast hpos, halt⟩

theorem satSet_exact_rat
    (hP : ∀ s t, 0 ≤ P s t) (hrow : ∀ s, ∑ t, P s t = 1)
    {Q : Finset α} {rank : α → ℕ} {wit : α → α}
    (hQA : Q ⊆ A) (hQB : ∀ s ∈ Q, s ∉ B)
    (hxB : ∀ s ∈ B, xq s = 1)
    (hxD : ∀ s, s ∉ B → s ∉ Q → xq s = 0)
    (hres : ∀ s ∈ Q, xq s = ∑ t, P s t * xq t)
    (hcl : ∀ s, s ∉ B → s ∉ Q → s ∈ A → ∀ t, 0 < P s t → t ∉ B ∧ t ∉ Q)
    (hwit : ∀ s ∈ Q, 0 < P s (wit s) ∧ (wit s ∉ Q ∨ rank (wit s) < rank s))
    (p : ℚ) (s : α) :
    p ≤ xq s ↔ (p : ℝ) ≤ uStar (fun s t => ((P s t : ℚ) : ℝ)) A B s := by
  rw [← solve_cert_exact_rat hP hrow hQA hQB hxB hxD hres hcl hwit s]
  exact_mod_cast Iff.rfl

end RatCert

def untilEventBdd (A' B' : Set α) (T : ℕ) : Set (ℕ → α) :=
  {ω | ∃ k ≤ T, ω k ∈ B' ∧ ∀ j < k, ω j ∈ A'}

def TrajBridgeStatement : Prop :=
  ∀ (S : Type) (_ : Fintype S) (_ : DecidableEq S)
    (_ : MeasurableSpace S) (_ : MeasurableSingletonClass S)
    (Kq : S → S → ℝ) (_ : IsMarkov Kq)
    (K : ProbabilityTheory.Kernel S S) (_ : ProbabilityTheory.IsMarkovKernel K),
    (∀ s t : S, K s {t} = ENNReal.ofReal (Kq s t)) →
    ∀ (A B : Finset S) (x : S) (T : ℕ),
      Battery.pathMeasure K x (untilEventBdd (↑A) (↑B) T)
        = ENNReal.ofReal (uBdd Kq A B T x)

end

end Tabular

end Qtsl
