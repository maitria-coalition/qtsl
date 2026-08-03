import Qtsl.Behavioral
import Mathlib.NumberTheory.Real.Irrational

/-!
# Timed-core soundness lemmas

Mechanized soundness for three timed-core axiom schemata that are not
admissible in the untimed fragment (each carries a machine independence
witness elsewhere): the time-uniformity schema and the two
first-service schemata. Builds on the behavioural floor, adding fusion
closure as a `Prop`-valued mixin (`Behavior.FusionClosed`) demanded
only where a schema genuinely needs it.
-/

namespace PPLC
namespace Qtsl

open scoped NNReal
open Set

noncomputable section

variable {X : Type*}

def fuseAt (γ : ℝ≥0 → X) (s : ℝ≥0) (σ : ℝ≥0 → X) : ℝ≥0 → X :=
  fun t => if t < s then γ t else σ (t - s)

def Behavior.FusionClosed (B : Behavior X) : Prop :=
  ∀ γ ∈ B.fwd, ∀ s : ℝ≥0, ∀ σ ∈ B.fwd, σ 0 = γ s →
    fuseAt γ s σ ∈ B.fwd

def Behavior.AService (B : Behavior X) (T : ℝ≥0) (φ : Set X) (x : X) : Prop :=
  ∀ γ ∈ B.fwd, γ 0 = x → ∀ ε : ℝ≥0, 0 < ε → ∃ t, t < T + ε ∧ γ t ∈ φ

def Behavior.BoxInv (B : Behavior X) (φ : Set X) (x : X) : Prop :=
  ∀ γ ∈ B.fwd, γ 0 = x → ∀ t : ℝ≥0, γ t ∈ φ

def Behavior.FirstVisits (B : Behavior X) (φ : Set X) : Prop :=
  ∀ γ ∈ B.fwd, (∃ t, γ t ∈ φ) → ∃ t₀, γ t₀ ∈ φ ∧ ∀ t, γ t ∈ φ → t₀ ≤ t

def Behavior.fsTarget (B : Behavior X) {n : ℕ}
    (α : Fin n → Set X) (T : Fin n → ℝ≥0) : Set X :=
  ⋃ i, α i ∩ {y | ∀ j, j ≠ i → B.AService (T j) (α j) y}

def Behavior.residualCell (B : Behavior X) {n : ℕ}
    (α : Fin n → Set X) (T : Fin n → ℝ≥0) (c : ℝ≥0) : Set X :=
  {y | ∀ i, B.AService (T i - c) (α i) y}

theorem sound_u10f (B : Behavior X) (T : ℝ≥0) (ν χ : Set X) (x : X)
    (hbox : B.BoxInv ν x) :
    B.AService T (χ ∩ ν) x ↔ B.AService T χ x := by
  constructor
  ·
    intro h γ hγ hγ0 ε hε
    obtain ⟨t, ht, htmem⟩ := h γ hγ hγ0 ε hε
    exact ⟨t, ht, htmem.1⟩
  ·
    intro h γ hγ hγ0 ε hε
    obtain ⟨t, ht, htmem⟩ := h γ hγ hγ0 ε hε
    exact ⟨t, ht, htmem, hbox γ hγ hγ0 t⟩

section FirstService

variable (B : Behavior X) {n : ℕ}

private lemma exists_first_visit (α : Fin n → Set X) (T : Fin n → ℝ≥0)
    {x : X} (hatt : ∀ i, B.FirstVisits (α i))
    (hx : ∀ i, B.AService (T i) (α i) x)
    {γ : ℝ≥0 → X} (hγ : γ ∈ B.fwd) (hγ0 : γ 0 = x) (i : Fin n) :
    ∃ t₀, γ t₀ ∈ α i ∧ (∀ t, γ t ∈ α i → t₀ ≤ t) ∧ t₀ ≤ T i := by
  obtain ⟨t, -, htmem⟩ := hx i γ hγ hγ0 1 one_pos
  obtain ⟨t₀, ht₀, hmin⟩ := hatt i γ hγ ⟨t, htmem⟩
  refine ⟨t₀, ht₀, hmin, ?_⟩

  by_contra hgt
  push Not at hgt
  obtain ⟨s, hs, hsmem⟩ := hx i γ hγ hγ0 (t₀ - T i) (tsub_pos_of_lt hgt)
  have h1 : t₀ ≤ s := hmin s hsmem
  have h2 : s < t₀ := by
    calc s < T i + (t₀ - T i) := hs
    _ = t₀ := add_tsub_cancel_of_le hgt.le
  exact absurd h1 (not_le.mpr h2)

private lemma exists_served_point (hB3 : B.FusionClosed) (hn : 0 < n)
    (α : Fin n → Set X) (T : Fin n → ℝ≥0) {x : X}
    (hatt : ∀ i, B.FirstVisits (α i))
    (hx : ∀ i, B.AService (T i) (α i) x)
    {γ : ℝ≥0 → X} (hγ : γ ∈ B.fwd) (hγ0 : γ 0 = x) :
    ∃ tstar : ℝ≥0,
      γ tstar ∈ B.fsTarget α T ∧
      (∀ i s, γ s ∈ α i → tstar ≤ s) ∧
      tstar ≤ Finset.univ.inf' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) T := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩

  have hfv := fun i => exists_first_visit B α T hatt hx hγ hγ0 i
  choose tv htv hmin htle using hfv
  have H : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩

  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_inf' H tv
  set tstar := Finset.univ.inf' H tv with htstar
  have htstar_le : ∀ i, tstar ≤ tv i := fun i =>
    Finset.inf'_le _ (Finset.mem_univ i)
  have hglobal : ∀ i s, γ s ∈ α i → tstar ≤ s := fun i s hs =>
    (htstar_le i).trans (hmin i s hs)
  have hbound : tstar ≤ Finset.univ.inf' H T := by
    apply Finset.le_inf'
    intro j _
    exact (htstar_le j).trans (htle j)
  refine ⟨tstar, ?_, hglobal, hbound⟩

  refine Set.mem_iUnion.mpr ⟨i₀, ?_, ?_⟩
  ·
    rw [hi₀]
    exact htv i₀
  ·
    intro j hj σ hσ hσ0 ε hε

    have hρ : fuseAt γ tstar σ ∈ B.fwd := hB3 γ hγ tstar σ hσ hσ0
    have hρ0 : fuseAt γ tstar σ 0 = x := by
      by_cases h0 : (0 : ℝ≥0) < tstar
      · simpa [fuseAt, h0] using hγ0
      · have hz : tstar = 0 := le_antisymm (not_lt.mp h0) zero_le
        rw [hz] at hσ0
        simp [fuseAt, hz, hσ0, hγ0]
    obtain ⟨s, hs, hsmem⟩ := hx j (fuseAt γ tstar σ) hρ hρ0 ε hε
    by_cases hcase : s < tstar
    ·
      exfalso
      have heqs : fuseAt γ tstar σ s = γ s := by simp [fuseAt, hcase]
      rw [heqs] at hsmem
      exact absurd (hglobal j s hsmem) (not_le.mpr hcase)
    ·
      have heq : fuseAt γ tstar σ s = σ (s - tstar) := by
        simp [fuseAt, hcase]
      exact ⟨s - tstar, lt_of_le_of_lt tsub_le_self hs, heq ▸ hsmem⟩

theorem sound_firstService (hB3 : B.FusionClosed) (hn : 0 < n)
    (α : Fin n → Set X) (T : Fin n → ℝ≥0) (x : X)
    (hatt : ∀ i, B.FirstVisits (α i))
    (hx : ∀ i, B.AService (T i) (α i) x) :
    B.AService (Finset.univ.inf' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) T)
      (B.fsTarget α T) x := by
  intro γ hγ hγ0 ε hε
  obtain ⟨tstar, hmem, -, hbound⟩ :=
    exists_served_point B hB3 hn α T hatt hx hγ hγ0
  exact ⟨tstar, lt_of_le_of_lt hbound (lt_add_of_pos_right _ hε), hmem⟩

theorem sound_fsResidual (hB3 : B.FusionClosed) (hn : 0 < n)
    (α : Fin n → Set X) (T : Fin n → ℝ≥0) (c : ℝ≥0) (x : X)
    (hc : ∀ i, c < T i)
    (hatt : ∀ i, B.FirstVisits (α i))
    (hx : ∀ i, B.AService (T i) (α i) x) :
    B.AService c (B.fsTarget α T ∪ B.residualCell α T c) x := by
  intro γ hγ hγ0 ε hε
  obtain ⟨tstar, hmem, hglobal, -⟩ :=
    exists_served_point B hB3 hn α T hatt hx hγ hγ0
  by_cases hsplit : tstar ≤ c
  ·
    exact ⟨tstar, lt_of_le_of_lt hsplit (lt_add_of_pos_right _ hε),
      Set.mem_union_left _ hmem⟩
  ·
    push Not at hsplit
    refine ⟨c, lt_add_of_pos_right _ hε, Set.mem_union_right _ ?_⟩
    intro i σ hσ hσ0 ε' hε'
    have hρ : fuseAt γ c σ ∈ B.fwd := hB3 γ hγ c σ hσ hσ0
    have hρ0 : fuseAt γ c σ 0 = x := by
      by_cases h0 : (0 : ℝ≥0) < c
      · simpa [fuseAt, h0] using hγ0
      · have hz : c = 0 := le_antisymm (not_lt.mp h0) zero_le
        rw [hz] at hσ0
        simp [fuseAt, hz, hσ0, hγ0]
    obtain ⟨s, hs, hsmem⟩ := hx i (fuseAt γ c σ) hρ hρ0 ε' hε'
    by_cases hcase : s < c
    ·
      exfalso
      have heqs : fuseAt γ c σ s = γ s := by simp [fuseAt, hcase]
      rw [heqs] at hsmem
      exact absurd (hglobal i s hsmem)
        (not_le.mpr (lt_trans hcase hsplit))
    ·
      push Not at hcase
      have heq : fuseAt γ c σ s = σ (s - c) := by
        simp [fuseAt, not_lt.mpr hcase]
      refine ⟨s - c, ?_, heq ▸ hsmem⟩

      rw [tsub_lt_iff_right hcase]
      calc s < T i + ε' := hs
      _ = (T i - c) + c + ε' := by rw [tsub_add_cancel_of_le (hc i).le]
      _ = (T i - c) + ε' + c := add_right_comm _ _ _

end FirstService

namespace TimedCoreCountermodel

inductive EState : Type
  | spine (p : ℝ≥0)
  | sink

open EState

def stay (p : ℝ≥0) : ℝ≥0 → EState := fun u => spine (p + u)

def esc (p s : ℝ≥0) : ℝ≥0 → EState :=
  fun u => if p + u ≤ s then spine (p + u) else sink

def sinkRun : ℝ≥0 → EState := fun _ => sink

def EFwd : Set (ℝ≥0 → EState) :=
  {γ | (∃ p, γ = stay p) ∨
       (∃ p s, p ≤ s ∧ 1 < s ∧ γ = esc p s) ∨
       γ = sinkRun}

lemma mem_EFwd {γ : ℝ≥0 → EState} :
    γ ∈ EFwd ↔
      (∃ p, γ = stay p) ∨
      (∃ p s, p ≤ s ∧ 1 < s ∧ γ = esc p s) ∨
      γ = sinkRun :=
  Iff.rfl

lemma stay_mem (p : ℝ≥0) : stay p ∈ EFwd := Or.inl ⟨p, rfl⟩

lemma esc_mem {p s : ℝ≥0} (hps : p ≤ s) (h1 : 1 < s) : esc p s ∈ EFwd :=
  Or.inr (Or.inl ⟨p, s, hps, h1, rfl⟩)

lemma sinkRun_mem : sinkRun ∈ EFwd := Or.inr (Or.inr rfl)

lemma stay_shift (p u : ℝ≥0) :
    (fun t : ℝ≥0 => stay p (u + t)) = stay (p + u) := by
  funext t
  simp only [stay, ← add_assoc]

lemma esc_shift (p s u : ℝ≥0) :
    (fun t : ℝ≥0 => esc p s (u + t)) =
      if p + u ≤ s then esc (p + u) s else sinkRun := by
  by_cases h : p + u ≤ s
  · rw [if_pos h]
    funext t
    simp only [esc, ← add_assoc]
  · rw [if_neg h]
    funext t
    have hnot : ¬ p + (u + t) ≤ s := fun hle =>
      h ((add_le_add_right le_self_add p).trans hle)
    simp [esc, sinkRun, hnot]

def EB : Behavior EState where
  fwd := EFwd
  cpl := ∅
  shift_fwd := by
    intro γ hγ u
    rcases mem_EFwd.mp hγ with ⟨p, rfl⟩ | ⟨p, s, hps, h1, rfl⟩ | rfl
    · rw [stay_shift]
      exact stay_mem (p + u)
    · rw [esc_shift]
      by_cases h : p + u ≤ s
      · rw [if_pos h]
        exact esc_mem h h1
      · rw [if_neg h]
        exact sinkRun_mem
    · exact sinkRun_mem
  shift_cpl := fun γ hγ => absurd hγ (Set.notMem_empty γ)
  restrict_cpl := fun γ hγ => absurd hγ (Set.notMem_empty γ)

lemma fuseAt_sinkRun {γ : ℝ≥0 → EState} {u : ℝ≥0}
    (hsunk : ∀ t, u ≤ t → γ t = sink) :
    fuseAt γ u sinkRun = γ := by
  funext t
  by_cases h : t < u
  · simp [fuseAt, h]
  · simp [fuseAt, h, sinkRun, hsunk t (not_lt.mp h)]

lemma fuse_stay_stay (p u : ℝ≥0) :
    fuseAt (stay p) u (stay (p + u)) = stay p := by
  funext t
  simp only [fuseAt, stay]
  by_cases ht : t < u
  · rw [if_pos ht]
  · rw [if_neg ht, add_assoc, add_tsub_cancel_of_le (not_lt.mp ht)]

lemma fuse_stay_esc (p u s' : ℝ≥0) (h : p + u ≤ s') :
    fuseAt (stay p) u (esc (p + u) s') = esc p s' := by
  funext t
  simp only [fuseAt, stay, esc]
  by_cases ht : t < u
  · rw [if_pos ht, if_pos ((add_le_add_right ht.le p).trans h)]
  · rw [if_neg ht, add_assoc, add_tsub_cancel_of_le (not_lt.mp ht)]

lemma fuse_esc_stay (p s0 u : ℝ≥0) (h : p + u ≤ s0) :
    fuseAt (esc p s0) u (stay (p + u)) = stay p := by
  funext t
  simp only [fuseAt, esc, stay]
  by_cases ht : t < u
  · rw [if_pos ht, if_pos ((add_le_add_right ht.le p).trans h)]
  · rw [if_neg ht, add_assoc, add_tsub_cancel_of_le (not_lt.mp ht)]

lemma fuse_esc_esc (p s0 u s' : ℝ≥0) (h0 : p + u ≤ s0) (h' : p + u ≤ s') :
    fuseAt (esc p s0) u (esc (p + u) s') = esc p s' := by
  funext t
  simp only [fuseAt, esc]
  by_cases ht : t < u
  · rw [if_pos ht, if_pos ((add_le_add_right ht.le p).trans h0),
      if_pos ((add_le_add_right ht.le p).trans h')]
  · rw [if_neg ht, add_assoc, add_tsub_cancel_of_le (not_lt.mp ht)]

lemma stay_param_of_anchor {p' q : ℝ≥0} (h : stay p' 0 = spine q) :
    p' = q := by
  simpa [stay] using h

lemma esc_param_of_anchor {p' s' q : ℝ≥0} (hps' : p' ≤ s')
    (h : esc p' s' 0 = spine q) : p' = q := by
  simpa [esc, hps'] using h

lemma eq_sinkRun_of_anchor_sink {σ : ℝ≥0 → EState} (hσ : σ ∈ EFwd)
    (h0 : σ 0 = sink) : σ = sinkRun := by
  rcases mem_EFwd.mp hσ with ⟨p', rfl⟩ | ⟨p', s', hps', h1', rfl⟩ | rfl
  · simp [stay] at h0
  · simp [esc, hps'] at h0
  · rfl

lemma EB_fusionClosed : EB.FusionClosed := by
  intro γ hγ u σ hσ hanchor
  rcases mem_EFwd.mp hγ with ⟨p, rfl⟩ | ⟨p, s0, hps, h1, rfl⟩ | rfl
  ·
    have hu : stay p u = spine (p + u) := rfl
    rcases mem_EFwd.mp hσ with ⟨p', rfl⟩ | ⟨p', s', hps', h1', rfl⟩ | rfl
    · have hp' : p' = p + u := stay_param_of_anchor (hanchor.trans hu)
      subst hp'
      rw [fuse_stay_stay]
      exact stay_mem p
    · have hp' : p' = p + u := esc_param_of_anchor hps' (hanchor.trans hu)
      subst hp'
      rw [fuse_stay_esc p u s' hps']
      exact esc_mem (le_self_add.trans hps') h1'
    · exact absurd (hanchor.trans hu) (by simp [sinkRun])
  ·
    by_cases hride : p + u ≤ s0
    ·
      have hu : esc p s0 u = spine (p + u) := by simp [esc, hride]
      rcases mem_EFwd.mp hσ with ⟨p', rfl⟩ | ⟨p', s', hps', h1', rfl⟩ | rfl
      · have hp' : p' = p + u := stay_param_of_anchor (hanchor.trans hu)
        subst hp'
        rw [fuse_esc_stay p s0 u hride]
        exact stay_mem p
      · have hp' : p' = p + u := esc_param_of_anchor hps' (hanchor.trans hu)
        subst hp'
        rw [fuse_esc_esc p s0 u s' hride hps']
        exact esc_mem (le_self_add.trans hps') h1'
      · exact absurd (hanchor.trans hu) (by simp [sinkRun])
    ·
      have hu : esc p s0 u = sink := by simp [esc, hride]
      have hσeq : σ = sinkRun := eq_sinkRun_of_anchor_sink hσ (hanchor.trans hu)
      subst hσeq
      have hfuse : fuseAt (esc p s0) u sinkRun = esc p s0 := by
        apply fuseAt_sinkRun
        intro w hw
        have hnot : ¬ p + w ≤ s0 := fun hle =>
          hride ((add_le_add_right hw p).trans hle)
        simp [esc, hnot]
      rw [hfuse]
      exact esc_mem hps h1
  ·
    have hσeq : σ = sinkRun := eq_sinkRun_of_anchor_sink hσ hanchor
    subst hσeq
    have hfuse : fuseAt sinkRun u sinkRun = sinkRun :=
      fuseAt_sinkRun fun t _ => rfl
    rw [hfuse]
    exact sinkRun_mem

def IsRatNN (p : ℝ≥0) : Prop := ∃ q : ℚ, (q : ℝ) = (p : ℝ)

def Ea : Set EState :=
  {y | ∃ p : ℝ≥0, y = spine p ∧ 1 < p ∧ p < 2 ∧ IsRatNN p}

def Eb : Set EState :=
  {y | ∃ p : ℝ≥0, y = spine p ∧ 1 < p ∧ p < 2 ∧ ¬ IsRatNN p}

lemma mem_Ea {y : EState} :
    y ∈ Ea ↔ ∃ p : ℝ≥0, y = spine p ∧ 1 < p ∧ p < 2 ∧ IsRatNN p :=
  Iff.rfl

lemma mem_Eb {y : EState} :
    y ∈ Eb ↔ ∃ p : ℝ≥0, y = spine p ∧ 1 < p ∧ p < 2 ∧ ¬ IsRatNN p :=
  Iff.rfl

def Eα : Fin 2 → Set EState := fun i => if i = 0 then Ea else Eb

lemma dense_visits {γ : ℝ≥0 → EState} {b : ℝ≥0} (h1b : 1 < b) (hb2 : b ≤ 2)
    (hride : ∀ t : ℝ≥0, 1 < t → t < b → γ t = spine t) :
    (∃ t, t < 2 ∧ γ t ∈ Ea) ∧ (∃ t, t < 2 ∧ γ t ∈ Eb) := by
  have h1bR : (1 : ℝ) < (b : ℝ) := by exact_mod_cast h1b
  constructor
  ·
    obtain ⟨q, hq1, hqb⟩ := exists_rat_btwn h1bR
    have h0r : (0 : ℝ) ≤ (q : ℝ) := le_of_lt (lt_trans one_pos hq1)
    set t : ℝ≥0 := Real.toNNReal (q : ℝ) with htdef
    have hcoe : (t : ℝ) = (q : ℝ) := Real.coe_toNNReal _ h0r
    have h1t : (1 : ℝ≥0) < t := by
      rw [← NNReal.coe_lt_coe, NNReal.coe_one, hcoe]
      exact hq1
    have htb : t < b := by
      rw [← NNReal.coe_lt_coe, hcoe]
      exact hqb
    have ht2 : t < 2 := lt_of_lt_of_le htb hb2
    refine ⟨t, ht2, ?_⟩
    rw [hride t h1t htb]
    exact mem_Ea.mpr ⟨t, rfl, h1t, ht2, q, hcoe.symm⟩
  ·
    obtain ⟨r, hirr, hr1, hrb⟩ := exists_irrational_btwn h1bR
    have h0r : (0 : ℝ) ≤ r := le_of_lt (lt_trans one_pos hr1)
    set t : ℝ≥0 := Real.toNNReal r with htdef
    have hcoe : (t : ℝ) = r := Real.coe_toNNReal _ h0r
    have h1t : (1 : ℝ≥0) < t := by
      rw [← NNReal.coe_lt_coe, NNReal.coe_one, hcoe]
      exact hr1
    have htb : t < b := by
      rw [← NNReal.coe_lt_coe, hcoe]
      exact hrb
    have ht2 : t < 2 := lt_of_lt_of_le htb hb2
    refine ⟨t, ht2, ?_⟩
    rw [hride t h1t htb]
    refine mem_Eb.mpr ⟨t, rfl, h1t, ht2, ?_⟩
    rintro ⟨q', hq'⟩
    exact hirr ⟨q', hq'.trans hcoe⟩

lemma visit_from_start (γ : ℝ≥0 → EState) (hγ : γ ∈ EFwd)
    (hγ0 : γ 0 = spine 0) :
    (∃ t, t < 2 ∧ γ t ∈ Ea) ∧ (∃ t, t < 2 ∧ γ t ∈ Eb) := by
  rcases mem_EFwd.mp hγ with ⟨p, rfl⟩ | ⟨p, s, hps, h1, rfl⟩ | rfl
  ·
    have hp : p = 0 := by simpa [stay] using hγ0
    subst hp
    exact dense_visits one_lt_two le_rfl (fun t _ _ => by simp [stay])
  ·
    have hp : p = 0 := by simpa [esc, hps] using hγ0
    subst hp
    refine dense_visits (lt_min h1 one_lt_two) (min_le_right s 2) ?_
    intro t h1t htb
    have hts : t ≤ s := (lt_of_lt_of_le htb (min_le_left s 2)).le
    simp [esc, hts]
  ·
    simp [sinkRun] at hγ0

lemma premise_holds : ∀ i : Fin 2, EB.AService 2 (Eα i) (spine 0) := by
  intro i γ hγ hγ0 ε hε
  obtain ⟨⟨ta, hta, hmema⟩, tb, htb, hmemb⟩ := visit_from_start γ hγ hγ0
  by_cases hi : i = 0
  · refine ⟨ta, lt_of_lt_of_le hta le_self_add, ?_⟩
    have hEα : Eα i = Ea := by rw [hi]; exact if_pos rfl
    rw [hEα]
    exact hmema
  · refine ⟨tb, lt_of_lt_of_le htb le_self_add, ?_⟩
    have hEα : Eα i = Eb := if_neg hi
    rw [hEα]
    exact hmemb

lemma not_service_Eb_of_rat {t : ℝ≥0} (h1t : 1 < t) (hrat : IsRatNN t) :
    ¬ EB.AService 2 Eb (spine t) := by
  intro hserv
  have hmem : esc t t ∈ EFwd := esc_mem le_rfl h1t
  have h0 : esc t t 0 = spine t := by simp [esc]
  obtain ⟨u, -, humem⟩ := hserv (esc t t) hmem h0 1 one_pos
  by_cases hcond : t + u ≤ t
  ·
    have hu0 : u = 0 := by
      have h1 : t + u ≤ t + 0 := by simpa using hcond
      exact le_antisymm (le_of_add_le_add_left h1) zero_le
    rw [hu0, h0] at humem
    obtain ⟨p, hp, -, -, hirr⟩ := mem_Eb.mp humem
    have hpt : t = p := by simpa using hp
    exact hirr (hpt ▸ hrat)
  ·
    have hsink : esc t t u = sink := by simp [esc, hcond]
    rw [hsink] at humem
    obtain ⟨p, hp, -⟩ := mem_Eb.mp humem
    exact EState.noConfusion hp

lemma not_service_Ea_of_irrat {t : ℝ≥0} (h1t : 1 < t) (hirr : ¬ IsRatNN t) :
    ¬ EB.AService 2 Ea (spine t) := by
  intro hserv
  have hmem : esc t t ∈ EFwd := esc_mem le_rfl h1t
  have h0 : esc t t 0 = spine t := by simp [esc]
  obtain ⟨u, -, humem⟩ := hserv (esc t t) hmem h0 1 one_pos
  by_cases hcond : t + u ≤ t
  · have hu0 : u = 0 := by
      have h1 : t + u ≤ t + 0 := by simpa using hcond
      exact le_antisymm (le_of_add_le_add_left h1) zero_le
    rw [hu0, h0] at humem
    obtain ⟨p, hp, -, -, hprat⟩ := mem_Ea.mp humem
    have hpt : t = p := by simpa using hp
    exact hirr (hpt.symm ▸ hprat)
  · have hsink : esc t t u = sink := by simp [esc, hcond]
    rw [hsink] at humem
    obtain ⟨p, hp, -⟩ := mem_Ea.mp humem
    exact EState.noConfusion hp

theorem firstService_attainment_necessary :
    ∃ (S : Type) (B : Behavior S) (α : Fin 2 → Set S) (x : S),
      B.FusionClosed ∧
      (∀ i, B.AService 2 (α i) x) ∧
      ¬ B.AService 2 (B.fsTarget α (fun _ => 2)) x := by
  refine ⟨EState, EB, Eα, spine 0, EB_fusionClosed, premise_holds, ?_⟩
  intro hcon
  have hstay0 : stay 0 0 = spine 0 := by simp [stay]
  obtain ⟨t, -, htmem⟩ := hcon (stay 0) (stay_mem 0) hstay0 1 one_pos
  have hst : stay 0 t = spine t := by simp [stay]
  rw [hst] at htmem
  obtain ⟨i, hmem_i, hco⟩ := Set.mem_iUnion.mp htmem
  by_cases hi : i = 0
  ·
    have hEαi : Eα i = Ea := by rw [hi]; exact if_pos rfl
    rw [hEαi] at hmem_i
    obtain ⟨p, hp, h1p, -, hrat⟩ := mem_Ea.mp hmem_i
    have hpt : t = p := by simpa using hp
    have h1t : 1 < t := hpt.symm ▸ h1p
    have hratt : IsRatNN t := hpt.symm ▸ hrat
    have hserv : EB.AService 2 (Eα 1) (spine t) := hco 1 (by rw [hi]; decide)
    rw [show Eα 1 = Eb from if_neg (by decide)] at hserv
    exact not_service_Eb_of_rat h1t hratt hserv
  ·
    have hEαi : Eα i = Eb := if_neg hi
    rw [hEαi] at hmem_i
    obtain ⟨p, hp, h1p, -, hirr⟩ := mem_Eb.mp hmem_i
    have hpt : t = p := by simpa using hp
    have h1t : 1 < t := hpt.symm ▸ h1p
    have hirrt : ¬ IsRatNN t := hpt.symm ▸ hirr
    have hserv : EB.AService 2 (Eα 0) (spine t) := hco 0 (Ne.symm hi)
    rw [show Eα 0 = Ea from if_pos rfl] at hserv
    exact not_service_Ea_of_irrat h1t hirrt hserv

end TimedCoreCountermodel

end

#print axioms sound_u10f
#print axioms sound_firstService
#print axioms sound_fsResidual
#print axioms TimedCoreCountermodel.EB_fusionClosed
#print axioms TimedCoreCountermodel.firstService_attainment_necessary

end Qtsl
end PPLC
