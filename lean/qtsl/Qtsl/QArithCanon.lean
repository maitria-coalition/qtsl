import Qtsl.QArithLemmas
import Mathlib.Data.List.Nodup

/-!
# Canonical forms and enumeration for sparse polynomials

Canonical-form structure and enumeration theory for the sparse
polynomial core: the order-free semantic coefficient `coeffSum` and its
stability under the algebra; sortedness of insert-built lists, hence
nodup keys and `coeffOf = coeffSum` on canonical outputs; canonical
monomials and their closure, injectivity, and exponent-vector
roundtrip; and membership/nodup for the composition enumeration.
-/

namespace PPLC.QArith

def coeffSum (p : Poly) (m : Mono) : ℚ :=
  p.foldr (fun t acc => if t.1 = m then t.2 + acc else acc) 0

@[simp] theorem coeffSum_nil (m : Mono) : coeffSum [] m = 0 := rfl

theorem coeffSum_cons (mo : Mono) (c : ℚ) (p : Poly) (k : Mono) :
    coeffSum ((mo, c) :: p) k
      = (if mo = k then c else 0) + coeffSum p k := by
  simp only [coeffSum, List.foldr_cons]
  split <;> simp

theorem coeffSum_append (p q : Poly) (k : Mono) :
    coeffSum (p ++ q) k = coeffSum p k + coeffSum q k := by
  induction p with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨mo, c⟩ := hd
    simp only [List.cons_append, coeffSum_cons, ih]
    ring

theorem coeffSum_insertTerm (mo : Mono) (c : ℚ) (p : Poly) (k : Mono) :
    coeffSum (insertTerm (mo, c) p) k
      = (if mo = k then c else 0) + coeffSum p k := by
  induction p with
  | nil => simp [insertTerm, coeffSum_cons]
  | cons hd tl ih =>
    obtain ⟨m', c'⟩ := hd
    simp only [insertTerm]
    split
    · rw [coeffSum_cons, coeffSum_cons]
    · next hcmp =>
      have : mo = m' := monoCmp_eq_iff.mp hcmp
      subst this
      rw [coeffSum_cons, coeffSum_cons]
      split <;> ring
    · rw [coeffSum_cons, ih, coeffSum_cons]
      ring

theorem coeffSum_foldr_insertTerm (p acc : Poly) (k : Mono) :
    coeffSum (p.foldr insertTerm acc) k = coeffSum p k + coeffSum acc k := by
  induction p with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨mo, c⟩ := hd
    simp only [List.foldr_cons]
    rw [coeffSum_insertTerm, ih, coeffSum_cons]
    ring

theorem coeffSum_filter_ne_zero (p : Poly) (k : Mono) :
    coeffSum (p.filter (fun t => t.2 ≠ 0)) k = coeffSum p k := by
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨mo, c⟩ := hd
    rw [List.filter_cons]
    split
    · rw [coeffSum_cons, coeffSum_cons, ih]
    · next hcond =>
      have hc : c = 0 := by simpa using hcond
      subst hc
      rw [ih, coeffSum_cons]
      split <;> ring

@[simp] theorem coeffSum_canon (p : Poly) (k : Mono) :
    coeffSum (Poly.canon p) k = coeffSum p k := by
  unfold Poly.canon
  rw [coeffSum_filter_ne_zero]
  simpa using coeffSum_foldr_insertTerm p [] k

theorem coeffSum_add (p q : Poly) (k : Mono) :
    coeffSum (Poly.add p q) k = coeffSum p k + coeffSum q k := by
  unfold Poly.add
  rw [coeffSum_canon, coeffSum_append]

theorem coeffSum_scale (a : ℚ) (p : Poly) (k : Mono) :
    coeffSum (Poly.scale a p) k = a * coeffSum p k := by
  unfold Poly.scale
  by_cases ha : a = 0
  · simp [ha]
  · rw [if_neg ha]
    induction p with
    | nil => simp
    | cons hd tl ih =>
      obtain ⟨mo, c⟩ := hd
      simp only [List.map_cons, coeffSum_cons, ih]
      split <;> ring

theorem coeffSum_map_rows {α : Type} (L : List α) (g : α → Mono) (h : α → ℚ)
    (k : Mono) :
    coeffSum (L.map fun x => (g x, h x)) k
      = (L.map fun x => if g x = k then h x else 0).sum := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, coeffSum_cons, ih, List.sum_cons]

def keyLT (a b : Mono) : Prop := monoCmp a b = .lt

theorem monoCmp_self (a : Mono) : monoCmp a a = .eq := monoCmp_eq_iff.mpr rfl

theorem monoCmp_swap : ∀ a b : Mono, monoCmp b a = (monoCmp a b).swap := by
  intro a
  induction a with
  | nil =>
    intro b
    cases b <;> simp [monoCmp]
  | cons hd tl ih =>
    intro b
    cases b with
    | nil => simp [monoCmp]
    | cons hd' tl' =>
      obtain ⟨v, e⟩ := hd
      obtain ⟨v', e'⟩ := hd'
      simp only [monoCmp]
      rcases Nat.lt_trichotomy v v' with hv | hv | hv
      · rw [compare_lt_iff_lt.mpr hv, compare_gt_iff_gt.mpr hv]
        rfl
      · subst hv
        rw [compare_eq_iff_eq.mpr rfl]
        rcases Nat.lt_trichotomy e e' with he | he | he
        · rw [compare_lt_iff_lt.mpr he, compare_gt_iff_gt.mpr he]
          rfl
        · subst he
          rw [compare_eq_iff_eq.mpr rfl]
          exact ih tl'
        · rw [compare_gt_iff_gt.mpr he, compare_lt_iff_lt.mpr he]
          rfl
      · rw [compare_gt_iff_gt.mpr hv, compare_lt_iff_lt.mpr hv]
        rfl

theorem monoCmp_gt_iff (a b : Mono) : monoCmp a b = .gt ↔ monoCmp b a = .lt := by
  rw [monoCmp_swap b a]
  rcases h : monoCmp b a <;> decide

theorem keyLT_trans : ∀ {a b c : Mono}, keyLT a b → keyLT b c → keyLT a c := by
  unfold keyLT
  intro a
  induction a with
  | nil =>
    intro b c hab hbc
    cases b with
    | nil => simp [monoCmp] at hab
    | cons hdb tlb =>
      cases c with
      | nil => simp [monoCmp] at hbc
      | cons hdc tlc => simp [monoCmp]
  | cons hda tla ih =>
    intro b c hab hbc
    cases b with
    | nil => simp [monoCmp] at hab
    | cons hdb tlb =>
      cases c with
      | nil => simp [monoCmp] at hbc
      | cons hdc tlc =>
        obtain ⟨v₁, e₁⟩ := hda
        obtain ⟨v₂, e₂⟩ := hdb
        obtain ⟨v₃, e₃⟩ := hdc
        simp only [monoCmp] at hab hbc ⊢
        rcases Nat.lt_trichotomy v₁ v₂ with h12 | h12 | h12
        ·
          rcases Nat.lt_trichotomy v₂ v₃ with h23 | h23 | h23
          · rw [compare_lt_iff_lt.mpr (h12.trans h23)]
          · subst h23
            rw [compare_lt_iff_lt.mpr h12]
          · rw [compare_gt_iff_gt.mpr h23] at hbc
            simp at hbc
        ·
          subst h12
          rw [compare_eq_iff_eq.mpr rfl] at hab
          rcases Nat.lt_trichotomy v₁ v₃ with h13 | h13 | h13
          · rw [compare_lt_iff_lt.mpr h13]
          ·
            subst h13
            rw [compare_eq_iff_eq.mpr rfl] at hbc ⊢
            rcases Nat.lt_trichotomy e₁ e₂ with he12 | he12 | he12
            · rcases Nat.lt_trichotomy e₂ e₃ with he23 | he23 | he23
              · rw [compare_lt_iff_lt.mpr (he12.trans he23)]
              · subst he23
                rw [compare_lt_iff_lt.mpr he12]
              · rw [compare_gt_iff_gt.mpr he23] at hbc
                simp at hbc
            ·
              subst he12
              rw [compare_eq_iff_eq.mpr rfl] at hab
              rcases Nat.lt_trichotomy e₁ e₃ with he13 | he13 | he13
              · rw [compare_lt_iff_lt.mpr he13]
              · subst he13
                rw [compare_eq_iff_eq.mpr rfl] at hbc ⊢
                exact ih hab hbc
              · rw [compare_gt_iff_gt.mpr he13] at hbc
                simp at hbc
            · rw [compare_gt_iff_gt.mpr he12] at hab
              simp at hab
          · rw [compare_gt_iff_gt.mpr h13] at hbc
            simp at hbc
        · rw [compare_gt_iff_gt.mpr h12] at hab
          simp at hab

theorem insertTerm_keys_subset (t : Mono × ℚ) (p : Poly) :
    ∀ s ∈ insertTerm t p, s.1 = t.1 ∨ s.1 ∈ p.map (·.1) := by
  induction p with
  | nil =>
    intro s hs
    obtain ⟨mo, c⟩ := t
    simp [insertTerm] at hs
    subst hs
    exact Or.inl rfl
  | cons hd tl ih =>
    obtain ⟨mo, c⟩ := t
    obtain ⟨m', c'⟩ := hd
    intro s hs
    simp only [insertTerm] at hs
    split at hs
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact Or.inl rfl
      · exact Or.inr (List.mem_map.mpr ⟨s, hs, rfl⟩)
    · next hcmp =>
      have : mo = m' := monoCmp_eq_iff.mp hcmp
      subst this
      rcases List.mem_cons.mp hs with rfl | hs
      · exact Or.inl rfl
      · exact Or.inr (List.mem_map.mpr ⟨s, List.mem_cons_of_mem _ hs, rfl⟩)
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact Or.inr (List.mem_map.mpr ⟨(m', c'), List.mem_cons_self .., rfl⟩)
      · rcases ih s hs with h | h
        · exact Or.inl h
        · obtain ⟨u, hu, hu1⟩ := List.mem_map.mp h
          exact Or.inr (List.mem_map.mpr ⟨u, List.mem_cons_of_mem _ hu, hu1⟩)

theorem insertTerm_pairwise (t : Mono × ℚ) (p : Poly)
    (hp : p.Pairwise (fun s u => keyLT s.1 u.1)) :
    (insertTerm t p).Pairwise (fun s u => keyLT s.1 u.1) := by
  induction p with
  | nil =>
    obtain ⟨mo, c⟩ := t
    simp [insertTerm]
  | cons hd tl ih =>
    obtain ⟨mo, c⟩ := t
    obtain ⟨m', c'⟩ := hd
    rw [List.pairwise_cons] at hp
    obtain ⟨hhead, htail⟩ := hp
    simp only [insertTerm]
    split
    · next hcmp =>
      rw [List.pairwise_cons]
      constructor
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hcmp
        · exact keyLT_trans hcmp (hhead u hu)
      · rw [List.pairwise_cons]
        exact ⟨hhead, htail⟩
    · next hcmp =>
      have : mo = m' := monoCmp_eq_iff.mp hcmp
      subst this
      rw [List.pairwise_cons]
      exact ⟨hhead, htail⟩
    · next hcmp =>
      rw [List.pairwise_cons]
      constructor
      · intro u hu
        rcases insertTerm_keys_subset (mo, c) tl u hu with h | h
        · rw [h]
          exact (monoCmp_gt_iff mo m').mp hcmp
        · obtain ⟨s, hs, hs1⟩ := List.mem_map.mp h
          rw [← hs1]
          exact hhead s hs
      · exact ih htail

theorem foldr_insertTerm_pairwise (p : Poly) :
    (p.foldr insertTerm []).Pairwise (fun s u => keyLT s.1 u.1) := by
  induction p with
  | nil => simp
  | cons hd tl ih => exact insertTerm_pairwise hd _ ih

theorem canon_pairwise (p : Poly) :
    (Poly.canon p).Pairwise (fun s u => keyLT s.1 u.1) :=
  (foldr_insertTerm_pairwise p).filter _

theorem keyLT_irrefl (a : Mono) : ¬ keyLT a a := by
  unfold keyLT
  rw [monoCmp_self]
  simp

theorem coeffOf_eq_coeffSum_of_pairwise (p : Poly)
    (hp : p.Pairwise (fun s u => keyLT s.1 u.1)) (k : Mono) :
    Poly.coeffOf p k = coeffSum p k := by
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨mo, c⟩ := hd
    rw [List.pairwise_cons] at hp
    obtain ⟨hhead, htail⟩ := hp
    rw [coeffSum_cons]
    by_cases hk : mo = k
    · subst hk

      have htl : coeffSum tl mo = 0 := by
        clear ih
        induction tl with
        | nil => rfl
        | cons hd2 tl2 ih2 =>
          obtain ⟨m2, c2⟩ := hd2
          rw [coeffSum_cons]
          have hne : m2 ≠ mo := by
            intro h
            subst h
            exact keyLT_irrefl m2 (hhead (m2, c2) (by simp))
          rw [if_neg hne]
          have : ∀ u ∈ tl2, keyLT mo u.1 := fun u hu => hhead u (by simp [hu])
          rw [ih2 this (List.Pairwise.sublist (by simp) htail)]
          simp
      have hfind : Poly.coeffOf ((mo, c) :: tl) mo = c := by
        unfold Poly.coeffOf
        rw [List.find?_cons_of_pos (by simp)]
      rw [hfind, htl, if_pos rfl]
      ring
    · have hfind : Poly.coeffOf ((mo, c) :: tl) k = Poly.coeffOf tl k := by
        unfold Poly.coeffOf
        rw [List.find?_cons_of_neg (by simp [hk])]
      rw [hfind, if_neg hk, ih htail]
      ring

theorem coeffOf_canon_eq_coeffSum (p : Poly) (k : Mono) :
    Poly.coeffOf (Poly.canon p) k = coeffSum p k := by
  rw [coeffOf_eq_coeffSum_of_pairwise _ (canon_pairwise p), coeffSum_canon]

def MonoGood (m : Nat) (mo : Mono) : Prop :=
  mo.Pairwise (fun s t => s.1 < t.1) ∧ (∀ p ∈ mo, p.2 ≠ 0) ∧ ∀ p ∈ mo, p.1 < m

theorem monoDeg_cons (v e : Nat) (mo : Mono) :
    monoDeg ((v, e) :: mo) = e + monoDeg mo := rfl

@[simp] theorem monoDeg_nil : monoDeg [] = 0 := rfl

theorem insertVar_keys_subset (t : Nat × Nat) (mo : Mono) :
    ∀ s ∈ insertVar t mo, s.1 = t.1 ∨ s.1 ∈ mo.map (·.1) := by
  induction mo with
  | nil =>
    intro s hs
    obtain ⟨v, e⟩ := t
    simp [insertVar] at hs
    subst hs
    exact Or.inl rfl
  | cons hd tl ih =>
    obtain ⟨v, e⟩ := t
    obtain ⟨v', e'⟩ := hd
    intro s hs
    simp only [insertVar] at hs
    split at hs
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact Or.inl rfl
      · exact Or.inr (List.mem_map.mpr ⟨s, hs, rfl⟩)
    · split at hs
      · next hveq =>
        rcases List.mem_cons.mp hs with rfl | hs
        · exact Or.inr (List.mem_map.mpr ⟨(v', e'), List.mem_cons_self .., by simp [hveq]⟩)
        · exact Or.inr (List.mem_map.mpr ⟨s, List.mem_cons_of_mem _ hs, rfl⟩)
      · rcases List.mem_cons.mp hs with rfl | hs
        · exact Or.inr (List.mem_map.mpr ⟨(v', e'), List.mem_cons_self .., rfl⟩)
        · rcases ih s hs with h | h
          · exact Or.inl h
          · obtain ⟨u, hu, hu1⟩ := List.mem_map.mp h
            exact Or.inr (List.mem_map.mpr ⟨u, List.mem_cons_of_mem _ hu, hu1⟩)

theorem insertVar_pairwise (t : Nat × Nat) (mo : Mono)
    (hmo : mo.Pairwise (fun s u => s.1 < u.1)) :
    (insertVar t mo).Pairwise (fun s u => s.1 < u.1) := by
  induction mo with
  | nil =>
    obtain ⟨v, e⟩ := t
    simp [insertVar]
  | cons hd tl ih =>
    obtain ⟨v, e⟩ := t
    obtain ⟨v', e'⟩ := hd
    rw [List.pairwise_cons] at hmo
    obtain ⟨hhead, htail⟩ := hmo
    simp only [insertVar]
    split
    · next hlt =>
      rw [List.pairwise_cons]
      constructor
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hlt
        · exact hlt.trans (hhead u hu)
      · rw [List.pairwise_cons]
        exact ⟨hhead, htail⟩
    · split
      · next hveq =>
        rw [List.pairwise_cons]
        subst hveq
        exact ⟨hhead, htail⟩
      · next hnlt hne =>
        rw [List.pairwise_cons]
        constructor
        · intro u hu
          rcases insertVar_keys_subset (v, e) tl u hu with h | h
          · rw [h]
            omega
          · obtain ⟨s, hs, hs1⟩ := List.mem_map.mp h
            rw [← hs1]
            exact hhead s hs
        · exact ih htail

theorem monoDeg_insertVar (t : Nat × Nat) (mo : Mono) :
    monoDeg (insertVar t mo) = t.2 + monoDeg mo := by
  induction mo with
  | nil =>
    obtain ⟨v, e⟩ := t
    simp [insertVar, monoDeg]
  | cons hd tl ih =>
    obtain ⟨v, e⟩ := t
    obtain ⟨v', e'⟩ := hd
    simp only [insertVar]
    split
    · rfl
    · split
      · simp only [monoDeg_cons]
        omega
      · simp only [monoDeg_cons, ih]
        omega

theorem monoDeg_filter_ne_zero (mo : Mono) :
    monoDeg (mo.filter (fun p => p.2 ≠ 0)) = monoDeg mo := by
  induction mo with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨v, e⟩ := hd
    rw [List.filter_cons]
    split
    · rw [monoDeg_cons, monoDeg_cons, ih]
    · next hcond =>
      have he : e = 0 := by simpa using hcond
      subst he
      rw [ih, monoDeg_cons]
      omega

theorem monoDeg_foldr_insertVar (mo acc : Mono) :
    monoDeg (mo.foldr insertVar acc) = monoDeg mo + monoDeg acc := by
  induction mo with
  | nil => simp [monoDeg]
  | cons hd tl ih =>
    obtain ⟨v, e⟩ := hd
    simp only [List.foldr_cons, monoDeg_insertVar, ih, monoDeg_cons]
    omega

theorem monoDeg_monoCanon (mo : Mono) : monoDeg (monoCanon mo) = monoDeg mo := by
  unfold monoCanon
  rw [monoDeg_filter_ne_zero]
  simpa [monoDeg] using monoDeg_foldr_insertVar mo []

theorem monoDeg_append (a b : Mono) :
    monoDeg (a ++ b) = monoDeg a + monoDeg b := by
  induction a with
  | nil => simp [monoDeg]
  | cons hd tl ih =>
    obtain ⟨v, e⟩ := hd
    simp only [List.cons_append, monoDeg_cons, ih]
    omega

theorem monoDeg_monoMul (a b : Mono) :
    monoDeg (monoMul a b) = monoDeg a + monoDeg b := by
  unfold monoMul
  rw [monoDeg_monoCanon, monoDeg_append]

theorem foldr_insertVar_pairwise (mo : Mono) :
    (mo.foldr insertVar []).Pairwise (fun s u => s.1 < u.1) := by
  induction mo with
  | nil => simp
  | cons hd tl ih => exact insertVar_pairwise hd _ ih

theorem monoCanon_good (m : Nat) (mo : Mono) (hv : ∀ p ∈ mo, p.1 < m) :
    MonoGood m (monoCanon mo) := by
  unfold monoCanon
  refine ⟨(foldr_insertVar_pairwise mo).filter _, ?_, ?_⟩
  · intro p hp
    have := List.of_mem_filter hp
    simpa using this
  · intro p hp
    have hp' := List.mem_of_mem_filter hp

    have hkeys : ∀ s ∈ mo.foldr insertVar [], s.1 ∈ mo.map (·.1) := by
      clear hp hp' p
      induction mo with
      | nil => intro s hs; cases hs
      | cons hd tl ih2 =>
        intro s hs
        rcases insertVar_keys_subset hd _ s hs with h | h
        · simp [h]
        · obtain ⟨u, hu, hu1⟩ := List.mem_map.mp h
          have := ih2 (fun q hq => hv q (by simp [hq])) u hu
          rcases List.mem_map.mp this with ⟨w, hw, hw1⟩
          simp only [List.map_cons, List.mem_cons]
          right
          rw [← hu1, ← hw1]
          exact List.mem_map_of_mem hw
    have := hkeys p hp'
    obtain ⟨u, hu, hu1⟩ := List.mem_map.mp this
    rw [← hu1]
    exact hv u hu

theorem monoMul_good {m : Nat} {a b : Mono}
    (ha : ∀ p ∈ a, p.1 < m) (hb : ∀ p ∈ b, p.1 < m) :
    MonoGood m (monoMul a b) := by
  unfold monoMul
  apply monoCanon_good
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact ha p h
  · exact hb p h

def vtmAux : Nat → List Nat → Mono
  | _, [] => []
  | i, a :: rest => (if a ≠ 0 then [(i, a)] else []) ++ vtmAux (i + 1) rest

theorem filter_zip_range' (i : Nat) (v : List Nat) :
    ((List.range' i v.length).zip v).filter (fun p => p.2 ≠ 0) = vtmAux i v := by
  induction v generalizing i with
  | nil => simp [vtmAux]
  | cons a rest ih =>
    have hr : List.range' i (a :: rest).length = i :: List.range' (i + 1) rest.length := rfl
    rw [hr, List.zip_cons_cons, List.filter_cons]
    split
    · next h =>
      have ha : a ≠ 0 := by simpa using h
      simp only [vtmAux, if_pos ha, List.singleton_append]
      rw [ih]
    · next h =>
      have ha : ¬ a ≠ 0 := by simpa using h
      simp only [vtmAux, if_neg ha, List.nil_append]
      rw [ih]

theorem vecToMono_eq_vtmAux (v : List Nat) : vecToMono v = vtmAux 0 v := by
  unfold vecToMono
  rw [← filter_zip_range', List.range_eq_range']

theorem vtmAux_key_band : ∀ (i : Nat) (v : List Nat), ∀ p ∈ vtmAux i v,
    i ≤ p.1 ∧ p.1 < i + v.length := by
  intro i v
  induction v generalizing i with
  | nil => intro p hp; cases hp
  | cons a rest ih =>
    intro p hp
    simp only [vtmAux] at hp
    rcases List.mem_append.mp hp with h | h
    · split at h
      · rcases List.mem_cons.mp h with rfl | h
        · simp
        · cases h
      · cases h
    · have := ih (i + 1) p h
      constructor
      · omega
      · simp only [List.length_cons]
        omega

theorem vtmAux_canonical : ∀ (i : Nat) (v : List Nat),
    (vtmAux i v).Pairwise (fun s t => s.1 < t.1) ∧ ∀ p ∈ vtmAux i v, p.2 ≠ 0 := by
  intro i v
  induction v generalizing i with
  | nil => exact ⟨List.Pairwise.nil, fun p hp => absurd hp (List.not_mem_nil)⟩
  | cons a rest ih =>
    obtain ⟨ihp, ihz⟩ := ih (i + 1)
    constructor
    · simp only [vtmAux]
      split
      · rw [List.singleton_append, List.pairwise_cons]
        constructor
        · intro p hp
          have := vtmAux_key_band (i + 1) rest p hp
          omega
        · exact ihp
      · simpa using ihp
    · intro p hp
      simp only [vtmAux] at hp
      rcases List.mem_append.mp hp with h | h
      · split at h
        · next ha =>
          rcases List.mem_cons.mp h with rfl | h
          · simpa using ha
          · cases h
        · cases h
      · exact ihz p h

theorem vecToMono_good {m d : Nat} {γ : List Nat}
    (hlen : γ.length = m) (hdeg : γ.sum = d) :
    MonoGood m (vecToMono γ) ∧ monoDeg (vecToMono γ) = d := by
  rw [vecToMono_eq_vtmAux]
  obtain ⟨hp, hz⟩ := vtmAux_canonical 0 γ
  refine ⟨⟨hp, hz, ?_⟩, ?_⟩
  · intro p hp'
    have := vtmAux_key_band 0 γ p hp'
    omega
  ·
    subst hdeg
    clear hp hz hlen
    suffices h : ∀ (v : List Nat) (i : Nat), monoDeg (vtmAux i v) = v.sum from h γ 0
    intro v
    induction v with
    | nil => intro i; rfl
    | cons a rest ih =>
      intro i
      simp only [vtmAux]
      rw [monoDeg_append]
      split
      · simp only [monoDeg_cons, monoDeg_nil, List.sum_cons, ih]
        omega
      · next ha =>
        have : a = 0 := by simpa using ha
        simp only [List.sum_cons, this, ih, monoDeg_nil]

theorem vtmAux_inj : ∀ (i : Nat) (v w : List Nat), v.length = w.length →
    vtmAux i v = vtmAux i w → v = w := by
  intro i v
  induction v generalizing i with
  | nil =>
    intro w hlen _
    cases w with
    | nil => rfl
    | cons b rest => simp at hlen
  | cons a resta ih =>
    intro w hlen heq
    cases w with
    | nil => simp at hlen
    | cons b restb =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [vtmAux] at heq
      by_cases ha : a = 0 <;> by_cases hb : b = 0
      ·
        subst ha; subst hb
        simp only [ne_eq, not_true_eq_false, ite_false, List.nil_append] at heq
        rw [ih (i + 1) restb hlen heq]
      ·
        exfalso
        subst ha
        simp only [ne_eq, hb, not_true_eq_false, ite_false, not_false_eq_true,
          ite_true, List.nil_append, List.singleton_append] at heq
        have hmem : (i, b) ∈ vtmAux (i + 1) resta := by
          rw [heq]; simp
        have := vtmAux_key_band (i + 1) resta (i, b) hmem
        omega
      ·
        exfalso
        subst hb
        simp only [ne_eq, ha, not_true_eq_false, ite_false, not_false_eq_true,
          ite_true, List.nil_append, List.singleton_append] at heq
        have hmem : (i, a) ∈ vtmAux (i + 1) restb := by
          rw [← heq]; simp
        have := vtmAux_key_band (i + 1) restb (i, a) hmem
        omega
      ·
        simp only [ne_eq, ha, hb, not_false_eq_true, ite_true,
          List.singleton_append, List.cons.injEq, Prod.mk.injEq] at heq
        obtain ⟨⟨_, hab⟩, htails⟩ := heq
        rw [hab, ih (i + 1) restb hlen htails]

theorem vecToMono_inj {v w : List Nat} (hlen : v.length = w.length)
    (h : vecToMono v = vecToMono w) : v = w := by
  rw [vecToMono_eq_vtmAux, vecToMono_eq_vtmAux] at h
  exact vtmAux_inj 0 v w hlen h

def MonoBand (i m : Nat) (mo : Mono) : Prop :=
  mo.Pairwise (fun s t => s.1 < t.1) ∧ (∀ p ∈ mo, p.2 ≠ 0) ∧
    ∀ p ∈ mo, i ≤ p.1 ∧ p.1 < i + m

theorem vtmAux_surj : ∀ (m i : Nat) (mo : Mono), MonoBand i m mo →
    ∃ γ : List Nat, γ.length = m ∧ γ.sum = monoDeg mo ∧ vtmAux i γ = mo := by
  intro m
  induction m with
  | zero =>
    intro i mo hband
    obtain ⟨_, _, hb⟩ := hband
    cases mo with
    | nil => exact ⟨[], rfl, rfl, rfl⟩
    | cons p rest =>
      have := hb p (by simp)
      omega
  | succ m ih =>
    intro i mo hband
    obtain ⟨hsort, hnz, hb⟩ := hband
    cases mo with
    | nil =>
      refine ⟨0 :: List.replicate m 0, by simp, by simp, ?_⟩
      clear hsort hnz hb
      suffices h : ∀ (k j : Nat), vtmAux j (List.replicate k 0) = [] by
        have := h (m + 1) i
        rwa [List.replicate_succ] at this
      intro k
      induction k with
      | zero => intro j; rfl
      | succ k ihk =>
        intro j
        rw [List.replicate_succ]
        simp only [vtmAux, ne_eq, not_true_eq_false, ite_false, List.nil_append]
        exact ihk (j + 1)
    | cons p rest =>
      obtain ⟨v, e⟩ := p
      have hvi : i ≤ v ∧ v < i + (m + 1) := hb (v, e) (by simp)
      by_cases hv : v = i
      ·
        subst hv
        have hrest : MonoBand (v + 1) m rest := by
          refine ⟨(List.pairwise_cons.mp hsort).2, fun q hq => hnz q (by simp [hq]), ?_⟩
          intro q hq
          have hlt := (List.pairwise_cons.mp hsort).1 q hq
          have := hb q (by simp [hq])
          omega
        obtain ⟨γ', hlen, hsum, heq⟩ := ih (v + 1) rest hrest
        refine ⟨e :: γ', by simp [hlen], by simp [hsum, monoDeg_cons], ?_⟩
        have he : e ≠ 0 := hnz (v, e) (by simp)
        simp only [vtmAux, if_pos he, List.singleton_append, heq]
      ·
        have hmo : MonoBand (i + 1) m ((v, e) :: rest) := by
          refine ⟨hsort, hnz, ?_⟩
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · omega
          · have hlt := (List.pairwise_cons.mp hsort).1 q hq
            have := hb q (by simp [hq])
            omega
        obtain ⟨γ', hlen, hsum, heq⟩ := ih (i + 1) ((v, e) :: rest) hmo
        refine ⟨0 :: γ', by simp [hlen], by simp [hsum], ?_⟩
        simp only [vtmAux, ne_eq, not_true_eq_false, ite_false, List.nil_append]
        exact heq

theorem mem_compositions_iff : ∀ {parts total : Nat} {γ : List Nat},
    γ ∈ compositions parts total ↔ γ.length = parts ∧ γ.sum = total := by
  intro parts
  induction parts with
  | zero =>
    intro total γ
    cases total with
    | zero =>
      simp only [compositions, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨hlen, hsum⟩
        exact List.eq_nil_of_length_eq_zero hlen
    | succ t =>
      simp only [compositions, List.not_mem_nil, false_iff, not_and]
      intro hlen
      rw [List.eq_nil_of_length_eq_zero hlen]
      simp
  | succ parts ih =>
    intro total γ
    simp only [compositions, List.mem_flatMap, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨a, ha, δ, hδ, rfl⟩
      obtain ⟨hlen, hsum⟩ := ih.mp hδ
      refine ⟨by simp [hlen], ?_⟩
      simp only [List.sum_cons, hsum]
      omega
    · rintro ⟨hlen, hsum⟩
      cases γ with
      | nil => simp at hlen
      | cons g δ =>
        simp only [List.sum_cons] at hsum
        refine ⟨g, by omega, δ, ih.mpr ⟨by simpa using hlen, by omega⟩, rfl⟩

theorem nodup_flatMap_disjoint {α β : Type} (l : List α) (f : α → List β)
    (hl : l.Nodup) (hf : ∀ a ∈ l, (f a).Nodup)
    (hdisj : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ x ∈ f a, x ∉ f b) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.flatMap_cons]
    have hnd_tl := (List.nodup_cons.mp hl).2
    have hhd_notmem := (List.nodup_cons.mp hl).1
    rw [List.nodup_append]
    refine ⟨hf hd (by simp), ?_, ?_⟩
    · exact ih hnd_tl (fun a ha => hf a (by simp [ha]))
        (fun a ha b hb hab => hdisj a (by simp [ha]) b (by simp [hb]) hab)
    · intro x hx y hy
      obtain ⟨b, hb, hyb⟩ := List.mem_flatMap.mp hy
      have hne : hd ≠ b := by
        rintro rfl
        exact hhd_notmem hb
      intro hxy
      subst hxy
      exact hdisj hd (by simp) b (by simp [hb]) hne x hx hyb

theorem compositions_nodup : ∀ (parts total : Nat),
    (compositions parts total).Nodup := by
  intro parts
  induction parts with
  | zero =>
    intro total
    cases total <;> simp [compositions]
  | succ parts ih =>
    intro total
    apply nodup_flatMap_disjoint
    · exact List.nodup_range
    · intro a _
      refine List.Nodup.map ?_ (ih (total - a))
      intro x y h
      injection h
    · intro a _ b _ hab x hx hx'
      obtain ⟨δ, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨δ', _, heq⟩ := List.mem_map.mp hx'
      injection heq with h1 _
      exact hab h1.symm

theorem compositions_ne_nil {m d : Nat} (hm : 0 < m) :
    ∃ γ, γ ∈ compositions m d := by
  refine ⟨d :: List.replicate (m - 1) 0, mem_compositions_iff.mpr ⟨?_, ?_⟩⟩
  · simp
    omega
  · simp

theorem exists_composition_of_monoGood {m d : Nat} {mo : Mono}
    (hgood : MonoGood m mo) (hdeg : monoDeg mo = d) :
    ∃ γ ∈ compositions m d, vecToMono γ = mo := by
  obtain ⟨hsort, hnz, hb⟩ := hgood
  obtain ⟨γ, hlen, hsum, heq⟩ := vtmAux_surj m 0 mo ⟨hsort, hnz, by
    intro p hp
    exact ⟨Nat.zero_le _, by simpa using hb p hp⟩⟩
  refine ⟨γ, ?_, by rw [vecToMono_eq_vtmAux]; exact heq⟩
  rw [mem_compositions_iff]
  exact ⟨hlen, by rw [hsum, hdeg]⟩

theorem sum_map_add {α : Type} (L : List α) (f g : α → ℚ) :
    (L.map fun x => f x + g x).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem sum_map_zero_of_all {α : Type} (L : List α) (f : α → ℚ)
    (h : ∀ x ∈ L, f x = 0) : (L.map f).sum = 0 := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, h hd (by simp),
      ih (fun x hx => h x (by simp [hx]))]
    ring

theorem sum_map_single_witness {α : Type} [DecidableEq α] (L : List α)
    (f : α → ℚ) (x₀ : α) (hx₀ : x₀ ∈ L) (hnd : L.Nodup) :
    (L.map fun x => if x = x₀ then f x else 0).sum = f x₀ := by
  induction L with
  | nil => cases hx₀
  | cons hd tl ih =>
    rcases List.mem_cons.mp hx₀ with rfl | hmem
    · have hz : ∀ x ∈ tl, (if x = x₀ then f x else 0) = 0 := by
        intro x hx
        have hne : x ≠ x₀ := by
          rintro rfl
          exact (List.nodup_cons.mp hnd).1 hx
        rw [if_neg hne]
      rw [List.map_cons, List.sum_cons, if_pos rfl, sum_map_zero_of_all tl _ hz]
      ring
    · have hne : hd ≠ x₀ := by
        rintro rfl
        exact (List.nodup_cons.mp hnd).1 hmem
      simp only [List.map_cons, List.sum_cons, if_neg hne]
      rw [ih hmem (List.nodup_cons.mp hnd).2]
      ring

theorem eval_eq_enum_sum (ρ : Nat → ℚ) (m d : Nat) (p : Poly)
    (hgood : ∀ t ∈ p, MonoGood m t.1 ∧ monoDeg t.1 = d) :
    Poly.eval ρ p
      = ((compositions m d).map
          (fun γ => coeffSum p (vecToMono γ) * monoEval ρ (vecToMono γ))).sum := by
  induction p with
  | nil => simp [sum_map_zero_of_all]
  | cons hd tl ih =>
    obtain ⟨mo, c⟩ := hd
    obtain ⟨hgood₀, hdeg₀⟩ := hgood (mo, c) (by simp)
    obtain ⟨γ₀, hγ₀, hvtm₀⟩ := exists_composition_of_monoGood hgood₀ hdeg₀
    have htl := ih (fun t ht => hgood t (by simp [ht]))
    rw [Poly.eval_cons, htl]
    have hsplit : ∀ γ ∈ compositions m d,
        coeffSum ((mo, c) :: tl) (vecToMono γ) * monoEval ρ (vecToMono γ)
          = (if γ = γ₀ then c * monoEval ρ (vecToMono γ) else 0)
            + coeffSum tl (vecToMono γ) * monoEval ρ (vecToMono γ) := by
      intro γ hγ
      rw [coeffSum_cons]
      by_cases hγeq : γ = γ₀
      · subst hγeq
        rw [if_pos hvtm₀.symm, if_pos rfl]
        ring
      · have : mo ≠ vecToMono γ := by
          intro h
          apply hγeq
          apply vecToMono_inj
          · rw [(mem_compositions_iff.mp hγ).1, (mem_compositions_iff.mp hγ₀).1]
          · rw [← h, hvtm₀]
        rw [if_neg this, if_neg hγeq]
        ring
    rw [List.map_congr_left hsplit, sum_map_add]
    have hwit : ((compositions m d).map
        fun γ => if γ = γ₀ then c * monoEval ρ (vecToMono γ) else 0).sum
        = c * monoEval ρ (vecToMono γ₀) :=
      sum_map_single_witness (compositions m d)
        (fun γ => c * monoEval ρ (vecToMono γ)) γ₀ hγ₀ (compositions_nodup m d)
    rw [hwit, hvtm₀]

end PPLC.QArith
