import Qtsl.QArithCanon
import Mathlib.Algebra.Order.Field.Basic

/-!
# The extension-free Bernstein-cone kernel

Headline: `fdBernstein_S_empty_sound` — if the exact-ℚ
forward-difference table of an extension-free mask passes a
convex-predicate sweep, then the polynomial's value at every
nonnegative unit-sum weighting of the vertices satisfies the predicate.
This is the mathematical content of the Bernstein-cone rule restricted
to `S = ∅`. The route: support closure through the sparse algebra,
canonicalization as the semantic normal form, and the multinomial
enumeration identity.
-/

namespace PPLC.QArith

def PolyBand (m d : Nat) (p : Poly) : Prop :=
  ∀ t ∈ p, MonoGood m t.1 ∧ monoDeg t.1 = d

theorem foldr_insertTerm_keys_subset (p acc : Poly) :
    ∀ t ∈ p.foldr insertTerm acc, t.1 ∈ p.map (·.1) ++ acc.map (·.1) := by
  induction p with
  | nil =>
    intro t ht
    simp only [List.map_nil, List.nil_append]
    exact List.mem_map.mpr ⟨t, ht, rfl⟩
  | cons hd tl ih =>
    intro t ht
    simp only [List.foldr_cons] at ht
    rcases insertTerm_keys_subset hd _ t ht with h | h
    · simp [h]
    · obtain ⟨u, hu, hu1⟩ := List.mem_map.mp h
      have := ih u hu
      rcases List.mem_append.mp this with h' | h'
      · exact List.mem_append.mpr (Or.inl (by
          simp only [List.map_cons, List.mem_cons]
          right
          rw [← hu1]; exact h'))
      · exact List.mem_append.mpr (Or.inr (hu1 ▸ h'))

theorem canon_keys_subset (p : Poly) :
    ∀ t ∈ Poly.canon p, t.1 ∈ p.map (·.1) := by
  intro t ht
  have ht' := List.mem_of_mem_filter ht
  have := foldr_insertTerm_keys_subset p [] t ht'
  simpa using this

theorem polyBand_of_keys {m d : Nat} {p q : Poly}
    (hsub : ∀ t ∈ q, t.1 ∈ p.map (·.1)) (hp : PolyBand m d p) :
    PolyBand m d q := by
  intro t ht
  obtain ⟨u, hu, hu1⟩ := List.mem_map.mp (hsub t ht)
  have := hp u hu
  rw [← hu1]
  exact this

theorem polyBand_canon {m d : Nat} {p : Poly} (hp : PolyBand m d p) :
    PolyBand m d (Poly.canon p) :=
  polyBand_of_keys (canon_keys_subset p) hp

theorem polyBand_append {m d : Nat} {p q : Poly}
    (hp : PolyBand m d p) (hq : PolyBand m d q) : PolyBand m d (p ++ q) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact hp t h
  · exact hq t h

theorem polyBand_add {m d : Nat} {p q : Poly}
    (hp : PolyBand m d p) (hq : PolyBand m d q) :
    PolyBand m d (Poly.add p q) :=
  polyBand_canon (polyBand_append hp hq)

theorem polyBand_mul {m d₁ d₂ : Nat} {p q : Poly}
    (hp : PolyBand m d₁ p) (hq : PolyBand m d₂ q) :
    PolyBand m (d₁ + d₂) (Poly.mul p q) := by
  unfold Poly.mul
  apply polyBand_canon
  intro t ht
  obtain ⟨u, hu, ht'⟩ := List.mem_flatMap.mp ht
  obtain ⟨w, hw, hw1⟩ := List.mem_map.mp ht'
  obtain ⟨hgu, hdu⟩ := hp u hu
  obtain ⟨hgw, hdw⟩ := hq w hw
  have hkey : t.1 = monoMul u.1 w.1 := by rw [← hw1]
  rw [hkey]
  constructor
  · exact monoMul_good hgu.2.2 hgw.2.2
  · rw [monoDeg_monoMul, hdu, hdw]

theorem polyBand_sumVars (m : Nat) : PolyBand m 1 (sumVars m) := by
  unfold sumVars
  apply polyBand_canon
  intro t ht
  obtain ⟨i, hi, hi1⟩ := List.mem_map.mp ht
  rw [← hi1]
  refine ⟨⟨by simp, by simp, ?_⟩, by simp [monoDeg]⟩
  intro q hq
  rcases List.mem_singleton.mp hq with rfl
  simpa using List.mem_range.mp hi

theorem polyBand_const_one (m : Nat) : PolyBand m 0 (Poly.const 1) := by
  intro t ht
  unfold Poly.const at ht
  rw [if_neg one_ne_zero] at ht
  rcases List.mem_singleton.mp ht with rfl
  exact ⟨⟨List.Pairwise.nil, by simp, by simp⟩, rfl⟩

theorem polyBand_sumVars_pow (m : Nat) : ∀ d, PolyBand m d (Poly.pow (sumVars m) d)
  | 0 => polyBand_const_one m
  | d + 1 => by
    have := polyBand_mul (polyBand_sumVars m) (polyBand_sumVars_pow m d)
    simpa [Poly.pow, Nat.add_comm 1 d] using this

theorem insertTerm_of_keyLT_head (t : Mono × ℚ) (p : Poly)
    (h : ∀ u ∈ p, keyLT t.1 u.1) : insertTerm t p = t :: p := by
  cases p with
  | nil =>
    obtain ⟨mo, c⟩ := t
    rfl
  | cons hd tl =>
    obtain ⟨mo, c⟩ := t
    obtain ⟨m', c'⟩ := hd
    have hlt : monoCmp mo m' = .lt := h (m', c') (by simp)
    simp only [insertTerm, hlt]

theorem foldr_insertTerm_eq_self (p : Poly)
    (hp : p.Pairwise (fun s u => keyLT s.1 u.1)) :
    p.foldr insertTerm [] = p := by
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.pairwise_cons] at hp
    simp only [List.foldr_cons, ih hp.2]
    exact insertTerm_of_keyLT_head hd tl hp.1

theorem canon_eq_self (p : Poly)
    (hsort : p.Pairwise (fun s u => keyLT s.1 u.1))
    (hnz : ∀ t ∈ p, t.2 ≠ 0) : Poly.canon p = p := by
  unfold Poly.canon
  rw [foldr_insertTerm_eq_self p hsort]
  exact List.filter_eq_self.mpr (fun t ht => by simpa using hnz t ht)

theorem sumVars_eq_literal (m : Nat) :
    sumVars m = (List.range m).map fun i => (([(i, 1)] : Mono), (1 : ℚ)) := by
  unfold sumVars
  apply canon_eq_self
  ·
    refine List.Pairwise.map _ ?_ (List.pairwise_lt_range (n := m))
    intro a b hab
    show keyLT [(a, 1)] [(b, 1)]
    unfold keyLT
    simp only [monoCmp]
    rw [compare_lt_iff_lt.mpr hab]
  · intro t ht
    obtain ⟨i, _, hi1⟩ := List.mem_map.mp ht
    rw [← hi1]
    exact one_ne_zero

theorem coeffSum_mul (p q : Poly) (k : Mono) :
    coeffSum (Poly.mul p q) k
      = (p.map fun t =>
          (q.map fun u => if monoMul t.1 u.1 = k then t.2 * u.2 else 0).sum).sum := by
  unfold Poly.mul
  rw [coeffSum_canon]
  induction p with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨mo, c⟩ := hd
    rw [List.flatMap_cons, coeffSum_append, ih, List.map_cons, List.sum_cons]
    congr 1
    show coeffSum (q.map fun u => (monoMul mo u.1, c * u.2)) k = _
    rw [coeffSum_map_rows]

def expSum (mo : Mono) (v : Nat) : Nat :=
  mo.foldr (fun p acc => (if p.1 = v then p.2 else 0) + acc) 0

@[simp] theorem expSum_nil (v : Nat) : expSum [] v = 0 := rfl

theorem expSum_cons (u : Nat × Nat) (mo : Mono) (v : Nat) :
    expSum (u :: mo) v = (if u.1 = v then u.2 else 0) + expSum mo v := rfl

theorem expSum_cons' (u e : Nat) (mo : Mono) (v : Nat) :
    expSum ((u, e) :: mo) v = (if u = v then e else 0) + expSum mo v := rfl

theorem expSum_append (a b : Mono) (v : Nat) :
    expSum (a ++ b) v = expSum a v + expSum b v := by
  induction a with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.cons_append, expSum_cons, ih]
    omega

theorem expSum_insertVar : ∀ (u e : Nat) (mo : Mono) (v : Nat),
    expSum (insertVar (u, e) mo) v = (if u = v then e else 0) + expSum mo v := by
  intro u e mo v
  induction mo with
  | nil => simp [insertVar, expSum_cons']
  | cons hd tl ih =>
    obtain ⟨u', e'⟩ := hd
    simp only [insertVar]
    split
    · rw [expSum_cons', expSum_cons']
    · split
      · next heq =>
        subst heq
        rw [expSum_cons', expSum_cons']
        split_ifs <;> omega
      · rw [expSum_cons', ih, expSum_cons']
        omega

theorem expSum_foldr_insertVar (mo acc : Mono) (v : Nat) :
    expSum (mo.foldr insertVar acc) v = expSum mo v + expSum acc v := by
  induction mo with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨u, e⟩ := hd
    simp only [List.foldr_cons]
    rw [expSum_insertVar, ih, expSum_cons']
    omega

theorem expSum_filter_ne_zero (mo : Mono) (v : Nat) :
    expSum (mo.filter (fun p => p.2 ≠ 0)) v = expSum mo v := by
  induction mo with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨u, e⟩ := hd
    rw [List.filter_cons]
    split
    · rw [expSum_cons', expSum_cons', ih]
    · next hcond =>
      have he : e = 0 := by simpa using hcond
      subst he
      rw [ih, expSum_cons']
      split <;> omega

theorem expSum_monoCanon (mo : Mono) (v : Nat) :
    expSum (monoCanon mo) v = expSum mo v := by
  unfold monoCanon
  rw [expSum_filter_ne_zero]
  simpa using expSum_foldr_insertVar mo [] v

theorem expSum_monoMul (a b : Mono) (v : Nat) :
    expSum (monoMul a b) v = expSum a v + expSum b v := by
  unfold monoMul
  rw [expSum_monoCanon, expSum_append]

theorem getD_of_le {l : List Nat} {i : Nat} (h : l.length ≤ i) :
    l.getD i 0 = 0 := by
  induction l generalizing i with
  | nil => simp
  | cons hd tl ih =>
    cases i with
    | zero => simp at h
    | succ i' =>
      simp only [List.getD_cons_succ]
      exact ih (by simpa using h)

theorem expSum_vtmAux : ∀ (γ : List Nat) (i v : Nat),
    expSum (vtmAux i γ) v
      = if i ≤ v ∧ v < i + γ.length then γ.getD (v - i) 0 else 0 := by
  intro γ
  induction γ with
  | nil =>
    intro i v
    simp [vtmAux]
  | cons a rest ih =>
    intro i v
    simp only [vtmAux]
    rw [expSum_append]
    have htail := ih (i + 1) v
    by_cases hv : v = i
    · subst hv
      have h1 : expSum (if a ≠ 0 then [(v, a)] else []) v = a := by
        split
        · rw [expSum_cons']
          simp
        · next h => simp only [expSum_nil]; omega
      have hc2 : ¬ (v + 1 ≤ v ∧ v < v + 1 + rest.length) := by omega
      rw [h1, htail, if_neg hc2]
      have hc3 : v ≤ v ∧ v < v + (a :: rest).length := by
        simp only [List.length_cons]
        omega
      rw [if_pos hc3]
      simp
    · have h1 : expSum (if a ≠ 0 then [(i, a)] else []) v = 0 := by
        split
        · rw [expSum_cons']
          rw [if_neg (fun h => hv h.symm)]
          rfl
        · rfl
      rw [h1, htail]
      simp only [List.length_cons]
      by_cases hband : i ≤ v ∧ v < i + (rest.length + 1)
      · have hb1 : i + 1 ≤ v := by omega
        have hb2 : v < i + 1 + rest.length := by omega
        rw [if_pos ⟨hb1, hb2⟩, if_pos hband]
        have hvi : v - i = (v - (i + 1)) + 1 := by omega
        rw [hvi]
        simp
      · have hb : ¬ (i + 1 ≤ v ∧ v < i + 1 + rest.length) := by omega
        rw [if_neg hb, if_neg hband]

theorem expSum_vecToMono (γ : List Nat) (v : Nat) :
    expSum (vecToMono γ) v = γ.getD v 0 := by
  rw [vecToMono_eq_vtmAux, expSum_vtmAux]
  by_cases h : v < γ.length
  · rw [if_pos ⟨Nat.zero_le _, by omega⟩]
    simp
  · rw [if_neg (by omega), getD_of_le (by omega)]

theorem monoBand_of_canonical {mo : Mono}
    (hsort : mo.Pairwise (fun s t => s.1 < t.1)) (hnz : ∀ p ∈ mo, p.2 ≠ 0)
    {m : Nat} (hb : ∀ p ∈ mo, p.1 < m) : MonoBand 0 m mo :=
  ⟨hsort, hnz, fun p hp => ⟨Nat.zero_le _, by simpa using hb p hp⟩⟩

theorem list_ext_getD : ∀ (a b : List Nat), a.length = b.length →
    (∀ v, a.getD v 0 = b.getD v 0) → a = b := by
  intro a
  induction a with
  | nil =>
    intro b hlen _
    cases b with
    | nil => rfl
    | cons x xs => simp at hlen
  | cons x xs ih =>
    intro b hlen hget
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      have h0 := hget 0
      simp only [List.getD_cons_zero] at h0
      subst h0
      congr 1
      refine ih ys (by simpa using hlen) (fun v => ?_)
      have := hget (v + 1)
      simpa using this

theorem canonical_mono_ext {a b : Mono}
    (hsa : a.Pairwise (fun s t => s.1 < t.1)) (hza : ∀ p ∈ a, p.2 ≠ 0)
    (hsb : b.Pairwise (fun s t => s.1 < t.1)) (hzb : ∀ p ∈ b, p.2 ≠ 0)
    (h : ∀ v, expSum a v = expSum b v) : a = b := by

  set M := (a.map (·.1)).foldr max 0 + (b.map (·.1)).foldr max 0 + 1 with hM
  have hbound : ∀ (c : Mono), (∀ p ∈ c, p.1 ≤ (c.map (·.1)).foldr max 0) := by
    intro c
    induction c with
    | nil => intro p hp; cases hp
    | cons hd tl ih =>
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simp only [List.map_cons, List.foldr_cons]
        exact Nat.le_max_left _ _
      · simp only [List.map_cons, List.foldr_cons]
        exact le_trans (ih p hp) (Nat.le_max_right _ _)
  have hba : MonoBand 0 M a :=
    monoBand_of_canonical hsa hza (fun p hp => by
      have := hbound a p hp; omega)
  have hbb : MonoBand 0 M b :=
    monoBand_of_canonical hsb hzb (fun p hp => by
      have := hbound b p hp; omega)
  obtain ⟨γa, hlena, _, heqa⟩ := vtmAux_surj M 0 a hba
  obtain ⟨γb, hlenb, _, heqb⟩ := vtmAux_surj M 0 b hbb
  have hγ : γa = γb := by
    apply list_ext_getD γa γb (by omega)
    intro v
    have h1 : expSum (vtmAux 0 γa) v = γa.getD v 0 := by
      rw [← vecToMono_eq_vtmAux, expSum_vecToMono]
    have h2 : expSum (vtmAux 0 γb) v = γb.getD v 0 := by
      rw [← vecToMono_eq_vtmAux, expSum_vecToMono]
    rw [← h1, ← h2, heqa, heqb]
    exact h v
  rw [← heqa, ← heqb, hγ]

theorem getD_set : ∀ (γ : List Nat) (i v x : Nat),
    (γ.set i x).getD v 0 = if v = i ∧ i < γ.length then x else γ.getD v 0 := by
  intro γ
  induction γ with
  | nil => intro i v x; simp
  | cons a rest ih =>
    intro i v x
    cases i with
    | zero =>
      cases v with
      | zero => simp
      | succ v' => simp
    | succ i' =>
      cases v with
      | zero => simp
      | succ v' =>
        simp only [List.set_cons_succ, List.getD_cons_succ, List.length_cons]
        rw [ih]
        by_cases h : v' = i' ∧ i' < rest.length
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]

theorem monoCanon_sorted (mo : Mono) :
    (monoCanon mo).Pairwise (fun s t => s.1 < t.1) :=
  (foldr_insertVar_pairwise mo).filter _

theorem monoCanon_nonzero (mo : Mono) : ∀ p ∈ monoCanon mo, p.2 ≠ 0 := by
  intro p hp
  have := List.of_mem_filter hp
  simpa using this

theorem monoMul_sorted (a b : Mono) :
    (monoMul a b).Pairwise (fun s t => s.1 < t.1) := monoCanon_sorted _

theorem monoMul_nonzero (a b : Mono) : ∀ p ∈ monoMul a b, p.2 ≠ 0 :=
  monoCanon_nonzero _

theorem monoMul_var_vecToMono {γ : List Nat} {i : Nat} (hi : i < γ.length) :
    monoMul [(i, 1)] (vecToMono γ) = vecToMono (γ.set i (γ.getD i 0 + 1)) := by
  have hcanA := vtmAux_canonical 0 γ
  have hcanB := vtmAux_canonical 0 (γ.set i (γ.getD i 0 + 1))
  apply canonical_mono_ext (monoMul_sorted _ _) (monoMul_nonzero _ _)
  · rw [vecToMono_eq_vtmAux]; exact hcanB.1
  · rw [vecToMono_eq_vtmAux]; exact hcanB.2
  · intro v
    rw [expSum_monoMul, expSum_vecToMono, expSum_vecToMono, getD_set,
      expSum_cons']
    simp only [expSum_nil]
    by_cases hv : v = i
    · subst hv
      have hc : v = v ∧ v < γ.length := ⟨rfl, hi⟩
      rw [if_pos hc, if_pos rfl]
      omega
    · have hc : ¬ (v = i ∧ i < γ.length) := fun h => hv h.1
      rw [if_neg hc, if_neg (fun h => hv h.symm)]
      omega

theorem monoMul_var_eq_iff {m d : Nat} {γ δ : List Nat} {i : Nat}
    (hγ : γ ∈ compositions m (d + 1)) (hδ : δ ∈ compositions m d)
    (hi : i < m) :
    monoMul [(i, 1)] (vecToMono δ) = vecToMono γ
      ↔ 0 < γ.getD i 0 ∧ δ = γ.set i (γ.getD i 0 - 1) := by
  obtain ⟨hγlen, hγsum⟩ := mem_compositions_iff.mp hγ
  obtain ⟨hδlen, hδsum⟩ := mem_compositions_iff.mp hδ
  rw [monoMul_var_vecToMono (by omega)]
  constructor
  · intro h
    have hvec : δ.set i (δ.getD i 0 + 1) = γ :=
      vecToMono_inj (by simp [hδlen, hγlen]) h
    have hgi : γ.getD i 0 = δ.getD i 0 + 1 := by
      rw [← hvec, getD_set]
      have hc : i = i ∧ i < δ.length := ⟨rfl, by omega⟩
      rw [if_pos hc]
    refine ⟨by omega, ?_⟩
    apply list_ext_getD _ _ (by simp [hδlen, hγlen])
    intro v
    rw [getD_set]
    by_cases hv : v = i
    · subst hv
      have hc : v = v ∧ v < γ.length := ⟨rfl, by omega⟩
      rw [if_pos hc]
      omega
    · have hc : ¬ (v = i ∧ i < γ.length) := fun hh => hv hh.1
      rw [if_neg hc, ← hvec, getD_set]
      have hc2 : ¬ (v = i ∧ i < δ.length) := fun hh => hv hh.1
      rw [if_neg hc2]
  · rintro ⟨hpos, rfl⟩
    have hilen : i < γ.length := by omega
    have hinner : (γ.set i (γ.getD i 0 - 1)).getD i 0 = γ.getD i 0 - 1 := by
      rw [getD_set]
      have hc : i = i ∧ i < γ.length := ⟨rfl, hilen⟩
      rw [if_pos hc]
    rw [hinner]
    congr 1
    apply list_ext_getD _ _ (by simp)
    intro v
    rw [getD_set, getD_set]
    simp only [List.length_set]
    by_cases hv : v = i
    · subst hv
      have hc : v = v ∧ v < γ.length := ⟨rfl, hilen⟩
      rw [if_pos hc]
      omega
    · have hc : ¬ (v = i ∧ i < γ.length) := fun hh => hv hh.1
      rw [if_neg hc, if_neg hc]

theorem foldr_add_eq_sum (l : List Nat) : l.foldr (·+·) 0 = l.sum := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [ih]

theorem multinomial_cons (a : Nat) (rest : List Nat) :
    multinomial (a :: rest) = Nat.choose (a + rest.sum) a * multinomial rest := by
  show Prim.nchoose (a + rest.foldr (·+·) 0) a * multinomial rest = _
  rw [foldr_add_eq_sum, Prim.nchoose_eq_choose]

theorem multinomial_pos : ∀ (γ : List Nat), 0 < multinomial γ := by
  intro γ
  induction γ with
  | nil => exact Nat.one_pos
  | cons a rest ih =>
    rw [multinomial_cons]
    exact Nat.mul_pos (Nat.choose_pos (Nat.le_add_right a _)) ih

theorem multinomial_replicate_zero : ∀ (m : Nat),
    multinomial (List.replicate m 0) = 1 := by
  intro m
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, multinomial_cons, ih]
    simp

theorem sum_set_dec {γ : List Nat} {i : Nat} (hi : i < γ.length)
    (hpos : 0 < γ.getD i 0) :
    (γ.set i (γ.getD i 0 - 1)).sum = γ.sum - 1 ∧ 0 < γ.sum := by
  induction γ generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
    cases i with
    | zero =>
      simp only [List.getD_cons_zero] at hpos
      simp only [List.set_cons_zero, List.sum_cons, List.getD_cons_zero]
      omega
    | succ i' =>
      simp only [List.getD_cons_succ] at hpos
      simp only [List.length_cons] at hi
      obtain ⟨h1, h2⟩ := ih (by omega) hpos
      simp only [List.set_cons_succ, List.sum_cons, List.getD_cons_succ, h1]
      omega

theorem nat_sum_eq_zero {l : List Nat} (h : l.sum = 0) : ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => intro x hx; cases hx
  | cons hd tl ih =>
    simp only [List.sum_cons] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · exact ih (by omega) x hx

theorem getD_zero_of_all_zero {l : List Nat} (h : ∀ x ∈ l, x = 0) (i : Nat) :
    l.getD i 0 = 0 := by
  induction l generalizing i with
  | nil => simp
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getD_cons_zero]
      exact h hd (by simp)
    | succ i' =>
      simp only [List.getD_cons_succ]
      exact ih (fun x hx => h x (by simp [hx])) i'

theorem nat_sum_map_zero {α : Type} (L : List α) (f : α → Nat)
    (h : ∀ x ∈ L, f x = 0) : (L.map f).sum = 0 := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, h hd (by simp),
      ih (fun x hx => h x (by simp [hx]))]

theorem sum_map_mul_left_nat {α : Type} (L : List α) (c : Nat) (f : α → Nat) :
    (L.map fun x => c * f x).sum = c * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem sum_range_succ_shift (n : Nat) (f : Nat → Nat) :
    ((List.range (n + 1)).map f).sum
      = f 0 + ((List.range n).map (fun i => f (i + 1))).sum := by
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.sum_cons, List.map_map]
  rfl

theorem multinomial_pascal : ∀ (γ : List Nat), 0 < γ.sum →
    multinomial γ
      = ((List.range γ.length).map fun i =>
          if 0 < γ.getD i 0 then multinomial (γ.set i (γ.getD i 0 - 1)) else 0).sum := by
  intro γ
  induction γ with
  | nil => intro h; simp at h
  | cons a rest ih =>
    intro hsum
    simp only [List.sum_cons] at hsum
    rw [List.length_cons, sum_range_succ_shift]
    simp only [List.getD_cons_zero, List.getD_cons_succ,
      List.set_cons_zero, List.set_cons_succ]
    by_cases hS : 0 < rest.sum
    ·
      have htail : ∀ i ∈ List.range rest.length,
          (if 0 < rest.getD i 0
           then multinomial (a :: rest.set i (rest.getD i 0 - 1)) else 0)
          = Nat.choose (a + (rest.sum - 1)) a *
            (if 0 < rest.getD i 0
             then multinomial (rest.set i (rest.getD i 0 - 1)) else 0) := by
        intro i hi
        by_cases hpos : 0 < rest.getD i 0
        · rw [if_pos hpos, if_pos hpos, multinomial_cons,
            (sum_set_dec (List.mem_range.mp hi) hpos).1]
        · rw [if_neg hpos, if_neg hpos, Nat.mul_zero]
      rw [List.map_congr_left htail, sum_map_mul_left_nat, ← ih hS,
        multinomial_cons]
      by_cases ha : 0 < a
      · rw [if_pos ha, multinomial_cons, ← Nat.add_mul]
        congr 1
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        obtain ⟨S', hS'⟩ : ∃ S', rest.sum = S' + 1 := ⟨rest.sum - 1, by omega⟩
        rw [hS']
        rw [show a' + 1 - 1 = a' from by omega,
          show a' + (S' + 1) = a' + S' + 1 from by omega,
          show a' + 1 + (S' + 1 - 1) = a' + S' + 1 from by omega,
          show a' + 1 + (S' + 1) = a' + S' + 1 + 1 from by omega]
        exact (Nat.choose_succ_succ' (a' + S' + 1) a').symm
      · rw [if_neg ha]
        have ha0 : a = 0 := by omega
        subst ha0
        simp [Nat.choose_zero_right]
    ·
      have ha : 0 < a := by omega
      have hS0 : rest.sum = 0 := by omega
      have hrest0 := nat_sum_eq_zero hS0
      have htail0 : ∀ i ∈ List.range rest.length,
          (if 0 < rest.getD i 0
           then multinomial (a :: rest.set i (rest.getD i 0 - 1)) else 0) = 0 := by
        intro i _
        rw [if_neg (by rw [getD_zero_of_all_zero hrest0]; omega)]
      rw [List.map_congr_left htail0, nat_sum_map_zero _ _ (fun x hx => rfl),
        if_pos ha, multinomial_cons, multinomial_cons, hS0]
      rw [show a - 1 + 0 = a - 1 from by omega, show a + 0 = a from by omega,
        Nat.choose_self, Nat.choose_self]
      omega

theorem coeffSum_as_map_sum (p : Poly) (k : Mono) :
    coeffSum p k = (p.map fun t => if t.1 = k then t.2 else 0).sum := by
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨mo, c⟩ := hd
    rw [coeffSum_cons, List.map_cons, List.sum_cons, ih]

theorem vtmAux_replicate_zero : ∀ (k j : Nat),
    vtmAux j (List.replicate k 0) = [] := by
  intro k
  induction k with
  | zero => intro j; rfl
  | succ k ihk =>
    intro j
    rw [List.replicate_succ]
    simp only [vtmAux, ne_eq, not_true_eq_false, ite_false, List.nil_append]
    exact ihk (j + 1)

theorem getD_replicate_zero (m v : Nat) :
    (List.replicate m 0).getD v 0 = 0 :=
  getD_zero_of_all_zero (fun x hx => List.eq_of_mem_replicate hx) v

theorem sum_map_cast {α : Type} (L : List α) (f : α → Nat) :
    (L.map fun x => ((f x : Nat) : ℚ)).sum = ((L.map f).sum : ℚ) := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
    push_cast
    ring

theorem coeffSum_sumVars_pow (m : Nat) : ∀ (d : Nat) (γ : List Nat),
    γ ∈ compositions m d →
    coeffSum (Poly.pow (sumVars m) d) (vecToMono γ) = (multinomial γ : ℚ) := by
  intro d
  induction d with
  | zero =>
    intro γ hγ
    obtain ⟨hlen, hsum⟩ := mem_compositions_iff.mp hγ
    have hγ0 : γ = List.replicate m 0 := by
      apply list_ext_getD _ _ (by simp [hlen])
      intro v
      rw [getD_zero_of_all_zero (nat_sum_eq_zero hsum), getD_replicate_zero]
    subst hγ0
    have hvtm : vecToMono (List.replicate m 0) = [] := by
      rw [vecToMono_eq_vtmAux, vtmAux_replicate_zero]
    rw [hvtm, multinomial_replicate_zero]
    show coeffSum (Poly.const 1) [] = (1 : ℚ)
    unfold Poly.const
    rw [if_neg one_ne_zero, coeffSum_cons]
    simp
  | succ d ih =>
    intro γ hγ
    obtain ⟨hγlen, hγsum⟩ := mem_compositions_iff.mp hγ
    show coeffSum (Poly.mul (sumVars m) (Poly.pow (sumVars m) d)) _ = _
    set q := Poly.pow (sumVars m) d with hq
    rw [coeffSum_mul, sumVars_eq_literal, List.map_map]

    have hterm : ∀ i ∈ List.range m,
        ((fun t : Mono × ℚ =>
            (q.map fun u => if monoMul t.1 u.1 = vecToMono γ
              then t.2 * u.2 else 0).sum) ∘ fun i => (([(i, 1)] : Mono), (1 : ℚ))) i
        = if 0 < γ.getD i 0
          then (multinomial (γ.set i (γ.getD i 0 - 1)) : ℚ) else 0 := by
      intro i hi
      have hilt : i < m := List.mem_range.mp hi
      show (q.map fun u => if monoMul [(i, 1)] u.1 = vecToMono γ
              then 1 * u.2 else 0).sum = _
      have hδmem : 0 < γ.getD i 0 →
          γ.set i (γ.getD i 0 - 1) ∈ compositions m d := by
        intro hpos
        obtain ⟨h1, h2⟩ := sum_set_dec (by omega) hpos
        exact mem_compositions_iff.mpr ⟨by simp [hγlen], by omega⟩
      have hcong : ∀ u ∈ q, (if monoMul [(i, 1)] u.1 = vecToMono γ
            then 1 * u.2 else 0)
          = if 0 < γ.getD i 0 then
              (if u.1 = vecToMono (γ.set i (γ.getD i 0 - 1)) then u.2 else 0)
            else 0 := by
        intro u hu
        rw [hq] at hu
        obtain ⟨hgood, hdeg⟩ := polyBand_sumVars_pow m d u hu
        obtain ⟨δ, hδ, hδvtm⟩ := exists_composition_of_monoGood hgood hdeg
        by_cases hcond : monoMul [(i, 1)] u.1 = vecToMono γ
        · rw [if_pos hcond, one_mul]
          have hiff := (monoMul_var_eq_iff hγ hδ hilt).mp
            (by rw [hδvtm]; exact hcond)
          obtain ⟨hpos, hδeq⟩ := hiff
          rw [if_pos hpos, if_pos (by rw [← hδvtm, hδeq])]
        · rw [if_neg hcond]
          by_cases hpos : 0 < γ.getD i 0
          · rw [if_pos hpos]
            by_cases hueq : u.1 = vecToMono (γ.set i (γ.getD i 0 - 1))
            · exfalso
              apply hcond
              have hδeq : δ = γ.set i (γ.getD i 0 - 1) := by
                apply vecToMono_inj
                · simp [(mem_compositions_iff.mp hδ).1, hγlen]
                · rw [hδvtm]; exact hueq
              rw [← hδvtm]
              exact (monoMul_var_eq_iff hγ hδ hilt).mpr ⟨hpos, hδeq⟩
            · rw [if_neg hueq]
          · rw [if_neg hpos]
      rw [List.map_congr_left hcong]
      by_cases hpos : 0 < γ.getD i 0
      · simp only [if_pos hpos]
        rw [← coeffSum_as_map_sum, hq]
        rw [ih _ (hδmem hpos)]
      · simp only [if_neg hpos]
        exact sum_map_zero_of_all _ _ (fun x hx => rfl)
    rw [List.map_congr_left hterm]

    have hpascal := multinomial_pascal γ (by omega)
    have hcast : (multinomial γ : ℚ)
        = ((List.range γ.length).map fun i =>
            (((if 0 < γ.getD i 0
              then multinomial (γ.set i (γ.getD i 0 - 1)) else 0 : Nat)) : ℚ)).sum := by
      rw [sum_map_cast, ← hpascal]
    rw [hγlen] at hcast
    rw [hcast]
    congr 1
    apply List.map_congr_left
    intro i _
    split
    · rfl
    · simp

theorem sum_map_mul_left_rat {α : Type} (L : List α) (c : ℚ) (f : α → ℚ) :
    (L.map fun x => c * f x).sum = c * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem sum_nonneg_of_all : ∀ (M : List ℚ), (∀ x ∈ M, 0 ≤ x) → 0 ≤ M.sum := by
  intro M
  induction M with
  | nil => intro _; simp
  | cons hd tl ih =>
    intro h
    simp only [List.sum_cons]
    have h1 := h hd (by simp)
    have h2 := ih (fun y hy => h y (by simp [hy]))
    linarith

theorem sum_zero_all_zero : ∀ (M : List ℚ), (∀ x ∈ M, 0 ≤ x) → M.sum = 0 →
    ∀ x ∈ M, x = 0 := by
  intro M
  induction M with
  | nil => intro _ _ x hx; cases hx
  | cons hd tl ih =>
    intro hnn hsum x hx
    simp only [List.sum_cons] at hsum
    have h1 : 0 ≤ hd := hnn hd (by simp)
    have h2 : 0 ≤ tl.sum := sum_nonneg_of_all tl (fun y hy => hnn y (by simp [hy]))
    rcases List.mem_cons.mp hx with rfl | hx
    · linarith
    · exact ih (fun y hy => hnn y (by simp [hy])) (by linarith) x hx

theorem pred_convex_scaled (pred : ℚ → Bool)
    (hconv : ∀ a b l : ℚ, 0 ≤ l → l ≤ 1 → pred a = true → pred b = true →
      pred (l * a + (1 - l) * b) = true) :
    ∀ (L : List (ℚ × ℚ)) (s : ℚ), 0 < s →
      (∀ wb ∈ L, 0 ≤ wb.1) → (L.map (·.1)).sum = s →
      (∀ wb ∈ L, pred wb.2 = true) →
      pred ((L.map fun wb => (wb.1 / s) * wb.2).sum) = true := by
  intro L
  induction L with
  | nil =>
    intro s hs _ hsum _
    exfalso
    simp only [List.map_nil, List.sum_nil] at hsum
    rw [← hsum] at hs
    exact lt_irrefl 0 hs
  | cons hd tl ih =>
    intro s hs hw hsum hp
    obtain ⟨w, b⟩ := hd
    simp only [List.map_cons, List.sum_cons] at hsum ⊢
    have htl_nn : ∀ x ∈ tl.map (·.1), 0 ≤ x := by
      intro x hx
      obtain ⟨u, hu, hu1⟩ := List.mem_map.mp hx
      rw [← hu1]
      exact hw u (by simp [hu])
    by_cases hT0 : (tl.map (·.1)).sum = 0
    ·
      have hws : w = s := by
        have := hsum
        rw [hT0] at this
        linarith
      have htail : ∀ wb ∈ tl, ((wb.1 / s) * wb.2) = 0 := by
        intro wb hwb
        have h0 : wb.1 = 0 :=
          sum_zero_all_zero _ htl_nn hT0 wb.1 (List.mem_map.mpr ⟨wb, hwb, rfl⟩)
        rw [h0]
        ring
      rw [sum_map_zero_of_all _ _ htail, hws, div_self (ne_of_gt hs)]
      have := hp (s, b) (by rw [← hws]; simp)
      simpa using this
    ·
      have hTpos : 0 < (tl.map (·.1)).sum :=
        lt_of_le_of_ne (sum_nonneg_of_all _ htl_nn) (Ne.symm hT0)
      have hcomb := ih ((tl.map (·.1)).sum) hTpos
        (fun wb hwb => hw wb (by simp [hwb])) rfl
        (fun wb hwb => hp wb (by simp [hwb]))
      have hsplit : (tl.map fun wb => (wb.1 / s) * wb.2).sum
          = ((tl.map (·.1)).sum / s)
            * (tl.map fun wb => (wb.1 / (tl.map (·.1)).sum) * wb.2).sum := by
        rw [← sum_map_mul_left_rat]
        apply congrArg List.sum
        apply List.map_congr_left
        intro u _
        field_simp
      rw [hsplit]
      have hw0 : 0 ≤ w := hw (w, b) (by simp)
      have hwle : w ≤ s := by
        have := sum_nonneg_of_all _ htl_nn
        linarith
      have h1ws : 1 - w / s = (tl.map (·.1)).sum / s := by
        field_simp
        linarith
      rw [← h1ws]
      exact hconv b _ (w / s) (div_nonneg hw0 (le_of_lt hs))
        ((div_le_one hs).mpr hwle)
        (hp (w, b) (by simp)) hcomb

theorem option_guard_bind_eq_some {c : Prop} [Decidable c] {α : Type}
    {f : Unit → Option α} {b : α}
    (h : ((guard c : Option Unit) >>= f) = some b) : c ∧ f () = some b := by
  by_cases hc : c
  · refine ⟨hc, ?_⟩
    have hg : (guard c : Option Unit) = some () := by
      unfold guard
      rw [if_pos hc]
      rfl
    rwa [hg] at h
  · exfalso
    have hg : (guard c : Option Unit) = none := by
      unfold guard
      rw [if_neg hc]
      rfl
    rw [hg] at h
    simp at h

theorem option_bind_eq_some' {α β : Type} {x : Option α} {f : α → Option β}
    {b : β} (h : (x >>= f) = some b) : ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => simp at h
  | some a =>
    refine ⟨a, rfl, ?_⟩
    simpa using h

theorem filter_id_allFalse {smask : List Bool}
    (hmask : ∀ b ∈ smask, b = false) : smask.filter id = [] := by
  induction smask with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : hd = false := hmask hd (by simp)
    subst hhd
    simp only [List.filter_cons]
    rw [if_neg (by simp)]
    exact ih (fun b hb => hmask b (by simp [hb]))

theorem assembleVec_allFalse : ∀ (smask : List Bool) (β : List Nat),
    (∀ b ∈ smask, b = false) → β.length = smask.length →
    assembleVec smask [] β = β := by
  intro smask
  induction smask with
  | nil =>
    intro β _ hlen
    rw [List.length_nil] at hlen
    rw [List.eq_nil_of_length_eq_zero hlen]
    rfl
  | cons hd tl ih =>
    intro β hmask hlen
    have hhd : hd = false := hmask hd (by simp)
    subst hhd
    cases β with
    | nil => simp at hlen
    | cons b bs =>
      show b :: assembleVec tl [] bs = b :: bs
      rw [ih bs (fun x hx => hmask x (by simp [hx])) (by simpa using hlen)]

theorem compositionsUpTo_zero (d : Nat) : compositionsUpTo 0 d = [[]] := by
  unfold compositionsUpTo
  induction d with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, ih]
    simp [compositions]

theorem monoEval_nonneg {ρ : Nat → ℚ} (hρ : ∀ v, 0 ≤ ρ v) (mo : Mono) :
    0 ≤ monoEval ρ mo := by
  induction mo with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨v, e⟩ := hd
    rw [monoEval_cons]
    exact mul_nonneg (pow_nonneg (hρ v) e) ih

theorem homogenize_cons {m d : Nat} {mo : Mono} {c : ℚ} {tl : Poly} {hp : Poly}
    (h : homogenize m d ((mo, c) :: tl) = some hp) :
    ∃ acc, homogenize m d tl = some acc ∧ monoDeg mo ≤ d ∧
      hp = Poly.add acc
        (Poly.mul [(mo, c)] (Poly.pow (sumVars m) (d - monoDeg mo))) := by
  have hstep : homogenize m d ((mo, c) :: tl)
      = (homogenize m d tl).bind fun acc =>
          if monoDeg mo ≤ d
          then some (Poly.add acc
            (Poly.mul [(mo, c)] (Poly.pow (sumVars m) (d - monoDeg mo))))
          else none := rfl
  rw [hstep] at h
  obtain ⟨acc, hacc, hf⟩ := option_bind_eq_some' h
  refine ⟨acc, hacc, ?_⟩
  by_cases hdeg : monoDeg mo ≤ d
  · rw [if_pos hdeg] at hf
    exact ⟨hdeg, (Option.some.injEq _ _ ▸ hf).symm⟩
  · rw [if_neg hdeg] at hf
    cases hf

theorem homogenize_nil (m d : Nat) : homogenize m d [] = some [] := rfl

theorem homogenize_pairwise {m d : Nat} : ∀ {p hp : Poly},
    homogenize m d p = some hp →
    hp.Pairwise (fun s u => keyLT s.1 u.1) := by
  intro p
  induction p with
  | nil =>
    intro hp h
    rw [homogenize_nil] at h
    injection h with h
    rw [← h]
    exact List.Pairwise.nil
  | cons hd tl ih =>
    intro hp h
    obtain ⟨mo, c⟩ := hd
    obtain ⟨acc, _, _, rfl⟩ := homogenize_cons h
    exact canon_pairwise _

theorem homogenize_band {m d : Nat} : ∀ {p hp : Poly},
    (∀ t ∈ p, MonoGood m t.1) →
    homogenize m d p = some hp →
    PolyBand m d hp := by
  intro p
  induction p with
  | nil =>
    intro hp _ h
    rw [homogenize_nil] at h
    injection h with h
    rw [← h]
    intro t ht
    cases ht
  | cons hd tl ih =>
    intro hp hgood h
    obtain ⟨mo, c⟩ := hd
    obtain ⟨acc, hacc, hdeg, rfl⟩ := homogenize_cons h
    apply polyBand_add
    · exact ih (fun t ht => hgood t (by simp [ht])) hacc
    · have hterm : PolyBand m (monoDeg mo) [(mo, c)] := by
        intro t ht
        rcases List.mem_singleton.mp ht with rfl
        exact ⟨hgood (mo, c) (by simp), rfl⟩
      have := polyBand_mul hterm (polyBand_sumVars_pow m (d - monoDeg mo))
      have heq : monoDeg mo + (d - monoDeg mo) = d := by omega
      rwa [heq] at this

theorem homogenize_eval {m d : Nat} {ρ : Nat → ℚ}
    (hρsum : ((List.range m).map ρ).sum = 1) : ∀ {p hp : Poly},
    homogenize m d p = some hp →
    Poly.eval ρ hp = Poly.eval ρ p := by
  intro p
  induction p with
  | nil =>
    intro hp h
    rw [homogenize_nil] at h
    injection h with h
    rw [← h]
  | cons hd tl ih =>
    intro hp h
    obtain ⟨mo, c⟩ := hd
    obtain ⟨acc, hacc, _, rfl⟩ := homogenize_cons h
    rw [Poly.eval_add, Poly.eval_mul, Poly.eval_pow, Poly.eval_sumVars,
      hρsum, one_pow, mul_one, ih hacc]
    simp only [Poly.eval_cons, Poly.eval_nil]
    ring

theorem polyGood_const_one {m : Nat} : ∀ t ∈ Poly.const (1 : ℚ), MonoGood m t.1 := by
  intro t ht
  unfold Poly.const at ht
  rw [if_neg one_ne_zero] at ht
  rcases List.mem_singleton.mp ht with rfl
  exact ⟨List.Pairwise.nil, by simp, by simp⟩

theorem polyGood_canon {m : Nat} {p : Poly} (hp : ∀ t ∈ p, MonoGood m t.1) :
    ∀ t ∈ Poly.canon p, MonoGood m t.1 := by
  intro t ht
  obtain ⟨u, hu, hu1⟩ := List.mem_map.mp (canon_keys_subset p t ht)
  rw [← hu1]
  exact hp u hu

theorem polyGood_append {m : Nat} {p q : Poly}
    (hp : ∀ t ∈ p, MonoGood m t.1) (hq : ∀ t ∈ q, MonoGood m t.1) :
    ∀ t ∈ p ++ q, MonoGood m t.1 := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact hp t h
  · exact hq t h

theorem polyGood_add {m : Nat} {p q : Poly}
    (hp : ∀ t ∈ p, MonoGood m t.1) (hq : ∀ t ∈ q, MonoGood m t.1) :
    ∀ t ∈ Poly.add p q, MonoGood m t.1 :=
  polyGood_canon (polyGood_append hp hq)

theorem polyGood_scale {m : Nat} {c : ℚ} {p : Poly}
    (hp : ∀ t ∈ p, MonoGood m t.1) :
    ∀ t ∈ Poly.scale c p, MonoGood m t.1 := by
  intro t ht
  unfold Poly.scale at ht
  split at ht
  · cases ht
  · obtain ⟨u, hu, hu1⟩ := List.mem_map.mp ht
    rw [← hu1]
    exact hp u hu

theorem polyGood_mul {m : Nat} {p q : Poly}
    (hp : ∀ t ∈ p, MonoGood m t.1) (hq : ∀ t ∈ q, MonoGood m t.1) :
    ∀ t ∈ Poly.mul p q, MonoGood m t.1 := by
  intro t ht
  unfold Poly.mul at ht
  obtain ⟨x, hx, hx1⟩ := List.mem_map.mp (canon_keys_subset _ t ht)
  obtain ⟨a, ha, hx2⟩ := List.mem_flatMap.mp hx
  obtain ⟨w, hw, hw1⟩ := List.mem_map.mp hx2
  rw [← hx1, ← hw1]
  exact monoMul_good (hp a ha).2.2 (hq w hw).2.2

theorem polyGood_pow {m : Nat} {p : Poly} (hp : ∀ t ∈ p, MonoGood m t.1) :
    ∀ (n : Nat), ∀ t ∈ Poly.pow p n, MonoGood m t.1
  | 0 => polyGood_const_one
  | n + 1 => polyGood_mul hp (polyGood_pow hp n)

theorem coordPoly_good (verts : List (List ℚ)) (j : Nat) :
    ∀ t ∈ coordPoly verts j, MonoGood verts.length t.1 := by
  unfold coordPoly
  apply polyGood_canon
  intro t ht
  obtain ⟨i, hi, hi1⟩ := List.mem_map.mp ht
  rw [← hi1]
  refine ⟨by simp, by simp, ?_⟩
  intro q hq
  rcases List.mem_singleton.mp hq with rfl
  simpa using List.mem_range.mp hi

theorem monoSubstFold_good {m : Nat} {σp : Nat → Poly}
    (hσ : ∀ v, ∀ t ∈ σp v, MonoGood m t.1) : ∀ (mo : Mono),
    ∀ t ∈ mo.foldr (fun q a => Poly.mul (Poly.pow (σp q.1) q.2) a)
      (Poly.const 1), MonoGood m t.1 := by
  intro mo
  induction mo with
  | nil => exact polyGood_const_one
  | cons hd tl ih =>
    simp only [List.foldr_cons]
    exact polyGood_mul (polyGood_pow (hσ hd.1) hd.2) ih

theorem substInto_good {m : Nat} {σp : Nat → Poly}
    (hσ : ∀ v, ∀ t ∈ σp v, MonoGood m t.1) (p : Poly) :
    ∀ t ∈ Poly.substInto σp p, MonoGood m t.1 := by
  unfold Poly.substInto
  induction p with
  | nil => intro t ht; cases ht
  | cons hd tl ih =>
    obtain ⟨mo, c⟩ := hd
    simp only [List.foldr_cons]
    exact polyGood_add ih (polyGood_scale (monoSubstFold_good hσ mo))

theorem insertVar_of_lt_head (t : Nat × Nat) (mo : Mono)
    (h : ∀ u ∈ mo, t.1 < u.1) : insertVar t mo = t :: mo := by
  cases mo with
  | nil =>
    obtain ⟨v, e⟩ := t
    rfl
  | cons hd tl =>
    obtain ⟨v, e⟩ := t
    obtain ⟨v', e'⟩ := hd
    have hlt : v < v' := h (v', e') (by simp)
    simp only [insertVar, if_pos hlt]

theorem foldr_insertVar_eq_self (mo : Mono)
    (hsort : mo.Pairwise (fun s u => s.1 < u.1)) :
    mo.foldr insertVar [] = mo := by
  induction mo with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.pairwise_cons] at hsort
    simp only [List.foldr_cons, ih hsort.2]
    exact insertVar_of_lt_head hd tl hsort.1

theorem monoCanon_eq_self {mo : Mono}
    (hsort : mo.Pairwise (fun s u => s.1 < u.1))
    (hnz : ∀ p ∈ mo, p.2 ≠ 0) : monoCanon mo = mo := by
  unfold monoCanon
  rw [foldr_insertVar_eq_self mo hsort]
  exact List.filter_eq_self.mpr (fun t ht => by simpa using hnz t ht)

theorem monoMul_nil_right {mo : Mono}
    (hsort : mo.Pairwise (fun s u => s.1 < u.1))
    (hnz : ∀ p ∈ mo, p.2 ≠ 0) : monoMul mo [] = mo := by
  unfold monoMul
  rw [List.append_nil]
  exact monoCanon_eq_self hsort hnz

theorem pj_coeffOf_eq (m d : Nat) (hp : Poly) (F : List Nat → List Nat)
    (hF : ∀ β ∈ compositions m d, F β = β)
    (hpPW : hp.Pairwise (fun s u => keyLT s.1 u.1))
    (γ : List Nat) (hγ : γ ∈ compositions m d) :
    Poly.coeffOf
      ((subCompositions ([] : List Nat)).foldr
        (fun k acc => Poly.add acc (Poly.scale
          ((if (k.foldr (·+·) 0) % 2 = 0 then 1 else -1) *
            (((((([] : List Nat)).zip k).map fun q => Prim.nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ))
          (Poly.mul (Poly.canon ((compositions m (d - k.foldr (·+·) 0)).map fun β =>
              (vecToMono β,
               hp.coeffOf (vecToMono (F β)) / ((multinomial (F β) : Nat) : ℚ)
                 * ((multinomial β : Nat) : ℚ))))
            (Poly.pow (sumVars m) (k.foldr (·+·) 0))))) [])
      (vecToMono γ)
    = coeffSum hp (vecToMono γ) := by
  obtain ⟨hγlen, hγsum⟩ := mem_compositions_iff.mp hγ

  show Poly.coeffOf (Poly.add [] (Poly.scale _ (Poly.mul _ _))) _ = _

  have hqk : ∀ β ∈ compositions m (d - ([] : List Nat).foldr (·+·) 0),
      (vecToMono β,
       hp.coeffOf (vecToMono (F β)) / ((multinomial (F β) : Nat) : ℚ)
         * ((multinomial β : Nat) : ℚ))
      = (vecToMono β,
         hp.coeffOf (vecToMono β) / ((multinomial β : Nat) : ℚ)
           * ((multinomial β : Nat) : ℚ)) := by
    intro β hβ
    rw [hF β (by simpa using hβ)]

  set qk := Poly.canon ((compositions m (d - ([] : List Nat).foldr (·+·) 0)).map fun β =>
      (vecToMono β,
       hp.coeffOf (vecToMono (F β)) / ((multinomial (F β) : Nat) : ℚ)
         * ((multinomial β : Nat) : ℚ))) with hqkdef

  have hPW : (Poly.add [] (Poly.scale
      ((if (([] : List Nat).foldr (·+·) 0) % 2 = 0 then 1 else -1) *
        (((((([] : List Nat)).zip ([] : List Nat)).map fun q => Prim.nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ))
      (Poly.mul qk (Poly.pow (sumVars m) (([] : List Nat).foldr (·+·) 0))))).Pairwise
        (fun s u => keyLT s.1 u.1) := canon_pairwise _
  rw [coeffOf_eq_coeffSum_of_pairwise _ hPW, coeffSum_add, coeffSum_nil,
    coeffSum_scale]
  have hfac : ((if (([] : List Nat).foldr (·+·) 0) % 2 = 0 then 1 else -1) *
      (((((([] : List Nat)).zip ([] : List Nat)).map fun q => Prim.nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ)) = 1 := by
    norm_num
  rw [hfac, one_mul, zero_add]

  show coeffSum (Poly.mul qk (Poly.const 1)) _ = _
  rw [coeffSum_mul]
  have hconst : Poly.const (1 : ℚ) = [(([] : Mono), (1 : ℚ))] := by
    unfold Poly.const
    rw [if_neg one_ne_zero]
  rw [hconst]

  have hqk_keys : ∀ u ∈ qk, u.1.Pairwise (fun s t => s.1 < t.1) ∧
      ∀ q ∈ u.1, q.2 ≠ 0 := by
    intro u hu
    rw [hqkdef] at hu
    obtain ⟨x, hx, hx1⟩ := List.mem_map.mp (canon_keys_subset _ u hu)
    obtain ⟨β, hβ, hβ1⟩ := List.mem_map.mp hx
    have hxkey : u.1 = vecToMono β := by
      rw [← hx1, ← hβ1]
    rw [hxkey, vecToMono_eq_vtmAux]
    exact vtmAux_canonical 0 β
  have hinner : ∀ u ∈ qk,
      ([(([] : Mono), (1 : ℚ))].map fun w =>
        if monoMul u.1 w.1 = vecToMono γ then u.2 * w.2 else 0).sum
      = if u.1 = vecToMono γ then u.2 else 0 := by
    intro u hu
    obtain ⟨hs, hz⟩ := hqk_keys u hu
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [monoMul_nil_right hs hz]
    split
    · ring
    · ring
  rw [List.map_congr_left hinner, ← coeffSum_as_map_sum, hqkdef, coeffSum_canon,
    coeffSum_map_rows]

  have hcond : ∀ β ∈ compositions m (d - ([] : List Nat).foldr (·+·) 0),
      (if vecToMono β = vecToMono γ
       then hp.coeffOf (vecToMono (F β)) / ((multinomial (F β) : Nat) : ℚ)
              * ((multinomial β : Nat) : ℚ) else 0)
      = (if β = γ
         then hp.coeffOf (vecToMono (F β)) / ((multinomial (F β) : Nat) : ℚ)
              * ((multinomial β : Nat) : ℚ) else 0) := by
    intro β hβ
    by_cases hβγ : β = γ
    · subst hβγ
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg ?_, if_neg hβγ]
      intro hvtm
      apply hβγ
      apply vecToMono_inj ?_ hvtm
      rw [(mem_compositions_iff.mp (by simpa using hβ)).1, hγlen]

  rw [List.map_congr_left hcond,
    sum_map_single_witness _ _ γ (by simpa using hγ)
      (compositions_nodup _ _)]
  rw [hF γ hγ]
  rw [div_mul_cancel₀ _ (by
    exact_mod_cast (multinomial_pos γ).ne')]
  exact coeffOf_eq_coeffSum_of_pairwise hp hpPW _

/-- The extension-free Bernstein-cone kernel: if the exact-rational
forward-difference table passes a convex-predicate sweep, then the
polynomial's value at every nonnegative unit-sum weighting of the
vertices satisfies the predicate. -/
theorem fdBernstein_empty_sound
    (verts : List (List ℚ)) (smask : List Bool) (d : Nat) (p : Poly)
    (t : FDTable) (pred : ℚ → Bool)
    (hmask : ∀ b ∈ smask, b = false)
    (hfd : fdBernstein verts smask d p = some t)
    (hgrid : gridAll pred t = true)
    (hconv : ∀ a b l : ℚ, 0 ≤ l → l ≤ 1 → pred a = true → pred b = true →
      pred (l * a + (1 - l) * b) = true)
    (ρ : Nat → ℚ) (hρ : ∀ v, 0 ≤ ρ v)
    (hρsum : ((List.range verts.length).map ρ).sum = 1) :
    pred (Poly.eval (fun j =>
      ((List.range verts.length).map
        fun i => (verts.getD i []).getD j 0 * ρ i).sum) p) = true := by

  simp only [fdBernstein] at hfd
  obtain ⟨hlen, hfd⟩ := option_guard_bind_eq_some hfd
  obtain ⟨hmB, hfd⟩ := option_guard_bind_eq_some hfd
  obtain ⟨hp, hhp, hfd⟩ := option_bind_eq_some' hfd
  have ht : t.grid = (compositionsUpTo (smask.filter id).length d).map fun j =>
      (j, bernCoeffRows (verts.length - (smask.filter id).length) d
        ((subCompositions j).foldr
          (fun k acc =>
            Poly.add acc (Poly.scale
              ((if (k.foldr (·+·) 0) % 2 = 0 then 1 else -1) *
                ((((j.zip k).map fun q => Prim.nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ))
              (Poly.mul
                (Poly.canon ((compositions
                    (verts.length - (smask.filter id).length)
                    (d - k.foldr (·+·) 0)).map fun β =>
                  (vecToMono β,
                   hp.coeffOf (vecToMono (assembleVec smask k β))
                     / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                     * ((multinomial β : Nat) : ℚ))))
                (Poly.pow (sumVars
                    (verts.length - (smask.filter id).length))
                  (k.foldr (·+·) 0)))))
          [])) := by
    have := hfd.symm
    injection this with h
    rw [h]

  rw [filter_id_allFalse hmask] at ht
  simp only [List.length_nil, Nat.sub_zero, compositionsUpTo_zero,
    List.map_cons, List.map_nil] at ht

  unfold gridAll at hgrid
  rw [ht] at hgrid
  simp only [List.all_cons, List.all_nil, Bool.and_true] at hgrid

  have hband : PolyBand verts.length d hp :=
    homogenize_band (substInto_good (coordPoly_good verts) p) hhp
  have hpPW := homogenize_pairwise hhp
  have hpred : ∀ γ ∈ compositions verts.length d,
      pred (coeffSum hp (vecToMono γ) / ((multinomial γ : Nat) : ℚ)) = true := by
    intro γ hγ
    have hFγ : ∀ β ∈ compositions verts.length d, assembleVec smask [] β = β := by
      intro β hβ
      exact assembleVec_allFalse smask β hmask
        (by rw [(mem_compositions_iff.mp hβ).1, hlen])
    have hval := pj_coeffOf_eq verts.length d hp (assembleVec smask []) hFγ hpPW γ hγ
    have hall := List.all_eq_true.mp hgrid
    have hthis := hall _ (List.mem_map.mpr ⟨γ, hγ, rfl⟩)
    rw [← hval]
    exact hthis

  set x : Nat → ℚ := fun j =>
    ((List.range verts.length).map fun i => (verts.getD i []).getD j 0 * ρ i).sum
    with hxdef
  have hval : Poly.eval x p = Poly.eval ρ hp := by
    rw [homogenize_eval hρsum hhp, Poly.eval_substInto]
    congr 1
    funext j
    rw [Poly.eval_coordPoly]
  rw [hval]

  rw [eval_eq_enum_sum ρ verts.length d hp hband]

  have hsplit : ∀ γ ∈ compositions verts.length d,
      coeffSum hp (vecToMono γ) * monoEval ρ (vecToMono γ)
      = ((((multinomial γ : Nat) : ℚ) * monoEval ρ (vecToMono γ)) / 1)
        * (coeffSum hp (vecToMono γ) / ((multinomial γ : Nat) : ℚ)) := by
    intro γ _
    have hm0 : ((multinomial γ : Nat) : ℚ) ≠ 0 := by
      exact_mod_cast (multinomial_pos γ).ne'
    field_simp
  rw [List.map_congr_left hsplit]

  have hwsum : ((compositions verts.length d).map
      (fun γ => ((multinomial γ : Nat) : ℚ) * monoEval ρ (vecToMono γ))).sum = 1 := by
    have henum := eval_eq_enum_sum ρ verts.length d
      (Poly.pow (sumVars verts.length) d) (polyBand_sumVars_pow _ _)
    rw [Poly.eval_pow, Poly.eval_sumVars, hρsum, one_pow] at henum
    rw [show ((compositions verts.length d).map
        (fun γ => ((multinomial γ : Nat) : ℚ) * monoEval ρ (vecToMono γ)))
      = ((compositions verts.length d).map
        (fun γ => coeffSum (Poly.pow (sumVars verts.length) d) (vecToMono γ)
          * monoEval ρ (vecToMono γ))) from
      List.map_congr_left (fun γ hγ => by
        rw [coeffSum_sumVars_pow verts.length d γ hγ])]
    exact henum.symm

  have hfinal := pred_convex_scaled pred hconv
    ((compositions verts.length d).map fun γ =>
      (((multinomial γ : Nat) : ℚ) * monoEval ρ (vecToMono γ),
       coeffSum hp (vecToMono γ) / ((multinomial γ : Nat) : ℚ)))
    1 one_pos
    (by
      intro wb hwb
      obtain ⟨γ, _, hγ1⟩ := List.mem_map.mp hwb
      rw [← hγ1]
      exact mul_nonneg (by exact_mod_cast Nat.zero_le _)
        (monoEval_nonneg hρ _))
    (by
      rw [List.map_map]
      rw [show ((fun wb : ℚ × ℚ => wb.1) ∘ fun γ =>
          (((multinomial γ : Nat) : ℚ) * monoEval ρ (vecToMono γ),
           coeffSum hp (vecToMono γ) / ((multinomial γ : Nat) : ℚ)))
        = fun γ => ((multinomial γ : Nat) : ℚ) * monoEval ρ (vecToMono γ) from rfl]
      exact hwsum)
    (by
      intro wb hwb
      obtain ⟨γ, hγ, hγ1⟩ := List.mem_map.mp hwb
      rw [← hγ1]
      exact hpred γ hγ)
  rw [List.map_map] at hfinal
  have hfeq : (List.map ((fun wb : ℚ × ℚ => wb.1 / 1 * wb.2) ∘ fun γ =>
      (((multinomial γ : Nat) : ℚ) * monoEval ρ (vecToMono γ),
       coeffSum hp (vecToMono γ) / ((multinomial γ : Nat) : ℚ)))
      (compositions verts.length d))
      = (List.map (fun γ => (((multinomial γ : Nat) : ℚ)
            * monoEval ρ (vecToMono γ)) / 1
          * (coeffSum hp (vecToMono γ) / ((multinomial γ : Nat) : ℚ)))
        (compositions verts.length d)) := by
    apply List.map_congr_left
    intro γ _
    rfl
  rw [hfeq] at hfinal
  exact hfinal

theorem sum_map_range_succ_head (n : Nat) (f : Nat → ℚ) :
    ((List.range (n + 1)).map f).sum
      = f 0 + ((List.range n).map (fun t => f (t + 1))).sum := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  rfl

theorem sum_map_range_succ_last (n : Nat) (f : Nat → ℚ) :
    ((List.range (n + 1)).map f).sum
      = ((List.range n).map f).sum + f n := by
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

theorem triangle_exchange (d : Nat) (G : Nat → Nat → ℚ) :
    ((List.range (d + 1)).map (fun a =>
      ((List.range (d - a + 1)).map (fun t => G a t)).sum)).sum
    = ((List.range (d + 1)).map (fun r =>
        ((List.range (r + 1)).map (fun k => G k (r - k))).sum)).sum := by
  induction d with
  | zero => simp
  | succ n ih =>

    rw [sum_map_range_succ_last (n + 1) (fun r =>
      ((List.range (r + 1)).map (fun k => G k (r - k))).sum),
      sum_map_range_succ_last (n + 1) (fun k => G k (n + 1 - k))]

    rw [sum_map_range_succ_last (n + 1) (fun a =>
      ((List.range (n + 1 - a + 1)).map (fun t => G a t)).sum)]
    have hrow : ∀ a ∈ List.range (n + 1),
        ((List.range (n + 1 - a + 1)).map (fun t => G a t)).sum
          = ((List.range (n - a + 1)).map (fun t => G a t)).sum
            + G a (n + 1 - a) := by
      intro a ha
      have haLt : a < n + 1 := List.mem_range.mp ha
      have hstep : n + 1 - a = (n - a) + 1 := by omega
      rw [hstep, sum_map_range_succ_last]
    rw [List.map_congr_left hrow, sum_map_add]

    have h0 : n + 1 - (n + 1) + 1 = 1 := by omega
    have h1 : n + 1 - (n + 1) = 0 := by omega
    rw [h0, h1, List.range_one]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [ih]
    ring

theorem one_add_pow_enum (x : ℚ) : ∀ (n : Nat),
    (1 + x) ^ n
      = ((List.range (n + 1)).map
          (fun t => (Nat.choose n t : ℚ) * x ^ t)).sum := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
    have hsplit : (1 + x) ^ (m + 1) = (1 + x) ^ m + x * (1 + x) ^ m := by
      ring
    rw [hsplit, ih]

    have hpascal : ∀ t ∈ List.range (m + 1 + 1),
        ((Nat.choose (m + 1) t : ℚ) * x ^ t)
          = (Nat.choose m t : ℚ) * x ^ t
            + (if t = 0 then 0 else (Nat.choose m (t - 1) : ℚ) * x ^ t) := by
      intro t _
      cases t with
      | zero => simp
      | succ t' =>
        rw [if_neg (Nat.succ_ne_zero t')]
        rw [Nat.choose_succ_succ m t']
        push_cast
        ring
    rw [List.map_congr_left hpascal, sum_map_add]
    congr 1
    ·
      rw [sum_map_range_succ_last (m + 1) (fun t => (Nat.choose m t : ℚ) * x ^ t),
        Nat.choose_eq_zero_of_lt (by omega)]
      simp
    ·
      rw [sum_map_range_succ_head (m + 1)
        (fun t => if t = 0 then 0 else (Nat.choose m (t - 1) : ℚ) * x ^ t)]
      rw [if_pos rfl, zero_add]
      rw [show ((List.range (m + 1)).map fun t =>
          if t + 1 = 0 then 0 else (Nat.choose m (t + 1 - 1) : ℚ) * x ^ (t + 1))
          = ((List.range (m + 1)).map fun t =>
              x * ((Nat.choose m t : ℚ) * x ^ t)) from
        List.map_congr_left (fun t _ => by
          rw [if_neg (Nat.succ_ne_zero t)]
          have : t + 1 - 1 = t := by omega
          rw [this]
          ring)]
      rw [sum_map_mul_left_rat]

theorem choose_sub_sub {d r k : Nat} (hkr : k ≤ r) (hrd : r ≤ d) :
    Nat.choose d k * Nat.choose (d - k) (r - k)
      = Nat.choose d r * Nat.choose r k := by
  have hkd : k ≤ d := le_trans hkr hrd
  have hrk : r - k ≤ d - k := by omega
  apply Nat.eq_of_mul_eq_mul_right
    (Nat.mul_pos (Nat.factorial_pos k)
      (Nat.mul_pos (Nat.factorial_pos (r - k)) (Nat.factorial_pos (d - r))))
  have h1 : Nat.choose d k * Nat.choose (d - k) (r - k)
        * (k.factorial * ((r - k).factorial * (d - r).factorial))
      = Nat.choose d k * k.factorial
        * (Nat.choose (d - k) (r - k) * (r - k).factorial
            * (d - k - (r - k)).factorial) := by
    have : d - k - (r - k) = d - r := by omega
    rw [this]
    ring
  have h2 : Nat.choose d r * Nat.choose r k
        * (k.factorial * ((r - k).factorial * (d - r).factorial))
      = Nat.choose d r * (Nat.choose r k * k.factorial * (r - k).factorial)
        * (d - r).factorial := by
    ring
  rw [h1, h2, Nat.choose_mul_factorial_mul_factorial hrk,
    Nat.choose_mul_factorial_mul_factorial hkr]
  have h3 : Nat.choose d k * k.factorial * (d - k).factorial = d.factorial :=
    Nat.choose_mul_factorial_mul_factorial hkd
  have h4 : Nat.choose d r * r.factorial * (d - r).factorial = d.factorial :=
    Nat.choose_mul_factorial_mul_factorial hrd
  calc Nat.choose d k * k.factorial * (d - k).factorial
      = d.factorial := h3
    _ = Nat.choose d r * r.factorial * (d - r).factorial := h4.symm

theorem compositions_zero_iff (t : Nat) :
    compositions 0 t = if t = 0 then [[]] else [] := by
  cases t with
  | zero => rfl
  | succ t' => rfl

theorem compositions_one (t : Nat) : compositions 1 t = [[t]] := by
  show (List.range (t + 1)).flatMap
    (fun a => (compositions 0 (t - a)).map (a :: ·)) = [[t]]
  rw [List.range_succ, List.flatMap_append]
  have h1 : (List.range t).flatMap
      (fun a => (compositions 0 (t - a)).map (a :: ·)) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro a ha
    have : t - a ≠ 0 := by
      have := List.mem_range.mp ha
      omega
    rw [compositions_zero_iff, if_neg this]
    rfl
  rw [h1, List.nil_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Nat.sub_self, compositions_zero_iff, if_pos rfl]
  rfl

theorem compositionsUpTo_one (d : Nat) :
    compositionsUpTo 1 d = (List.range (d + 1)).map (fun r => [r]) := by
  unfold compositionsUpTo
  rw [show (List.range (d + 1)).flatMap (compositions 1)
      = (List.range (d + 1)).flatMap (fun r => [[r]]) from
    List.flatMap_congr (fun r _ => compositions_one r)]
  induction (List.range (d + 1)) with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.flatMap_cons, List.map_cons, ih]
    rfl

theorem compositions_two (d : Nat) :
    compositions 2 d = (List.range (d + 1)).map (fun a => [a, d - a]) := by
  show (List.range (d + 1)).flatMap
    (fun a => (compositions 1 (d - a)).map (a :: ·)) = _
  rw [show (List.range (d + 1)).flatMap
      (fun a => (compositions 1 (d - a)).map (a :: ·))
      = (List.range (d + 1)).flatMap (fun a => [[a, d - a]]) from
    List.flatMap_congr (fun a _ => by rw [compositions_one]; rfl)]
  induction (List.range (d + 1)) with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.flatMap_cons, List.map_cons, ih]
    rfl

theorem subCompositions_single (r : Nat) :
    subCompositions [r] = (List.range (r + 1)).map (fun k => [k]) := by
  show (List.range (r + 1)).flatMap
    (fun k => (subCompositions []).map (k :: ·)) = _
  rw [show (List.range (r + 1)).flatMap
      (fun k => (subCompositions []).map (k :: ·))
      = (List.range (r + 1)).flatMap (fun k => [[k]]) from
    List.flatMap_congr (fun k _ => rfl)]
  induction (List.range (r + 1)) with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.flatMap_cons, List.map_cons, ih]
    rfl

theorem compositions_zero_total (m : Nat) :
    compositions m 0 = [List.replicate m 0] := by
  induction m with
  | zero => rfl
  | succ n ih =>
    show (List.range 1).flatMap
      (fun a => (compositions n (0 - a)).map (a :: ·)) = _
    rw [List.range_one, List.flatMap_cons]
    simp [ih, List.replicate_succ]

theorem subCompositions_replicate_zero (m : Nat) :
    subCompositions (List.replicate m 0) = [List.replicate m 0] := by
  induction m with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    show (List.range 1).flatMap
      (fun k => (subCompositions (List.replicate n 0)).map (k :: ·)) = _
    rw [List.range_one, List.flatMap_cons]
    simp [ih, List.replicate_succ]

theorem replicate_zero_foldr_add (m : Nat) :
    (List.replicate m 0).foldr (· + ·) 0 = 0 := by
  induction m with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.foldr_cons, ih]

theorem zip_replicate_binom_one (j : List Nat) :
    (((j.zip j).map fun q => Prim.nchoose q.1 q.2).foldr (· * ·) 1) = 1 := by
  induction j with
  | nil => rfl
  | cons a rest ih =>
    rw [List.zip_cons_cons, List.map_cons, List.foldr_cons, ih,
      Prim.nchoose_eq_choose, Nat.choose_self]

theorem mem_compositionsUpTo_of_sum_le {parts : Nat} {k : List Nat}
    {bound : Nat} (hk : k ∈ compositions parts (k.foldr (· + ·) 0))
    (hle : k.foldr (· + ·) 0 ≤ bound) :
    k ∈ compositionsUpTo parts bound := by
  unfold compositionsUpTo
  apply List.mem_flatMap.mpr
  exact ⟨k.foldr (· + ·) 0, List.mem_range.mpr (by omega), hk⟩

theorem filter_not_length (smask : List Bool) :
    (smask.filter (!·)).length = smask.length - (smask.filter id).length := by
  induction smask with
  | nil => rfl
  | cons b rest ih =>
    have hle := List.length_filter_le id rest
    cases b <;> simp_all [List.filter_cons] <;> omega

theorem assembleVec_length : ∀ (smask : List Bool) (k β : List Nat),
    k.length = (smask.filter id).length →
    β.length = (smask.filter (!·)).length →
    (assembleVec smask k β).length = smask.length := by
  intro smask
  induction smask with
  | nil => intro k β _ _; rfl
  | cons b rest ih =>
    intro k β hk hβ
    cases b with
    | true =>
      cases k with
      | nil => simp [List.filter_cons] at hk
      | cons k₀ ks =>
        show (k₀ :: assembleVec rest ks β).length = _
        rw [List.length_cons, ih ks β (by simpa [List.filter_cons] using hk)
          (by simpa [List.filter_cons] using hβ), List.length_cons]
    | false =>
      cases β with
      | nil => simp [List.filter_cons] at hβ
      | cons b₀ bs =>
        show (b₀ :: assembleVec rest k bs).length = _
        rw [List.length_cons, ih k bs (by simpa [List.filter_cons] using hk)
          (by simpa [List.filter_cons] using hβ), List.length_cons]

theorem assembleVec_foldr_add : ∀ (smask : List Bool) (k β : List Nat),
    k.length = (smask.filter id).length →
    β.length = (smask.filter (!·)).length →
    (assembleVec smask k β).foldr (· + ·) 0
      = k.foldr (· + ·) 0 + β.foldr (· + ·) 0 := by
  intro smask
  induction smask with
  | nil =>
    intro k β hk hβ
    simp at hk hβ
    subst hk
    subst hβ
    rfl
  | cons b rest ih =>
    intro k β hk hβ
    cases b with
    | true =>
      cases k with
      | nil => simp [List.filter_cons] at hk
      | cons k₀ ks =>
        show (k₀ :: assembleVec rest ks β).foldr (· + ·) 0 = _
        rw [List.foldr_cons, ih ks β (by simpa [List.filter_cons] using hk)
          (by simpa [List.filter_cons] using hβ), List.foldr_cons]
        omega
    | false =>
      cases β with
      | nil => simp [List.filter_cons] at hβ
      | cons b₀ bs =>
        show (b₀ :: assembleVec rest k bs).foldr (· + ·) 0 = _
        rw [List.foldr_cons, ih k bs (by simpa [List.filter_cons] using hk)
          (by simpa [List.filter_cons] using hβ), List.foldr_cons]
        omega

theorem coeffSum_mul_const_left {c₀ : ℚ} {Q : Poly} {k : Mono}
    (hQ : ∀ u ∈ Q, u.1.Pairwise (fun s t => s.1 < t.1) ∧
      ∀ q ∈ u.1, q.2 ≠ 0) :
    coeffSum (Poly.mul [([], c₀)] Q) k = c₀ * coeffSum Q k := by
  rw [coeffSum_mul]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have hcongr : ∀ u ∈ Q,
      (if monoMul ([] : Mono) u.1 = k then c₀ * u.2 else 0)
        = c₀ * (if u.1 = k then u.2 else 0) := by
    intro u hu
    have hcanon : monoMul ([] : Mono) u.1 = u.1 := by
      show monoCanon ([] ++ u.1) = u.1
      rw [List.nil_append]
      exact monoCanon_eq_self (hQ u hu).1 (hQ u hu).2
    rw [hcanon]
    split
    · rfl
    · ring
  rw [List.map_congr_left hcongr, sum_map_mul_left_rat, ← coeffSum_as_map_sum]
  ring

theorem homogenize_const_coeffSum {m d : Nat} {c₀ : ℚ} {hp : Poly}
    (hhp : homogenize m d (Poly.const c₀) = some hp) :
    ∀ γ ∈ compositions m d,
      coeffSum hp (vecToMono γ) = c₀ * (multinomial γ : ℚ) := by
  intro γ hγ
  by_cases hc : c₀ = 0
  · subst hc
    have hpn : hp = [] := by
      have : Poly.const (0 : ℚ) = [] := by
        unfold Poly.const
        rw [if_pos rfl]
      rw [this, homogenize_nil] at hhp
      injection hhp with h
      exact h.symm
    rw [hpn]
    simp
  · have hpc : Poly.const c₀ = [(([] : Mono), c₀)] := by
      unfold Poly.const
      rw [if_neg hc]
    rw [hpc] at hhp
    obtain ⟨acc, hacc, _, rfl⟩ := homogenize_cons hhp
    rw [homogenize_nil] at hacc
    injection hacc with hacc
    subst hacc
    show coeffSum (Poly.add []
      (Poly.mul [(([] : Mono), c₀)]
        (Poly.pow (sumVars m) (d - monoDeg ([] : Mono))))) (vecToMono γ) = _
    rw [coeffSum_add, coeffSum_nil, zero_add]
    have hdeg : monoDeg ([] : Mono) = 0 := rfl
    rw [hdeg, Nat.sub_zero]
    rw [coeffSum_mul_const_left (fun u hu =>
      ⟨((polyBand_sumVars_pow m d) u hu).1.1,
       ((polyBand_sumVars_pow m d) u hu).1.2.1⟩)]
    rw [coeffSum_sumVars_pow m d γ hγ]

theorem fdBernstein_sound_const
    (verts : List (List ℚ)) (smask : List Bool) (d : Nat) (c₀ : ℚ)
    (t : FDTable) (pred : ℚ → Bool)
    (hfd : fdBernstein verts smask d (Poly.const c₀) = some t)
    (hgrid : gridAll pred t = true) :
    pred c₀ = true := by

  simp only [fdBernstein] at hfd
  obtain ⟨hlen, hfd⟩ := option_guard_bind_eq_some hfd
  obtain ⟨hmB, hfd⟩ := option_guard_bind_eq_some hfd
  obtain ⟨hp, hhp, hfd⟩ := option_bind_eq_some' hfd

  have hpLam : Poly.substInto (coordPoly verts) (Poly.const c₀)
      = Poly.const c₀ := by
    by_cases hc : c₀ = 0
    · subst hc
      rw [show Poly.const (0 : ℚ) = [] from by
        unfold Poly.const
        rw [if_pos rfl]]
      rfl
    · rw [show Poly.const c₀ = [(([] : Mono), c₀)] from by
        unfold Poly.const
        rw [if_neg hc]]
      show Poly.add [] (Poly.scale c₀
        ((([] : Mono)).foldr
          (fun q a => Poly.mul (Poly.pow (coordPoly verts q.1) q.2) a)
          (Poly.const 1))) = [(([] : Mono), c₀)]
      have hscale : Poly.scale c₀ (Poly.const 1) = [(([] : Mono), c₀)] := by
        unfold Poly.const
        rw [if_neg one_ne_zero]
        unfold Poly.scale
        rw [if_neg hc]
        simp
      show Poly.add [] (Poly.scale c₀ (Poly.const 1)) = _
      rw [hscale]
      show Poly.canon ([] ++ [(([] : Mono), c₀)]) = _
      rw [List.nil_append]
      unfold Poly.canon
      show ([(([] : Mono), c₀)]).filter (fun t => decide (t.2 ≠ 0)) = _
      rw [List.filter_cons]
      simp [hc]
  rw [hpLam] at hhp

  set m := verts.length with hm
  set mS := (smask.filter id).length with hmS
  set mB := verts.length - (smask.filter id).length with hmBdef
  have ht : t.grid = (compositionsUpTo mS d).map fun j =>
      (j, bernCoeffRows mB d
        ((subCompositions j).foldr
          (fun k acc =>
            Poly.add acc (Poly.scale
              ((if (k.foldr (·+·) 0) % 2 = 0 then 1 else -1) *
                ((((j.zip k).map fun q => Prim.nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ))
              (Poly.mul
                (Poly.canon ((compositions mB
                    (d - k.foldr (·+·) 0)).map fun β =>
                  (vecToMono β,
                   hp.coeffOf (vecToMono (assembleVec smask k β))
                     / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                     * ((multinomial β : Nat) : ℚ))))
                (Poly.pow (sumVars mB) (k.foldr (·+·) 0)))))
          [])) := by
    have := hfd.symm
    injection this with h
    rw [h]

  have hj₀sum : (List.replicate mS 0).foldr (· + ·) 0 = 0 :=
    replicate_zero_foldr_add mS
  have hj₀mem : List.replicate mS 0 ∈ compositionsUpTo mS d := by
    apply mem_compositionsUpTo_of_sum_le
    · rw [hj₀sum, compositions_zero_total]
      simp
    · rw [hj₀sum]
      omega
  obtain ⟨γ₀, hγ₀⟩ := compositions_ne_nil (d := d) hmB

  set rows := (compositions mB (d - (List.replicate mS 0).foldr (·+·) 0)).map
    (fun β =>
      (vecToMono β,
       hp.coeffOf (vecToMono (assembleVec smask (List.replicate mS 0) β))
         / ((multinomial (assembleVec smask (List.replicate mS 0) β) : Nat) : ℚ)
         * ((multinomial β : Nat) : ℚ))) with hrows
  have hfold : (subCompositions (List.replicate mS 0)).foldr
      (fun k acc =>
        Poly.add acc (Poly.scale
          ((if (k.foldr (·+·) 0) % 2 = 0 then 1 else -1) *
            (((((List.replicate mS 0).zip k).map
              fun q => Prim.nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ))
          (Poly.mul
            (Poly.canon ((compositions mB (d - k.foldr (·+·) 0)).map fun β =>
              (vecToMono β,
               hp.coeffOf (vecToMono (assembleVec smask k β))
                 / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                 * ((multinomial β : Nat) : ℚ))))
            (Poly.pow (sumVars mB) (k.foldr (·+·) 0)))))
      []
      = Poly.add [] (Poly.scale
          ((if ((List.replicate mS 0).foldr (·+·) 0) % 2 = 0 then 1 else -1) *
            (((((List.replicate mS 0).zip (List.replicate mS 0)).map
              fun q => Prim.nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ))
          (Poly.mul (Poly.canon rows)
            (Poly.pow (sumVars mB)
              ((List.replicate mS 0).foldr (·+·) 0)))) := by
    rw [subCompositions_replicate_zero]
    rfl

  have hβval : ∀ β ∈ compositions mB (d - (List.replicate mS 0).foldr (·+·) 0),
      hp.coeffOf (vecToMono (assembleVec smask (List.replicate mS 0) β))
        / ((multinomial (assembleVec smask (List.replicate mS 0) β) : Nat) : ℚ)
        * ((multinomial β : Nat) : ℚ)
      = c₀ * ((multinomial β : Nat) : ℚ) := by
    intro β hβ
    rw [hj₀sum] at hβ
    obtain ⟨hβlen, hβsum⟩ := mem_compositions_iff.mp hβ
    have hasm_len : (assembleVec smask (List.replicate mS 0) β).length
        = smask.length := by
      apply assembleVec_length
      · rw [List.length_replicate]
      · rw [hβlen, filter_not_length, hlen]
    have hasm_sum : (assembleVec smask (List.replicate mS 0) β).foldr (·+·) 0
        = d := by
      rw [assembleVec_foldr_add smask _ β (by rw [List.length_replicate])
        (by rw [hβlen, filter_not_length, hlen]), hj₀sum,
        foldr_add_eq_sum, hβsum]
      omega
    have hasm_mem : assembleVec smask (List.replicate mS 0) β
        ∈ compositions m d := by
      rw [mem_compositions_iff]
      exact ⟨by rw [hasm_len, hlen], hasm_sum⟩
    rw [coeffOf_eq_coeffSum_of_pairwise hp (homogenize_pairwise hhp),
      homogenize_const_coeffSum hhp _ hasm_mem]
    have hmne : ((multinomial (assembleVec smask (List.replicate mS 0) β)
        : Nat) : ℚ) ≠ 0 := by
      exact_mod_cast (multinomial_pos _).ne'
    field_simp

  have hval : Poly.coeffOf ((subCompositions (List.replicate mS 0)).foldr
      (fun k acc =>
        Poly.add acc (Poly.scale
          ((if (k.foldr (·+·) 0) % 2 = 0 then 1 else -1) *
            (((((List.replicate mS 0).zip k).map
              fun q => Prim.nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ))
          (Poly.mul
            (Poly.canon ((compositions mB (d - k.foldr (·+·) 0)).map fun β =>
              (vecToMono β,
               hp.coeffOf (vecToMono (assembleVec smask k β))
                 / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                 * ((multinomial β : Nat) : ℚ))))
            (Poly.pow (sumVars mB) (k.foldr (·+·) 0)))))
      []) (vecToMono γ₀)
      = c₀ * ((multinomial γ₀ : Nat) : ℚ) := by
    rw [hfold, hj₀sum, zip_replicate_binom_one, Nat.cast_one,
      if_pos (show (0 : Nat) % 2 = 0 from rfl), one_mul]
    show Poly.coeffOf (Poly.canon ([] ++ Poly.scale 1
      (Poly.mul (Poly.canon rows) (Poly.pow (sumVars mB) 0)))) _ = _
    rw [List.nil_append, coeffOf_canon_eq_coeffSum, coeffSum_scale, one_mul]

    show coeffSum (Poly.mul (Poly.canon rows) (Poly.const 1)) _ = _
    rw [coeffSum_mul]
    have hrows_keys : ∀ u ∈ Poly.canon rows,
        u.1.Pairwise (fun s t => s.1 < t.1) ∧ ∀ q ∈ u.1, q.2 ≠ 0 := by
      intro u hu
      obtain ⟨x, hx, hx1⟩ := List.mem_map.mp (canon_keys_subset _ u hu)
      rw [hrows] at hx
      obtain ⟨β, hβ, hβ1⟩ := List.mem_map.mp hx
      have hxkey : u.1 = vecToMono β := by
        rw [← hx1, ← hβ1]
      rw [hxkey, vecToMono_eq_vtmAux]
      exact vtmAux_canonical 0 β
    have hinner : ∀ u ∈ Poly.canon rows,
        ((Poly.const (1 : ℚ)).map fun w =>
          if monoMul u.1 w.1 = vecToMono γ₀ then u.2 * w.2 else 0).sum
        = if u.1 = vecToMono γ₀ then u.2 else 0 := by
      intro u hu
      obtain ⟨hs, hz⟩ := hrows_keys u hu
      rw [show Poly.const (1 : ℚ) = [(([] : Mono), 1)] from by
        unfold Poly.const
        rw [if_neg one_ne_zero]]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [monoMul_nil_right hs hz]
      split
      · ring
      · ring
    rw [List.map_congr_left hinner, ← coeffSum_as_map_sum, coeffSum_canon,
      hrows, coeffSum_map_rows]

    have hcond : ∀ β ∈ compositions mB (d - (List.replicate mS 0).foldr (·+·) 0),
        (if vecToMono β = vecToMono γ₀
         then hp.coeffOf (vecToMono (assembleVec smask (List.replicate mS 0) β))
             / ((multinomial (assembleVec smask (List.replicate mS 0) β) : Nat) : ℚ)
             * ((multinomial β : Nat) : ℚ)
         else 0)
        = (if β = γ₀ then c₀ * ((multinomial β : Nat) : ℚ) else 0) := by
      intro β hβ
      by_cases hβγ : β = γ₀
      · subst hβγ
        rw [if_pos rfl, if_pos rfl]
        exact hβval β hβ
      · rw [if_neg ?_, if_neg hβγ]
        intro hvtm
        apply hβγ
        apply vecToMono_inj ?_ hvtm
        rw [(mem_compositions_iff.mp (by rwa [hj₀sum] at hβ)).1,
          (mem_compositions_iff.mp hγ₀).1]
    rw [List.map_congr_left hcond,
      sum_map_single_witness _ _ γ₀ (by rwa [hj₀sum]) (compositions_nodup _ _)]

  unfold gridAll at hgrid
  have hrow_mem : (List.replicate mS 0, bernCoeffRows mB d
      ((subCompositions (List.replicate mS 0)).foldr
        (fun k acc =>
          Poly.add acc (Poly.scale
            ((if (k.foldr (·+·) 0) % 2 = 0 then 1 else -1) *
              (((((List.replicate mS 0).zip k).map
                fun q => Prim.nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ))
            (Poly.mul
              (Poly.canon ((compositions mB (d - k.foldr (·+·) 0)).map fun β =>
                (vecToMono β,
                 hp.coeffOf (vecToMono (assembleVec smask k β))
                   / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                   * ((multinomial β : Nat) : ℚ))))
              (Poly.pow (sumVars mB) (k.foldr (·+·) 0)))))
        [])) ∈ t.grid := by
    rw [ht]
    exact List.mem_map.mpr ⟨List.replicate mS 0, hj₀mem, rfl⟩
  have hrow := List.all_eq_true.mp hgrid _ hrow_mem
  have hentry := List.all_eq_true.mp hrow
    (γ₀, Poly.coeffOf _ (vecToMono γ₀) / ((multinomial γ₀ : Nat) : ℚ))
    (List.mem_map.mpr ⟨γ₀, hγ₀, rfl⟩)
  rw [hval] at hentry
  have hγ₀ne : ((multinomial γ₀ : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (multinomial_pos γ₀).ne'
  rwa [mul_div_assoc, div_self hγ₀ne, mul_one] at hentry

theorem sum_map_range_reflect (n : Nat) (f : Nat → ℚ) :
    ((List.range (n + 1)).map f).sum
      = ((List.range (n + 1)).map (fun a => f (n - a))).sum := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_map_range_succ_last (m + 1) f,
      sum_map_range_succ_head (m + 1) (fun a => f (m + 1 - a))]
    have hshift : ((List.range (m + 1)).map
        (fun t => f (m + 1 - (t + 1)))).sum
        = ((List.range (m + 1)).map (fun a => f (m - a))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro t _
      have : m + 1 - (t + 1) = m - t := by omega
      rw [this]
    rw [hshift, ← ih]
    have h0 : m + 1 - 0 = m + 1 := by omega
    rw [h0]
    ring

theorem univariate_star (d : Nat) (B : Nat → ℚ) (u : ℚ) :
    ((List.range (d + 1)).map (fun a =>
      B a * (Nat.choose d a : ℚ) * (-u) ^ a * (1 + u) ^ (d - a))).sum
    = ((List.range (d + 1)).map (fun r =>
        (Nat.choose d r : ℚ) * u ^ r *
          ((List.range (r + 1)).map (fun k =>
            (-1 : ℚ) ^ k * (Nat.choose r k : ℚ) * B k)).sum)).sum := by

  have hexp : ∀ a ∈ List.range (d + 1),
      B a * (Nat.choose d a : ℚ) * (-u) ^ a * (1 + u) ^ (d - a)
        = ((List.range (d - a + 1)).map (fun t =>
            B a * (Nat.choose d a : ℚ) * (-1 : ℚ) ^ a
              * (Nat.choose (d - a) t : ℚ) * u ^ (a + t))).sum := by
    intro a _
    rw [one_add_pow_enum u (d - a), ← sum_map_mul_left_rat]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t _
    rw [neg_pow, pow_add]
    ring
  rw [List.map_congr_left hexp, triangle_exchange d (fun a t =>
    B a * (Nat.choose d a : ℚ) * (-1 : ℚ) ^ a
      * (Nat.choose (d - a) t : ℚ) * u ^ (a + t))]

  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  rw [← sum_map_mul_left_rat]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  have hkr : k ≤ r := by
    have := List.mem_range.mp hk
    omega
  have hrd : r ≤ d := by
    have := List.mem_range.mp hr
    omega
  have hchoose : (Nat.choose d k : ℚ) * (Nat.choose (d - k) (r - k) : ℚ)
      = (Nat.choose d r : ℚ) * (Nat.choose r k : ℚ) := by
    exact_mod_cast congrArg (Nat.cast : Nat → ℚ) (choose_sub_sub hkr hrd)
  have hpow : k + (r - k) = r := by omega
  rw [hpow]
  calc B k * (Nat.choose d k : ℚ) * (-1 : ℚ) ^ k
        * (Nat.choose (d - k) (r - k) : ℚ) * u ^ r
      = ((Nat.choose d k : ℚ) * (Nat.choose (d - k) (r - k) : ℚ))
          * ((-1 : ℚ) ^ k * B k) * u ^ r := by ring
    _ = ((Nat.choose d r : ℚ) * (Nat.choose r k : ℚ))
          * ((-1 : ℚ) ^ k * B k) * u ^ r := by rw [hchoose]
    _ = (Nat.choose d r : ℚ) * u ^ r
          * ((-1 : ℚ) ^ k * (Nat.choose r k : ℚ) * B k) := by ring

theorem multinomial_single (x : Nat) : multinomial [x] = 1 := by
  show Prim.nchoose (x + ([] : List Nat).foldr (·+·) 0) x * multinomial [] = 1
  show Prim.nchoose (x + 0) x * 1 = 1
  rw [Nat.add_zero, Prim.nchoose_eq_choose, Nat.choose_self]

theorem monoGood_one_eq {mo : Mono} (hg : MonoGood 1 mo) :
    mo = vecToMono [monoDeg mo] := by
  obtain ⟨hsort, hnz, hlt⟩ := hg
  cases mo with
  | nil => rfl
  | cons hd tl =>
    obtain ⟨v, e⟩ := hd
    have hv : v = 0 := by
      have := hlt (v, e) (by simp)
      omega
    subst hv
    have htl : tl = [] := by
      cases tl with
      | nil => rfl
      | cons hd2 tl2 =>
        exfalso
        rw [List.pairwise_cons] at hsort
        have h1 := hsort.1 hd2 (by simp)
        have h2 := hlt hd2 (by simp)
        omega
    subst htl
    have he : e ≠ 0 := hnz (0, e) (by simp)
    show [(0, e)] = vecToMono [monoDeg [(0, e)]]
    rw [show monoDeg [(0, e)] = e from by
      show e + 0 = e
      omega]
    show [(0, e)] = ((List.range 1).zip [e]).filter (fun p => p.2 ≠ 0)
    rw [List.range_one]
    show [(0, e)] = ([(0, e)]).filter (fun p => decide (p.2 ≠ 0))
    rw [List.filter_cons]
    simp [he]

theorem vecToMono_zero : vecToMono [0] = [] := rfl

theorem vecToMono_single_pos (x : Nat) (hx : x ≠ 0) :
    vecToMono [x] = [(0, x)] := by
  show ((List.range 1).zip [x]).filter (fun p => decide (p.2 ≠ 0)) = _
  rw [List.range_one]
  show ([(0, x)]).filter (fun p => decide (p.2 ≠ 0)) = _
  rw [List.filter_cons]
  simp [hx]

theorem vecToMono_single_monoMul (a b : Nat) :
    monoMul (vecToMono [a]) (vecToMono [b]) = vecToMono [a + b] := by
  cases ha : a with
  | zero =>
    cases hb : b with
    | zero => rfl
    | succ b' =>
      rw [vecToMono_zero, vecToMono_single_pos (b' + 1) (by omega),
        Nat.zero_add, vecToMono_single_pos (b' + 1) (by omega)]
      show monoCanon ([] ++ [(0, b' + 1)]) = _
      rw [List.nil_append]
      exact monoCanon_eq_self (by simp) (by simp)
  | succ a' =>
    cases hb : b with
    | zero =>
      rw [vecToMono_zero]
      simp only [Nat.add_zero]
      rw [vecToMono_single_pos (a' + 1) (by omega)]
      exact monoMul_nil_right (by simp) (by simp)
    | succ b' =>
      rw [vecToMono_single_pos (a' + 1) (by omega),
        vecToMono_single_pos (b' + 1) (by omega),
        vecToMono_single_pos (a' + 1 + (b' + 1)) (by omega)]
      unfold monoMul monoCanon
      rw [show ([(0, a' + 1)] ++ [(0, b' + 1)] : Mono)
          = [(0, a' + 1), (0, b' + 1)] from rfl]
      show ((insertVar (0, a' + 1) (insertVar (0, b' + 1) []))).filter _ = _
      show ((insertVar (0, a' + 1) [(0, b' + 1)])).filter _ = _
      rw [show insertVar (0, a' + 1) [(0, b' + 1)]
          = [(0, a' + 1 + (b' + 1))] from by
        unfold insertVar
        rw [if_neg (by omega), if_pos rfl]]
      show ([(0, a' + 1 + (b' + 1))]).filter (fun p => decide (p.2 ≠ 0)) = _
      rw [List.filter_cons]
      simp

theorem coeffSum_grid_fold (mB : Nat) (L : List (List Nat))
    (F : List Nat → ℚ) (Q : List Nat → Poly) (E : List Nat → Nat) (k : Mono) :
    coeffSum (L.foldr (fun kk acc =>
      Poly.add acc (Poly.scale (F kk)
        (Poly.mul (Q kk) (Poly.pow (sumVars mB) (E kk))))) []) k
    = (L.map (fun kk =>
        F kk * coeffSum (Poly.mul (Q kk) (Poly.pow (sumVars mB) (E kk))) k)).sum := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [coeffSum_add, coeffSum_scale, ih]
    ring

theorem multinomial_pair (a b : Nat) :
    multinomial [a, b] = Nat.choose (a + b) a := by
  show Prim.nchoose (a + ([b] : List Nat).foldr (·+·) 0) a * multinomial [b] = _
  rw [multinomial_single]
  show Prim.nchoose (a + (b + 0)) a * 1 = _
  rw [Nat.add_zero, Nat.mul_one, Prim.nchoose_eq_choose]

theorem monoEval_vtm_pair (ρ : Nat → ℚ) (a b : Nat) :
    monoEval ρ (vecToMono [a, b]) = ρ 0 ^ a * ρ 1 ^ b := by
  show monoEval ρ
    (((List.range 2).zip [a, b]).filter (fun p => decide (p.2 ≠ 0))) = _
  rw [show List.range 2 = [0, 1] from rfl]
  show monoEval ρ (([(0, a), (1, b)]).filter (fun p => decide (p.2 ≠ 0))) = _
  rw [List.filter_cons, List.filter_cons, List.filter_nil]
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · subst ha
      subst hb
      simp
    · subst ha
      simp [hb]
  · by_cases hb : b = 0
    · subst hb
      simp [ha]
    · simp [ha, hb]

theorem neg_one_pow_ite (k : Nat) :
    ((-1 : ℚ)) ^ k = if k % 2 = 0 then 1 else -1 := by
  rcases Nat.even_or_odd k with he | ho
  · rw [he.neg_one_pow, if_pos (Nat.even_iff.mp he)]
  · rw [ho.neg_one_pow, if_neg (by
      have := Nat.odd_iff.mp ho
      omega)]

theorem canon_single (mo : Mono) (c : ℚ) :
    Poly.canon [(mo, c)] = if c = 0 then [] else [(mo, c)] := by
  unfold Poly.canon
  show (insertTerm (mo, c) []).filter _ = _
  show ([(mo, c)]).filter (fun t => decide (t.2 ≠ 0)) = _
  rw [List.filter_cons]
  by_cases hc : c = 0
  · simp [hc]
  · simp [hc]

theorem grid_fold_pairwise (mB : Nat) (L : List (List Nat))
    (F : List Nat → ℚ) (Q : List Nat → Poly) (E : List Nat → Nat)
    (hL : L ≠ []) :
    (L.foldr (fun kk acc =>
      Poly.add acc (Poly.scale (F kk)
        (Poly.mul (Q kk) (Poly.pow (sumVars mB) (E kk))))) []).Pairwise
      (fun s u => keyLT s.1 u.1) := by
  cases L with
  | nil => exact absurd rfl hL
  | cons hd tl =>
    rw [List.foldr_cons]
    exact canon_pairwise _

theorem pred_conic_fold (pred : ℚ → Bool)
    (hzero : pred 0 = true)
    (hscale : ∀ a c : ℚ, 0 ≤ c → pred a = true → pred (c * a) = true)
    (hconv : ∀ a b l : ℚ, 0 ≤ l → l ≤ 1 → pred a = true → pred b = true →
      pred (l * a + (1 - l) * b) = true) :
    ∀ (L : List (ℚ × ℚ)), (∀ wb ∈ L, 0 ≤ wb.1 ∧ pred wb.2 = true) →
    pred ((L.map (fun wb => wb.1 * wb.2)).sum) = true := by
  have hadd : ∀ a b : ℚ, pred a = true → pred b = true →
      pred (a + b) = true := by
    intro a b ha hb
    have h2 := hconv a b (1/2) (by norm_num) (by norm_num) ha hb
    have := hscale ((1/2 : ℚ) * a + (1 - 1/2) * b) 2 (by norm_num) h2
    rw [show (2 : ℚ) * ((1/2 : ℚ) * a + (1 - 1/2) * b) = a + b by ring] at this
    exact this
  intro L
  induction L with
  | nil =>
    intro _
    simpa using hzero
  | cons hd tl ih =>
    intro h
    obtain ⟨hw, hp⟩ := h hd (by simp)
    simp only [List.map_cons, List.sum_cons]
    exact hadd _ _ (hscale hd.2 hd.1 hw hp)
      (ih (fun wb hwb => h wb (by simp [hwb])))

theorem fdBernstein_sound_dim1
    (verts : List (List ℚ)) (smask : List Bool) (d : Nat) (p : Poly)
    (t : FDTable) (pred : ℚ → Bool) (u₀ : ℚ)
    (hmask : smask = [true, false] ∨ smask = [false, true])
    (hfd : fdBernstein verts smask d p = some t)
    (hgrid : gridAll pred t = true)
    (hu : 0 ≤ u₀)
    (hzero : pred 0 = true)
    (hscale : ∀ a c : ℚ, 0 ≤ c → pred a = true → pred (c * a) = true)
    (hconv : ∀ a b l : ℚ, 0 ≤ l → l ≤ 1 → pred a = true → pred b = true →
      pred (l * a + (1 - l) * b) = true) :
    pred (Poly.eval (fun j =>
      ((List.range verts.length).map
        fun i => (verts.getD i []).getD j 0 *
          (if smask.getD i false then -u₀ else 1 + u₀)).sum) p) = true := by

  simp only [fdBernstein] at hfd
  obtain ⟨hlen, hfd⟩ := option_guard_bind_eq_some hfd
  obtain ⟨hmB, hfd⟩ := option_guard_bind_eq_some hfd
  obtain ⟨hp, hhp, hfd⟩ := option_bind_eq_some' hfd
  have hs2 : smask.length = 2 := by
    rcases hmask with h | h <;> subst h <;> rfl
  have hmS1 : (smask.filter id).length = 1 := by
    rcases hmask with h | h <;> subst h <;> rfl
  have hv2 : verts.length = 2 := by omega
  have hmB1 : verts.length - (smask.filter id).length = 1 := by omega
  have hband : PolyBand verts.length d hp :=
    homogenize_band (substInto_good (coordPoly_good verts) p) hhp
  have hpPW := homogenize_pairwise hhp

  set B : Nat → ℚ := fun k =>
    Poly.coeffOf hp (vecToMono (assembleVec smask [k] [d - k]))
      / ((multinomial (assembleVec smask [k] [d - k]) : Nat) : ℚ) with hBdef

  have ht : t.grid = (compositionsUpTo (smask.filter id).length d).map fun j =>
      (j, bernCoeffRows (verts.length - (smask.filter id).length) d
        ((subCompositions j).foldr
          (fun k acc =>
            Poly.add acc (Poly.scale
              ((if (k.foldr (·+·) 0) % 2 = 0 then 1 else -1) *
                ((((j.zip k).map fun q => Prim.nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ))
              (Poly.mul
                (Poly.canon ((compositions
                    (verts.length - (smask.filter id).length)
                    (d - k.foldr (·+·) 0)).map fun β =>
                  (vecToMono β,
                   hp.coeffOf (vecToMono (assembleVec smask k β))
                     / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                     * ((multinomial β : Nat) : ℚ))))
                (Poly.pow (sumVars
                    (verts.length - (smask.filter id).length))
                  (k.foldr (·+·) 0)))))
          [])) := by
    have := hfd.symm
    injection this with h
    rw [h]
  rw [hmB1, hmS1] at ht

  have hrows : ∀ r ∈ List.range (d + 1),
      pred (((List.range (r + 1)).map (fun k =>
        (-1 : ℚ) ^ k * (Nat.choose r k : ℚ) * B k)).sum) = true := by
    intro r hr
    have hrd : r ≤ d := by
      have := List.mem_range.mp hr
      omega

    have hrow_mem : ([r], bernCoeffRows 1 d
        ((subCompositions [r]).foldr
          (fun k acc =>
            Poly.add acc (Poly.scale
              ((if (k.foldr (·+·) 0) % 2 = 0 then 1 else -1) *
                (((([r].zip k).map fun q => Prim.nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ))
              (Poly.mul
                (Poly.canon ((compositions 1 (d - k.foldr (·+·) 0)).map fun β =>
                  (vecToMono β,
                   hp.coeffOf (vecToMono (assembleVec smask k β))
                     / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                     * ((multinomial β : Nat) : ℚ))))
                (Poly.pow (sumVars 1) (k.foldr (·+·) 0)))))
          [])) ∈ t.grid := by
      rw [ht, compositionsUpTo_one]
      rw [List.map_map]
      exact List.mem_map.mpr ⟨r, hr, rfl⟩

    unfold gridAll at hgrid
    have hrowAll := List.all_eq_true.mp hgrid _ hrow_mem
    have hentry := List.all_eq_true.mp hrowAll
      ([d], Poly.coeffOf ((subCompositions [r]).foldr
        (fun k acc =>
          Poly.add acc (Poly.scale
            ((if (k.foldr (·+·) 0) % 2 = 0 then 1 else -1) *
              (((([r].zip k).map fun q => Prim.nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ))
            (Poly.mul
              (Poly.canon ((compositions 1 (d - k.foldr (·+·) 0)).map fun β =>
                (vecToMono β,
                 hp.coeffOf (vecToMono (assembleVec smask k β))
                   / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                   * ((multinomial β : Nat) : ℚ))))
              (Poly.pow (sumVars 1) (k.foldr (·+·) 0)))))
        []) (vecToMono [d]) / ((multinomial [d] : Nat) : ℚ))
      (by
        show _ ∈ bernCoeffRows 1 d _
        unfold bernCoeffRows
        rw [compositions_one]
        exact List.mem_map.mpr ⟨[d], by simp, rfl⟩)

    have hfoldval : Poly.coeffOf ((subCompositions [r]).foldr
        (fun k acc =>
          Poly.add acc (Poly.scale
            ((if (k.foldr (·+·) 0) % 2 = 0 then 1 else -1) *
              (((([r].zip k).map fun q => Prim.nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ))
            (Poly.mul
              (Poly.canon ((compositions 1 (d - k.foldr (·+·) 0)).map fun β =>
                (vecToMono β,
                 hp.coeffOf (vecToMono (assembleVec smask k β))
                   / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                   * ((multinomial β : Nat) : ℚ))))
              (Poly.pow (sumVars 1) (k.foldr (·+·) 0)))))
        []) (vecToMono [d])
        = ((List.range (r + 1)).map (fun k =>
            (-1 : ℚ) ^ k * (Nat.choose r k : ℚ) * B k)).sum := by
      rw [coeffOf_eq_coeffSum_of_pairwise _ (grid_fold_pairwise 1 _ _ _ _ (by
        rw [subCompositions_single]
        intro hcon
        have := congrArg List.length hcon
        simp at this))]
      rw [coeffSum_grid_fold, subCompositions_single, List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro k hk
      have hkr : k ≤ r := by
        have := List.mem_range.mp hk
        omega
      show ((if (([k] : List Nat).foldr (·+·) 0) % 2 = 0 then (1 : ℚ) else -1) *
          (((([r].zip [k]).map fun q => Prim.nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ))
        * coeffSum (Poly.mul
            (Poly.canon ((compositions 1 (d - ([k] : List Nat).foldr (·+·) 0)).map fun β =>
              (vecToMono β,
               hp.coeffOf (vecToMono (assembleVec smask [k] β))
                 / ((multinomial (assembleVec smask [k] β) : Nat) : ℚ)
                 * ((multinomial β : Nat) : ℚ))))
            (Poly.pow (sumVars 1) (([k] : List Nat).foldr (·+·) 0)))
          (vecToMono [d])
        = (-1 : ℚ) ^ k * (Nat.choose r k : ℚ) * B k
      have hfold1 : (([k] : List Nat).foldr (·+·) 0) = k := by
        show k + 0 = k
        omega
      have hbinom : ((([r].zip [k]).map fun q => Prim.nchoose q.1 q.2).foldr
          (·*·) 1 : Nat) = Nat.choose r k := by
        show Prim.nchoose r k * 1 = Nat.choose r k
        rw [Nat.mul_one, Prim.nchoose_eq_choose]
      rw [hfold1, hbinom, compositions_one]
      simp only [List.map_cons, List.map_nil]
      rw [show multinomial [d - k] = 1 from multinomial_single (d - k),
        Nat.cast_one, mul_one]

      show _ * coeffSum (Poly.mul (Poly.canon [(vecToMono [d - k], B k)])
        (Poly.pow (sumVars 1) k)) (vecToMono [d]) = _
      rw [canon_single]
      by_cases hBk : B k = 0
      · rw [if_pos hBk, hBk]
        show _ * coeffSum (Poly.canon (([] : Poly).flatMap _)) _ = _
        rw [show (([] : Poly).flatMap fun (t : Mono × ℚ) =>
            (Poly.pow (sumVars 1) k).map fun u => (monoMul t.1 u.1, t.2 * u.2))
            = ([] : Poly) from rfl]
        show _ * coeffSum ((([] : Poly).foldr insertTerm []).filter _) _ = _
        show _ * coeffSum (([] : Poly).filter _) _ = _
        show (_ : ℚ) * coeffSum ([] : Poly) _ = _
        rw [coeffSum_nil]
        ring
      · rw [if_neg hBk]
        rw [coeffSum_mul]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        have hkey : ∀ u ∈ Poly.pow (sumVars 1) k, u.1 = vecToMono [k] := by
          intro u hu
          have hg := (polyBand_sumVars_pow 1 k) u hu
          have := monoGood_one_eq hg.1
          rw [hg.2] at this
          exact this
        have hcongr : ∀ u ∈ Poly.pow (sumVars 1) k,
            (if monoMul (vecToMono [d - k]) u.1 = vecToMono [d]
             then B k * u.2 else 0) = B k * u.2 := by
          intro u hu
          rw [hkey u hu, vecToMono_single_monoMul]
          rw [show d - k + k = d from by omega]
          rw [if_pos rfl]
        rw [List.map_congr_left hcongr, sum_map_mul_left_rat]
        have hpowsum : ((Poly.pow (sumVars 1) k).map (fun u => u.2)).sum
            = 1 := by
          have hcs : coeffSum (Poly.pow (sumVars 1) k) (vecToMono [k]) = 1 := by
            rw [coeffSum_sumVars_pow 1 k [k] (by
              rw [compositions_one]
              simp), multinomial_single, Nat.cast_one]
          rw [← hcs, coeffSum_as_map_sum]
          apply congrArg List.sum
          apply List.map_congr_left
          intro u hu
          rw [if_pos (hkey u hu)]
        rw [hpowsum, mul_one, neg_one_pow_ite]
        ring
    rw [hfoldval, show multinomial [d] = 1 from multinomial_single d,
      Nat.cast_one, div_one] at hentry
    exact hentry

  have hρsum : ((List.range verts.length).map (fun i =>
      if smask.getD i false then -u₀ else 1 + u₀)).sum = 1 := by
    rw [hv2, show List.range 2 = [0, 1] from rfl]
    rcases hmask with h | h <;> subst h <;>
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          List.getD_cons_zero, List.getD_cons_succ]
        norm_num
  have heval : Poly.eval (fun j =>
      ((List.range verts.length).map
        fun i => (verts.getD i []).getD j 0 *
          (if smask.getD i false then -u₀ else 1 + u₀)).sum) p
      = ((List.range (d + 1)).map (fun a =>
          coeffSum hp (vecToMono [a, d - a])
            * (if smask.getD 0 false then -u₀ else 1 + u₀) ^ a
            * (if smask.getD 1 false then -u₀ else 1 + u₀) ^ (d - a))).sum := by
    have hx : Poly.eval (fun j =>
        ((List.range verts.length).map
          fun i => (verts.getD i []).getD j 0 *
            (if smask.getD i false then -u₀ else 1 + u₀)).sum) p
        = Poly.eval (fun i => if smask.getD i false then -u₀ else 1 + u₀) hp := by
      rw [homogenize_eval hρsum hhp, Poly.eval_substInto]
      congr 1
      funext j
      rw [Poly.eval_coordPoly]
    rw [hx]
    rw [hv2] at hband
    rw [show Poly.eval (fun i => if smask.getD i false then -u₀ else 1 + u₀) hp
        = ((compositions 2 d).map (fun γ =>
            coeffSum hp (vecToMono γ) * monoEval
              (fun i => if smask.getD i false then -u₀ else 1 + u₀)
              (vecToMono γ))).sum from
      eval_eq_enum_sum _ 2 d hp hband]
    rw [compositions_two, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a _
    show coeffSum hp (vecToMono [a, d - a]) * monoEval _ (vecToMono [a, d - a]) = _
    rw [monoEval_vtm_pair]
    ring

  have hstar : ((List.range (d + 1)).map (fun a =>
      coeffSum hp (vecToMono [a, d - a])
        * (if smask.getD 0 false then -u₀ else 1 + u₀) ^ a
        * (if smask.getD 1 false then -u₀ else 1 + u₀) ^ (d - a))).sum
      = ((List.range (d + 1)).map (fun a =>
          B a * (Nat.choose d a : ℚ) * (-u₀) ^ a * (1 + u₀) ^ (d - a))).sum := by
    have hBval : ∀ a, a ≤ d →
        coeffSum hp (vecToMono (assembleVec smask [a] [d - a]))
          = B a * ((multinomial (assembleVec smask [a] [d - a]) : Nat) : ℚ) := by
      intro a _
      have hBa : B a = Poly.coeffOf hp (vecToMono (assembleVec smask [a] [d - a]))
          / ((multinomial (assembleVec smask [a] [d - a]) : Nat) : ℚ) := by
        rw [hBdef]
      have hne : ((multinomial (assembleVec smask [a] [d - a]) : Nat) : ℚ) ≠ 0 := by
        exact_mod_cast (multinomial_pos _).ne'
      rw [hBa, coeffOf_eq_coeffSum_of_pairwise hp hpPW]
      field_simp
    rcases hmask with h | h <;> subst h
    ·
      apply congrArg List.sum
      apply List.map_congr_left
      intro a ha
      have had : a ≤ d := by
        have := List.mem_range.mp ha
        omega
      have hasm : assembleVec [true, false] [a] [d - a] = [a, d - a] := rfl
      have hB := hBval a had
      rw [hasm] at hB
      rw [hB, multinomial_pair, show a + (d - a) = d from by omega]
      simp only [List.getD_cons_zero, List.getD_cons_succ, if_true,
        Bool.false_eq_true, if_false]
    ·
      rw [sum_map_range_reflect d (fun a =>
        coeffSum hp (vecToMono [a, d - a])
          * (if ([false, true] : List Bool).getD 0 false then -u₀ else 1 + u₀) ^ a
          * (if ([false, true] : List Bool).getD 1 false then -u₀ else 1 + u₀) ^ (d - a))]
      apply congrArg List.sum
      apply List.map_congr_left
      intro a ha
      have had : a ≤ d := by
        have := List.mem_range.mp ha
        omega
      have hasm : assembleVec [false, true] [a] [d - a] = [d - a, a] := rfl
      have hB := hBval a had
      rw [hasm] at hB
      have hdd : d - (d - a) = a := by omega
      rw [hdd, hB, multinomial_pair]
      rw [show d - a + a = d from by omega]
      rw [show Nat.choose d (d - a) = Nat.choose d a from Nat.choose_symm had]
      simp only [List.getD_cons_zero, List.getD_cons_succ, if_true,
        Bool.false_eq_true, if_false]
      ring

  rw [heval, hstar, univariate_star d B u₀]
  have hfold := pred_conic_fold pred hzero hscale hconv
    ((List.range (d + 1)).map (fun r =>
      ((Nat.choose d r : ℚ) * u₀ ^ r,
        ((List.range (r + 1)).map (fun k =>
          (-1 : ℚ) ^ k * (Nat.choose r k : ℚ) * B k)).sum)))
    (by
      intro wb hwb
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hwb
      exact ⟨mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu r), hrows r hr⟩)
  rw [List.map_map] at hfold
  rw [show ((List.range (d + 1)).map ((fun (wb : ℚ × ℚ) => wb.1 * wb.2) ∘ fun r =>
      ((Nat.choose d r : ℚ) * u₀ ^ r,
        ((List.range (r + 1)).map (fun k =>
          (-1 : ℚ) ^ k * (Nat.choose r k : ℚ) * B k)).sum)))
      = ((List.range (d + 1)).map (fun r =>
          (Nat.choose d r : ℚ) * u₀ ^ r *
            ((List.range (r + 1)).map (fun k =>
              (-1 : ℚ) ^ k * (Nat.choose r k : ℚ) * B k)).sum)) from
    List.map_congr_left (fun r _ => rfl)] at hfold
  exact hfold

end PPLC.QArith
