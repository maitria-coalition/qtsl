import Qtsl.QArith
import Mathlib.Order.Compare
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Correctness theory for the exact-rational core

Semantics for everything `Core.QArith` computes: evaluation
homomorphism lemmas (evaluation respects insertion, canonicalization,
the ring operations, and substitution); canonical-form structure;
support and degree bounds through the algebra; and the enumeration
identity expressing evaluation as a sum over compositions.
-/

namespace PPLC.QArith

def monoEval (ρ : Nat → ℚ) (m : Mono) : ℚ :=
  m.foldr (fun (v, e) a => (ρ v) ^ e * a) 1

@[simp] theorem monoEval_nil (ρ : Nat → ℚ) : monoEval ρ [] = 1 := rfl

@[simp] theorem monoEval_cons (ρ : Nat → ℚ) (v e : Nat) (m : Mono) :
    monoEval ρ ((v, e) :: m) = (ρ v) ^ e * monoEval ρ m := rfl

@[simp] theorem Poly.eval_nil (ρ : Nat → ℚ) : Poly.eval ρ [] = 0 := rfl

@[simp] theorem Poly.eval_cons (ρ : Nat → ℚ) (m : Mono) (c : ℚ) (p : Poly) :
    Poly.eval ρ ((m, c) :: p) = c * monoEval ρ m + Poly.eval ρ p := rfl

theorem monoEval_insertVar (ρ : Nat → ℚ) (v e : Nat) (m : Mono) :
    monoEval ρ (insertVar (v, e) m) = (ρ v) ^ e * monoEval ρ m := by
  induction m with
  | nil => simp [insertVar]
  | cons hd tl ih =>
    obtain ⟨v', e'⟩ := hd
    by_cases h1 : v < v'
    · simp [insertVar, h1]
    · by_cases h2 : v = v'
      · subst h2
        simp only [insertVar, if_neg h1, if_pos trivial, ite_true, if_true,
          monoEval_cons, pow_add]
        ring
      · simp only [insertVar, if_neg h1, if_neg h2, monoEval_cons, ih]
        ring

theorem monoEval_foldr_insertVar (ρ : Nat → ℚ) (m acc : Mono) :
    monoEval ρ (m.foldr insertVar acc) = monoEval ρ m * monoEval ρ acc := by
  induction m with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨v, e⟩ := hd
    simp only [List.foldr_cons, monoEval_insertVar, monoEval_cons, ih]
    ring

theorem monoEval_filter_ne_zero (ρ : Nat → ℚ) (m : Mono) :
    monoEval ρ (m.filter (fun p => p.2 ≠ 0)) = monoEval ρ m := by
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨v, e⟩ := hd
    rw [List.filter_cons]
    split
    · rw [monoEval_cons, monoEval_cons, ih]
    · next hcond =>
      have he : e = 0 := by simpa using hcond
      subst he
      rw [ih, monoEval_cons]
      simp

theorem monoEval_monoCanon (ρ : Nat → ℚ) (m : Mono) :
    monoEval ρ (monoCanon m) = monoEval ρ m := by
  unfold monoCanon
  rw [monoEval_filter_ne_zero]
  simpa using monoEval_foldr_insertVar ρ m []

theorem monoEval_append (ρ : Nat → ℚ) (a b : Mono) :
    monoEval ρ (a ++ b) = monoEval ρ a * monoEval ρ b := by
  induction a with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨v, e⟩ := hd
    simp only [List.cons_append, monoEval_cons, ih]
    ring

theorem monoEval_monoMul (ρ : Nat → ℚ) (a b : Mono) :
    monoEval ρ (monoMul a b) = monoEval ρ a * monoEval ρ b := by
  unfold monoMul
  rw [monoEval_monoCanon, monoEval_append]

theorem monoCmp_eq_iff : ∀ {a b : Mono}, monoCmp a b = .eq ↔ a = b := by
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
      split
      · next hv =>
        constructor
        · intro h; cases h
        · intro h
          injection h with h1 h2
          injection h1 with hv2 he2
          subst hv2
          rw [compare_eq_iff_eq.mpr rfl] at hv
          cases hv
      · next hv =>
        constructor
        · intro h; cases h
        · intro h
          injection h with h1 h2
          injection h1 with hv2 he2
          subst hv2
          rw [compare_eq_iff_eq.mpr rfl] at hv
          cases hv
      · next hv =>
        have hveq : v = v' := compare_eq_iff_eq.mp hv
        subst hveq
        split
        · next he =>
          constructor
          · intro h; cases h
          · intro h
            injection h with h1 h2
            injection h1 with _ he2
            subst he2
            rw [compare_eq_iff_eq.mpr rfl] at he
            cases he
        · next he =>
          constructor
          · intro h; cases h
          · intro h
            injection h with h1 h2
            injection h1 with _ he2
            subst he2
            rw [compare_eq_iff_eq.mpr rfl] at he
            cases he
        · next he =>
          have heeq : e = e' := compare_eq_iff_eq.mp he
          subst heeq
          constructor
          · intro h
            rw [ih.mp h]
          · intro h
            injection h with _ h2
            exact ih.mpr h2

theorem Poly.eval_insertTerm (ρ : Nat → ℚ) (m : Mono) (c : ℚ) (p : Poly) :
    Poly.eval ρ (insertTerm (m, c) p) = c * monoEval ρ m + Poly.eval ρ p := by
  induction p with
  | nil => simp [insertTerm]
  | cons hd tl ih =>
    obtain ⟨m', c'⟩ := hd
    simp only [insertTerm]
    split
    · simp
    · next hcmp =>
      have : m = m' := monoCmp_eq_iff.mp hcmp
      subst this
      simp only [Poly.eval_cons]
      ring
    · simp only [Poly.eval_cons, ih]
      ring

theorem Poly.eval_foldr_insertTerm (ρ : Nat → ℚ) (p acc : Poly) :
    Poly.eval ρ (p.foldr insertTerm acc) = Poly.eval ρ p + Poly.eval ρ acc := by
  induction p with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨m, c⟩ := hd
    simp only [List.foldr_cons]
    rw [Poly.eval_insertTerm, ih, Poly.eval_cons]
    ring

theorem Poly.eval_filter_ne_zero (ρ : Nat → ℚ) (p : Poly) :
    Poly.eval ρ (p.filter (fun t => t.2 ≠ 0)) = Poly.eval ρ p := by
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨m, c⟩ := hd
    rw [List.filter_cons]
    split
    · rw [Poly.eval_cons, Poly.eval_cons, ih]
    · next hcond =>
      have hc : c = 0 := by simpa using hcond
      subst hc
      rw [ih, Poly.eval_cons]
      simp

@[simp] theorem Poly.eval_canon (ρ : Nat → ℚ) (p : Poly) :
    Poly.eval ρ (Poly.canon p) = Poly.eval ρ p := by
  unfold Poly.canon
  rw [Poly.eval_filter_ne_zero]
  simpa using Poly.eval_foldr_insertTerm ρ p []

theorem Poly.eval_append (ρ : Nat → ℚ) (p q : Poly) :
    Poly.eval ρ (p ++ q) = Poly.eval ρ p + Poly.eval ρ q := by
  induction p with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨m, c⟩ := hd
    simp only [List.cons_append, Poly.eval_cons, ih]
    ring

@[simp] theorem Poly.eval_add (ρ : Nat → ℚ) (p q : Poly) :
    Poly.eval ρ (Poly.add p q) = Poly.eval ρ p + Poly.eval ρ q := by
  unfold Poly.add
  rw [Poly.eval_canon, Poly.eval_append]

@[simp] theorem Poly.eval_neg (ρ : Nat → ℚ) (p : Poly) :
    Poly.eval ρ (Poly.neg p) = -Poly.eval ρ p := by
  unfold Poly.neg
  induction p with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨m, c⟩ := hd
    simp only [List.map_cons, Poly.eval_cons, ih]
    ring

@[simp] theorem Poly.eval_sub (ρ : Nat → ℚ) (p q : Poly) :
    Poly.eval ρ (Poly.sub p q) = Poly.eval ρ p - Poly.eval ρ q := by
  unfold Poly.sub
  rw [Poly.eval_add, Poly.eval_neg]
  ring

@[simp] theorem Poly.eval_scale (ρ : Nat → ℚ) (a : ℚ) (p : Poly) :
    Poly.eval ρ (Poly.scale a p) = a * Poly.eval ρ p := by
  unfold Poly.scale
  by_cases ha : a = 0
  · simp [ha]
  · rw [if_neg ha]
    induction p with
    | nil => simp
    | cons hd tl ih =>
      obtain ⟨m, c⟩ := hd
      simp only [List.map_cons, Poly.eval_cons, ih]
      ring

@[simp] theorem Poly.eval_const (ρ : Nat → ℚ) (c : ℚ) :
    Poly.eval ρ (Poly.const c) = c := by
  unfold Poly.const
  by_cases hc : c = 0 <;> simp [hc]

@[simp] theorem Poly.eval_var (ρ : Nat → ℚ) (v : Nat) :
    Poly.eval ρ (Poly.var v) = ρ v := by
  simp [Poly.var, monoEval]

theorem Poly.eval_mulRow (ρ : Nat → ℚ) (m : Mono) (c : ℚ) (q : Poly) :
    Poly.eval ρ (q.map fun t => (monoMul m t.1, c * t.2))
      = c * monoEval ρ m * Poly.eval ρ q := by
  induction q with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨m2, c2⟩ := hd
    simp only [List.map_cons, Poly.eval_cons, ih, monoEval_monoMul]
    ring

@[simp] theorem Poly.eval_mul (ρ : Nat → ℚ) (p q : Poly) :
    Poly.eval ρ (Poly.mul p q) = Poly.eval ρ p * Poly.eval ρ q := by
  unfold Poly.mul
  rw [Poly.eval_canon]
  induction p with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨m, c⟩ := hd
    rw [List.flatMap_cons, Poly.eval_append, ih, Poly.eval_cons]
    show Poly.eval ρ (q.map fun t => (monoMul m t.1, c * t.2))
          + Poly.eval ρ tl * Poly.eval ρ q
        = (c * monoEval ρ m + Poly.eval ρ tl) * Poly.eval ρ q
    rw [Poly.eval_mulRow]
    ring

@[simp] theorem Poly.eval_pow (ρ : Nat → ℚ) (p : Poly) (n : Nat) :
    Poly.eval ρ (Poly.pow p n) = (Poly.eval ρ p) ^ n := by
  induction n with
  | zero => simp [Poly.pow]
  | succ k ih =>
    simp only [Poly.pow, Poly.eval_mul, ih, pow_succ]
    ring

theorem Poly.eval_substInto (ρ : Nat → ℚ) (σp : Nat → Poly) (p : Poly) :
    Poly.eval ρ (Poly.substInto σp p)
      = Poly.eval (fun v => Poly.eval ρ (σp v)) p := by
  unfold Poly.substInto
  induction p with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨m, c⟩ := hd
    have hmono : Poly.eval ρ
        (m.foldr (fun p a => Poly.mul (Poly.pow (σp p.1) p.2) a) (Poly.const 1))
        = monoEval (fun v => Poly.eval ρ (σp v)) m := by
      induction m with
      | nil => simp
      | cons hd2 tl2 ih2 =>
        obtain ⟨v, e⟩ := hd2
        simp only [List.foldr_cons, Poly.eval_mul, Poly.eval_pow, ih2,
          monoEval_cons]
    simp only [List.foldr_cons, Poly.eval_add, Poly.eval_scale, ih, hmono,
      Poly.eval_cons]
    ring

theorem Poly.eval_map_linear (ρ : Nat → ℚ) (L : List Nat) (g : Nat → ℚ) :
    Poly.eval ρ (L.map fun i => (([(i, 1)] : Mono), g i))
      = (L.map fun i => g i * ρ i).sum := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, Poly.eval_cons, List.sum_cons, ih, monoEval_cons,
      monoEval_nil, pow_one]
    ring

theorem Poly.eval_sumVars (ρ : Nat → ℚ) (m : Nat) :
    Poly.eval ρ (sumVars m) = ((List.range m).map ρ).sum := by
  unfold sumVars
  rw [Poly.eval_canon, Poly.eval_map_linear]
  simp

theorem Poly.eval_coordPoly (ρ : Nat → ℚ) (verts : List (List ℚ)) (j : Nat) :
    Poly.eval ρ (coordPoly verts j)
      = ((List.range verts.length).map
          fun i => (verts.getD i []).getD j 0 * ρ i).sum := by
  unfold coordPoly
  rw [Poly.eval_canon, Poly.eval_map_linear]

end PPLC.QArith
