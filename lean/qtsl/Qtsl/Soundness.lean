import Qtsl.Catalogue
import Qtsl.QArithKernel
import Qtsl.ConvexRat
import Qtsl.PsdCert
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Pairing

/-!
# Per-rule soundness

Soundness of the certificate calculus: since well-typedness is the
check, the statement is that every inhabitant of `ProofObject H seq`
witnesses `seq.semanticallyValid H`, proven by structural recursion
with one lemma per rule (`ProofObject.sound`), together with a parallel
recursion (`ProofObject.sound_v0`) over the Boolean fragment recognizer
`ProofObject.v0frag`.

The supporting theory: exact tensor extensionality and singleton-shape
lemmas, evaluation under substitution and closedness, the
barycentric-halfspace construction, and the polynomial reflection
(`Term.toPoly` and its evaluation correspondence).
-/

namespace PPLC

open QArith

theorem QTensor.ext' {a b : QTensor} (hs : a.shape = b.shape)
    (he : a.entries = b.entries) : a = b := by
  cases a; cases b
  simp_all

noncomputable def Hypernet.Valuation.rho {H : Hypernet} (σ : H.Valuation)
    (w : Wire) : ℚ :=
  match σ.wireQ w with
  | some q => q.scalar
  | none => 0

theorem Hypernet.Valuation.rho_eq {H : Hypernet} (σ : H.Valuation)
    {w : Wire} {q : QTensor} (h : σ.wireQ w = some q) :
    σ.rho w = q.scalar := by
  unfold Hypernet.Valuation.rho
  rw [h]

theorem Hypernet.Valuation.wireQ_shape {H : Hypernet} (σ : H.Valuation)
    {w : Wire} {q : QTensor} (h : σ.wireQ w = some q) :
    ∃ τ, H.wireType w = some τ ∧ q.shape = τ.shape := by
  unfold Hypernet.Valuation.wireQ at h
  split at h
  · cases h
  · next τ hτ =>
    split at h
    · cases h
    · injection h with h
      exact ⟨τ, hτ, by rw [← h]⟩

theorem ERat.allFinQ_of_all_fin : ∀ (l : List ERat),
    (∀ e ∈ l, ∃ q, e = ERat.fin q) → ∃ l', ERat.allFinQ l = some l' := by
  intro l
  induction l with
  | nil => exact fun _ => ⟨[], rfl⟩
  | cons hd tl ih =>
    intro h
    obtain ⟨q, hq⟩ := h hd (by simp)
    subst hq
    obtain ⟨l', hl'⟩ := ih (fun e he => h e (by simp [he]))
    exact ⟨q :: l', by simp [ERat.allFinQ, hl']⟩

theorem Hypernet.Valuation.wireQ_isSome {H : Hypernet} (σ : H.Valuation)
    {w : Wire} {τ : TensorType} (hτ : H.wireType w = some τ)
    (hfin : τ.dtype.ext = Ext.fin) : ∃ q, σ.wireQ w = some q := by
  unfold Hypernet.Valuation.wireQ
  split
  · next h => rw [hτ] at h; cases h
  · next τ' hτ' =>
    have hττ' : τ' = τ := by
      rw [hτ] at hτ'
      injection hτ' with h
      exact h.symm
    subst hττ'
    split
    · next hf =>
      exfalso
      have hall : ∀ e ∈ (σ w τ' hτ').val.map Subtype.val, ∃ q, e = ERat.fin q := by
        intro e he
        obtain ⟨x, hx, hx1⟩ := List.mem_map.mp he
        cases hval : x.val with
        | fin q => exact ⟨q, by rw [← hx1, hval]⟩
        | negInf =>
          have := x.property
          rw [hval] at this
          simp only [Dtype.ValueSet] at this
          rw [hfin] at this
          exact absurd this.1 (by simp)
        | posInf =>
          have := x.property
          rw [hval] at this
          simp only [Dtype.ValueSet] at this
          rw [hfin] at this
          exact absurd this (by simp)
      obtain ⟨l', hl'⟩ := ERat.allFinQ_of_all_fin _ hall
      rw [hf] at hl'
      cases hl'
    · exact ⟨_, rfl⟩

def SingletonShape (s : Shape) : Prop := s = [] ∨ s = [1]

theorem QTensor.entries_singleton {q : QTensor} (h : SingletonShape q.shape) :
    q.entries = [q.scalar] := by
  have hlen : q.entries.length = 1 := by
    have := q.len_eq
    rcases h with h | h <;> rw [h] at this <;> simpa [Shape.totalSize] using this
  cases he : q.entries with
  | nil => rw [he] at hlen; simp at hlen
  | cons a tl =>
    cases tl with
    | nil =>
      unfold QTensor.scalar
      rw [he]
      rfl
    | cons b tl2 => rw [he] at hlen; simp at hlen

theorem QTensor.rel2_singleton {r : ℚ → ℚ → Prop} {a b : QTensor}
    (ha : SingletonShape a.shape) (hb : SingletonShape b.shape) :
    QTensor.rel2 r a b ↔ r a.scalar b.scalar := by
  have hae := QTensor.entries_singleton ha
  have hbe := QTensor.entries_singleton hb
  unfold QTensor.rel2
  by_cases hs : a.shape = b.shape
  · rw [if_pos hs, hae, hbe]
    simp [List.zip_cons_cons]
  · rw [if_neg hs]
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact absurd (ha.trans hb.symm) hs
    · rw [if_pos ha, hbe]
      constructor
      · intro h2
        exact h2 _ (by simp)
      · intro h2 y hy
        rcases List.mem_singleton.mp hy with rfl
        exact h2
    · have hna : ¬ a.shape = [] := by rw [ha]; simp
      rw [if_neg hna, if_pos hb, hae]
      constructor
      · intro h2
        exact h2 _ (by simp)
      · intro h2 y hy
        rcases List.mem_singleton.mp hy with rfl
        exact h2
    · exact absurd (ha.trans hb.symm) hs

theorem QTensor.map2_singleton {f : ℚ → ℚ → ℚ} {a b : QTensor}
    (ha : SingletonShape a.shape) (hb : SingletonShape b.shape) :
    ∃ c, QTensor.map2 f a b = some c ∧ SingletonShape c.shape ∧
      c.scalar = f a.scalar b.scalar := by
  have hae := QTensor.entries_singleton ha
  have hbe := QTensor.entries_singleton hb
  unfold QTensor.map2
  by_cases hs : a.shape = b.shape
  · refine ⟨_, dif_pos hs, ?_, ?_⟩
    · exact ha
    · show (a.entries.zipWith f b.entries).getD 0 0 = _
      rw [hae, hbe]
      rfl
  · rw [dif_neg hs]
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact absurd (ha.trans hb.symm) hs
    · rw [if_pos ha]
      refine ⟨_, rfl, Or.inr hb, ?_⟩
      show (b.entries.map (f a.scalar)).getD 0 0 = _
      rw [hbe]
      rfl
    · have hna : ¬ a.shape = [] := by rw [ha]; simp
      rw [if_neg hna, if_pos hb]
      refine ⟨_, rfl, Or.inr ha, ?_⟩
      show (a.entries.map (f · b.scalar)).getD 0 0 = _
      rw [hae]
      rfl
    · exact absurd (ha.trans hb.symm) hs

theorem Term.evalQ_singleton {H : Hypernet} (σ : H.Valuation) :
    ∀ (t : Term) (q : QTensor), Term.evalQ σ t = some q →
    (∀ w ∈ t.freeWires, ∀ qw, σ.wireQ w = some qw → SingletonShape qw.shape) →
    t.idxFree = true →
    SingletonShape q.shape ∧
      q.scalar = Poly.eval σ.rho t.toPoly := by
  intro t
  induction t with
  | var w =>
    intro q h hw _
    have hs := hw w (by simp [Term.freeWires]) q h
    refine ⟨hs, ?_⟩
    show q.scalar = Poly.eval σ.rho (Poly.var w)
    rw [Poly.eval_var, Hypernet.Valuation.rho_eq σ h]
  | const c =>
    intro q h _ _
    injection h with h
    subst h
    exact ⟨Or.inl rfl, by simp [QTensor.scalar, Term.toPoly]⟩
  | add l r ihl ihr =>
    intro q h hw hix
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    simp only [Term.evalQ, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, h⟩ := option_bind_eq_some' h
    obtain ⟨hsa, hva⟩ := ihl a ha (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.1
    obtain ⟨hsb, hvb⟩ := ihr b hb (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.2
    obtain ⟨c, hc, hsc, hvc⟩ := QTensor.map2_singleton (f := (· + ·)) hsa hsb
    rw [hc] at h
    injection h with h
    subst h
    refine ⟨hsc, ?_⟩
    show c.scalar = Poly.eval σ.rho (Poly.add l.toPoly r.toPoly)
    rw [Poly.eval_add, hvc, hva, hvb]
  | mul l r ihl ihr =>
    intro q h hw hix
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    simp only [Term.evalQ, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, h⟩ := option_bind_eq_some' h
    obtain ⟨hsa, hva⟩ := ihl a ha (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.1
    obtain ⟨hsb, hvb⟩ := ihr b hb (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.2
    obtain ⟨c, hc, hsc, hvc⟩ := QTensor.map2_singleton (f := (· * ·)) hsa hsb
    rw [hc] at h
    injection h with h
    subst h
    refine ⟨hsc, ?_⟩
    show c.scalar = Poly.eval σ.rho (Poly.mul l.toPoly r.toPoly)
    rw [Poly.eval_mul, hvc, hva, hvb]
  | sub l r ihl ihr =>
    intro q h hw hix
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    simp only [Term.evalQ, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, h⟩ := option_bind_eq_some' h
    obtain ⟨hsa, hva⟩ := ihl a ha (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.1
    obtain ⟨hsb, hvb⟩ := ihr b hb (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.2
    obtain ⟨c, hc, hsc, hvc⟩ := QTensor.map2_singleton (f := (· - ·)) hsa hsb
    rw [hc] at h
    injection h with h
    subst h
    refine ⟨hsc, ?_⟩
    show c.scalar = Poly.eval σ.rho (Poly.sub l.toPoly r.toPoly)
    rw [Poly.eval_sub, hvc, hva, hvb]
  | neg t iht =>
    intro q h hw hix
    simp only [Term.evalQ] at h
    cases ht : Term.evalQ σ t with
    | none => rw [ht] at h; cases h
    | some a =>
      rw [ht] at h
      injection h with h
      subst h
      obtain ⟨hsa, hva⟩ := iht a ht
        (fun w hw' => hw w (by simpa [Term.freeWires] using hw'))
        (by simpa [Term.idxFree] using hix)
      refine ⟨?_, ?_⟩
      · show SingletonShape (QTensor.map1 _ a).shape
        exact hsa
      · show (QTensor.map1 Neg.neg a).scalar = Poly.eval σ.rho (Poly.neg t.toPoly)
        rw [Poly.eval_neg, ← hva]
        show (a.entries.map Neg.neg).getD 0 0 = -a.scalar
        rw [QTensor.entries_singleton hsa]
        rfl
  | idx t i ih =>
    intro q h hw hix
    simp [Term.idxFree] at hix

theorem Term.evalQ_subst_congr {H : Hypernet} (σ : H.Valuation)
    {w : Wire} {u₁ u₂ : Term} (hu : Term.evalQ σ u₁ = Term.evalQ σ u₂) :
    ∀ (t : Term),
      Term.evalQ σ (Term.subst w u₁ t) = Term.evalQ σ (Term.subst w u₂ t) := by
  intro t
  induction t with
  | var w' =>
    by_cases hw : w' = w
    · simp only [Term.subst, if_pos hw]
      exact hu
    · simp only [Term.subst, if_neg hw]
  | const c => rfl
  | add l r ihl ihr => simp only [Term.subst, Term.evalQ, ihl, ihr]
  | mul l r ihl ihr => simp only [Term.subst, Term.evalQ, ihl, ihr]
  | sub l r ihl ihr => simp only [Term.subst, Term.evalQ, ihl, ihr]
  | neg t iht => simp only [Term.subst, Term.evalQ, iht]
  | idx t i iht => simp only [Term.subst, Term.evalQ, iht]

theorem Formula.holds_subst_congr {H : Hypernet} (σ : H.Valuation)
    {w : Wire} {u₁ u₂ : Term} (hu : Term.evalQ σ u₁ = Term.evalQ σ u₂) :
    ∀ (F : Formula), (Formula.holds σ (F.subst w u₁) ↔ Formula.holds σ (F.subst w u₂)) := by
  intro F
  induction F with
  | atom b l r =>
    simp only [Formula.subst, Formula.holds]
    rw [Term.evalQ_subst_congr σ hu l, Term.evalQ_subst_congr σ hu r]
  | inRegion t simplex S =>
    simp only [Formula.subst, Formula.holds]
    rw [Term.evalQ_subst_congr σ hu t]
  | and l r ihl ihr =>
    simp only [Formula.subst, Formula.holds]
    rw [ihl, ihr]
  | or l r ihl ihr =>
    simp only [Formula.subst, Formula.holds]
    rw [ihl, ihr]
  | tt => simp [Formula.subst]
  | ff => simp [Formula.subst]

theorem Term.evalQ_of_closed {H : Hypernet} (σ : H.Valuation) :
    ∀ (t : Term) (c : ℚ), t.evalQ? = some c →
    Term.evalQ σ t = some ⟨[], [c], rfl⟩ := by
  intro t
  induction t with
  | var w => intro c h; cases h
  | const c' =>
    intro c h
    injection h with h
    subst h
    rfl
  | add l r ihl ihr =>
    intro c h
    simp only [Term.evalQ?, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, h⟩ := option_bind_eq_some' h
    injection h with h
    subst h
    simp only [Term.evalQ, ihl a ha, ihr b hb, Option.bind_eq_bind,
      Option.bind_some]
    rfl
  | mul l r ihl ihr =>
    intro c h
    simp only [Term.evalQ?, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, h⟩ := option_bind_eq_some' h
    injection h with h
    subst h
    simp only [Term.evalQ, ihl a ha, ihr b hb, Option.bind_eq_bind,
      Option.bind_some]
    rfl
  | sub l r ihl ihr =>
    intro c h
    simp only [Term.evalQ?, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, h⟩ := option_bind_eq_some' h
    injection h with h
    subst h
    simp only [Term.evalQ, ihl a ha, ihr b hb, Option.bind_eq_bind,
      Option.bind_some]
    rfl
  | neg t iht =>
    intro c h
    simp only [Term.evalQ?, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    injection h with h
    subst h
    simp only [Term.evalQ, iht a ha, Option.map_some]
    rfl
  | idx t i ih => intro c h; cases h

theorem Term.freeWires_nil_of_closed :
    ∀ (t : Term) (c : ℚ), t.evalQ? = some c → t.freeWires = [] := by
  intro t
  induction t with
  | var w => intro c h; cases h
  | const c' => intro c h; rfl
  | add l r ihl ihr =>
    intro c h
    simp only [Term.evalQ?, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, _⟩ := option_bind_eq_some' h
    show l.freeWires ++ r.freeWires = []
    rw [ihl a ha, ihr b hb]
    rfl
  | mul l r ihl ihr =>
    intro c h
    simp only [Term.evalQ?, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, _⟩ := option_bind_eq_some' h
    show l.freeWires ++ r.freeWires = []
    rw [ihl a ha, ihr b hb]
    rfl
  | sub l r ihl ihr =>
    intro c h
    simp only [Term.evalQ?, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, _⟩ := option_bind_eq_some' h
    show l.freeWires ++ r.freeWires = []
    rw [ihl a ha, ihr b hb]
    rfl
  | neg t iht =>
    intro c h
    simp only [Term.evalQ?, Option.bind_eq_bind] at h
    obtain ⟨a, ha, _⟩ := option_bind_eq_some' h
    show t.freeWires = []
    exact iht a ha
  | idx t i ih => intro c h; cases h

theorem Term.subst_of_closed {w : Wire} {u : Term} :
    ∀ (t : Term) (c : ℚ), t.evalQ? = some c → Term.subst w u t = t := by
  intro t
  induction t with
  | var w' => intro c h; cases h
  | const c' => intro c h; rfl
  | add l r ihl ihr =>
    intro c h
    simp only [Term.evalQ?, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, _⟩ := option_bind_eq_some' h
    show Term.add (Term.subst w u l) (Term.subst w u r) = Term.add l r
    rw [ihl a ha, ihr b hb]
  | mul l r ihl ihr =>
    intro c h
    simp only [Term.evalQ?, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, _⟩ := option_bind_eq_some' h
    show Term.mul (Term.subst w u l) (Term.subst w u r) = Term.mul l r
    rw [ihl a ha, ihr b hb]
  | sub l r ihl ihr =>
    intro c h
    simp only [Term.evalQ?, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, _⟩ := option_bind_eq_some' h
    show Term.sub (Term.subst w u l) (Term.subst w u r) = Term.sub l r
    rw [ihl a ha, ihr b hb]
  | neg t iht =>
    intro c h
    simp only [Term.evalQ?, Option.bind_eq_bind] at h
    obtain ⟨a, ha, _⟩ := option_bind_eq_some' h
    show Term.neg (Term.subst w u t) = Term.neg t
    rw [iht a ha]
  | idx t i ih => intro c h; cases h

theorem QTensor.map2_shape_join {s₁ s₂ s : Shape} {a b c : QTensor}
    {f : ℚ → ℚ → ℚ}
    (hqa : a.shape = s₁) (hqb : b.shape = s₂)
    (hj : (if s₁ = s₂ then some s₁ else if s₁ = [] then some s₂
        else if s₂ = [] then some s₁ else none) = some s)
    (h : QTensor.map2 f a b = some c) : c.shape = s := by
  unfold QTensor.map2 at h
  split at h
  · next hsh =>
    injection h with h
    subst h
    have hjoin : s₁ = s₂ := by rw [← hqa, ← hqb]; exact hsh
    rw [if_pos hjoin] at hj
    injection hj with hj
    show a.shape = s
    rw [hqa]; exact hj
  · next hsh =>
    split at h
    · next hsa =>
      injection h with h
      subst h
      have hs1 : s₁ = [] := by rw [← hqa]; exact hsa
      have hne : ¬ s₁ = s₂ := by
        intro hc
        exact hsh (by rw [hqa, hqb, hc])
      rw [if_neg hne, if_pos hs1] at hj
      injection hj with hj
      show b.shape = s
      rw [hqb]; exact hj
    · next hsa =>
      split at h
      · next hsb =>
        injection h with h
        subst h
        have hs2 : s₂ = [] := by rw [← hqb]; exact hsb
        have hne : ¬ s₁ = s₂ := by
          intro hc
          exact hsh (by rw [hqa, hqb, hc])
        have hna : ¬ s₁ = [] := by
          intro hc
          exact hsa (by rw [hqa]; exact hc)
        rw [if_neg hne, if_neg hna, if_pos hs2] at hj
        injection hj with hj
        show a.shape = s
        rw [hqa]; exact hj
      · cases h

theorem Term.evalQ_bshape {H : Hypernet} (σ : H.Valuation) :
    ∀ (t : Term) (s : Shape) (q : QTensor),
    t.bshape H = some s → Term.evalQ σ t = some q → q.shape = s := by
  intro t
  induction t with
  | var w =>
    intro s q hb h
    simp only [Term.bshape, Option.map_eq_some_iff] at hb
    obtain ⟨τ, hτ, hs⟩ := hb
    obtain ⟨τ', hτ', hq⟩ := Hypernet.Valuation.wireQ_shape σ h
    rw [hτ] at hτ'
    injection hτ' with h'
    rw [hq, ← h', hs]
  | const c =>
    intro s q hb h
    injection hb with hb
    injection h with h
    subst h
    simpa using hb.symm
  | add l r ihl ihr =>
    intro s q hb h
    simp only [Term.evalQ, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hbb, h⟩ := option_bind_eq_some' h
    simp only [Term.bshape] at hb
    rcases hla : Term.bshape H l with _ | s₁ <;> rw [hla] at hb
    · cases hb
    rcases hra : Term.bshape H r with _ | s₂ <;> rw [hra] at hb
    · cases hb
    have hb' : (if s₁ = s₂ then some s₁ else if s₁ = [] then some s₂
        else if s₂ = [] then some s₁ else none) = some s := hb
    exact QTensor.map2_shape_join (ihl s₁ a hla ha) (ihr s₂ b hra hbb) hb' h
  | mul l r ihl ihr =>
    intro s q hb h
    simp only [Term.evalQ, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hbb, h⟩ := option_bind_eq_some' h
    simp only [Term.bshape] at hb
    rcases hla : Term.bshape H l with _ | s₁ <;> rw [hla] at hb
    · cases hb
    rcases hra : Term.bshape H r with _ | s₂ <;> rw [hra] at hb
    · cases hb
    have hb' : (if s₁ = s₂ then some s₁ else if s₁ = [] then some s₂
        else if s₂ = [] then some s₁ else none) = some s := hb
    exact QTensor.map2_shape_join (ihl s₁ a hla ha) (ihr s₂ b hra hbb) hb' h
  | sub l r ihl ihr =>
    intro s q hb h
    simp only [Term.evalQ, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hbb, h⟩ := option_bind_eq_some' h
    simp only [Term.bshape] at hb
    rcases hla : Term.bshape H l with _ | s₁ <;> rw [hla] at hb
    · cases hb
    rcases hra : Term.bshape H r with _ | s₂ <;> rw [hra] at hb
    · cases hb
    have hb' : (if s₁ = s₂ then some s₁ else if s₁ = [] then some s₂
        else if s₂ = [] then some s₁ else none) = some s := hb
    exact QTensor.map2_shape_join (ihl s₁ a hla ha) (ihr s₂ b hra hbb) hb' h
  | neg t iht =>
    intro s q hb h
    simp only [Term.evalQ, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, hq⟩ := h
    subst hq
    exact iht s a hb ha
  | idx t i iht =>
    intro s q hb h
    simp only [Term.evalQ, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    simp only [Term.bshape] at hb
    split at hb
    · next e hbs =>
      split at hb
      · next hi =>
        injection hb with hb
        have hae : a.shape = [e] := iht [e] a hbs ha
        split at h
        · next e' hae' =>
          split at h
          · injection h with h
            subst h
            exact hb
          · cases h
        · next hne =>
          exact (hne e hae).elim
      · cases hb
    · cases hb

theorem finSum_support_pair {n : Nat} (msk : Fin n → Bool) (f : Fin n → ℝ)
    (a b : Fin n)
    (hfil : (List.finRange n).filter (fun v => msk v) = [a, b])
    (hzero : ∀ v, msk v = false → f v = 0) :
    finSum n f = f a + f b := by
  unfold finSum
  have key : ∀ (l : List (Fin n)), l.filter (fun v => msk v) = [a, b] →
      (l.map f).sum = f a + f b := by
    intro l
    induction l with
    | nil => intro h; cases h
    | cons hd tl ih =>
      intro h
      rw [List.filter_cons] at h
      split at h
      ·
        injection h with h1 h2
        subst h1

        have key2 : ∀ (l2 : List (Fin n)), l2.filter (fun v => msk v) = [b] →
            (l2.map f).sum = f b := by
          intro l2
          induction l2 with
          | nil => intro hh; cases hh
          | cons hd2 tl2 ih2 =>
            intro hh
            rw [List.filter_cons] at hh
            split at hh
            · injection hh with hh1 hh2
              subst hh1
              have hz : ∀ v ∈ tl2.map f, v = 0 := by
                intro v hv
                obtain ⟨u, hu, hu1⟩ := List.mem_map.mp hv
                have : msk u = false := by
                  by_contra hc
                  have : u ∈ tl2.filter (fun v => msk v) := by
                    rw [List.mem_filter]
                    exact ⟨hu, by simpa using hc⟩
                  rw [hh2] at this
                  cases this
                rw [← hu1, hzero u this]
              simp only [List.map_cons, List.sum_cons]
              rw [sum_eq_zero_of_all _ hz]
              ring
            · next hcond =>
              have : msk hd2 = false := by
                by_contra hc
                exact hcond (by simpa using hc)
              simp only [List.map_cons, List.sum_cons, hzero hd2 this, ih2 hh]
              ring
        simp only [List.map_cons, List.sum_cons, key2 tl h2]
      · next hcond =>
        have : msk hd = false := by
          by_contra hc
          exact hcond (by simpa using hc)
        simp only [List.map_cons, List.sum_cons, hzero hd this, ih h]
        ring
  exact key _ hfil
where
  sum_eq_zero_of_all : ∀ (M : List ℝ), (∀ x ∈ M, x = 0) → M.sum = 0 := by
    intro M
    induction M with
    | nil => intro _; rfl
    | cons hd tl ih =>
      intro h
      simp only [List.sum_cons, h hd (by simp), ih (fun x hx => h x (by simp [hx]))]
      ring

theorem barycentricHalfspaceBuild_spec {t : Term} {simplex : Simplex}
    {S : ExtensionSet} {F : Formula}
    (h : barycentricHalfspaceBuild t simplex S = some F) :
    S.simplex = simplex ∧ simplex.complex.ambDim = 1 ∧
    ∃ (a b : Fin simplex.complex.nVertices) (V₀ V₁ : ℚ),
      (List.finRange simplex.complex.nVertices).filter
        (fun v => simplex.contains v) = [a, b] ∧
      (∀ j, simplex.complex.coord a j = V₀) ∧
      (∀ j, simplex.complex.coord b j = V₁) ∧
      V₀ ≠ V₁ ∧
      F = .and
        (f4VertexAtom (S.containsNat a.val)
          (V₁ / (V₁ - V₀)) (-1 / (V₁ - V₀)) t)
        (f4VertexAtom (S.containsNat b.val)
          (-V₀ / (V₁ - V₀)) (1 / (V₁ - V₀)) t) := by
  unfold barycentricHalfspaceBuild at h
  obtain ⟨hguard, h⟩ := option_guard_bind_eq_some h
  obtain ⟨cs, hcs, h⟩ := option_bind_eq_some' h
  unfold baryCoeffs1D at hcs
  split at hcs
  · next hd1 =>
    refine ⟨hguard, hd1, ?_⟩
    split at hcs
    · next a b hfil =>
      simp only [] at hcs
      split at hcs
      · cases hcs
      · next hVne =>
        injection hcs with hcs
        subst hcs
        simp only [List.map_cons, List.map_nil] at h
        injection h with h
        refine ⟨a, b, simplex.complex.coord a ⟨0, by omega⟩,
          simplex.complex.coord b ⟨0, by omega⟩, hfil, ?_, ?_, ?_, ?_⟩
        · intro j
          have hj : j = ⟨0, by omega⟩ := by
            apply Fin.ext
            have := j.isLt
            omega
          rw [hj]
        · intro j
          have hj : j = ⟨0, by omega⟩ := by
            apply Fin.ext
            have := j.isLt
            omega
          rw [hj]
        · exact hVne
        · rw [← h]
    · cases hcs
  · cases hcs

private theorem eraseDupsBy_loop_eq_nil {α : Type} (r : α → α → Bool) :
    ∀ (as bs : List α), List.eraseDupsBy.loop r as bs = [] → as = [] ∧ bs = [] := by
  intro as
  induction as with
  | nil =>
    intro bs h
    simp only [List.eraseDupsBy.loop] at h
    simpa using congrArg List.reverse h
  | cons a as ih =>
    intro bs h
    rw [List.eraseDupsBy.loop] at h
    split at h
    · next hguard =>
      obtain ⟨-, h2⟩ := ih _ h
      subst h2
      simp at hguard
    · obtain ⟨-, h2⟩ := ih _ h
      cases h2

theorem eraseDups_eq_nil {α : Type} [BEq α] {l : List α}
    (h : l.eraseDups = []) : l = [] :=
  (eraseDupsBy_loop_eq_nil _ _ _ h).1

theorem Poly.monos_nil_of_vars_nil {p : QArith.Poly}
    (h : QArith.Poly.vars p = []) : ∀ t ∈ p, t.1 = [] := by
  intro t ht
  have hflat := eraseDups_eq_nil h
  rw [List.flatMap_eq_nil_iff] at hflat
  exact List.map_eq_nil_iff.mp (hflat t ht)

theorem monoEval_congr {ρ₁ ρ₂ : Nat → ℚ} {m : QArith.Mono}
    (h : ∀ ve ∈ m, ρ₁ ve.1 = ρ₂ ve.1) :
    QArith.monoEval ρ₁ m = QArith.monoEval ρ₂ m := by
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨v, e⟩ := hd
    rw [monoEval_cons, monoEval_cons, h (v, e) (by simp),
      ih (fun ve hve => h ve (by simp [hve]))]

theorem Poly.eval_congr_keys {ρ₁ ρ₂ : Nat → ℚ} {p : QArith.Poly}
    (h : ∀ t ∈ p, ∀ ve ∈ t.1, ρ₁ ve.1 = ρ₂ ve.1) :
    QArith.Poly.eval ρ₁ p = QArith.Poly.eval ρ₂ p := by
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨m, c⟩ := hd
    rw [Poly.eval_cons, Poly.eval_cons,
      monoEval_congr (h (m, c) (by simp)),
      ih (fun t ht ve hve => h t (by simp [ht]) ve hve)]

theorem monoEval_remap0 (ρ : Nat → ℚ) (m : QArith.Mono) :
    QArith.monoEval ρ (m.map fun ve => (0, ve.2))
      = QArith.monoEval (fun _ => ρ 0) m := by
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨v, e⟩ := hd
    simp only [List.map_cons, monoEval_cons, ih]

theorem Poly.eval_remap0 (ρ : Nat → ℚ) (p : QArith.Poly) :
    QArith.Poly.eval ρ (p.map fun t => (t.1.map fun ve => (0, ve.2), t.2))
      = QArith.Poly.eval (fun _ => ρ 0) p := by
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨m, c⟩ := hd
    simp only [List.map_cons, Poly.eval_cons, monoEval_remap0, ih]

theorem canon_keys_subset {p : QArith.Poly} :
    ∀ t ∈ QArith.Poly.canon p, t.1 ∈ p.map (·.1) := by
  unfold QArith.Poly.canon
  intro t ht
  have ht' := List.mem_filter.mp ht |>.1

  have key : ∀ (q acc : QArith.Poly), ∀ s ∈ q.foldr QArith.insertTerm acc,
      s.1 ∈ q.map (·.1) ∨ s.1 ∈ acc.map (·.1) := by
    intro q
    induction q with
    | nil => intro acc s hs; exact Or.inr (List.mem_map.mpr ⟨s, hs, rfl⟩)
    | cons hd tl ih =>
      intro acc s hs
      simp only [List.foldr_cons] at hs
      rcases QArith.insertTerm_keys_subset hd _ s hs with h1 | h1
      · exact Or.inl (by simp [h1])
      · obtain ⟨s', hs', hkey⟩ := List.mem_map.mp h1
        rcases ih acc s' hs' with h2 | h2
        · exact Or.inl (by
            rcases List.mem_map.mp h2 with ⟨u, hu, hukey⟩
            exact List.mem_map.mpr ⟨u, by simp [hu], by rw [← hkey, hukey]⟩)
        · exact Or.inr (by
            rcases List.mem_map.mp h2 with ⟨u, hu, hukey⟩
            exact List.mem_map.mpr ⟨u, hu, by rw [← hkey, hukey]⟩)
  rcases key p [] t ht' with h | h
  · exact h
  · simp at h

theorem monoCanon_keys_subset {m : QArith.Mono} :
    ∀ ve ∈ QArith.monoCanon m, ve.1 ∈ m.map (·.1) := by
  unfold QArith.monoCanon
  intro ve hve
  have hve' := List.mem_filter.mp hve |>.1
  have key : ∀ (q acc : QArith.Mono), ∀ s ∈ q.foldr QArith.insertVar acc,
      s.1 ∈ q.map (·.1) ∨ s.1 ∈ acc.map (·.1) := by
    intro q
    induction q with
    | nil => intro acc s hs; exact Or.inr (List.mem_map.mpr ⟨s, hs, rfl⟩)
    | cons hd tl ih =>
      intro acc s hs
      simp only [List.foldr_cons] at hs
      rcases QArith.insertVar_keys_subset hd _ s hs with h1 | h1
      · exact Or.inl (by simp [h1])
      · obtain ⟨s', hs', hkey⟩ := List.mem_map.mp h1
        rcases ih acc s' hs' with h2 | h2
        · exact Or.inl (by
            rcases List.mem_map.mp h2 with ⟨u, hu, hukey⟩
            exact List.mem_map.mpr ⟨u, by simp [hu], by rw [← hkey, hukey]⟩)
        · exact Or.inr (by
            rcases List.mem_map.mp h2 with ⟨u, hu, hukey⟩
            exact List.mem_map.mpr ⟨u, hu, by rw [← hkey, hukey]⟩)
  rcases key m [] ve hve' with h | h
  · exact h
  · simp at h

theorem Term.toPoly_keys :
    ∀ (t : Term), ∀ tm ∈ t.toPoly, ∀ ve ∈ tm.1, ve.1 ∈ t.freeWires := by
  intro t
  induction t with
  | var w =>
    intro tm htm ve hve
    simp only [Term.toPoly, QArith.Poly.var, List.mem_singleton] at htm
    subst htm
    simp only [List.mem_singleton] at hve
    subst hve
    simp [Term.freeWires]
  | const c =>
    intro tm htm ve hve
    simp only [Term.toPoly, QArith.Poly.const] at htm
    split at htm
    · cases htm
    · simp only [List.mem_singleton] at htm
      subst htm
      cases hve
  | idx t i ih =>

    intro tm htm ve hve
    simp [Term.toPoly, QArith.Poly.const] at htm
  | add l r ihl ihr =>
    intro tm htm ve hve
    have hkey := canon_keys_subset tm htm
    obtain ⟨s, hs, hkeyeq⟩ := List.mem_map.mp hkey
    rw [← hkeyeq] at hve
    show ve.1 ∈ l.freeWires ++ r.freeWires
    rcases List.mem_append.mp hs with h | h
    · exact List.mem_append.mpr (Or.inl (ihl s h ve hve))
    · exact List.mem_append.mpr (Or.inr (ihr s h ve hve))
  | mul l r ihl ihr =>
    intro tm htm ve hve
    have hkey := canon_keys_subset tm htm
    obtain ⟨s, hs, hkeyeq⟩ := List.mem_map.mp hkey
    rw [← hkeyeq] at hve
    obtain ⟨⟨m₁, c₁⟩, hm₁, hs'⟩ := List.mem_flatMap.mp hs
    obtain ⟨⟨m₂, c₂⟩, hm₂, hpair⟩ := List.mem_map.mp hs'
    have hmono : s.1 = QArith.monoMul m₁ m₂ := by rw [← hpair]
    rw [hmono] at hve
    have hv' := monoCanon_keys_subset ve hve
    obtain ⟨u, hu, hueq⟩ := List.mem_map.mp hv'
    show ve.1 ∈ l.freeWires ++ r.freeWires
    rcases List.mem_append.mp hu with h | h
    · exact List.mem_append.mpr (Or.inl (by
        have := ihl (m₁, c₁) hm₁ u h
        rwa [hueq] at this))
    · exact List.mem_append.mpr (Or.inr (by
        have := ihr (m₂, c₂) hm₂ u h
        rwa [hueq] at this))
  | sub l r ihl ihr =>
    intro tm htm ve hve
    have hkey := canon_keys_subset tm htm
    obtain ⟨s, hs, hkeyeq⟩ := List.mem_map.mp hkey
    rw [← hkeyeq] at hve
    show ve.1 ∈ l.freeWires ++ r.freeWires
    rcases List.mem_append.mp hs with h | h
    · exact List.mem_append.mpr (Or.inl (ihl s h ve hve))
    · obtain ⟨s₀, hs₀, hnegeq⟩ := List.mem_map.mp h
      have : ve ∈ s₀.1 := by
        have : s.1 = s₀.1 := by rw [← hnegeq]
        rwa [this] at hve
      exact List.mem_append.mpr (Or.inr (ihr s₀ hs₀ ve this))
  | neg t iht =>
    intro tm htm ve hve
    obtain ⟨s₀, hs₀, hnegeq⟩ := List.mem_map.mp htm
    have : ve ∈ s₀.1 := by
      have : tm.1 = s₀.1 := by rw [← hnegeq]
      rwa [this] at hve
    exact iht s₀ hs₀ ve this

theorem Term.toPoly_coeff_ne_zero :
    ∀ (t : Term), ∀ tm ∈ t.toPoly, tm.2 ≠ 0 := by
  have hcanon : ∀ (p : QArith.Poly), ∀ tm ∈ QArith.Poly.canon p, tm.2 ≠ 0 := by
    intro p tm htm
    unfold QArith.Poly.canon at htm
    have := List.mem_filter.mp htm
    simpa using this.2
  intro t
  induction t with
  | var w =>
    intro tm htm
    simp only [Term.toPoly, QArith.Poly.var, List.mem_singleton] at htm
    subst htm
    exact one_ne_zero
  | const c =>
    intro tm htm
    simp only [Term.toPoly, QArith.Poly.const] at htm
    split at htm
    · cases htm
    · next hc =>
      simp only [List.mem_singleton] at htm
      subst htm
      exact hc
  | idx t i ih =>
    intro tm htm
    simp [Term.toPoly, QArith.Poly.const] at htm
  | add l r ihl ihr =>
    intro tm htm
    exact hcanon _ tm htm
  | mul l r ihl ihr =>
    intro tm htm
    exact hcanon _ tm htm
  | sub l r ihl ihr =>
    intro tm htm
    exact hcanon _ tm htm
  | neg t iht =>
    intro tm htm hc
    obtain ⟨u, hu, hueq⟩ := List.mem_map.mp htm
    apply iht u hu
    have h2 : tm.2 = -u.2 := by
      rw [← hueq]
    rw [h2] at hc
    linarith

theorem Term.toPoly_pairwise :
    ∀ (t : Term), t.toPoly.Pairwise (fun s u => keyLT s.1 u.1) := by
  intro t
  induction t with
  | var w => exact List.pairwise_singleton _ _
  | const c =>
    show (QArith.Poly.const c).Pairwise _
    unfold QArith.Poly.const
    split
    · exact List.Pairwise.nil
    · exact List.pairwise_singleton _ _
  | idx t i ih =>
    show (QArith.Poly.const 0).Pairwise _
    simp [QArith.Poly.const]
  | add l r ihl ihr => exact canon_pairwise _
  | mul l r ihl ihr => exact canon_pairwise _
  | sub l r ihl ihr => exact canon_pairwise _
  | neg t iht =>
    show (t.toPoly.map _).Pairwise _
    apply List.Pairwise.map
    · intro a b hab
      show keyLT a.1 b.1
      exact hab
    · exact iht

theorem Term.toPoly_const_form {t : Term}
    (hvars : QArith.Poly.vars t.toPoly = []) :
    t.toPoly = QArith.Poly.const
      (QArith.Poly.eval (fun _ => 0) t.toPoly) := by
  have hmono := Poly.monos_nil_of_vars_nil hvars
  have hpair := Term.toPoly_pairwise t
  have hnz := Term.toPoly_coeff_ne_zero t
  cases ht : t.toPoly with
  | nil =>
    show ([] : QArith.Poly) = QArith.Poly.const (QArith.Poly.eval _ [])
    rw [Poly.eval_nil]
    unfold Poly.const
    rw [if_pos rfl]
  | cons hd tl =>
    obtain ⟨mo, c⟩ := hd
    have hmo : mo = [] := hmono (mo, c) (by rw [ht]; simp)
    subst hmo
    cases tl with
    | nil =>
      show [(([] : QArith.Mono), c)] = QArith.Poly.const (QArith.Poly.eval _ _)
      rw [Poly.eval_cons, Poly.eval_nil, monoEval_nil]
      have hc : c ≠ 0 := hnz ([], c) (by rw [ht]; simp)
      rw [show c * 1 + 0 = c from by ring]
      unfold Poly.const
      rw [if_neg hc]
    | cons hd2 tl2 =>
      exfalso
      obtain ⟨mo2, c2⟩ := hd2
      have hmo2 : mo2 = [] := hmono (mo2, c2) (by rw [ht]; simp)
      subst hmo2
      rw [ht] at hpair
      rw [List.pairwise_cons] at hpair
      have := hpair.1 ([], c2) (by simp)
      exact keyLT_irrefl [] this

theorem asCoordPoly?_eval {t : Term} {p : QArith.Poly}
    (h : Term.asCoordPoly? t = some p) (hix : t.idxFree = true)
    (ρ : Nat → ℚ) :
    QArith.Poly.eval ρ p = QArith.Poly.eval (fun _ => ρ 0) t.toPoly := by
  simp only [Term.asCoordPoly?] at h
  split at h
  case isFalse hnf => exact absurd hix hnf
  case isTrue =>
  split at h
  · next hv =>

    injection h with h
    subst h
    exact Poly.eval_congr_keys (fun tm htm ve hve => by
      have := Poly.monos_nil_of_vars_nil hv tm htm
      rw [this] at hve
      cases hve)
  · next x hv =>

    injection h with h
    subst h
    exact Poly.eval_remap0 ρ t.toPoly
  · cases h

theorem Term.evalQ_total_singleton {H : Hypernet} (σ : H.Valuation) :
    ∀ (t : Term),
    (∀ w ∈ t.freeWires, ∃ qw, σ.wireQ w = some qw ∧ SingletonShape qw.shape) →
    t.idxFree = true →
    ∃ q, Term.evalQ σ t = some q ∧ SingletonShape q.shape ∧
      q.scalar = QArith.Poly.eval σ.rho t.toPoly := by
  intro t
  induction t with
  | var w =>
    intro hw _
    obtain ⟨qw, hqw, hs⟩ := hw w (by simp [Term.freeWires])
    refine ⟨qw, hqw, hs, ?_⟩
    show qw.scalar = QArith.Poly.eval σ.rho (QArith.Poly.var w)
    rw [Poly.eval_var, Hypernet.Valuation.rho_eq σ hqw]
  | const c =>
    intro _ _
    exact ⟨⟨[], [c], rfl⟩, rfl, Or.inl rfl, by simp [QTensor.scalar, Term.toPoly]⟩
  | add l r ihl ihr =>
    intro hw hix
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    obtain ⟨a, ha, hsa, hva⟩ :=
      ihl (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.1
    obtain ⟨b, hb, hsb, hvb⟩ :=
      ihr (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.2
    obtain ⟨c, hc, hsc, hvc⟩ := QTensor.map2_singleton (f := (· + ·)) hsa hsb
    refine ⟨c, ?_, hsc, ?_⟩
    · show (do QTensor.map2 (· + ·) (← Term.evalQ σ l) (← Term.evalQ σ r)) = some c
      rw [ha, hb]
      simpa using hc
    · show c.scalar = QArith.Poly.eval σ.rho (QArith.Poly.add l.toPoly r.toPoly)
      rw [Poly.eval_add, hvc, hva, hvb]
  | mul l r ihl ihr =>
    intro hw hix
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    obtain ⟨a, ha, hsa, hva⟩ :=
      ihl (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.1
    obtain ⟨b, hb, hsb, hvb⟩ :=
      ihr (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.2
    obtain ⟨c, hc, hsc, hvc⟩ := QTensor.map2_singleton (f := (· * ·)) hsa hsb
    refine ⟨c, ?_, hsc, ?_⟩
    · show (do QTensor.map2 (· * ·) (← Term.evalQ σ l) (← Term.evalQ σ r)) = some c
      rw [ha, hb]
      simpa using hc
    · show c.scalar = QArith.Poly.eval σ.rho (QArith.Poly.mul l.toPoly r.toPoly)
      rw [Poly.eval_mul, hvc, hva, hvb]
  | sub l r ihl ihr =>
    intro hw hix
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    obtain ⟨a, ha, hsa, hva⟩ :=
      ihl (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.1
    obtain ⟨b, hb, hsb, hvb⟩ :=
      ihr (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.2
    obtain ⟨c, hc, hsc, hvc⟩ := QTensor.map2_singleton (f := (· - ·)) hsa hsb
    refine ⟨c, ?_, hsc, ?_⟩
    · show (do QTensor.map2 (· - ·) (← Term.evalQ σ l) (← Term.evalQ σ r)) = some c
      rw [ha, hb]
      simpa using hc
    · show c.scalar = QArith.Poly.eval σ.rho (QArith.Poly.sub l.toPoly r.toPoly)
      rw [Poly.eval_sub, hvc, hva, hvb]
  | neg t iht =>
    intro hw hix
    obtain ⟨a, ha, hsa, hva⟩ := iht
      (fun w hw' => hw w (by simpa [Term.freeWires] using hw'))
      (by simpa [Term.idxFree] using hix)
    refine ⟨QTensor.map1 Neg.neg a, ?_, hsa, ?_⟩
    · show (Term.evalQ σ t).map (QTensor.map1 Neg.neg) = _
      rw [ha]
      rfl
    · show (QTensor.map1 Neg.neg a).scalar = QArith.Poly.eval σ.rho (QArith.Poly.neg t.toPoly)
      rw [Poly.eval_neg, ← hva]
      show (a.entries.map Neg.neg).getD 0 0 = -a.scalar
      rw [QTensor.entries_singleton hsa]
      rfl
  | idx t i ih =>
    intro _ hix
    simp [Term.idxFree] at hix

theorem QTensor.map2_singleton_inv {f : ℚ → ℚ → ℚ} {a b c : QTensor}
    (h : QTensor.map2 f a b = some c) (hc : SingletonShape c.shape) :
    SingletonShape a.shape ∧ SingletonShape b.shape := by
  unfold QTensor.map2 at h
  split at h
  · next hs =>
    injection h with h
    subst h
    exact ⟨hc, by rw [← hs]; exact hc⟩
  · split at h
    · next hsa =>
      injection h with h
      subst h
      exact ⟨Or.inl hsa, hc⟩
    · split at h
      · next hsb =>
        injection h with h
        subst h
        exact ⟨hc, Or.inl hsb⟩
      · cases h

theorem Term.evalQ_singleton_wires {H : Hypernet} (σ : H.Valuation) :
    ∀ (t : Term) (q : QTensor), Term.evalQ σ t = some q →
    SingletonShape q.shape → t.idxFree = true →
    ∀ w ∈ t.freeWires, ∀ qw, σ.wireQ w = some qw → SingletonShape qw.shape := by
  intro t
  induction t with
  | var w =>
    intro q h hq _ w' hw' qw hqw
    simp only [Term.freeWires, List.mem_singleton] at hw'
    subst hw'
    have hwq : σ.wireQ w' = some q := h
    rw [hqw] at hwq
    injection hwq with hwq
    rwa [hwq]
  | const c =>
    intro q h hq _ w' hw'
    cases hw'
  | add l r ihl ihr =>
    intro q h hq hix w' hw' qw hqw
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    simp only [Term.evalQ, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, h⟩ := option_bind_eq_some' h
    obtain ⟨hsa, hsb⟩ := QTensor.map2_singleton_inv h hq
    rcases List.mem_append.mp hw' with hw'' | hw''
    · exact ihl a ha hsa hix.1 w' hw'' qw hqw
    · exact ihr b hb hsb hix.2 w' hw'' qw hqw
  | mul l r ihl ihr =>
    intro q h hq hix w' hw' qw hqw
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    simp only [Term.evalQ, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, h⟩ := option_bind_eq_some' h
    obtain ⟨hsa, hsb⟩ := QTensor.map2_singleton_inv h hq
    rcases List.mem_append.mp hw' with hw'' | hw''
    · exact ihl a ha hsa hix.1 w' hw'' qw hqw
    · exact ihr b hb hsb hix.2 w' hw'' qw hqw
  | sub l r ihl ihr =>
    intro q h hq hix w' hw' qw hqw
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    simp only [Term.evalQ, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, h⟩ := option_bind_eq_some' h
    obtain ⟨hsa, hsb⟩ := QTensor.map2_singleton_inv h hq
    rcases List.mem_append.mp hw' with hw'' | hw''
    · exact ihl a ha hsa hix.1 w' hw'' qw hqw
    · exact ihr b hb hsb hix.2 w' hw'' qw hqw
  | neg t iht =>
    intro q h hq hix w' hw' qw hqw
    simp only [Term.evalQ, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, hqeq⟩ := h
    have hsa : SingletonShape a.shape := by
      subst hqeq
      exact hq
    exact iht a ha hsa (by simpa [Term.idxFree] using hix) w'
      (by simpa [Term.freeWires] using hw') qw hqw
  | idx t i ih =>
    intro q h hq hix
    simp [Term.idxFree] at hix

theorem Term.evalQ?_of_no_wires :
    ∀ (t : Term), t.freeWires = [] → t.idxFree = true →
    ∃ c, t.evalQ? = some c := by
  intro t
  induction t with
  | var w => intro h _; cases h
  | const c => intro _ _; exact ⟨c, rfl⟩
  | add l r ihl ihr =>
    intro h hix
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    obtain ⟨a, ha⟩ := ihl (List.append_eq_nil_iff.mp h).1 hix.1
    obtain ⟨b, hb⟩ := ihr (List.append_eq_nil_iff.mp h).2 hix.2
    exact ⟨a + b, by simp [Term.evalQ?, ha, hb]⟩
  | mul l r ihl ihr =>
    intro h hix
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    obtain ⟨a, ha⟩ := ihl (List.append_eq_nil_iff.mp h).1 hix.1
    obtain ⟨b, hb⟩ := ihr (List.append_eq_nil_iff.mp h).2 hix.2
    exact ⟨a * b, by simp [Term.evalQ?, ha, hb]⟩
  | sub l r ihl ihr =>
    intro h hix
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    obtain ⟨a, ha⟩ := ihl (List.append_eq_nil_iff.mp h).1 hix.1
    obtain ⟨b, hb⟩ := ihr (List.append_eq_nil_iff.mp h).2 hix.2
    exact ⟨a - b, by simp [Term.evalQ?, ha, hb]⟩
  | neg t iht =>
    intro h hix
    obtain ⟨a, ha⟩ := iht h (by simpa [Term.idxFree] using hix)
    exact ⟨-a, by simp [Term.evalQ?, ha]⟩
  | idx t i ih =>
    intro _ hix
    simp [Term.idxFree] at hix

theorem Poly.eval_toPoly_closed {t : Term} {c : ℚ}
    (h : t.evalQ? = some c) (ρ : Nat → ℚ) :
    QArith.Poly.eval ρ t.toPoly = c := by
  induction t generalizing c with
  | var w => cases h
  | const c' =>
    injection h with h
    subst h
    show QArith.Poly.eval ρ (QArith.Poly.const c') = c'
    simp
  | add l r ihl ihr =>
    simp only [Term.evalQ?, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, h⟩ := option_bind_eq_some' h
    injection h with h
    subst h
    show QArith.Poly.eval ρ (QArith.Poly.add l.toPoly r.toPoly) = _
    rw [Poly.eval_add, ihl ha, ihr hb]
  | mul l r ihl ihr =>
    simp only [Term.evalQ?, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, h⟩ := option_bind_eq_some' h
    injection h with h
    subst h
    show QArith.Poly.eval ρ (QArith.Poly.mul l.toPoly r.toPoly) = _
    rw [Poly.eval_mul, ihl ha, ihr hb]
  | sub l r ihl ihr =>
    simp only [Term.evalQ?, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    obtain ⟨b, hb, h⟩ := option_bind_eq_some' h
    injection h with h
    subst h
    show QArith.Poly.eval ρ (QArith.Poly.sub l.toPoly r.toPoly) = _
    rw [Poly.eval_sub, ihl ha, ihr hb]
  | neg t iht =>
    simp only [Term.evalQ?, Option.bind_eq_bind] at h
    obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
    injection h with h
    subst h
    show QArith.Poly.eval ρ (QArith.Poly.neg t.toPoly) = _
    rw [Poly.eval_neg, iht ha]
  | idx t i ih => cases h

def QTensor.brRead (q : QTensor) (i : ℕ) : ℚ :=
  if q.shape = [] then q.scalar else q.entries.getD i 0

theorem QTensor.brRead_scalar {q : QTensor} (h : q.shape = []) (i : ℕ) :
    q.brRead i = q.scalar := by
  unfold QTensor.brRead
  rw [if_pos h]

theorem QTensor.brRead_pos {q : QTensor} (h : ¬ q.shape = []) (i : ℕ) :
    q.brRead i = q.entries.getD i 0 := by
  unfold QTensor.brRead
  rw [if_neg h]

theorem QTensor.brRead_mk {sh : Shape} {es : List ℚ}
    {pf : es.length = Shape.totalSize sh} (i : ℕ) :
    (QTensor.mk sh es pf).brRead i
      = if sh = [] then es.getD 0 0 else es.getD i 0 := rfl

noncomputable def Hypernet.Valuation.entryVal {H : Hypernet}
    (σ : H.Valuation) (i : ℕ) (w : Wire) : ℚ :=
  match σ.wireQ w with
  | some qw => qw.brRead i
  | none => 0

theorem Hypernet.Valuation.entryVal_eq {H : Hypernet} (σ : H.Valuation)
    {w : Wire} {qw : QTensor} (h : σ.wireQ w = some qw) (i : ℕ) :
    σ.entryVal i w = qw.brRead i := by
  unfold Hypernet.Valuation.entryVal
  rw [h]

theorem Term.evalQ_add_inv {H : Hypernet} (σ : H.Valuation) {l r : Term}
    {q : QTensor} (h : Term.evalQ σ (.add l r) = some q) :
    ∃ a b, Term.evalQ σ l = some a ∧ Term.evalQ σ r = some b ∧
      QTensor.map2 (· + ·) a b = some q := by
  simp only [Term.evalQ, Option.bind_eq_bind] at h
  obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
  obtain ⟨b, hb, h⟩ := option_bind_eq_some' h
  exact ⟨a, b, ha, hb, h⟩

theorem Term.evalQ_idx_inv {H : Hypernet} (σ : H.Valuation) {t : Term}
    {i : Nat} {q : QTensor} (h : Term.evalQ σ (.idx t i) = some q) :
    ∃ a e, Term.evalQ σ t = some a ∧ a.shape = [e] ∧ i < e ∧
      q = ⟨[], [a.entries.getD i 0], rfl⟩ := by
  simp only [Term.evalQ, Option.bind_eq_bind] at h
  obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
  split at h
  · next e hae =>
    split at h
    · next hi =>
      injection h with h
      exact ⟨a, e, ha, hae, hi, h.symm⟩
    · cases h
  · cases h

theorem Term.evalQ_mul_inv {H : Hypernet} (σ : H.Valuation) {l r : Term}
    {q : QTensor} (h : Term.evalQ σ (.mul l r) = some q) :
    ∃ a b, Term.evalQ σ l = some a ∧ Term.evalQ σ r = some b ∧
      QTensor.map2 (· * ·) a b = some q := by
  simp only [Term.evalQ, Option.bind_eq_bind] at h
  obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
  obtain ⟨b, hb, h⟩ := option_bind_eq_some' h
  exact ⟨a, b, ha, hb, h⟩

theorem Term.evalQ_sub_inv {H : Hypernet} (σ : H.Valuation) {l r : Term}
    {q : QTensor} (h : Term.evalQ σ (.sub l r) = some q) :
    ∃ a b, Term.evalQ σ l = some a ∧ Term.evalQ σ r = some b ∧
      QTensor.map2 (· - ·) a b = some q := by
  simp only [Term.evalQ, Option.bind_eq_bind] at h
  obtain ⟨a, ha, h⟩ := option_bind_eq_some' h
  obtain ⟨b, hb, h⟩ := option_bind_eq_some' h
  exact ⟨a, b, ha, hb, h⟩

theorem scaled_nonpos_iff {k x : ℚ} (hk : 0 < k) : k * x ≤ 0 ↔ x ≤ 0 := by
  constructor
  · intro h
    by_contra hx
    push_neg at hx
    exact absurd (mul_pos hk hx) (not_lt.mpr h)
  · intro h
    calc k * x ≤ k * 0 := mul_le_mul_of_nonneg_left h hk.le
    _ = 0 := mul_zero k

theorem primAffine_spec (s c : ℚ) :
    ∃ k : ℚ, 0 < k ∧ (primAffine s c).1 = k * s ∧ (primAffine s c).2 = k * c := by
  unfold primAffine
  split
  · next hc =>
    subst hc
    rcases lt_trichotomy s 0 with hs | hs | hs
    · refine ⟨-s⁻¹, neg_pos.mpr (inv_lt_zero.mpr hs), ?_, by ring⟩
      rw [if_pos hs, neg_mul, inv_mul_cancel₀ hs.ne]
    · subst hs
      exact ⟨1, one_pos, by norm_num, by ring⟩
    · refine ⟨s⁻¹, inv_pos.mpr hs, ?_, by ring⟩
      rw [if_neg (not_lt.mpr hs.le), if_neg hs.ne', inv_mul_cancel₀ hs.ne']
  · next hc =>
    have hLpos : 0 < Nat.lcm s.den c.den :=
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero s.den_nz c.den_nz)
    have hdvd : c.den ∣ Nat.lcm s.den c.den := Nat.dvd_lcm_right _ _
    have hquot : 0 < Nat.lcm s.den c.den / c.den :=
      Nat.div_pos (Nat.le_of_dvd hLpos hdvd) c.den_pos
    have hn2 : c.num * ((Nat.lcm s.den c.den / c.den : Nat) : Int) ≠ 0 :=
      mul_ne_zero (Rat.num_ne_zero.mpr hc) (by exact_mod_cast hquot.ne')
    have hgpos : 0 < Int.gcd (s.num * (Nat.lcm s.den c.den / s.den : Nat))
        (c.num * (Nat.lcm s.den c.den / c.den : Nat)) :=
      Nat.pos_of_ne_zero fun h0 => hn2 (Int.gcd_eq_zero_iff.mp h0).2
    refine ⟨(Nat.lcm s.den c.den : ℚ) /
      ((Int.gcd (s.num * (Nat.lcm s.den c.den / s.den : Nat))
        (c.num * (Nat.lcm s.den c.den / c.den : Nat)) : ℕ) : ℚ),
      div_pos (by exact_mod_cast hLpos) (by exact_mod_cast hgpos), rfl, rfl⟩

theorem f4Lhs_evalQ {H : Hypernet} (σ : H.Valuation) {t : Term} {q : QTensor}
    (hq : Term.evalQ σ t = some q) (hsq : SingletonShape q.shape) (s' c' : ℚ) :
    ∃ qa, Term.evalQ σ (f4Lhs s' c' t) = some qa ∧
      SingletonShape qa.shape ∧ qa.scalar = s' * q.scalar + c' := by
  obtain ⟨m, hm, hsm, hvm⟩ :=
    QTensor.map2_singleton (f := (· * ·)) (a := (⟨[], [s'], rfl⟩ : QTensor))
      (b := q) (Or.inl rfl) hsq
  unfold f4Lhs
  split
  · next hc =>
    subst hc
    refine ⟨m, ?_, hsm, ?_⟩
    · simp only [Term.evalQ, Option.bind_eq_bind, hq, Option.bind_some]
      exact hm
    · rw [hvm, add_zero]
      rfl
  · obtain ⟨qa, hqa, hsqa, hvqa⟩ :=
      QTensor.map2_singleton (f := (· + ·)) (a := m)
        (b := (⟨[], [c'], rfl⟩ : QTensor)) hsm (Or.inl rfl)
    refine ⟨qa, ?_, hsqa, ?_⟩
    · simp only [Term.evalQ, Option.bind_eq_bind, hq, Option.bind_some]
      rw [hm]
      simp only [Option.bind_some]
      exact hqa
    · rw [hvqa, hvm]
      rfl

theorem f4Lhs_evalQ_inv {H : Hypernet} (σ : H.Valuation) {t : Term}
    {s' c' : ℚ} {qa : QTensor}
    (h : Term.evalQ σ (f4Lhs s' c' t) = some qa) :
    ∃ q, Term.evalQ σ t = some q := by
  unfold f4Lhs at h
  split at h
  · obtain ⟨s1, q, hs1, hq, _⟩ := Term.evalQ_mul_inv σ h
    exact ⟨q, hq⟩
  · obtain ⟨m1, c1, hm1, hc1, _⟩ := Term.evalQ_add_inv σ h
    obtain ⟨s1, q, hs1, hq, _⟩ := Term.evalQ_mul_inv σ hm1
    exact ⟨q, hq⟩

theorem f4VertexAtom_holds_iff {H : Hypernet} {σ : H.Valuation} {t : Term}
    {q : QTensor} (hq : Term.evalQ σ t = some q) (hsq : SingletonShape q.shape)
    (inS : Bool) (off slp : ℚ) :
    Formula.holds σ (f4VertexAtom inS off slp t) ↔
      (if inS then off + slp * q.scalar ≤ 0
       else 0 ≤ off + slp * q.scalar) := by
  have key : ∀ s c : ℚ,
      Formula.holds σ (.atom .le
        (f4Lhs (primAffine s c).1 (primAffine s c).2 t) (.const 0)) ↔
      c + s * q.scalar ≤ 0 := by
    intro s c
    obtain ⟨k, hk, h1, h2⟩ := primAffine_spec s c
    obtain ⟨qa, hqa, hsqa, hvqa⟩ := f4Lhs_evalQ σ hq hsq
      (primAffine s c).1 (primAffine s c).2
    constructor
    · rintro ⟨a0, a1, ha0, ha1, hrel⟩
      have haeq : a0 = qa := by
        have h' := ha0.symm.trans hqa
        injection h'
      rw [haeq] at hrel
      have hz : a1 = ⟨[], [0], rfl⟩ := by
        have h' : some (⟨[], [0], rfl⟩ : QTensor) = some a1 := ha1
        injection h' with h'
        exact h'.symm
      rw [hz] at hrel
      have hscal := (QTensor.rel2_singleton hsqa (Or.inl rfl)).mp hrel
      have hscal' : qa.scalar ≤ 0 := hscal
      rw [hvqa, h1, h2] at hscal'
      have hexp : k * s * q.scalar + k * c = k * (c + s * q.scalar) := by ring
      rw [hexp] at hscal'
      exact (scaled_nonpos_iff hk).mp hscal'
    · intro hsign
      refine ⟨qa, ⟨[], [0], rfl⟩, hqa, rfl, ?_⟩
      rw [QTensor.rel2_singleton hsqa (Or.inl rfl)]
      show qa.scalar ≤ QTensor.scalar ⟨[], [0], rfl⟩
      have hgoal : qa.scalar ≤ 0 := by
        rw [hvqa, h1, h2]
        have hexp : k * s * q.scalar + k * c = k * (c + s * q.scalar) := by ring
        rw [hexp]
        exact (scaled_nonpos_iff hk).mpr hsign
      exact hgoal
  unfold f4VertexAtom
  cases inS
  · simp only [Bool.false_eq_true, if_false]
    rw [key (-slp) (-off)]
    constructor <;> intro h <;> linarith
  · simp only [if_true]
    rw [key slp off]

theorem f4VertexAtom_holds_inv {H : Hypernet} {σ : H.Valuation} {t : Term}
    {inS : Bool} {off slp : ℚ}
    (h : Formula.holds σ (f4VertexAtom inS off slp t)) :
    ∃ q, Term.evalQ σ t = some q := by
  unfold f4VertexAtom at h
  obtain ⟨a0, a1, ha0, ha1, hrel⟩ := h
  exact f4Lhs_evalQ_inv σ ha0

theorem QTensor.map2_defined_broadcast {f : ℚ → ℚ → ℚ} {a b : QTensor}
    {s : Shape} (ha : a.shape = [] ∨ a.shape = s)
    (hb : b.shape = [] ∨ b.shape = s) :
    ∃ c, QTensor.map2 f a b = some c := by
  unfold QTensor.map2
  by_cases hs : a.shape = b.shape
  · exact ⟨_, dif_pos hs⟩
  · rw [dif_neg hs]
    by_cases hsa : a.shape = []
    · rw [if_pos hsa]
      exact ⟨_, rfl⟩
    · rw [if_neg hsa]
      by_cases hsb : b.shape = []
      · rw [if_pos hsb]
        exact ⟨_, rfl⟩
      · exfalso
        rcases ha with ha | ha
        · exact hsa ha
        · rcases hb with hb | hb
          · exact hsb hb
          · exact hs (ha.trans hb.symm)

theorem QTensor.map2_shape_broadcast {f : ℚ → ℚ → ℚ} {a b c : QTensor}
    {s : Shape} (h : QTensor.map2 f a b = some c)
    (ha : a.shape = [] ∨ a.shape = s) (hb : b.shape = [] ∨ b.shape = s) :
    (c.shape = [] ∨ c.shape = s) ∧
      (c.shape = [] → a.shape = [] ∧ b.shape = []) := by
  unfold QTensor.map2 at h
  split at h
  · next hs =>
    injection h with h
    subst h
    refine ⟨ha, fun hc => ⟨hc, ?_⟩⟩
    show b.shape = []
    rw [← hs]
    exact hc
  · next hs =>
    split at h
    · next hsa =>
      injection h with h
      subst h
      exact ⟨hb, fun hc => ⟨hsa, hc⟩⟩
    · next hsa =>
      split at h
      · next hsb =>
        injection h with h
        subst h
        exact ⟨ha, fun hc => ⟨hc, hsb⟩⟩
      · cases h

theorem QTensor.map2_brRead {f : ℚ → ℚ → ℚ} {a b c : QTensor} {s : Shape}
    (h : QTensor.map2 f a b = some c)
    (ha : a.shape = [] ∨ a.shape = s) (hb : b.shape = [] ∨ b.shape = s)
    {i : ℕ} (hi : i < Shape.totalSize s) :
    c.brRead i = f (a.brRead i) (b.brRead i) := by
  unfold QTensor.map2 at h
  split at h
  · next hs =>
    injection h with h
    subst h
    rw [QTensor.brRead_mk]
    by_cases hsa : a.shape = []
    · have hsb : b.shape = [] := by rw [← hs]; exact hsa
      have hae := QTensor.entries_singleton (q := a) (Or.inl hsa)
      have hbe := QTensor.entries_singleton (q := b) (Or.inl hsb)
      rw [if_pos hsa, QTensor.brRead_scalar hsa, QTensor.brRead_scalar hsb,
        hae, hbe]
      rfl
    · have hsA : a.shape = s := ha.resolve_left hsa
      have hsb : ¬ b.shape = [] := by rw [← hs]; exact hsa
      have hila : i < a.entries.length := by rw [a.len_eq, hsA]; exact hi
      have hilb : i < b.entries.length := by rw [b.len_eq, ← hs, hsA]; exact hi
      have hizw : i < (a.entries.zipWith f b.entries).length := by
        rw [List.length_zipWith]
        omega
      rw [if_neg hsa, QTensor.brRead_pos hsa, QTensor.brRead_pos hsb,
        List.getD_eq_getElem _ _ hizw, List.getD_eq_getElem _ _ hila,
        List.getD_eq_getElem _ _ hilb, List.getElem_zipWith]
  · next hs =>
    split at h
    · next hsa =>
      injection h with h
      subst h
      rw [QTensor.brRead_mk]
      have hsb : ¬ b.shape = [] := fun hc => hs (hsa.trans hc.symm)
      have hsB : b.shape = s := hb.resolve_left hsb
      have hilb : i < b.entries.length := by rw [b.len_eq, hsB]; exact hi
      have him : i < (b.entries.map (f a.scalar)).length := by
        rw [List.length_map]
        exact hilb
      rw [if_neg hsb, QTensor.brRead_scalar hsa, QTensor.brRead_pos hsb,
        List.getD_eq_getElem _ _ him, List.getD_eq_getElem _ _ hilb,
        List.getElem_map]
    · next hsa =>
      split at h
      · next hsb =>
        injection h with h
        subst h
        rw [QTensor.brRead_mk]
        have hsA : a.shape = s := ha.resolve_left hsa
        have hila : i < a.entries.length := by rw [a.len_eq, hsA]; exact hi
        have him : i < (a.entries.map (f · b.scalar)).length := by
          rw [List.length_map]
          exact hila
        rw [if_neg hsa, QTensor.brRead_pos hsa, QTensor.brRead_scalar hsb,
          List.getD_eq_getElem _ _ him, List.getD_eq_getElem _ _ hila,
          List.getElem_map]
      · cases h

theorem QTensor.map1_brRead {a : QTensor} {s : Shape}
    (ha : a.shape = [] ∨ a.shape = s) (f : ℚ → ℚ) {i : ℕ}
    (hi : i < Shape.totalSize s) :
    (QTensor.map1 f a).brRead i = f (a.brRead i) := by
  show (QTensor.mk a.shape (a.entries.map f) _).brRead i = _
  rw [QTensor.brRead_mk]
  by_cases hsa : a.shape = []
  · have hae := QTensor.entries_singleton (q := a) (Or.inl hsa)
    rw [if_pos hsa, QTensor.brRead_scalar hsa, hae]
    rfl
  · have hsA : a.shape = s := ha.resolve_left hsa
    have hila : i < a.entries.length := by rw [a.len_eq, hsA]; exact hi
    have him : i < (a.entries.map f).length := by
      rw [List.length_map]
      exact hila
    rw [if_neg hsa, QTensor.brRead_pos hsa,
      List.getD_eq_getElem _ _ him, List.getD_eq_getElem _ _ hila,
      List.getElem_map]

theorem Term.evalQ_brRead {H : Hypernet} (σ : H.Valuation) (s : Shape) :
    ∀ (t : Term),
    (∀ w ∈ t.freeWires, ∃ qw, σ.wireQ w = some qw ∧
      (qw.shape = [] ∨ qw.shape = s)) →
    t.idxFree = true →
    ∃ q, Term.evalQ σ t = some q ∧ (q.shape = [] ∨ q.shape = s) ∧
      (q.shape = [] → ∀ w ∈ t.freeWires, ∀ qw, σ.wireQ w = some qw →
        qw.shape = []) ∧
      ∀ i, i < Shape.totalSize s →
        q.brRead i = QArith.Poly.eval (σ.entryVal i) t.toPoly := by
  intro t
  induction t with
  | var w =>
    intro hw _
    obtain ⟨qw, hqw, hs⟩ := hw w (by simp [Term.freeWires])
    refine ⟨qw, hqw, hs, ?_, ?_⟩
    · intro hnil w' hw' qw' hqw'
      simp only [Term.freeWires, List.mem_singleton] at hw'
      subst hw'
      rw [hqw'] at hqw
      injection hqw with hqw
      rw [hqw]
      exact hnil
    · intro i _
      show qw.brRead i = QArith.Poly.eval (σ.entryVal i) (QArith.Poly.var w)
      rw [Poly.eval_var, Hypernet.Valuation.entryVal_eq σ hqw]
  | const c =>
    intro _ _
    refine ⟨⟨[], [c], rfl⟩, rfl, Or.inl rfl, fun _ w hw => absurd hw (by simp [Term.freeWires]), ?_⟩
    intro i _
    show QTensor.brRead ⟨[], [c], rfl⟩ i = QArith.Poly.eval (σ.entryVal i) (QArith.Poly.const c)
    rw [QTensor.brRead_scalar (q := ⟨[], [c], rfl⟩) rfl, Poly.eval_const]
    rfl
  | add l r ihl ihr =>
    intro hw hix
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    obtain ⟨a, ha, hja, hza, hea⟩ :=
      ihl (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.1
    obtain ⟨b, hb, hjb, hzb, heb⟩ :=
      ihr (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.2
    obtain ⟨c, hc⟩ := QTensor.map2_defined_broadcast (f := (· + ·)) hja hjb
    obtain ⟨hjc, hzc⟩ := QTensor.map2_shape_broadcast hc hja hjb
    refine ⟨c, ?_, hjc, ?_, ?_⟩
    · show (do QTensor.map2 (· + ·) (← Term.evalQ σ l) (← Term.evalQ σ r)) = some c
      rw [ha, hb]
      simpa using hc
    · intro hnil w hw' qw hqw
      obtain ⟨hza', hzb'⟩ := hzc hnil
      rcases List.mem_append.mp hw' with h' | h'
      · exact hza hza' w h' qw hqw
      · exact hzb hzb' w h' qw hqw
    · intro i hi
      show c.brRead i = QArith.Poly.eval (σ.entryVal i) (QArith.Poly.add l.toPoly r.toPoly)
      rw [Poly.eval_add, ← hea i hi, ← heb i hi]
      exact QTensor.map2_brRead hc hja hjb hi
  | mul l r ihl ihr =>
    intro hw hix
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    obtain ⟨a, ha, hja, hza, hea⟩ :=
      ihl (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.1
    obtain ⟨b, hb, hjb, hzb, heb⟩ :=
      ihr (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.2
    obtain ⟨c, hc⟩ := QTensor.map2_defined_broadcast (f := (· * ·)) hja hjb
    obtain ⟨hjc, hzc⟩ := QTensor.map2_shape_broadcast hc hja hjb
    refine ⟨c, ?_, hjc, ?_, ?_⟩
    · show (do QTensor.map2 (· * ·) (← Term.evalQ σ l) (← Term.evalQ σ r)) = some c
      rw [ha, hb]
      simpa using hc
    · intro hnil w hw' qw hqw
      obtain ⟨hza', hzb'⟩ := hzc hnil
      rcases List.mem_append.mp hw' with h' | h'
      · exact hza hza' w h' qw hqw
      · exact hzb hzb' w h' qw hqw
    · intro i hi
      show c.brRead i = QArith.Poly.eval (σ.entryVal i) (QArith.Poly.mul l.toPoly r.toPoly)
      rw [Poly.eval_mul, ← hea i hi, ← heb i hi]
      exact QTensor.map2_brRead hc hja hjb hi
  | sub l r ihl ihr =>
    intro hw hix
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    obtain ⟨a, ha, hja, hza, hea⟩ :=
      ihl (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.1
    obtain ⟨b, hb, hjb, hzb, heb⟩ :=
      ihr (fun w hw' => hw w (by simp [Term.freeWires, hw'])) hix.2
    obtain ⟨c, hc⟩ := QTensor.map2_defined_broadcast (f := (· - ·)) hja hjb
    obtain ⟨hjc, hzc⟩ := QTensor.map2_shape_broadcast hc hja hjb
    refine ⟨c, ?_, hjc, ?_, ?_⟩
    · show (do QTensor.map2 (· - ·) (← Term.evalQ σ l) (← Term.evalQ σ r)) = some c
      rw [ha, hb]
      simpa using hc
    · intro hnil w hw' qw hqw
      obtain ⟨hza', hzb'⟩ := hzc hnil
      rcases List.mem_append.mp hw' with h' | h'
      · exact hza hza' w h' qw hqw
      · exact hzb hzb' w h' qw hqw
    · intro i hi
      show c.brRead i = QArith.Poly.eval (σ.entryVal i) (QArith.Poly.sub l.toPoly r.toPoly)
      rw [Poly.eval_sub, ← hea i hi, ← heb i hi]
      exact QTensor.map2_brRead hc hja hjb hi
  | neg t iht =>
    intro hw hix
    obtain ⟨a, ha, hja, hza, hea⟩ :=
      iht (fun w hw' => hw w (by simpa [Term.freeWires] using hw'))
        (by simpa [Term.idxFree] using hix)
    refine ⟨QTensor.map1 Neg.neg a, ?_, ?_, ?_, ?_⟩
    · show (Term.evalQ σ t).map (QTensor.map1 Neg.neg) = _
      rw [ha]
      rfl
    · show (a.shape = [] ∨ a.shape = s)
      exact hja
    · intro hnil w hw' qw hqw
      exact hza hnil w (by simpa [Term.freeWires] using hw') qw hqw
    · intro i hi
      show (QTensor.map1 Neg.neg a).brRead i
        = QArith.Poly.eval (σ.entryVal i) (QArith.Poly.neg t.toPoly)
      rw [Poly.eval_neg, ← hea i hi]
      exact QTensor.map1_brRead hja Neg.neg hi
  | idx t i ih =>
    intro _ hix
    simp [Term.idxFree] at hix

def QTensor.brReadC (q : QTensor) (i : ℕ) : ℚ :=
  if q.shape = [] then q.scalar
  else q.entries.getD (if i < q.entries.length then i else 0) 0

theorem QTensor.brReadC_scalar {q : QTensor} (h : q.shape = []) (i : ℕ) :
    q.brReadC i = q.scalar := by
  unfold QTensor.brReadC
  rw [if_pos h]

theorem QTensor.brReadC_in_range {q : QTensor} {i : ℕ}
    (hi : i < q.entries.length) : q.brReadC i = q.entries.getD i 0 := by
  unfold QTensor.brReadC
  by_cases hs : q.shape = []
  · rw [if_pos hs]
    have hlen : q.entries.length = 1 := by
      have := q.len_eq
      rw [hs] at this
      simpa [Shape.totalSize] using this
    have : i = 0 := by omega
    subst this
    rfl
  · rw [if_neg hs, if_pos hi]

theorem QTensor.brReadC_eq_brRead {q : QTensor} {s : Shape}
    (hq : q.shape = [] ∨ q.shape = s) {i : ℕ}
    (hi : i < Shape.totalSize s) : q.brReadC i = q.brRead i := by
  rcases hq with h | h
  · rw [QTensor.brReadC_scalar h, QTensor.brRead_scalar h]
  · by_cases hs : q.shape = []
    · rw [QTensor.brReadC_scalar hs, QTensor.brRead_scalar hs]
    · have hil : i < q.entries.length := by
        rw [q.len_eq, h]
        exact hi
      rw [QTensor.brReadC_in_range hil, QTensor.brRead_pos hs]

noncomputable def Hypernet.Valuation.entryValC {H : Hypernet}
    (σ : H.Valuation) (i : ℕ) (w : Wire) : ℚ :=
  match σ.wireQ w with
  | some qw => qw.brReadC i
  | none => 0

theorem Hypernet.Valuation.entryValC_eq {H : Hypernet} (σ : H.Valuation)
    {w : Wire} {qw : QTensor} (h : σ.wireQ w = some qw) (i : ℕ) :
    σ.entryValC i w = qw.brReadC i := by
  unfold Hypernet.Valuation.entryValC
  rw [h]

theorem QTensor.map2_shape_inv {f : ℚ → ℚ → ℚ} {a b c : QTensor}
    (h : QTensor.map2 f a b = some c) :
    (a.shape = c.shape ∨ a.shape = []) ∧
      (b.shape = c.shape ∨ b.shape = []) := by
  unfold QTensor.map2 at h
  split at h
  · next hs =>
    injection h with h
    subst h
    exact ⟨Or.inl rfl, Or.inl hs.symm⟩
  · next hs =>
    split at h
    · next hsa =>
      injection h with h
      subst h
      exact ⟨Or.inr hsa, Or.inl rfl⟩
    · next hsa =>
      split at h
      · next hsb =>
        injection h with h
        subst h
        exact ⟨Or.inl rfl, Or.inr hsb⟩
      · cases h

theorem Term.evalQ_wires_shape {H : Hypernet} (σ : H.Valuation) :
    ∀ (t : Term) (q : QTensor), Term.evalQ σ t = some q →
    t.idxFree = true →
    ∀ w ∈ t.freeWires, ∀ qw, σ.wireQ w = some qw →
      qw.shape = [] ∨ qw.shape = q.shape := by
  intro t
  induction t with
  | var w =>
    intro q h _ w' hw' qw hqw
    simp only [Term.freeWires, List.mem_singleton] at hw'
    subst hw'
    have : σ.wireQ w' = some q := h
    rw [hqw] at this
    injection this with this
    rw [this]
    exact Or.inr rfl
  | const c =>
    intro q h _ w' hw'
    cases hw'
  | add l r ihl ihr =>
    intro q h hix w' hw' qw hqw
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    obtain ⟨a, b, ha, hb, hm⟩ := Term.evalQ_add_inv σ h
    obtain ⟨hsa, hsb⟩ := QTensor.map2_shape_inv hm
    rcases List.mem_append.mp hw' with h' | h'
    · rcases ihl a ha hix.1 w' h' qw hqw with h1 | h1
      · exact Or.inl h1
      · rcases hsa with h2 | h2
        · exact Or.inr (h1.trans h2)
        · exact Or.inl (h1.trans h2)
    · rcases ihr b hb hix.2 w' h' qw hqw with h1 | h1
      · exact Or.inl h1
      · rcases hsb with h2 | h2
        · exact Or.inr (h1.trans h2)
        · exact Or.inl (h1.trans h2)
  | mul l r ihl ihr =>
    intro q h hix w' hw' qw hqw
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    obtain ⟨a, b, ha, hb, hm⟩ := Term.evalQ_mul_inv σ h
    obtain ⟨hsa, hsb⟩ := QTensor.map2_shape_inv hm
    rcases List.mem_append.mp hw' with h' | h'
    · rcases ihl a ha hix.1 w' h' qw hqw with h1 | h1
      · exact Or.inl h1
      · rcases hsa with h2 | h2
        · exact Or.inr (h1.trans h2)
        · exact Or.inl (h1.trans h2)
    · rcases ihr b hb hix.2 w' h' qw hqw with h1 | h1
      · exact Or.inl h1
      · rcases hsb with h2 | h2
        · exact Or.inr (h1.trans h2)
        · exact Or.inl (h1.trans h2)
  | sub l r ihl ihr =>
    intro q h hix w' hw' qw hqw
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    obtain ⟨a, b, ha, hb, hm⟩ := Term.evalQ_sub_inv σ h
    obtain ⟨hsa, hsb⟩ := QTensor.map2_shape_inv hm
    rcases List.mem_append.mp hw' with h' | h'
    · rcases ihl a ha hix.1 w' h' qw hqw with h1 | h1
      · exact Or.inl h1
      · rcases hsa with h2 | h2
        · exact Or.inr (h1.trans h2)
        · exact Or.inl (h1.trans h2)
    · rcases ihr b hb hix.2 w' h' qw hqw with h1 | h1
      · exact Or.inl h1
      · rcases hsb with h2 | h2
        · exact Or.inr (h1.trans h2)
        · exact Or.inl (h1.trans h2)
  | neg t iht =>
    intro q h hix w' hw' qw hqw
    simp only [Term.evalQ, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, hqeq⟩ := h
    have hsh : a.shape = q.shape := by
      rw [← hqeq]
      rfl
    rcases iht a ha (by simpa [Term.idxFree] using hix) w'
        (by simpa [Term.freeWires] using hw') qw hqw with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (h1.trans hsh)
  | idx t i ih =>
    intro q h hix
    simp [Term.idxFree] at hix

theorem Term.evalQ_wires_defined {H : Hypernet} (σ : H.Valuation) :
    ∀ (t : Term) (q : QTensor), Term.evalQ σ t = some q →
    ∀ w ∈ t.freeWires, ∃ qw, σ.wireQ w = some qw := by
  intro t
  induction t with
  | var w =>
    intro q h w' hw'
    simp only [Term.freeWires, List.mem_singleton] at hw'
    subst hw'
    exact ⟨q, h⟩
  | const c =>
    intro q h w' hw'
    cases hw'
  | add l r ihl ihr =>
    intro q h w' hw'
    obtain ⟨a, b, ha, hb, _⟩ := Term.evalQ_add_inv σ h
    rcases List.mem_append.mp hw' with h' | h'
    · exact ihl a ha w' h'
    · exact ihr b hb w' h'
  | mul l r ihl ihr =>
    intro q h w' hw'
    obtain ⟨a, b, ha, hb, _⟩ := Term.evalQ_mul_inv σ h
    rcases List.mem_append.mp hw' with h' | h'
    · exact ihl a ha w' h'
    · exact ihr b hb w' h'
  | sub l r ihl ihr =>
    intro q h w' hw'
    obtain ⟨a, b, ha, hb, _⟩ := Term.evalQ_sub_inv σ h
    rcases List.mem_append.mp hw' with h' | h'
    · exact ihl a ha w' h'
    · exact ihr b hb w' h'
  | neg t iht =>
    intro q h w' hw'
    simp only [Term.evalQ, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, _⟩ := h
    exact iht a ha w' (by simpa [Term.freeWires] using hw')
  | idx t i ih =>
    intro q h w' hw'
    obtain ⟨a, e, ha, _, _, _⟩ := Term.evalQ_idx_inv σ h
    exact ih a ha w' (by simpa [Term.freeWires] using hw')

theorem Term.evalQ_nonnil_shape_wire {H : Hypernet} (σ : H.Valuation) :
    ∀ (t : Term) (q : QTensor), Term.evalQ σ t = some q →
    ¬ q.shape = [] →
    ∃ w ∈ t.freeWires, ∃ qw, σ.wireQ w = some qw ∧ qw.shape = q.shape := by
  intro t
  induction t with
  | var w =>
    intro q h hne
    exact ⟨w, by simp [Term.freeWires], q, h, rfl⟩
  | const c =>
    intro q h hne
    injection h with h
    subst h
    exact absurd rfl hne
  | add l r ihl ihr =>
    intro q h hne
    obtain ⟨a, b, ha, hb, hm⟩ := Term.evalQ_add_inv σ h
    obtain ⟨hsa, hsb⟩ := QTensor.map2_shape_inv hm
    rcases hsa with h1 | h1
    · by_cases hae : a.shape = []
      · rcases hsb with h2 | h2
        · obtain ⟨w, hw, qw, hqw, hqs⟩ := ihr b hb (fun hc => hne (h2 ▸ hc))
          exact ⟨w, by simp [Term.freeWires, hw], qw, hqw, hqs.trans h2⟩
        · exact absurd (h1.symm.trans hae) hne
      · obtain ⟨w, hw, qw, hqw, hqs⟩ := ihl a ha hae
        exact ⟨w, by simp [Term.freeWires, hw], qw, hqw, hqs.trans h1⟩
    · rcases hsb with h2 | h2
      · obtain ⟨w, hw, qw, hqw, hqs⟩ := ihr b hb (fun hc => hne (h2 ▸ hc))
        exact ⟨w, by simp [Term.freeWires, hw], qw, hqw, hqs.trans h2⟩
      ·
        exfalso
        obtain ⟨hj, _⟩ := QTensor.map2_shape_broadcast (s := []) hm
          (Or.inl h1) (Or.inl h2)
        rcases hj with hj | hj
        · exact hne hj
        · exact hne hj
  | mul l r ihl ihr =>
    intro q h hne
    obtain ⟨a, b, ha, hb, hm⟩ := Term.evalQ_mul_inv σ h
    obtain ⟨hsa, hsb⟩ := QTensor.map2_shape_inv hm
    rcases hsa with h1 | h1
    · by_cases hae : a.shape = []
      · rcases hsb with h2 | h2
        · obtain ⟨w, hw, qw, hqw, hqs⟩ := ihr b hb (fun hc => hne (h2 ▸ hc))
          exact ⟨w, by simp [Term.freeWires, hw], qw, hqw, hqs.trans h2⟩
        · exact absurd (h1.symm.trans hae) hne
      · obtain ⟨w, hw, qw, hqw, hqs⟩ := ihl a ha hae
        exact ⟨w, by simp [Term.freeWires, hw], qw, hqw, hqs.trans h1⟩
    · rcases hsb with h2 | h2
      · obtain ⟨w, hw, qw, hqw, hqs⟩ := ihr b hb (fun hc => hne (h2 ▸ hc))
        exact ⟨w, by simp [Term.freeWires, hw], qw, hqw, hqs.trans h2⟩
      · exfalso
        obtain ⟨hj, _⟩ := QTensor.map2_shape_broadcast (s := []) hm
          (Or.inl h1) (Or.inl h2)
        rcases hj with hj | hj
        · exact hne hj
        · exact hne hj
  | sub l r ihl ihr =>
    intro q h hne
    obtain ⟨a, b, ha, hb, hm⟩ := Term.evalQ_sub_inv σ h
    obtain ⟨hsa, hsb⟩ := QTensor.map2_shape_inv hm
    rcases hsa with h1 | h1
    · by_cases hae : a.shape = []
      · rcases hsb with h2 | h2
        · obtain ⟨w, hw, qw, hqw, hqs⟩ := ihr b hb (fun hc => hne (h2 ▸ hc))
          exact ⟨w, by simp [Term.freeWires, hw], qw, hqw, hqs.trans h2⟩
        · exact absurd (h1.symm.trans hae) hne
      · obtain ⟨w, hw, qw, hqw, hqs⟩ := ihl a ha hae
        exact ⟨w, by simp [Term.freeWires, hw], qw, hqw, hqs.trans h1⟩
    · rcases hsb with h2 | h2
      · obtain ⟨w, hw, qw, hqw, hqs⟩ := ihr b hb (fun hc => hne (h2 ▸ hc))
        exact ⟨w, by simp [Term.freeWires, hw], qw, hqw, hqs.trans h2⟩
      · exfalso
        obtain ⟨hj, _⟩ := QTensor.map2_shape_broadcast (s := []) hm
          (Or.inl h1) (Or.inl h2)
        rcases hj with hj | hj
        · exact hne hj
        · exact hne hj
  | neg t iht =>
    intro q h hne
    simp only [Term.evalQ, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, hqeq⟩ := h
    have hsh : a.shape = q.shape := by
      rw [← hqeq]
      rfl
    obtain ⟨w, hw, qw, hqw, hqs⟩ := iht a ha (fun hc => hne (hsh ▸ hc))
    exact ⟨w, by simpa [Term.freeWires] using hw, qw, hqw, hqs.trans hsh⟩
  | idx t i ih =>
    intro q h hne
    obtain ⟨a, e, ha, hae, hi, hq⟩ := Term.evalQ_idx_inv σ h
    exact absurd (by rw [hq]) hne

theorem Term.evalQ_brReadC {H : Hypernet} (σ : H.Valuation)
    {t : Term} {q : QTensor} (h : Term.evalQ σ t = some q)
    (hpos : ∀ w ∈ t.freeWires, ∀ qw, σ.wireQ w = some qw →
      0 < Shape.totalSize qw.shape)
    (hix : t.idxFree = true) (i : ℕ) :
    q.brReadC i = QArith.Poly.eval (σ.entryValC i) t.toPoly := by
  by_cases hq : q.shape = []
  ·
    have hwires := Term.evalQ_wires_shape σ t q h hix
    have hsing : ∀ w ∈ t.freeWires, ∀ qw, σ.wireQ w = some qw →
        SingletonShape qw.shape := by
      intro w hw qw hqw
      rcases hwires w hw qw hqw with h1 | h1
      · exact Or.inl h1
      · rw [hq] at h1
        exact Or.inl h1
    obtain ⟨hqs, hval⟩ := Term.evalQ_singleton σ t q h hsing hix
    rw [QTensor.brReadC_scalar hq, hval]
    apply Poly.eval_congr_keys
    intro tm htm ve hve
    have hkey : ve.1 ∈ t.freeWires := Term.toPoly_keys t tm htm ve hve
    obtain ⟨qw, hqw⟩ := Term.evalQ_wires_defined σ t q h ve.1 hkey
    rw [Hypernet.Valuation.entryValC_eq σ hqw,
      QTensor.brReadC_scalar (by
        rcases hwires ve.1 hkey qw hqw with h1 | h1
        · exact h1
        · rw [hq] at h1
          exact h1)]
    rw [Hypernet.Valuation.rho_eq σ hqw]
  ·

    obtain ⟨w₀, hw₀, qw₀, hqw₀, hqs₀⟩ := Term.evalQ_nonnil_shape_wire σ t q h hq
    have hposq : 0 < Shape.totalSize q.shape := by
      rw [← hqs₀]
      exact hpos w₀ hw₀ qw₀ hqw₀
    set j : ℕ := if i < Shape.totalSize q.shape then i else 0 with hjdef
    have hj : j < Shape.totalSize q.shape := by
      rw [hjdef]
      split
      · assumption
      · exact hposq
    have hwires := Term.evalQ_wires_shape σ t q h hix
    have hdisc : ∀ w ∈ t.freeWires, ∃ qw, σ.wireQ w = some qw ∧
        (qw.shape = [] ∨ qw.shape = q.shape) := by
      intro w hw
      obtain ⟨qw, hqw⟩ := Term.evalQ_wires_defined σ t q h w hw
      exact ⟨qw, hqw, hwires w hw qw hqw⟩
    obtain ⟨q', hq', hqj', _, hqe'⟩ := Term.evalQ_brRead σ q.shape t hdisc hix
    have hqq' : q' = q := by
      rw [h] at hq'
      injection hq' with hqq
      exact hqq.symm
    rw [hqq'] at hqe'
    have hmain := hqe' j hj

    have hagree : QArith.Poly.eval (σ.entryVal j) t.toPoly
        = QArith.Poly.eval (σ.entryValC i) t.toPoly := by
      apply Poly.eval_congr_keys
      intro tm htm ve hve
      have hkey : ve.1 ∈ t.freeWires := Term.toPoly_keys t tm htm ve hve
      obtain ⟨qw, hqw, hqwj⟩ := hdisc ve.1 hkey
      rw [Hypernet.Valuation.entryVal_eq σ hqw,
        Hypernet.Valuation.entryValC_eq σ hqw]
      rcases hqwj with h1 | h1
      · rw [QTensor.brRead_scalar h1, QTensor.brReadC_scalar h1]
      · rw [QTensor.brRead_pos (by rw [h1]; exact hq) j]
        unfold QTensor.brReadC
        rw [if_neg (by rw [h1]; exact hq)]
        congr 1
        rw [qw.len_eq, h1]
    rw [← hagree, ← hmain]

    unfold QTensor.brReadC
    rw [if_neg hq, QTensor.brRead_pos hq]
    congr 1
    rw [q.len_eq]

theorem QTensor.rel2_brReadC {r : ℚ → ℚ → Prop} {a b : QTensor}
    (h : QTensor.rel2 r a b) (hpa : 0 < a.entries.length)
    (hpb : 0 < b.entries.length) (i : ℕ) :
    r (a.brReadC i) (b.brReadC i) := by
  unfold QTensor.rel2 at h
  by_cases hs : a.shape = b.shape
  · rw [if_pos hs] at h
    have hlen : a.entries.length = b.entries.length := by
      rw [a.len_eq, b.len_eq, hs]
    by_cases hsa : a.shape = []
    · have hsb : b.shape = [] := hs ▸ hsa
      have hmem : (a.entries[0]'hpa, b.entries[0]'hpb)
          ∈ a.entries.zip b.entries := by
        apply List.mem_iff_getElem.mpr
        refine ⟨0, by rw [List.length_zip]; omega, ?_⟩
        rw [List.getElem_zip]
      rw [QTensor.brReadC_scalar hsa, QTensor.brReadC_scalar hsb]
      show r (a.entries.getD 0 0) (b.entries.getD 0 0)
      rw [List.getD_eq_getElem _ _ hpa, List.getD_eq_getElem _ _ hpb]
      exact h _ hmem
    · have hsb : ¬ b.shape = [] := by
        rw [← hs]
        exact hsa
      set j : ℕ := if i < a.entries.length then i else 0 with hjdef
      have hja : j < a.entries.length := by
        rw [hjdef]
        split
        · assumption
        · exact hpa
      have hjb : j < b.entries.length := by
        rw [← hlen]
        exact hja
      have hmem : (a.entries[j]'hja, b.entries[j]'hjb)
          ∈ a.entries.zip b.entries := by
        apply List.mem_iff_getElem.mpr
        refine ⟨j, by rw [List.length_zip]; omega, ?_⟩
        rw [List.getElem_zip]
      unfold QTensor.brReadC
      rw [if_neg hsa, if_neg hsb, ← hlen,
        show (if i < a.entries.length then i else 0) = j from hjdef.symm]
      rw [List.getD_eq_getElem _ _ hja, List.getD_eq_getElem _ _ hjb]
      exact h _ hmem
  · rw [if_neg hs] at h
    by_cases hsa : a.shape = []
    · rw [if_pos hsa] at h
      rw [QTensor.brReadC_scalar hsa]
      unfold QTensor.brReadC
      by_cases hsb : b.shape = []
      · rw [if_pos hsb]
        apply h
        show b.entries.getD 0 0 ∈ b.entries
        rw [List.getD_eq_getElem _ _ hpb]
        exact List.getElem_mem _
      · rw [if_neg hsb]
        apply h
        have hjb : (if i < b.entries.length then i else 0) < b.entries.length := by
          split
          · assumption
          · exact hpb
        rw [List.getD_eq_getElem _ _ hjb]
        exact List.getElem_mem _
    · rw [if_neg hsa] at h
      by_cases hsb : b.shape = []
      · rw [if_pos hsb] at h
        rw [QTensor.brReadC_scalar hsb]
        unfold QTensor.brReadC
        rw [if_neg hsa]
        apply h
        have hja : (if i < a.entries.length then i else 0) < a.entries.length := by
          split
          · assumption
          · exact hpa
        rw [List.getD_eq_getElem _ _ hja]
        exact List.getElem_mem _
      · rw [if_neg hsb] at h
        cases h

theorem bshape_join_cases {s₁ s₂ s : Shape}
    (h : (if s₁ = s₂ then some s₁ else if s₁ = [] then some s₂
          else if s₂ = [] then some s₁ else none) = some s) :
    (s₁ = s ∨ s₁ = []) ∧ (s₂ = s ∨ s₂ = []) := by
  split at h
  · next h12 =>
    injection h with h
    exact ⟨Or.inl h, Or.inl (h12.symm.trans h)⟩
  · next h12 =>
    split at h
    · next h1n =>
      injection h with h
      exact ⟨Or.inr h1n, Or.inl h⟩
    · next h1n =>
      split at h
      · next h2n =>
        injection h with h
        exact ⟨Or.inl h, Or.inr h2n⟩
      · next h2n => cases h

theorem Term.bshape_wires {H : Hypernet} :
    ∀ (t : Term) (s : Shape), t.bshape H = some s →
    t.idxFree = true →
    ∀ w ∈ t.freeWires, ∃ τ, H.wireType w = some τ ∧
      (τ.shape = [] ∨ τ.shape = s) := by
  intro t
  induction t with
  | var w =>
    intro s hb _ w' hw'
    simp only [Term.freeWires, List.mem_singleton] at hw'
    subst hw'
    simp only [Term.bshape, Option.map_eq_some_iff] at hb
    obtain ⟨τ, hτ, hs⟩ := hb
    exact ⟨τ, hτ, Or.inr hs⟩
  | const c =>
    intro s hb _ w' hw'
    cases hw'
  | add l r ihl ihr =>
    intro s hb hix w' hw'
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    simp only [Term.bshape] at hb
    cases hl : l.bshape H with
    | none => rw [hl] at hb; cases hb
    | some s₁ =>
      cases hr : r.bshape H with
      | none => rw [hl, hr] at hb; cases hb
      | some s₂ =>
        rw [hl, hr] at hb
        obtain ⟨hs₁, hs₂⟩ := bshape_join_cases hb
        rcases List.mem_append.mp hw' with h' | h'
        · obtain ⟨τ, hτ, hτs⟩ := ihl s₁ hl hix.1 w' h'
          refine ⟨τ, hτ, ?_⟩
          rcases hτs with h2 | h2
          · exact Or.inl h2
          · rcases hs₁ with h3 | h3
            · exact Or.inr (h2.trans h3)
            · exact Or.inl (h2.trans h3)
        · obtain ⟨τ, hτ, hτs⟩ := ihr s₂ hr hix.2 w' h'
          refine ⟨τ, hτ, ?_⟩
          rcases hτs with h2 | h2
          · exact Or.inl h2
          · rcases hs₂ with h3 | h3
            · exact Or.inr (h2.trans h3)
            · exact Or.inl (h2.trans h3)
  | mul l r ihl ihr =>
    intro s hb hix w' hw'
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    simp only [Term.bshape] at hb
    cases hl : l.bshape H with
    | none => rw [hl] at hb; cases hb
    | some s₁ =>
      cases hr : r.bshape H with
      | none => rw [hl, hr] at hb; cases hb
      | some s₂ =>
        rw [hl, hr] at hb
        obtain ⟨hs₁, hs₂⟩ := bshape_join_cases hb
        rcases List.mem_append.mp hw' with h' | h'
        · obtain ⟨τ, hτ, hτs⟩ := ihl s₁ hl hix.1 w' h'
          refine ⟨τ, hτ, ?_⟩
          rcases hτs with h2 | h2
          · exact Or.inl h2
          · rcases hs₁ with h3 | h3
            · exact Or.inr (h2.trans h3)
            · exact Or.inl (h2.trans h3)
        · obtain ⟨τ, hτ, hτs⟩ := ihr s₂ hr hix.2 w' h'
          refine ⟨τ, hτ, ?_⟩
          rcases hτs with h2 | h2
          · exact Or.inl h2
          · rcases hs₂ with h3 | h3
            · exact Or.inr (h2.trans h3)
            · exact Or.inl (h2.trans h3)
  | sub l r ihl ihr =>
    intro s hb hix w' hw'
    simp only [Term.idxFree, Bool.and_eq_true] at hix
    simp only [Term.bshape] at hb
    cases hl : l.bshape H with
    | none => rw [hl] at hb; cases hb
    | some s₁ =>
      cases hr : r.bshape H with
      | none => rw [hl, hr] at hb; cases hb
      | some s₂ =>
        rw [hl, hr] at hb
        obtain ⟨hs₁, hs₂⟩ := bshape_join_cases hb
        rcases List.mem_append.mp hw' with h' | h'
        · obtain ⟨τ, hτ, hτs⟩ := ihl s₁ hl hix.1 w' h'
          refine ⟨τ, hτ, ?_⟩
          rcases hτs with h2 | h2
          · exact Or.inl h2
          · rcases hs₁ with h3 | h3
            · exact Or.inr (h2.trans h3)
            · exact Or.inl (h2.trans h3)
        · obtain ⟨τ, hτ, hτs⟩ := ihr s₂ hr hix.2 w' h'
          refine ⟨τ, hτ, ?_⟩
          rcases hτs with h2 | h2
          · exact Or.inl h2
          · rcases hs₂ with h3 | h3
            · exact Or.inr (h2.trans h3)
            · exact Or.inl (h2.trans h3)
  | neg t iht =>
    intro s hb hix w' hw'
    exact iht s hb (by simpa [Term.idxFree] using hix) w'
      (by simpa [Term.freeWires] using hw')
  | idx t i ih =>
    intro s hb hix
    simp [Term.idxFree] at hix

theorem wire_discipline_of_bshape_fin {H : Hypernet} (σ : H.Valuation)
    {t : Term} {s : Shape} (hb : t.bshape H = some s)
    (hf : t.finWires H) (hix : t.idxFree = true) :
    ∀ w ∈ t.freeWires, ∃ qw, σ.wireQ w = some qw ∧
      (qw.shape = [] ∨ qw.shape = s) := by
  intro w hw
  obtain ⟨τ, hτ, hτs⟩ := Term.bshape_wires t s hb hix w hw
  obtain ⟨τ', hτ', hext⟩ := hf w hw
  rw [hτ] at hτ'
  injection hτ' with hττ
  obtain ⟨qw, hqw⟩ := σ.wireQ_isSome hτ (by rw [hττ]; exact hext)
  obtain ⟨τ₂, hτ₂, hqs⟩ := σ.wireQ_shape hqw
  rw [hτ] at hτ₂
  injection hτ₂ with hττ₂
  refine ⟨qw, hqw, ?_⟩
  rw [hqs, ← hττ₂]
  exact hτs

theorem QTensor.map2_const_left {f : ℚ → ℚ → ℚ} {x : ℚ} {b : QTensor} :
    ∃ c, QTensor.map2 f ⟨[], [x], rfl⟩ b = some c ∧ c.shape = b.shape ∧
      c.entries = b.entries.map (f x) := by
  unfold QTensor.map2
  by_cases hs : (⟨[], [x], rfl⟩ : QTensor).shape = b.shape
  · refine ⟨_, dif_pos hs, hs, ?_⟩
    have hbe := QTensor.entries_singleton (q := b) (Or.inl hs.symm)
    show List.zipWith f [x] b.entries = _
    rw [hbe]
    rfl
  · rw [dif_neg hs, if_pos rfl]
    exact ⟨_, rfl, rfl, rfl⟩

theorem QTensor.map2_const_right {f : ℚ → ℚ → ℚ} {x : ℚ} {a : QTensor} :
    ∃ c, QTensor.map2 f a ⟨[], [x], rfl⟩ = some c ∧ c.shape = a.shape ∧
      c.entries = a.entries.map (f · x) := by
  unfold QTensor.map2
  by_cases hs : a.shape = (⟨[], [x], rfl⟩ : QTensor).shape
  · refine ⟨_, dif_pos hs, rfl, ?_⟩
    have hae := QTensor.entries_singleton (q := a) (Or.inl hs)
    show a.entries.zipWith f [x] = _
    rw [hae]
    rfl
  · rw [dif_neg hs, if_neg hs, if_pos rfl]
    exact ⟨_, rfl, rfl, rfl⟩

theorem parseHoleSide_subst_evalQ_entries {H : Hypernet} (σ : H.Valuation)
    {t : Term} {sc : ℚ} (h : parseHoleSide t = some sc)
    {arg : Term} {qa : QTensor} (ha : Term.evalQ σ arg = some qa) :
    ∃ q, Term.evalQ σ (Term.subst predicateHole arg t) = some q ∧
      q.shape = qa.shape ∧ q.entries = qa.entries.map (sc * ·) := by
  unfold parseHoleSide at h
  split at h
  · next w =>
    split at h
    · next hw =>
      injection h with h
      subst hw
      refine ⟨qa, ?_, rfl, ?_⟩
      · simpa [Term.subst] using ha
      · rw [← h]
        simp
    · cases h
  · next a w =>
    split at h
    · next hcond =>
      injection h with h
      obtain ⟨c, hc, hcs, hce⟩ :=
        QTensor.map2_const_left (f := (· * ·)) (x := a) (b := qa)
      refine ⟨c, ?_, hcs, ?_⟩
      · have hsubst : Term.subst predicateHole arg (.mul (.const a) (.var w))
            = .mul (.const a) arg := by
          simp [Term.subst, hcond.1]
        rw [hsubst]
        simp only [Term.evalQ, Option.bind_eq_bind, ha, Option.bind_some]
        exact hc
      · rw [hce, ← h]
    · cases h
  · next w a =>
    split at h
    · next hcond =>
      injection h with h
      obtain ⟨c, hc, hcs, hce⟩ :=
        QTensor.map2_const_right (f := (· * ·)) (x := a) (a := qa)
      refine ⟨c, ?_, hcs, ?_⟩
      · have hsubst : Term.subst predicateHole arg (.mul (.var w) (.const a))
            = .mul arg (.const a) := by
          simp [Term.subst, hcond.1]
        rw [hsubst]
        simp only [Term.evalQ, Option.bind_eq_bind, ha, Option.bind_some]
        exact hc
      · rw [hce, ← h]
        apply List.map_congr_left
        intro e _
        rw [mul_comm]
    · cases h
  · cases h

theorem QTensor.rel2_const_right {r : ℚ → ℚ → Prop} {a : QTensor} {c : ℚ}
    (h : ∀ x ∈ a.entries, r x c) :
    QTensor.rel2 r a ⟨[], [c], rfl⟩ := by
  unfold QTensor.rel2
  by_cases hs : a.shape = (⟨[], [c], rfl⟩ : QTensor).shape
  · rw [if_pos hs]
    have hae := QTensor.entries_singleton (q := a) (Or.inl hs)
    rw [hae]
    intro p hp
    show r p.1 p.2
    have : p = (a.scalar, c) := by
      simpa [List.zip] using hp
    rw [this]
    exact h a.scalar (by rw [hae]; simp)
  · rw [if_neg hs, if_neg hs, if_pos rfl]
    exact h

theorem QTensor.rel2_const_left {r : ℚ → ℚ → Prop} {b : QTensor} {c : ℚ}
    (h : ∀ x ∈ b.entries, r c x) :
    QTensor.rel2 r (⟨[], [c], rfl⟩ : QTensor) b := by
  unfold QTensor.rel2
  by_cases hs : (⟨[], [c], rfl⟩ : QTensor).shape = b.shape
  · rw [if_pos hs]
    have hbe := QTensor.entries_singleton (q := b) (Or.inl hs.symm)
    rw [hbe]
    intro p hp
    show r p.1 p.2
    have : p = (c, b.scalar) := by
      simpa [List.zip] using hp
    rw [this]
    exact h b.scalar (by rw [hbe]; simp)
  · rw [if_neg hs, if_pos rfl]
    exact h

theorem BowTie.holdsQ_iff_evalQ (b : BowTie) (x y : ℚ) :
    b.holdsQ x y ↔ b.evalQ x y = true := by
  cases b <;> simp [BowTie.holdsQ, BowTie.evalQ]

theorem BowTie.holdsQ_sub_zero (b : BowTie) (x y : ℚ) :
    b.holdsQ (x - y) 0 ↔ b.holdsQ x y := by
  cases b
  · exact sub_neg
  · exact sub_nonpos
  · exact sub_eq_zero
  · show (0 : ℚ) ≤ x - y ↔ y ≤ x
    exact sub_nonneg
  · show (0 : ℚ) < x - y ↔ y < x
    exact sub_pos
  · exact sub_ne_zero

theorem List.eq_of_zip_pointwise {α : Type} :
    ∀ {l₁ l₂ : List α}, l₁.length = l₂.length →
    (∀ p ∈ l₁.zip l₂, p.1 = p.2) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ hlen _
    cases l₂ with
    | nil => rfl
    | cons b tl => simp at hlen
  | cons a tl ih =>
    intro l₂ hlen h
    cases l₂ with
    | nil => simp at hlen
    | cons b tl₂ =>
      have h1 : a = b := h (a, b) (by simp)
      have h2 : tl = tl₂ := ih (by simpa using hlen)
        (fun p hp => h p (by simp [hp]))
      rw [h1, h2]

theorem QTensor.eq_of_rel2 {r : ℚ → ℚ → Prop} {a b : QTensor}
    (hr : ∀ x y, r x y → x = y) (hs : a.shape = b.shape)
    (h : QTensor.rel2 r a b) : a = b := by
  unfold QTensor.rel2 at h
  rw [if_pos hs] at h
  refine QTensor.ext' hs (List.eq_of_zip_pointwise ?_ (fun p hp => hr p.1 p.2 (h p hp)))
  rw [a.len_eq, b.len_eq, hs]

theorem List.forall_zipWith_iff {α β γ : Type} {f : α → β → γ} {P : γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List β},
    ((∀ x ∈ List.zipWith f l₁ l₂, P x) ↔ (∀ p ∈ l₁.zip l₂, P (f p.1 p.2))) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; simp
  | cons a tl ih =>
    intro l₂
    cases l₂ with
    | nil => simp
    | cons b tl₂ =>
      simp only [List.zipWith_cons_cons, List.zip_cons_cons, List.mem_cons,
        forall_eq_or_imp]
      exact and_congr Iff.rfl ih

theorem QTensor.rel2_zero_right {r : ℚ → ℚ → Prop} {d : QTensor} :
    QTensor.rel2 r d ⟨[], [0], rfl⟩ ↔ ∀ x ∈ d.entries, r x 0 := by
  unfold QTensor.rel2
  by_cases hd : d.shape = []
  · rw [if_pos hd]
    have hde : d.entries = [d.scalar] := QTensor.entries_singleton (Or.inl hd)
    rw [hde]
    show (∀ p ∈ [d.scalar].zip [(0:ℚ)], r p.1 p.2) ↔ ∀ x ∈ [d.scalar], r x 0
    simp [List.zip_cons_cons]
  · rw [if_neg hd, if_neg hd, if_pos rfl]
    exact Iff.rfl

theorem QTensor.rel2_sub_zero_iff {b : BowTie} {al ar d : QTensor}
    (hd : QTensor.map2 (· - ·) al ar = some d) :
    QTensor.rel2 (BowTie.holdsQ b) d ⟨[], [0], rfl⟩
      ↔ QTensor.rel2 (BowTie.holdsQ b) al ar := by
  rw [QTensor.rel2_zero_right]
  unfold QTensor.map2 at hd
  split at hd
  · next hs =>

    injection hd with hd
    subst hd
    show (∀ x ∈ List.zipWith (· - ·) al.entries ar.entries, BowTie.holdsQ b x 0) ↔ _
    unfold QTensor.rel2
    rw [if_pos hs, List.forall_zipWith_iff]
    exact forall₂_congr (fun p _ => BowTie.holdsQ_sub_zero b p.1 p.2)
  · next hs =>
    split at hd
    · next hsa =>

      injection hd with hd
      subst hd
      show (∀ x ∈ ar.entries.map (al.scalar - ·), BowTie.holdsQ b x 0) ↔ _
      unfold QTensor.rel2
      rw [if_neg hs, if_pos hsa]
      simp only [List.mem_map, forall_exists_index, and_imp]
      constructor
      · intro h y hy
        exact (BowTie.holdsQ_sub_zero b _ _).mp (h _ y hy rfl)
      · intro h x y hy hxy
        subst hxy
        exact (BowTie.holdsQ_sub_zero b _ _).mpr (h y hy)
    · next hsa =>
      split at hd
      · next hsb =>

        injection hd with hd
        subst hd
        show (∀ x ∈ al.entries.map (· - ar.scalar), BowTie.holdsQ b x 0) ↔ _
        unfold QTensor.rel2
        rw [if_neg hs, if_neg hsa, if_pos hsb]
        simp only [List.mem_map, forall_exists_index, and_imp]
        constructor
        · intro h x hx
          exact (BowTie.holdsQ_sub_zero b _ _).mp (h _ x hx rfl)
        · intro h x y hy hxy
          subst hxy
          exact (BowTie.holdsQ_sub_zero b _ _).mpr (h y hy)
      · cases hd

theorem mask_true_of_filter_pair {n : Nat} {mask : Fin n → Bool} {a b : Fin n}
    (hfil : (List.finRange n).filter (fun v => mask v) = [a, b]) :
    mask a = true ∧ mask b = true := by
  constructor
  · have ha : a ∈ (List.finRange n).filter (fun v => mask v) := by
      rw [hfil]; simp
    simpa using (List.mem_filter.mp ha).2
  · have hb : b ∈ (List.finRange n).filter (fun v => mask v) := by
      rw [hfil]; simp
    simpa using (List.mem_filter.mp hb).2

theorem maskRegion_pair_elim {C : SimpC} {mask ext : Fin C.nVertices → Bool}
    {x : Fin C.ambDim → ℚ} {a b : Fin C.nVertices} {V₀ V₁ : ℚ}
    (hfil : (List.finRange C.nVertices).filter (fun v => mask v) = [a, b])
    (hVa : ∀ j, C.coord a j = V₀) (hVb : ∀ j, C.coord b j = V₁)
    (hne : V₀ ≠ V₁) (j0 : Fin C.ambDim)
    (h : MaskRegion C mask ext x) :
    (ext a = true → (V₁ - x j0) / (V₁ - V₀) ≤ 0) ∧
    (ext a = false → 0 ≤ (V₁ - x j0) / (V₁ - V₀)) ∧
    (ext b = true → (x j0 - V₀) / (V₁ - V₀) ≤ 0) ∧
    (ext b = false → 0 ≤ (x j0 - V₀) / (V₁ - V₀)) := by
  obtain ⟨lam, hsupp, hsum, hcoord, hext, hcore⟩ := h
  obtain ⟨hma, hmb⟩ := mask_true_of_filter_pair hfil
  have h1 : lam a + lam b = 1 := by
    rw [← finSum_support_pair mask lam a b hfil hsupp]
    exact hsum
  have h2 : lam a * (V₀ : ℝ) + lam b * (V₁ : ℝ) = (x j0 : ℝ) := by
    have hc := hcoord j0
    rw [finSum_support_pair mask _ a b hfil
      (fun v hv => by rw [hsupp v hv]; ring)] at hc
    rw [hVa j0, hVb j0] at hc
    exact hc
  have hdenR : (V₁ : ℝ) - (V₀ : ℝ) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hne.symm
  have hb' : lam b = 1 - lam a := by linarith
  rw [hb'] at h2
  have hla : lam a = (((V₁ - x j0) / (V₁ - V₀) : ℚ) : ℝ) := by
    push_cast
    rw [eq_div_iff hdenR]
    linarith [h2]
  have hlb : lam b = (((x j0 - V₀) / (V₁ - V₀) : ℚ) : ℝ) := by
    rw [hb']
    push_cast
    rw [sub_eq_iff_eq_add, div_add' _ _ _ hdenR, eq_div_iff hdenR]
    linarith [h2]
  refine ⟨fun hea => ?_, fun hea => ?_, fun heb => ?_, fun heb => ?_⟩
  · have := hext a hea
    rw [hla] at this
    exact_mod_cast this
  · have := hcore a hma hea
    rw [hla] at this
    exact_mod_cast this
  · have := hext b heb
    rw [hlb] at this
    exact_mod_cast this
  · have := hcore b hmb heb
    rw [hlb] at this
    exact_mod_cast this

theorem maskRegion_pair_intro {C : SimpC} {mask ext : Fin C.nVertices → Bool}
    {x : Fin C.ambDim → ℚ} {a b : Fin C.nVertices} {V₀ V₁ : ℚ}
    (hfil : (List.finRange C.nVertices).filter (fun v => mask v) = [a, b])
    (hVa : ∀ j, C.coord a j = V₀) (hVb : ∀ j, C.coord b j = V₁)
    (hne : V₀ ≠ V₁) (hdim : C.ambDim = 1) (j0 : Fin C.ambDim)
    (hw0t : ext a = true → (V₁ - x j0) / (V₁ - V₀) ≤ 0)
    (hw0f : ext a = false → 0 ≤ (V₁ - x j0) / (V₁ - V₀))
    (hw1t : ext b = true → (x j0 - V₀) / (V₁ - V₀) ≤ 0)
    (hw1f : ext b = false → 0 ≤ (x j0 - V₀) / (V₁ - V₀)) :
    MaskRegion C mask ext x := by
  have hab : a ≠ b := fun hc => hne (by rw [← hVa j0, ← hVb j0, hc])
  obtain ⟨hma, hmb⟩ := mask_true_of_filter_pair hfil
  have hden : (V₁ : ℚ) - V₀ ≠ 0 := sub_ne_zero.mpr hne.symm
  set lam : Fin C.nVertices → ℝ := fun v =>
    if v = a then (((V₁ - x j0) / (V₁ - V₀) : ℚ) : ℝ)
    else if v = b then (((x j0 - V₀) / (V₁ - V₀) : ℚ) : ℝ) else 0 with hlam
  have hzero : ∀ v, mask v = false → lam v = 0 := by
    intro v hv
    rw [hlam]
    simp only []
    rw [if_neg (fun hc => by subst hc; rw [hma] at hv; cases hv),
        if_neg (fun hc => by subst hc; rw [hmb] at hv; cases hv)]
  have hdenR : (V₁ : ℝ) - (V₀ : ℝ) ≠ 0 := by exact_mod_cast hden
  refine ⟨lam, hzero, ?_, ?_, ?_, ?_⟩
  ·
    rw [finSum_support_pair mask lam a b hfil hzero, hlam]
    simp only [if_pos rfl, if_neg (Ne.symm hab)]
    push_cast
    field_simp
    ring
  ·
    intro j
    have hj : j = j0 := by
      apply Fin.ext
      have h1 := j.isLt
      have h2 := j0.isLt
      omega
    subst hj
    rw [finSum_support_pair mask _ a b hfil
      (fun v hv => by rw [hzero v hv]; ring)]
    rw [hlam]
    simp only [if_pos rfl, if_neg (Ne.symm hab)]
    rw [hVa j, hVb j]
    push_cast
    field_simp
    ring
  ·
    intro v hv
    rw [hlam]
    simp only []
    by_cases hva : v = a
    · subst hva
      rw [if_pos rfl]
      exact_mod_cast hw0t hv
    · by_cases hvb : v = b
      · subst hvb
        rw [if_neg hva, if_pos rfl]
        exact_mod_cast hw1t hv
      · rw [if_neg hva, if_neg hvb]
  ·
    intro v hmv hv
    rw [hlam]
    simp only []
    by_cases hva : v = a
    · subst hva
      rw [if_pos rfl]
      exact_mod_cast hw0f hv
    · by_cases hvb : v = b
      · subst hvb
        rw [if_neg hva, if_pos rfl]
        exact_mod_cast hw1f hv
      · rw [if_neg hva, if_neg hvb]

theorem parseHoleSide_subst_evalQ? {t : Term} {s : ℚ}
    (h : parseHoleSide t = some s) (v : ℚ) :
    (Term.subst predicateHole (.const v) t).evalQ? = some (s * v) := by
  unfold parseHoleSide at h
  split at h
  · next w =>
    split at h
    · next hw =>
      injection h with h
      subst hw
      rw [← h, one_mul]
      simp [Term.subst, Term.evalQ?]
    · cases h
  · next a w =>
    split at h
    · next hcond =>
      injection h with h
      rw [← h]
      simp [Term.subst, hcond.1, Term.evalQ?]
    · cases h
  · next w a =>
    split at h
    · next hcond =>
      injection h with h
      rw [← h]
      simp [Term.subst, hcond.1, Term.evalQ?, mul_comm]
    · cases h
  · cases h

theorem parseHoleSide_subst_evalQ {H : Hypernet} (σ : H.Valuation)
    {t : Term} {s : ℚ} (h : parseHoleSide t = some s)
    {arg : Term} {qa : QTensor}
    (ha : Term.evalQ σ arg = some qa) (hsa : SingletonShape qa.shape) :
    ∃ q, Term.evalQ σ (Term.subst predicateHole arg t) = some q ∧
      SingletonShape q.shape ∧ q.scalar = s * qa.scalar := by
  unfold parseHoleSide at h
  split at h
  · next w =>
    split at h
    · next hw =>
      injection h with h
      subst hw
      rw [← h]
      refine ⟨qa, ?_, hsa, (one_mul _).symm⟩
      simpa [Term.subst] using ha
    · cases h
  · next a w =>
    split at h
    · next hcond =>
      injection h with h
      rw [← h]
      obtain ⟨q, hq, hsq, hvq⟩ :=
        QTensor.map2_singleton (f := (· * ·)) (a := (⟨[], [a], rfl⟩ : QTensor))
          (b := qa) (Or.inl rfl) hsa
      refine ⟨q, ?_, hsq, by rw [hvq]; rfl⟩
      have hsubst : Term.subst predicateHole arg (.mul (.const a) (.var w))
          = .mul (.const a) arg := by
        simp [Term.subst, hcond.1]
      rw [hsubst]
      simp only [Term.evalQ, Option.bind_eq_bind, ha, Option.bind_some]
      exact hq
    · cases h
  · next w a =>
    split at h
    · next hcond =>
      injection h with h
      rw [← h]
      obtain ⟨q, hq, hsq, hvq⟩ :=
        QTensor.map2_singleton (f := (· * ·)) (a := qa)
          (b := (⟨[], [a], rfl⟩ : QTensor)) hsa (Or.inl rfl)
      refine ⟨q, ?_, hsq, by rw [hvq, mul_comm]; rfl⟩
      have hsubst : Term.subst predicateHole arg (.mul (.var w) (.const a))
          = .mul arg (.const a) := by
        simp [Term.subst, hcond.1]
      rw [hsubst]
      simp only [Term.evalQ, Option.bind_eq_bind, ha, Option.bind_some]
      exact hq
    · cases h
  · cases h

theorem Formula.holds_of_evalClosed_true {H : Hypernet} (σ : H.Valuation) :
    ∀ (F : Formula), F.evalClosed = some true → F.holds σ := by
  intro F
  induction F with
  | atom b l r =>
    intro h
    simp only [Formula.evalClosed, Option.bind_eq_bind] at h
    obtain ⟨cl, hcl, h⟩ := option_bind_eq_some' h
    obtain ⟨cr, hcr, h⟩ := option_bind_eq_some' h
    injection h with h
    refine ⟨⟨[], [cl], rfl⟩, ⟨[], [cr], rfl⟩,
      Term.evalQ_of_closed σ l cl hcl, Term.evalQ_of_closed σ r cr hcr, ?_⟩
    rw [QTensor.rel2_singleton (Or.inl rfl) (Or.inl rfl)]
    exact (BowTie.holdsQ_iff_evalQ b cl cr).mpr h
  | inRegion t simplex S => intro h; cases h
  | and l r ihl ihr =>
    intro h
    simp only [Formula.evalClosed, Option.bind_eq_bind] at h
    obtain ⟨bl, hbl, h⟩ := option_bind_eq_some' h
    obtain ⟨br, hbr, h⟩ := option_bind_eq_some' h
    injection h with h
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    exact ⟨ihl hbl, ihr hbr⟩
  | or l r ihl ihr =>
    intro h
    simp only [Formula.evalClosed, Option.bind_eq_bind] at h
    obtain ⟨bl, hbl, h⟩ := option_bind_eq_some' h
    obtain ⟨br, hbr, h⟩ := option_bind_eq_some' h
    injection h with h
    rw [Bool.or_eq_true] at h
    rcases h with h1 | h1
    · subst h1
      exact Or.inl (ihl hbl)
    · subst h1
      exact Or.inr (ihr hbr)
  | tt => intro _; trivial
  | ff => intro h; injection h with h; cases h

theorem satisfiesPredQ_and {P₁ P₂ : Formula} {c : ℚ} :
    satisfiesPredQ (.and P₁ P₂) c = true ↔
      satisfiesPredQ P₁ c = true ∧ satisfiesPredQ P₂ c = true := by
  unfold satisfiesPredQ
  simp only [decide_eq_true_eq, Formula.subst, Formula.evalClosed,
    Option.bind_eq_bind]
  constructor
  · intro h
    obtain ⟨b₁, hb₁, h⟩ := option_bind_eq_some' h
    obtain ⟨b₂, hb₂, h⟩ := option_bind_eq_some' h
    injection h with h
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    exact ⟨hb₁, hb₂⟩
  · intro ⟨h1, h2⟩
    rw [h1, h2]
    rfl

theorem satisfiesPredQ_orient1_iff {b : BowTie} {tl tr : Term} {s c : ℚ}
    (hpl : parseHoleSide tl = some s) (hre : tr.evalQ? = some c) (v : ℚ) :
    (satisfiesPredQ (.atom b tl tr) v = true) ↔ b.holdsQ (s * v) c := by
  unfold satisfiesPredQ
  have h2 : (Term.subst predicateHole (Term.const v) tr).evalQ? = some c := by
    rw [Term.subst_of_closed tr c hre]
    exact hre
  simp only [decide_eq_true_eq, Formula.subst, Formula.evalClosed,
    Option.bind_eq_bind, parseHoleSide_subst_evalQ? hpl v, h2, Option.bind_some]
  constructor
  · intro hh
    injection hh with hh
    exact (BowTie.holdsQ_iff_evalQ _ _ _).mpr hh
  · intro hh
    rw [show (pure (b.evalQ (s * v) c) : Option Bool)
      = some (b.evalQ (s * v) c) from rfl,
      (BowTie.holdsQ_iff_evalQ _ _ _).mp hh]

theorem satisfiesPredQ_orient2_iff {b : BowTie} {tl tr : Term} {s c : ℚ}
    (hpr : parseHoleSide tr = some s) (hle : tl.evalQ? = some c) (v : ℚ) :
    (satisfiesPredQ (.atom b tl tr) v = true) ↔ b.holdsQ c (s * v) := by
  unfold satisfiesPredQ
  have h2 : (Term.subst predicateHole (Term.const v) tl).evalQ? = some c := by
    rw [Term.subst_of_closed tl c hle]
    exact hle
  simp only [decide_eq_true_eq, Formula.subst, Formula.evalClosed,
    Option.bind_eq_bind, parseHoleSide_subst_evalQ? hpr v, h2, Option.bind_some]
  constructor
  · intro hh
    injection hh with hh
    exact (BowTie.holdsQ_iff_evalQ _ _ _).mpr hh
  · intro hh
    rw [show (pure (b.evalQ c (s * v)) : Option Bool)
      = some (b.evalQ c (s * v)) from rfl,
      (BowTie.holdsQ_iff_evalQ _ _ _).mp hh]

theorem holdsQ_convex_left {b : BowTie} (hb : b = .le ∨ b = .ge ∨ b = .eq)
    {s c a₁ b₁ l : ℚ} (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (h₁ : b.holdsQ (s * a₁) c) (h₂ : b.holdsQ (s * b₁) c) :
    b.holdsQ (s * (l * a₁ + (1 - l) * b₁)) c := by
  have e1 : l * (s * a₁) + (1 - l) * (s * b₁) = s * (l * a₁ + (1 - l) * b₁) := by
    ring
  rcases hb with hb | hb | hb <;> subst hb
  · show s * (l * a₁ + (1 - l) * b₁) ≤ c
    have k1 : l * (s * a₁) ≤ l * c := mul_le_mul_of_nonneg_left h₁ hl
    have k2 : (1 - l) * (s * b₁) ≤ (1 - l) * c :=
      mul_le_mul_of_nonneg_left h₂ (by linarith)
    nlinarith [k1, k2]
  · show c ≤ s * (l * a₁ + (1 - l) * b₁)
    have k1 : l * c ≤ l * (s * a₁) := mul_le_mul_of_nonneg_left h₁ hl
    have k2 : (1 - l) * c ≤ (1 - l) * (s * b₁) :=
      mul_le_mul_of_nonneg_left h₂ (by linarith)
    nlinarith [k1, k2]
  · show s * (l * a₁ + (1 - l) * b₁) = c
    have h₁' : s * a₁ = c := h₁
    have h₂' : s * b₁ = c := h₂
    rw [← e1, h₁', h₂']
    ring

theorem holdsQ_convex_right {b : BowTie} (hb : b = .le ∨ b = .ge ∨ b = .eq)
    {s c a₁ b₁ l : ℚ} (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (h₁ : b.holdsQ c (s * a₁)) (h₂ : b.holdsQ c (s * b₁)) :
    b.holdsQ c (s * (l * a₁ + (1 - l) * b₁)) := by
  rcases hb with hb | hb | hb <;> subst hb
  · show c ≤ s * (l * a₁ + (1 - l) * b₁)
    have k1 : l * c ≤ l * (s * a₁) := mul_le_mul_of_nonneg_left h₁ hl
    have k2 : (1 - l) * c ≤ (1 - l) * (s * b₁) :=
      mul_le_mul_of_nonneg_left h₂ (by linarith)
    nlinarith [k1, k2]
  · show s * (l * a₁ + (1 - l) * b₁) ≤ c
    have k1 : l * (s * a₁) ≤ l * c := mul_le_mul_of_nonneg_left h₁ hl
    have k2 : (1 - l) * (s * b₁) ≤ (1 - l) * c :=
      mul_le_mul_of_nonneg_left h₂ (by linarith)
    nlinarith [k1, k2]
  · show c = s * (l * a₁ + (1 - l) * b₁)
    have h₁' : c = s * a₁ := h₁
    have h₂' : c = s * b₁ := h₂
    have : l * (s * a₁) + (1 - l) * (s * b₁) = s * (l * a₁ + (1 - l) * b₁) := by
      ring
    rw [← this, ← h₁', ← h₂']
    ring

theorem satisfiesPredQ_convex {P : Formula} {cls : PredClass}
    (hP : classifyPred P = some cls) :
    ∀ a₁ b₁ l : ℚ, 0 ≤ l → l ≤ 1 →
      satisfiesPredQ P a₁ = true → satisfiesPredQ P b₁ = true →
      satisfiesPredQ P (l * a₁ + (1 - l) * b₁) = true := by
  induction P generalizing cls with
  | and P₁ P₂ ih₁ ih₂ =>
    intro a₁ b₁ l hl hl1 ha hb
    simp only [classifyPred, Option.bind_eq_bind] at hP
    obtain ⟨c₁, hc₁, hP⟩ := option_bind_eq_some' hP
    obtain ⟨c₂, hc₂, hP⟩ := option_bind_eq_some' hP
    obtain ⟨ha₁, ha₂⟩ := satisfiesPredQ_and.mp ha
    obtain ⟨hb₁, hb₂⟩ := satisfiesPredQ_and.mp hb
    exact satisfiesPredQ_and.mpr
      ⟨ih₁ hc₁ a₁ b₁ l hl hl1 ha₁ hb₁, ih₂ hc₂ a₁ b₁ l hl hl1 ha₂ hb₂⟩
  | atom b tl tr =>
    intro a₁ b₁ l hl hl1 ha hb
    have hP' : classifyPredAtom (.atom b tl tr) = some cls := hP
    simp only [classifyPredAtom] at hP'
    cases hpl : parseHoleSide tl with
    | some s =>
      cases hre : tr.evalQ? with
      | some c =>

        rw [hpl, hre] at hP'
        simp only [] at hP'
        rw [satisfiesPredQ_orient1_iff hpl hre] at ha hb ⊢
        cases b
        · cases hP'
        · exact holdsQ_convex_left (Or.inl rfl) hl hl1 ha hb
        · exact holdsQ_convex_left (Or.inr (Or.inr rfl)) hl hl1 ha hb
        · exact holdsQ_convex_left (Or.inr (Or.inl rfl)) hl hl1 ha hb
        · cases hP'
        · cases hP'
      | none =>
        rw [hpl, hre] at hP'
        cases hpr : parseHoleSide tr with
        | some s' =>
          cases hle : tl.evalQ? with
          | some c' =>
            rw [hpr, hle] at hP'
            simp only [] at hP'
            rw [satisfiesPredQ_orient2_iff hpr hle] at ha hb ⊢
            cases b
            · cases hP'
            · exact holdsQ_convex_right (Or.inl rfl) hl hl1 ha hb
            · exact holdsQ_convex_right (Or.inr (Or.inr rfl)) hl hl1 ha hb
            · exact holdsQ_convex_right (Or.inr (Or.inl rfl)) hl hl1 ha hb
            · cases hP'
            · cases hP'
          | none =>
            rw [hpr, hle] at hP'
            cases hP'
        | none =>
          rw [hpr] at hP'
          cases hle : tl.evalQ? <;> rw [hle] at hP' <;> cases hP'
    | none =>
      rw [hpl] at hP'
      cases hpr : parseHoleSide tr with
      | some s' =>
        cases hle : tl.evalQ? with
        | some c' =>
          rw [hpr, hle] at hP'
          simp only [] at hP'
          rw [satisfiesPredQ_orient2_iff hpr hle] at ha hb ⊢
          cases b
          · cases hP'
          · exact holdsQ_convex_right (Or.inl rfl) hl hl1 ha hb
          · exact holdsQ_convex_right (Or.inr (Or.inr rfl)) hl hl1 ha hb
          · exact holdsQ_convex_right (Or.inr (Or.inl rfl)) hl hl1 ha hb
          · cases hP'
          · cases hP'
        | none =>
          rw [hpr, hle] at hP'
          cases hP'
      | none =>
        rw [hpr] at hP'
        cases hle : tl.evalQ? <;> rw [hle] at hP' <;> cases hP'
  | inRegion t simplex S => intro _ _ _ _ _ _ _; cases hP
  | or P₁ P₂ _ _ => intro _ _ _ _ _ _ _; cases hP
  | tt => intro _ _ _ _ _ _ _; cases hP
  | ff => intro _ _ _ _ _ _ _; cases hP

theorem classifyPredAtom_conic_shape {b : BowTie} {tl tr : Term}
    {cls : PredClass}
    (hP : classifyPredAtom (.atom b tl tr) = some cls)
    (hc : cls.conic = true) :
    (∃ s, parseHoleSide tl = some s ∧ tr.evalQ? = some 0 ∧
      (b = .le ∨ b = .ge ∨ b = .eq)) ∨
    (∃ s, parseHoleSide tr = some s ∧ tl.evalQ? = some 0 ∧
      (b = .le ∨ b = .ge ∨ b = .eq)) := by
  cases hpl : parseHoleSide tl with
  | some s =>
    cases hre : tr.evalQ? with
    | some c =>
      cases b <;>
        simp only [classifyPredAtom, hpl, hre] at hP
      case le =>
        injection hP with hP
        rw [← hP] at hc
        have hc0 : c = 0 := of_decide_eq_true hc
        subst hc0
        exact Or.inl ⟨s, rfl, rfl, Or.inl rfl⟩
      case eq =>
        split at hP
        · next hc0 =>
          subst hc0
          exact Or.inl ⟨s, rfl, rfl, Or.inr (Or.inr rfl)⟩
        · cases hP
      case ge =>
        injection hP with hP
        rw [← hP] at hc
        have hc0 : c = 0 := of_decide_eq_true hc
        subst hc0
        exact Or.inl ⟨s, rfl, rfl, Or.inr (Or.inl rfl)⟩
      case lt => cases hP
      case gt => cases hP
      case ne => cases hP
    | none =>
      cases hpr : parseHoleSide tr with
      | some s' =>
        cases hle : tl.evalQ? with
        | some c' =>
          cases b <;>
            simp only [classifyPredAtom, hpl, hre, hpr, hle] at hP
          case le =>
            injection hP with hP
            rw [← hP] at hc
            have hc0 : c' = 0 := of_decide_eq_true hc
            subst hc0
            exact Or.inr ⟨s', rfl, rfl, Or.inl rfl⟩
          case eq =>
            split at hP
            · next hc0 =>
              subst hc0
              exact Or.inr ⟨s', rfl, rfl, Or.inr (Or.inr rfl)⟩
            · cases hP
          case ge =>
            injection hP with hP
            rw [← hP] at hc
            have hc0 : c' = 0 := of_decide_eq_true hc
            subst hc0
            exact Or.inr ⟨s', rfl, rfl, Or.inr (Or.inl rfl)⟩
          case lt => cases hP
          case gt => cases hP
          case ne => cases hP
        | none =>
          exfalso
          cases b <;>
            simp only [classifyPredAtom, hpl, hre, hpr, hle] at hP <;>
            cases hP
      | none =>
        exfalso
        cases hle : tl.evalQ? <;> cases b <;>
          simp only [classifyPredAtom, hpl, hre, hpr, hle] at hP <;>
          cases hP
  | none =>
    cases hpr : parseHoleSide tr with
    | some s' =>
      cases hle : tl.evalQ? with
      | some c' =>
        cases b <;>
          simp only [classifyPredAtom, hpl, hpr, hle] at hP
        case le =>
          injection hP with hP
          rw [← hP] at hc
          have hc0 : c' = 0 := of_decide_eq_true hc
          subst hc0
          exact Or.inr ⟨s', rfl, rfl, Or.inl rfl⟩
        case eq =>
          split at hP
          · next hc0 =>
            subst hc0
            exact Or.inr ⟨s', rfl, rfl, Or.inr (Or.inr rfl)⟩
          · cases hP
        case ge =>
          injection hP with hP
          rw [← hP] at hc
          have hc0 : c' = 0 := of_decide_eq_true hc
          subst hc0
          exact Or.inr ⟨s', rfl, rfl, Or.inr (Or.inl rfl)⟩
        case lt => cases hP
        case gt => cases hP
        case ne => cases hP
      | none =>
        exfalso
        cases b <;>
          simp only [classifyPredAtom, hpl, hpr, hle] at hP <;>
          cases hP
    | none =>
      exfalso
      cases hle : tl.evalQ? <;> cases b <;>
        simp only [classifyPredAtom, hpl, hpr, hle] at hP <;>
        cases hP

theorem satisfiesPredQ_conic_zero {P : Formula} {cls : PredClass}
    (hP : classifyPred P = some cls) (hc : cls.conic = true) :
    satisfiesPredQ P 0 = true := by
  induction P generalizing cls with
  | and P₁ P₂ ih₁ ih₂ =>
    simp only [classifyPred, Option.bind_eq_bind] at hP
    obtain ⟨c₁, hc₁, hP⟩ := option_bind_eq_some' hP
    obtain ⟨c₂, hc₂, hP⟩ := option_bind_eq_some' hP
    injection hP with hP
    rw [← hP] at hc
    rw [Bool.and_eq_true] at hc
    exact satisfiesPredQ_and.mpr ⟨ih₁ hc₁ hc.1, ih₂ hc₂ hc.2⟩
  | atom b tl tr =>
    rcases classifyPredAtom_conic_shape hP hc with
      ⟨s, hpl, hre, hb⟩ | ⟨s, hpr, hle, hb⟩
    · rw [satisfiesPredQ_orient1_iff hpl hre]
      rcases hb with hb | hb | hb <;> subst hb
      · show s * 0 ≤ 0
        simp
      · show (0 : ℚ) ≤ s * 0
        simp
      · show s * 0 = 0
        simp
    · rw [satisfiesPredQ_orient2_iff hpr hle]
      rcases hb with hb | hb | hb <;> subst hb
      · show (0 : ℚ) ≤ s * 0
        simp
      · show s * 0 ≤ 0
        simp
      · show (0 : ℚ) = s * 0
        simp
  | inRegion t simplex S => cases hP
  | or P₁ P₂ _ _ => cases hP
  | tt => cases hP
  | ff => cases hP

theorem satisfiesPredQ_conic_scale {P : Formula} {cls : PredClass}
    (hP : classifyPred P = some cls) (hc : cls.conic = true) :
    ∀ a c : ℚ, 0 ≤ c → satisfiesPredQ P a = true →
      satisfiesPredQ P (c * a) = true := by
  induction P generalizing cls with
  | and P₁ P₂ ih₁ ih₂ =>
    intro a c hcnn ha
    simp only [classifyPred, Option.bind_eq_bind] at hP
    obtain ⟨c₁, hc₁, hP⟩ := option_bind_eq_some' hP
    obtain ⟨c₂, hc₂, hP⟩ := option_bind_eq_some' hP
    injection hP with hP
    rw [← hP] at hc
    rw [Bool.and_eq_true] at hc
    obtain ⟨ha₁, ha₂⟩ := satisfiesPredQ_and.mp ha
    exact satisfiesPredQ_and.mpr
      ⟨ih₁ hc₁ hc.1 a c hcnn ha₁, ih₂ hc₂ hc.2 a c hcnn ha₂⟩
  | atom b tl tr =>
    intro a c hcnn ha
    have hkey : ∀ s : ℚ, s * (c * a) = c * (s * a) := fun s => by ring
    rcases classifyPredAtom_conic_shape hP hc with
      ⟨s, hpl, hre, hb⟩ | ⟨s, hpr, hle, hb⟩
    · rw [satisfiesPredQ_orient1_iff hpl hre] at ha ⊢
      rw [hkey s]
      rcases hb with hb | hb | hb <;> subst hb
      · exact mul_nonpos_of_nonneg_of_nonpos hcnn ha
      · exact mul_nonneg hcnn ha
      · show c * (s * a) = 0
        rw [show s * a = 0 from ha]
        ring
    · rw [satisfiesPredQ_orient2_iff hpr hle] at ha ⊢
      rw [hkey s]
      rcases hb with hb | hb | hb <;> subst hb
      · exact mul_nonneg hcnn ha
      · exact mul_nonpos_of_nonneg_of_nonpos hcnn ha
      · show (0 : ℚ) = c * (s * a)
        rw [show s * a = 0 from ha.symm]
        ring
  | inRegion t simplex S => intro _ _ _ _; cases hP
  | or P₁ P₂ _ _ => intro _ _ _ _; cases hP
  | tt => intro _ _ _ _; cases hP
  | ff => intro _ _ _ _; cases hP

theorem holds_substHole_of_satisfies {H : Hypernet} (σ : H.Valuation)
    {P : Formula} {cls : PredClass} (hP : classifyPred P = some cls)
    {arg : Term} {qa : QTensor}
    (ha : Term.evalQ σ arg = some qa) (hsa : SingletonShape qa.shape)
    (hsat : satisfiesPredQ P qa.scalar = true) :
    Formula.holds σ (Formula.subst predicateHole arg P) := by
  induction P generalizing cls with
  | and P₁ P₂ ih₁ ih₂ =>
    simp only [classifyPred, Option.bind_eq_bind] at hP
    obtain ⟨c₁, hc₁, hP⟩ := option_bind_eq_some' hP
    obtain ⟨c₂, hc₂, hP⟩ := option_bind_eq_some' hP
    obtain ⟨h1, h2⟩ := satisfiesPredQ_and.mp hsat
    exact ⟨ih₁ hc₁ h1, ih₂ hc₂ h2⟩
  | atom b tl tr =>
    have hP' : classifyPredAtom (.atom b tl tr) = some cls := hP
    simp only [classifyPredAtom] at hP'
    have main1 : ∀ s c, parseHoleSide tl = some s → tr.evalQ? = some c →
        Formula.holds σ (Formula.subst predicateHole arg (.atom b tl tr)) := by
      intro s c hpl hre
      have hh := (satisfiesPredQ_orient1_iff hpl hre qa.scalar).mp hsat
      obtain ⟨q, hq, hsq, hvq⟩ := parseHoleSide_subst_evalQ σ hpl ha hsa
      refine ⟨q, ⟨[], [c], rfl⟩, hq, ?_, ?_⟩
      · show Term.evalQ σ (Term.subst predicateHole arg tr) = _
        rw [Term.subst_of_closed tr c hre]
        exact Term.evalQ_of_closed σ tr c hre
      · rw [QTensor.rel2_singleton hsq (Or.inl rfl)]
        show BowTie.holdsQ b q.scalar (QTensor.scalar ⟨[], [c], rfl⟩)
        rw [hvq]
        exact hh
    have main2 : ∀ s c, parseHoleSide tr = some s → tl.evalQ? = some c →
        Formula.holds σ (Formula.subst predicateHole arg (.atom b tl tr)) := by
      intro s c hpr hle
      have hh := (satisfiesPredQ_orient2_iff hpr hle qa.scalar).mp hsat
      obtain ⟨q, hq, hsq, hvq⟩ := parseHoleSide_subst_evalQ σ hpr ha hsa
      refine ⟨⟨[], [c], rfl⟩, q, ?_, hq, ?_⟩
      · show Term.evalQ σ (Term.subst predicateHole arg tl) = _
        rw [Term.subst_of_closed tl c hle]
        exact Term.evalQ_of_closed σ tl c hle
      · rw [QTensor.rel2_singleton (Or.inl rfl) hsq]
        show BowTie.holdsQ b (QTensor.scalar ⟨[], [c], rfl⟩) q.scalar
        rw [hvq]
        exact hh
    cases hpl : parseHoleSide tl with
    | some s =>
      cases hre : tr.evalQ? with
      | some c => exact main1 s c hpl hre
      | none =>
        rw [hpl, hre] at hP'
        cases hpr : parseHoleSide tr with
        | some s' =>
          cases hle : tl.evalQ? with
          | some c' => exact main2 s' c' hpr hle
          | none => rw [hpr, hle] at hP'; cases hP'
        | none =>
          rw [hpr] at hP'
          cases hle : tl.evalQ? <;> rw [hle] at hP' <;> cases hP'
    | none =>
      rw [hpl] at hP'
      cases hpr : parseHoleSide tr with
      | some s' =>
        cases hle : tl.evalQ? with
        | some c' => exact main2 s' c' hpr hle
        | none => rw [hpr, hle] at hP'; cases hP'
      | none =>
        rw [hpr] at hP'
        cases hle : tl.evalQ? <;> rw [hle] at hP' <;> cases hP'
  | inRegion t simplex S => cases hP
  | or P₁ P₂ _ _ => cases hP
  | tt => cases hP
  | ff => cases hP

theorem holds_substHole_of_satisfies_entries {H : Hypernet} (σ : H.Valuation)
    {P : Formula} {cls : PredClass} (hP : classifyPred P = some cls)
    {arg : Term} {qa : QTensor}
    (ha : Term.evalQ σ arg = some qa)
    (hsat : ∀ e ∈ qa.entries, satisfiesPredQ P e = true) :
    Formula.holds σ (Formula.subst predicateHole arg P) := by
  induction P generalizing cls with
  | and P₁ P₂ ih₁ ih₂ =>
    simp only [classifyPred, Option.bind_eq_bind] at hP
    obtain ⟨c₁, hc₁, hP⟩ := option_bind_eq_some' hP
    obtain ⟨c₂, hc₂, hP⟩ := option_bind_eq_some' hP
    exact ⟨ih₁ hc₁ (fun e he => (satisfiesPredQ_and.mp (hsat e he)).1),
      ih₂ hc₂ (fun e he => (satisfiesPredQ_and.mp (hsat e he)).2)⟩
  | atom b tl tr =>
    have hP' : classifyPredAtom (.atom b tl tr) = some cls := hP
    simp only [classifyPredAtom] at hP'
    have main1 : ∀ s c, parseHoleSide tl = some s → tr.evalQ? = some c →
        Formula.holds σ (Formula.subst predicateHole arg (.atom b tl tr)) := by
      intro s c hpl hre
      obtain ⟨q, hq, hqs, hqe⟩ := parseHoleSide_subst_evalQ_entries σ hpl ha
      refine ⟨q, ⟨[], [c], rfl⟩, hq, ?_, ?_⟩
      · show Term.evalQ σ (Term.subst predicateHole arg tr) = _
        rw [Term.subst_of_closed tr c hre]
        exact Term.evalQ_of_closed σ tr c hre
      · apply QTensor.rel2_const_right
        intro x hx
        rw [hqe] at hx
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        exact (satisfiesPredQ_orient1_iff hpl hre e).mp (hsat e he)
    have main2 : ∀ s c, parseHoleSide tr = some s → tl.evalQ? = some c →
        Formula.holds σ (Formula.subst predicateHole arg (.atom b tl tr)) := by
      intro s c hpr hle
      obtain ⟨q, hq, hqs, hqe⟩ := parseHoleSide_subst_evalQ_entries σ hpr ha
      refine ⟨⟨[], [c], rfl⟩, q, ?_, hq, ?_⟩
      · show Term.evalQ σ (Term.subst predicateHole arg tl) = _
        rw [Term.subst_of_closed tl c hle]
        exact Term.evalQ_of_closed σ tl c hle
      · apply QTensor.rel2_const_left
        intro x hx
        rw [hqe] at hx
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        exact (satisfiesPredQ_orient2_iff hpr hle e).mp (hsat e he)
    cases hpl : parseHoleSide tl with
    | some s =>
      cases hre : tr.evalQ? with
      | some c => exact main1 s c hpl hre
      | none =>
        rw [hpl, hre] at hP'
        cases hpr : parseHoleSide tr with
        | some s' =>
          cases hle : tl.evalQ? with
          | some c' => exact main2 s' c' hpr hle
          | none => rw [hpr, hle] at hP'; cases hP'
        | none =>
          rw [hpr] at hP'
          cases hle : tl.evalQ? <;> rw [hle] at hP' <;> cases hP'
    | none =>
      rw [hpl] at hP'
      cases hpr : parseHoleSide tr with
      | some s' =>
        cases hle : tl.evalQ? with
        | some c' => exact main2 s' c' hpr hle
        | none => rw [hpr, hle] at hP'; cases hP'
      | none =>
        rw [hpr] at hP'
        cases hle : tl.evalQ? <;> rw [hle] at hP' <;> cases hP'
  | inRegion t simplex S => cases hP
  | or P₁ P₂ _ _ => cases hP
  | tt => cases hP
  | ff => cases hP

theorem Formula.holds_of_mem_conjunctList {H : Hypernet} (σ : H.Valuation) :
    ∀ (F : Formula), Formula.holds σ F → ∀ a ∈ F.conjunctList, Formula.holds σ a := by
  intro F
  induction F with
  | and l r ihl ihr =>
    intro h a ha
    rcases List.mem_append.mp ha with h' | h'
    · exact ihl h.1 a h'
    · exact ihr h.2 a h'
  | atom b l r =>
    intro h a ha
    simp only [Formula.conjunctList, List.mem_singleton] at ha
    subst ha
    exact h
  | inRegion t simplex S =>
    intro h a ha
    simp only [Formula.conjunctList, List.mem_singleton] at ha
    subst ha
    exact h
  | or l r _ _ =>
    intro h a ha
    simp only [Formula.conjunctList, List.mem_singleton] at ha
    subst ha
    exact h
  | tt =>
    intro h a ha
    simp only [Formula.conjunctList, List.mem_singleton] at ha
    subst ha
    exact h
  | ff =>
    intro h a ha
    simp only [Formula.conjunctList, List.mem_singleton] at ha
    subst ha
    exact h

theorem Formula.freeWires_of_mem_conjunctList :
    ∀ (F a : Formula), a ∈ F.conjunctList → ∀ w ∈ a.freeWires, w ∈ F.freeWires := by
  intro F
  induction F with
  | and l r ihl ihr =>
    intro a ha w hw
    rcases List.mem_append.mp ha with h' | h'
    · exact List.mem_append.mpr (Or.inl (ihl a h' w hw))
    · exact List.mem_append.mpr (Or.inr (ihr a h' w hw))
  | atom b l r =>
    intro a ha w hw
    simp only [Formula.conjunctList, List.mem_singleton] at ha
    subst ha
    exact hw
  | inRegion t simplex S =>
    intro a ha w hw
    simp only [Formula.conjunctList, List.mem_singleton] at ha
    subst ha
    exact hw
  | or l r _ _ =>
    intro a ha w hw
    simp only [Formula.conjunctList, List.mem_singleton] at ha
    subst ha
    exact hw
  | tt =>
    intro a ha w hw
    simp only [Formula.conjunctList, List.mem_singleton] at ha
    subst ha
    exact hw
  | ff =>
    intro a ha w hw
    simp only [Formula.conjunctList, List.mem_singleton] at ha
    subst ha
    exact hw

theorem wireQ_pos_of_type_pos {H : Hypernet} (σ : H.Valuation)
    {w : Wire} {qw : QTensor} (hqw : σ.wireQ w = some qw)
    (hpos : ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape) :
    0 < Shape.totalSize qw.shape := by
  obtain ⟨τ, hτ, hp⟩ := hpos
  obtain ⟨τ', hτ', hqs⟩ := σ.wireQ_shape hqw
  rw [hτ] at hτ'
  injection hτ' with hττ
  rw [hqs, ← hττ]
  exact hp

theorem Term.evalQ_pos {H : Hypernet} (σ : H.Valuation)
    {t : Term} {q : QTensor} (h : Term.evalQ σ t = some q)
    (hpos : ∀ w ∈ t.freeWires, ∃ τ, H.wireType w = some τ ∧
      0 < Shape.totalSize τ.shape) :
    0 < q.entries.length := by
  rw [q.len_eq]
  by_cases hq : q.shape = []
  · rw [hq]
    simp [Shape.totalSize]
  · obtain ⟨w₀, hw₀, qw₀, hqw₀, hqs₀⟩ := Term.evalQ_nonnil_shape_wire σ t q h hq
    rw [← hqs₀]
    exact wireQ_pos_of_type_pos σ hqw₀ (hpos w₀ hw₀)

theorem atomLeZeroPolys_sound_entryC {H : Hypernet} (σ : H.Valuation)
    {F : Formula} (hF : Formula.holds σ F)
    (hw : ∀ w ∈ F.freeWires, ∃ τ, H.wireType w = some τ ∧
      0 < Shape.totalSize τ.shape)
    (hix : F.atomSidesIdxFree = true) (i : ℕ) :
    ∀ pa ∈ atomLeZeroPolys F, QArith.Poly.eval (σ.entryValC i) pa ≤ 0 := by
  intro pa hpa
  match F, hix, hpa with
  | .atom bw l r, hix, hpa =>
    have hix' : l.idxFree = true ∧ r.idxFree = true := by
      simpa [Formula.atomSidesIdxFree, Bool.and_eq_true] using hix
    obtain ⟨al, ar, hal, har, hrel⟩ := hF
    have hwl : ∀ w ∈ l.freeWires, ∃ τ, H.wireType w = some τ ∧
        0 < Shape.totalSize τ.shape :=
      fun w hw' => hw w (List.mem_append.mpr (Or.inl hw'))
    have hwr : ∀ w ∈ r.freeWires, ∃ τ, H.wireType w = some τ ∧
        0 < Shape.totalSize τ.shape :=
      fun w hw' => hw w (List.mem_append.mpr (Or.inr hw'))
    have hvl := Term.evalQ_brReadC σ hal
      (fun w hw' qw hqw => wireQ_pos_of_type_pos σ hqw (hwl w hw')) hix'.1 i
    have hvr := Term.evalQ_brReadC σ har
      (fun w hw' qw hqw => wireQ_pos_of_type_pos σ hqw (hwr w hw')) hix'.2 i
    have hscal : BowTie.holdsQ bw (al.brReadC i) (ar.brReadC i) :=
      QTensor.rel2_brReadC hrel (Term.evalQ_pos σ hal hwl)
        (Term.evalQ_pos σ har hwr) i
    rw [hvl, hvr] at hscal
    match bw, hpa, hscal with
    | .le, hpa, hscal =>
      simp only [atomLeZeroPolys, List.mem_singleton] at hpa
      subst hpa
      rw [Poly.eval_sub]
      have : QArith.Poly.eval (σ.entryValC i) l.toPoly
          ≤ QArith.Poly.eval (σ.entryValC i) r.toPoly := hscal
      linarith
    | .lt, hpa, hscal =>
      simp only [atomLeZeroPolys, List.mem_singleton] at hpa
      subst hpa
      rw [Poly.eval_sub]
      have : QArith.Poly.eval (σ.entryValC i) l.toPoly
          < QArith.Poly.eval (σ.entryValC i) r.toPoly := hscal
      linarith
    | .ge, hpa, hscal =>
      simp only [atomLeZeroPolys, List.mem_singleton] at hpa
      subst hpa
      rw [Poly.eval_sub]
      have : QArith.Poly.eval (σ.entryValC i) r.toPoly
          ≤ QArith.Poly.eval (σ.entryValC i) l.toPoly := hscal
      linarith
    | .gt, hpa, hscal =>
      simp only [atomLeZeroPolys, List.mem_singleton] at hpa
      subst hpa
      rw [Poly.eval_sub]
      have : QArith.Poly.eval (σ.entryValC i) r.toPoly
          < QArith.Poly.eval (σ.entryValC i) l.toPoly := hscal
      linarith
    | .eq, hpa, hscal =>
      simp only [atomLeZeroPolys, List.mem_cons, List.not_mem_nil, or_false] at hpa
      have heq : QArith.Poly.eval (σ.entryValC i) l.toPoly
          = QArith.Poly.eval (σ.entryValC i) r.toPoly := hscal
      rcases hpa with hpa | hpa
      · rw [hpa, Poly.eval_sub]
        linarith
      · rw [hpa, Poly.eval_sub]
        linarith

theorem farkas_fold_eval_nonpos (ρ : Nat → ℚ) :
    ∀ (entries : List (ℚ × Term)),
    (∀ e ∈ entries, 0 ≤ e.1 ∧ QArith.Poly.eval ρ e.2.toPoly ≤ 0) →
    QArith.Poly.eval ρ
      (entries.foldr
        (fun (le : ℚ × Term) acc =>
          QArith.Poly.add (QArith.Poly.scale le.1 le.2.toPoly) acc) []) ≤ 0 := by
  intro entries
  induction entries with
  | nil => intro _; simp
  | cons hd tl ih =>
    intro h
    obtain ⟨hl, he⟩ := h hd (by simp)
    have htl := ih (fun e he' => h e (by simp [he']))
    simp only [List.foldr_cons, Poly.eval_add, Poly.eval_scale]
    nlinarith [mul_nonneg hl (neg_nonneg.mpr he)]

theorem QTensor.map2_defined_of_rel2 {r : ℚ → ℚ → Prop} {a b : QTensor}
    (h : QTensor.rel2 r a b) (f : ℚ → ℚ → ℚ) :
    ∃ c, QTensor.map2 f a b = some c := by
  unfold QTensor.rel2 at h
  unfold QTensor.map2
  by_cases hs : a.shape = b.shape
  · exact ⟨_, dif_pos hs⟩
  · rw [if_neg hs] at h
    rw [dif_neg hs]
    by_cases hsa : a.shape = []
    · rw [if_pos hsa]
      exact ⟨_, rfl⟩
    · rw [if_neg hsa] at h
      rw [if_neg hsa]
      by_cases hsb : b.shape = []
      · rw [if_pos hsb]
        exact ⟨_, rfl⟩
      · rw [if_neg hsb] at h
        cases h

theorem ExtensionSet.containsNat_val (S : ExtensionSet)
    (v : Fin S.simplex.complex.nVertices) :
    S.containsNat v.val = S.contains v := by
  unfold ExtensionSet.containsNat
  rw [dif_pos v.isLt]

theorem Term.evalQ_defined_of_bshape_fin {H : Hypernet} (σ : H.Valuation) :
    ∀ (t : Term) (s : Shape), t.bshape H = some s → t.finWires H →
    ∃ q, Term.evalQ σ t = some q ∧ q.shape = s := by
  intro t
  induction t with
  | var w =>
    intro s hb hf
    obtain ⟨qw, hqw, -⟩ := wire_discipline_of_bshape_fin σ hb hf rfl w
      (by simp [Term.freeWires])
    exact ⟨qw, hqw, Term.evalQ_bshape σ (.var w) s qw hb hqw⟩
  | const c =>
    intro s hb hf
    injection hb with hb
    exact ⟨⟨[], [c], rfl⟩, rfl, hb⟩
  | add l r ihl ihr =>
    intro s hb hf
    have hfl : l.finWires H := fun w hw => hf w (List.mem_append.mpr (Or.inl hw))
    have hfr : r.finWires H := fun w hw => hf w (List.mem_append.mpr (Or.inr hw))
    have hb' := hb
    simp only [Term.bshape] at hb'
    rcases hla : Term.bshape H l with _ | s₁ <;> rw [hla] at hb'
    · cases hb'
    rcases hra : Term.bshape H r with _ | s₂ <;> rw [hra] at hb'
    · cases hb'
    obtain ⟨a, ha, has⟩ := ihl s₁ hla hfl
    obtain ⟨b, hbb, hbs⟩ := ihr s₂ hra hfr
    obtain ⟨hs₁, hs₂⟩ := bshape_join_cases hb'
    have hja : a.shape = [] ∨ a.shape = s := by
      rw [has]
      exact hs₁.symm.imp id id
    have hjb : b.shape = [] ∨ b.shape = s := by
      rw [hbs]
      exact hs₂.symm.imp id id
    obtain ⟨c, hc⟩ := QTensor.map2_defined_broadcast (f := (· + ·)) hja hjb
    refine ⟨c, ?_, ?_⟩
    · show (do QTensor.map2 (· + ·) (← Term.evalQ σ l) (← Term.evalQ σ r)) = some c
      rw [ha, hbb]
      simpa using hc
    · exact Term.evalQ_bshape σ (.add l r) s c hb (by
        show (do QTensor.map2 (· + ·) (← Term.evalQ σ l) (← Term.evalQ σ r)) = some c
        rw [ha, hbb]
        simpa using hc)
  | mul l r ihl ihr =>
    intro s hb hf
    have hfl : l.finWires H := fun w hw => hf w (List.mem_append.mpr (Or.inl hw))
    have hfr : r.finWires H := fun w hw => hf w (List.mem_append.mpr (Or.inr hw))
    have hb' := hb
    simp only [Term.bshape] at hb'
    rcases hla : Term.bshape H l with _ | s₁ <;> rw [hla] at hb'
    · cases hb'
    rcases hra : Term.bshape H r with _ | s₂ <;> rw [hra] at hb'
    · cases hb'
    obtain ⟨a, ha, has⟩ := ihl s₁ hla hfl
    obtain ⟨b, hbb, hbs⟩ := ihr s₂ hra hfr
    obtain ⟨hs₁, hs₂⟩ := bshape_join_cases hb'
    have hja : a.shape = [] ∨ a.shape = s := by
      rw [has]
      exact hs₁.symm.imp id id
    have hjb : b.shape = [] ∨ b.shape = s := by
      rw [hbs]
      exact hs₂.symm.imp id id
    obtain ⟨c, hc⟩ := QTensor.map2_defined_broadcast (f := (· * ·)) hja hjb
    refine ⟨c, ?_, ?_⟩
    · show (do QTensor.map2 (· * ·) (← Term.evalQ σ l) (← Term.evalQ σ r)) = some c
      rw [ha, hbb]
      simpa using hc
    · exact Term.evalQ_bshape σ (.mul l r) s c hb (by
        show (do QTensor.map2 (· * ·) (← Term.evalQ σ l) (← Term.evalQ σ r)) = some c
        rw [ha, hbb]
        simpa using hc)
  | sub l r ihl ihr =>
    intro s hb hf
    have hfl : l.finWires H := fun w hw => hf w (List.mem_append.mpr (Or.inl hw))
    have hfr : r.finWires H := fun w hw => hf w (List.mem_append.mpr (Or.inr hw))
    have hb' := hb
    simp only [Term.bshape] at hb'
    rcases hla : Term.bshape H l with _ | s₁ <;> rw [hla] at hb'
    · cases hb'
    rcases hra : Term.bshape H r with _ | s₂ <;> rw [hra] at hb'
    · cases hb'
    obtain ⟨a, ha, has⟩ := ihl s₁ hla hfl
    obtain ⟨b, hbb, hbs⟩ := ihr s₂ hra hfr
    obtain ⟨hs₁, hs₂⟩ := bshape_join_cases hb'
    have hja : a.shape = [] ∨ a.shape = s := by
      rw [has]
      exact hs₁.symm.imp id id
    have hjb : b.shape = [] ∨ b.shape = s := by
      rw [hbs]
      exact hs₂.symm.imp id id
    obtain ⟨c, hc⟩ := QTensor.map2_defined_broadcast (f := (· - ·)) hja hjb
    refine ⟨c, ?_, ?_⟩
    · show (do QTensor.map2 (· - ·) (← Term.evalQ σ l) (← Term.evalQ σ r)) = some c
      rw [ha, hbb]
      simpa using hc
    · exact Term.evalQ_bshape σ (.sub l r) s c hb (by
        show (do QTensor.map2 (· - ·) (← Term.evalQ σ l) (← Term.evalQ σ r)) = some c
        rw [ha, hbb]
        simpa using hc)
  | neg u ih =>
    intro s hb hf
    obtain ⟨a, ha, has⟩ := ih s (by simpa [Term.bshape] using hb)
      (fun w hw => hf w (by simpa [Term.freeWires] using hw))
    refine ⟨QTensor.map1 Neg.neg a, ?_, ?_⟩
    · show (Term.evalQ σ u).map (QTensor.map1 Neg.neg) = _
      rw [ha]
      rfl
    · show a.shape = s
      exact has
  | idx u i ih =>
    intro s hb hf
    have hb' := hb
    simp only [Term.bshape] at hb'
    split at hb'
    · next e hbu =>
      split at hb'
      · next hi =>
        injection hb' with hb'
        obtain ⟨a, ha, has⟩ := ih [e] hbu
          (fun w hw => hf w (by simpa [Term.freeWires] using hw))
        refine ⟨⟨[], [a.entries.getD i 0], rfl⟩, ?_, hb'⟩
        simp only [Term.evalQ, Option.bind_eq_bind, ha, Option.bind_some]
        rw [has]
        show (if i < e then some (⟨[], [a.entries.getD i 0],
            (rfl : [a.entries.getD i 0].length = Shape.totalSize [])⟩ : QTensor)
          else none) = _
        rw [if_pos hi]
      · cases hb'
    · cases hb'

theorem wireCoordKey_eq_pair (w i : Nat) :
    wireCoordKey w i = Nat.pair w i := rfl

def Hypernet.Valuation.coordValW {H : Hypernet} (σ : H.Valuation) :
    Nat → ℚ :=
  fun k =>
    match σ.wireQ (Nat.unpair k).1 with
    | some q => q.entries.getD (Nat.unpair k).2 0
    | none => 0

theorem Hypernet.Valuation.coordValW_key {H : Hypernet} (σ : H.Valuation)
    {w : Wire} {q : QTensor} (hwq : σ.wireQ w = some q) (i : Nat) :
    σ.coordValW (wireCoordKey w i) = q.entries.getD i 0 := by
  unfold Hypernet.Valuation.coordValW
  rw [wireCoordKey_eq_pair, Nat.unpair_pair]
  simp only [hwq]

theorem Term.asCoordPolyIdxW?_idx_inv {t : Term} {i : Nat}
    {p : QArith.Poly} (h : Term.asCoordPolyIdxW? (.idx t i) = some p) :
    ∃ w, t = .var w ∧ p = QArith.Poly.var (wireCoordKey w i) := by
  cases t with
  | var w =>
    refine ⟨w, rfl, ?_⟩
    simp only [Term.asCoordPolyIdxW?] at h
    injection h with h
    exact h.symm
  | const c => cases h
  | add l r => cases h
  | mul l r => cases h
  | sub l r => cases h
  | neg u => cases h
  | idx u i' => cases h

theorem QTensor.scalar_mk_congr {a b : ℚ} (h : a = b) :
    (⟨[], [a], rfl⟩ : QTensor) = ⟨[], [b], rfl⟩ := by
  subst h
  rfl

theorem QTensor.map2_scalars (f : ℚ → ℚ → ℚ) (x y : ℚ) :
    QTensor.map2 f ⟨[], [x], rfl⟩ ⟨[], [y], rfl⟩
      = some ⟨[], [f x y], rfl⟩ := by
  unfold QTensor.map2
  rw [dif_pos rfl]
  rfl

theorem QTensor.map1_scalar (f : ℚ → ℚ) (x : ℚ) :
    QTensor.map1 f ⟨[], [x], rfl⟩ = ⟨[], [f x], rfl⟩ := rfl

theorem QTensor.rel2_scalars {r : ℚ → ℚ → Prop} (x y : ℚ) :
    QTensor.rel2 r ⟨[], [x], rfl⟩ ⟨[], [y], rfl⟩ ↔ r x y := by
  unfold QTensor.rel2
  rw [if_pos rfl]
  simp

theorem Term.evalQ_asCoordPolyIdxW {H : Hypernet} (σ : H.Valuation) :
    ∀ {t : Term} {p : QArith.Poly} {q : QTensor},
    Term.asCoordPolyIdxW? t = some p →
    Term.evalQ σ t = some q →
    q = ⟨[], [QArith.Poly.eval σ.coordValW p], rfl⟩ := by
  intro t
  induction t with
  | var w => intro p q h _; cases h
  | const c =>
    intro p q h heval
    simp only [Term.asCoordPolyIdxW?] at h
    injection h with h
    subst h
    injection heval with heval
    rw [← heval]
    exact QTensor.scalar_mk_congr (Poly.eval_const _ c).symm
  | add l r ihl ihr =>
    intro p q h heval
    simp only [Term.asCoordPolyIdxW?, Option.bind_eq_bind] at h
    obtain ⟨pl, hpl, h⟩ := option_bind_eq_some' h
    obtain ⟨pr, hpr, h⟩ := option_bind_eq_some' h
    injection h with h
    subst h
    simp only [Term.evalQ, Option.bind_eq_bind] at heval
    obtain ⟨ql, hql, heval⟩ := option_bind_eq_some' heval
    obtain ⟨qr, hqr, heval⟩ := option_bind_eq_some' heval
    have hl := ihl hpl hql
    have hr := ihr hpr hqr
    subst hl
    subst hr
    rw [QTensor.map2_scalars] at heval
    injection heval with heval
    rw [← heval]
    exact QTensor.scalar_mk_congr (Poly.eval_add _ pl pr).symm
  | mul l r ihl ihr =>
    intro p q h heval
    simp only [Term.asCoordPolyIdxW?, Option.bind_eq_bind] at h
    obtain ⟨pl, hpl, h⟩ := option_bind_eq_some' h
    obtain ⟨pr, hpr, h⟩ := option_bind_eq_some' h
    injection h with h
    subst h
    simp only [Term.evalQ, Option.bind_eq_bind] at heval
    obtain ⟨ql, hql, heval⟩ := option_bind_eq_some' heval
    obtain ⟨qr, hqr, heval⟩ := option_bind_eq_some' heval
    have hl := ihl hpl hql
    have hr := ihr hpr hqr
    subst hl
    subst hr
    rw [QTensor.map2_scalars] at heval
    injection heval with heval
    rw [← heval]
    exact QTensor.scalar_mk_congr (Poly.eval_mul _ pl pr).symm
  | sub l r ihl ihr =>
    intro p q h heval
    simp only [Term.asCoordPolyIdxW?, Option.bind_eq_bind] at h
    obtain ⟨pl, hpl, h⟩ := option_bind_eq_some' h
    obtain ⟨pr, hpr, h⟩ := option_bind_eq_some' h
    injection h with h
    subst h
    simp only [Term.evalQ, Option.bind_eq_bind] at heval
    obtain ⟨ql, hql, heval⟩ := option_bind_eq_some' heval
    obtain ⟨qr, hqr, heval⟩ := option_bind_eq_some' heval
    have hl := ihl hpl hql
    have hr := ihr hpr hqr
    subst hl
    subst hr
    rw [QTensor.map2_scalars] at heval
    injection heval with heval
    rw [← heval]
    exact QTensor.scalar_mk_congr (Poly.eval_sub _ pl pr).symm
  | neg u ih =>
    intro p q h heval
    simp only [Term.asCoordPolyIdxW?, Option.map_eq_some_iff] at h
    obtain ⟨pu, hpu, hp⟩ := h
    subst hp
    simp only [Term.evalQ, Option.map_eq_some_iff] at heval
    obtain ⟨qu, hqu, hq⟩ := heval
    subst hq
    have hu := ih hpu hqu
    subst hu
    rw [QTensor.map1_scalar]
    exact QTensor.scalar_mk_congr (Poly.eval_neg _ pu).symm
  | idx u i ih =>
    intro p q h heval
    obtain ⟨w, hw, hp⟩ := Term.asCoordPolyIdxW?_idx_inv h
    subst hw
    subst hp
    simp only [Term.evalQ, Option.bind_eq_bind] at heval
    obtain ⟨qw, hqw, heval⟩ := option_bind_eq_some' heval
    split at heval
    · next e hqs =>
      split at heval
      · next hi =>
        injection heval with heval
        rw [← heval]
        refine QTensor.scalar_mk_congr ?_
        rw [Poly.eval_var, Hypernet.Valuation.coordValW_key σ hqw i]
      · cases heval
    · cases heval

theorem atomLeZeroPolysW_sound {H : Hypernet} (σ : H.Valuation)
    {F : Formula} (hF : Formula.holds σ F) :
    ∀ pa ∈ atomLeZeroPolysW F, QArith.Poly.eval σ.coordValW pa ≤ 0 := by
  intro pa hpa
  match F, hpa with
  | .atom op l r, hpa =>
    simp only [atomLeZeroPolysW] at hpa
    split at hpa
    · exact absurd hpa (List.not_mem_nil)
    · next pl hpl =>
      split at hpa
      · exact absurd hpa (List.not_mem_nil)
      · next pr hpr =>
        obtain ⟨al, ar, hal, har, hrel⟩ := hF
        have hl := Term.evalQ_asCoordPolyIdxW σ hpl hal
        have hr := Term.evalQ_asCoordPolyIdxW σ hpr har
        subst hl
        subst hr
        rw [QTensor.rel2_scalars] at hrel
        match op, hpa, hrel with
        | .le, hpa, hrel =>
          simp only [List.mem_singleton] at hpa
          subst hpa
          rw [Poly.eval_sub]
          have : QArith.Poly.eval σ.coordValW pl
              ≤ QArith.Poly.eval σ.coordValW pr := hrel
          linarith
        | .lt, hpa, hrel =>
          simp only [List.mem_singleton] at hpa
          subst hpa
          rw [Poly.eval_sub]
          have : QArith.Poly.eval σ.coordValW pl
              < QArith.Poly.eval σ.coordValW pr := hrel
          linarith
        | .ge, hpa, hrel =>
          simp only [List.mem_singleton] at hpa
          subst hpa
          rw [Poly.eval_sub]
          have : QArith.Poly.eval σ.coordValW pr
              ≤ QArith.Poly.eval σ.coordValW pl := hrel
          linarith
        | .gt, hpa, hrel =>
          simp only [List.mem_singleton] at hpa
          subst hpa
          rw [Poly.eval_sub]
          have : QArith.Poly.eval σ.coordValW pr
              < QArith.Poly.eval σ.coordValW pl := hrel
          linarith
        | .eq, hpa, hrel =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpa
          have heq : QArith.Poly.eval σ.coordValW pl
              = QArith.Poly.eval σ.coordValW pr := hrel
          rcases hpa with hpa | hpa
          · rw [hpa, Poly.eval_sub]
            linarith
          · rw [hpa, Poly.eval_sub]
            linarith
        | .ne, hpa, hrel => cases hpa

theorem farkas_fold_eval_nonpos_polys (ρ : Nat → ℚ) :
    ∀ (pentries : List (ℚ × QArith.Poly)),
    (∀ e ∈ pentries, 0 ≤ e.1 ∧ QArith.Poly.eval ρ e.2 ≤ 0) →
    QArith.Poly.eval ρ
      (pentries.foldr
        (fun (le : ℚ × QArith.Poly) acc =>
          QArith.Poly.add (QArith.Poly.scale le.1 le.2) acc) []) ≤ 0 := by
  intro pentries
  induction pentries with
  | nil => intro _; simp
  | cons hd tl ih =>
    intro h
    obtain ⟨hl, he⟩ := h hd (by simp)
    have htl := ih (fun e he' => h e (by simp [he']))
    simp only [List.foldr_cons, Poly.eval_add, Poly.eval_scale]
    nlinarith [mul_nonneg hl (neg_nonneg.mpr he)]

theorem QTensor.map2_pos {f : ℚ → ℚ → ℚ} {a b c : QTensor}
    (h : QTensor.map2 f a b = some c)
    (hpa : 0 < a.entries.length) (hpb : 0 < b.entries.length) :
    0 < c.entries.length := by
  unfold QTensor.map2 at h
  split at h
  · injection h with h
    subst h
    show 0 < (a.entries.zipWith f b.entries).length
    rw [List.length_zipWith]
    omega
  · split at h
    · injection h with h
      subst h
      show 0 < (b.entries.map _).length
      rw [List.length_map]
      exact hpb
    · split at h
      · injection h with h
        subst h
        show 0 < (a.entries.map _).length
        rw [List.length_map]
        exact hpa
      · cases h

theorem QTensor.brReadC_eq_brRead_clamp {q : QTensor} {s : Shape}
    (hq : q.shape = [] ∨ q.shape = s) (hs : ¬ s = []) (i : ℕ) :
    q.brReadC i = q.brRead (if i < Shape.totalSize s then i else 0) := by
  rcases hq with h | h
  · rw [QTensor.brReadC_scalar h, QTensor.brRead_scalar h]
  · have hqs : ¬ q.shape = [] := by
      rw [h]
      exact hs
    unfold QTensor.brReadC
    rw [if_neg hqs, QTensor.brRead_pos hqs]
    have hix : (if i < q.entries.length then i else 0)
        = (if i < Shape.totalSize s then i else 0) := by
      rw [q.len_eq, h]
    rw [hix]

theorem QTensor.map2_brReadC {f : ℚ → ℚ → ℚ} {a b c : QTensor}
    (h : QTensor.map2 f a b = some c)
    (hpa : 0 < a.entries.length) (hpb : 0 < b.entries.length) (i : ℕ) :
    c.brReadC i = f (a.brReadC i) (b.brReadC i) := by
  obtain ⟨hsa, hsb⟩ := QTensor.map2_shape_inv h
  by_cases hcs : c.shape = []
  ·
    have hsa' : a.shape = [] := by
      rcases hsa with h1 | h1
      · rw [h1, hcs]
      · exact h1
    have hsb' : b.shape = [] := by
      rcases hsb with h1 | h1
      · rw [h1, hcs]
      · exact h1
    rw [QTensor.brReadC_scalar hcs, QTensor.brReadC_scalar hsa',
      QTensor.brReadC_scalar hsb']
    unfold QTensor.map2 at h
    rw [dif_pos (hsa'.trans hsb'.symm)] at h
    injection h with h
    subst h
    have hae := QTensor.entries_singleton (q := a) (Or.inl hsa')
    have hbe := QTensor.entries_singleton (q := b) (Or.inl hsb')
    show (a.entries.zipWith f b.entries).getD 0 0 = _
    rw [hae, hbe]
    rfl
  ·
    have hpc : 0 < Shape.totalSize c.shape := by
      rw [← c.len_eq]
      exact QTensor.map2_pos h hpa hpb
    have hj : (if i < Shape.totalSize c.shape then i else 0)
        < Shape.totalSize c.shape := by
      split
      · assumption
      · exact hpc
    have hja : a.shape = [] ∨ a.shape = c.shape := hsa.symm.imp id id
    have hjb : b.shape = [] ∨ b.shape = c.shape := hsb.symm.imp id id
    rw [QTensor.brReadC_eq_brRead_clamp (Or.inr rfl) hcs i,
      QTensor.brReadC_eq_brRead_clamp hja hcs i,
      QTensor.brReadC_eq_brRead_clamp hjb hcs i]
    exact QTensor.map2_brRead h hja hjb hj

theorem QTensor.map1_brReadC (f : ℚ → ℚ) {a : QTensor}
    (hpa : 0 < a.entries.length) (i : ℕ) :
    (QTensor.map1 f a).brReadC i = f (a.brReadC i) := by
  by_cases hsa : a.shape = []
  · rw [QTensor.brReadC_scalar (show (QTensor.map1 f a).shape = [] from hsa),
      QTensor.brReadC_scalar hsa]
    have hae := QTensor.entries_singleton (q := a) (Or.inl hsa)
    show (a.entries.map f).getD 0 0 = _
    rw [hae]
    rfl
  · have hpos : 0 < Shape.totalSize a.shape := by
      rw [← a.len_eq]
      exact hpa
    have hj : (if i < Shape.totalSize a.shape then i else 0)
        < Shape.totalSize a.shape := by
      split
      · assumption
      · exact hpos
    rw [QTensor.brReadC_eq_brRead_clamp (s := a.shape)
        (Or.inr (rfl : (QTensor.map1 f a).shape = a.shape)) hsa i,
      QTensor.brReadC_eq_brRead_clamp (s := a.shape) (Or.inr rfl) hsa i]
    exact QTensor.map1_brRead (Or.inr rfl) f hj

noncomputable def Hypernet.Valuation.entryValM {H : Hypernet}
    (σ : H.Valuation) (i : ℕ) : Nat → ℚ :=
  fun k =>
    if k % 2 = 0 then σ.entryValC i (k / 2)
    else
      match σ.wireQ (Nat.unpair (k / 2)).1 with
      | some qw => qw.entries.getD (Nat.unpair (k / 2)).2 0
      | none => 0

theorem Hypernet.Valuation.entryValM_even {H : Hypernet} (σ : H.Valuation)
    (i : ℕ) (w : Nat) : σ.entryValM i (2 * w) = σ.entryValC i w := by
  unfold Hypernet.Valuation.entryValM
  rw [if_pos (by omega : 2 * w % 2 = 0), (by omega : 2 * w / 2 = w)]

theorem Hypernet.Valuation.entryValM_odd {H : Hypernet} (σ : H.Valuation)
    (i : ℕ) {w : Nat} {qw : QTensor} (hwq : σ.wireQ w = some qw) (j : ℕ) :
    σ.entryValM i (2 * wireCoordKey w j + 1) = qw.entries.getD j 0 := by
  unfold Hypernet.Valuation.entryValM
  rw [if_neg (by omega : ¬ (2 * wireCoordKey w j + 1) % 2 = 0),
    (by omega : (2 * wireCoordKey w j + 1) / 2 = wireCoordKey w j),
    wireCoordKey_eq_pair, Nat.unpair_pair]
  simp only [hwq]

theorem Term.asCoordPolyMixed?_idx_inv {t : Term} {j : Nat}
    {p : QArith.Poly} (h : Term.asCoordPolyMixed? (.idx t j) = some p) :
    ∃ w, t = .var w ∧ p = QArith.Poly.var (2 * wireCoordKey w j + 1) := by
  cases t with
  | var w =>
    refine ⟨w, rfl, ?_⟩
    simp only [Term.asCoordPolyMixed?] at h
    injection h with h
    exact h.symm
  | const c => cases h
  | add l r => cases h
  | mul l r => cases h
  | sub l r => cases h
  | neg u => cases h
  | idx u i' => cases h

theorem Term.evalQ_asCoordPolyMixed {H : Hypernet} (σ : H.Valuation) :
    ∀ {t : Term} {p : QArith.Poly} {q : QTensor},
    Term.asCoordPolyMixed? t = some p →
    Term.evalQ σ t = some q →
    (∀ w ∈ t.freeWires, ∃ τ, H.wireType w = some τ ∧
      0 < Shape.totalSize τ.shape) →
    ∀ i, q.brReadC i = QArith.Poly.eval (σ.entryValM i) p := by
  intro t
  induction t with
  | var w =>
    intro p q h heval hpos i
    simp only [Term.asCoordPolyMixed?] at h
    injection h with h
    subst h
    rw [Poly.eval_var, Hypernet.Valuation.entryValM_even σ i w,
      Hypernet.Valuation.entryValC_eq σ (show σ.wireQ w = some q from heval) i]
  | const c =>
    intro p q h heval hpos i
    simp only [Term.asCoordPolyMixed?] at h
    injection h with h
    subst h
    injection heval with heval
    rw [← heval, Poly.eval_const, QTensor.brReadC_scalar rfl]
    rfl
  | add l r ihl ihr =>
    intro p q h heval hpos i
    simp only [Term.asCoordPolyMixed?, Option.bind_eq_bind] at h
    obtain ⟨pl, hpl, h⟩ := option_bind_eq_some' h
    obtain ⟨pr, hpr, h⟩ := option_bind_eq_some' h
    injection h with h
    subst h
    obtain ⟨a, b, ha, hb, hm⟩ := Term.evalQ_add_inv σ heval
    have hposl : ∀ w ∈ l.freeWires, ∃ τ, H.wireType w = some τ ∧
        0 < Shape.totalSize τ.shape :=
      fun w hw => hpos w (List.mem_append.mpr (Or.inl hw))
    have hposr : ∀ w ∈ r.freeWires, ∃ τ, H.wireType w = some τ ∧
        0 < Shape.totalSize τ.shape :=
      fun w hw => hpos w (List.mem_append.mpr (Or.inr hw))
    rw [Poly.eval_add, ← ihl hpl ha hposl i, ← ihr hpr hb hposr i]
    exact QTensor.map2_brReadC hm (Term.evalQ_pos σ ha hposl)
      (Term.evalQ_pos σ hb hposr) i
  | mul l r ihl ihr =>
    intro p q h heval hpos i
    simp only [Term.asCoordPolyMixed?, Option.bind_eq_bind] at h
    obtain ⟨pl, hpl, h⟩ := option_bind_eq_some' h
    obtain ⟨pr, hpr, h⟩ := option_bind_eq_some' h
    injection h with h
    subst h
    obtain ⟨a, b, ha, hb, hm⟩ := Term.evalQ_mul_inv σ heval
    have hposl : ∀ w ∈ l.freeWires, ∃ τ, H.wireType w = some τ ∧
        0 < Shape.totalSize τ.shape :=
      fun w hw => hpos w (List.mem_append.mpr (Or.inl hw))
    have hposr : ∀ w ∈ r.freeWires, ∃ τ, H.wireType w = some τ ∧
        0 < Shape.totalSize τ.shape :=
      fun w hw => hpos w (List.mem_append.mpr (Or.inr hw))
    rw [Poly.eval_mul, ← ihl hpl ha hposl i, ← ihr hpr hb hposr i]
    exact QTensor.map2_brReadC hm (Term.evalQ_pos σ ha hposl)
      (Term.evalQ_pos σ hb hposr) i
  | sub l r ihl ihr =>
    intro p q h heval hpos i
    simp only [Term.asCoordPolyMixed?, Option.bind_eq_bind] at h
    obtain ⟨pl, hpl, h⟩ := option_bind_eq_some' h
    obtain ⟨pr, hpr, h⟩ := option_bind_eq_some' h
    injection h with h
    subst h
    obtain ⟨a, b, ha, hb, hm⟩ := Term.evalQ_sub_inv σ heval
    have hposl : ∀ w ∈ l.freeWires, ∃ τ, H.wireType w = some τ ∧
        0 < Shape.totalSize τ.shape :=
      fun w hw => hpos w (List.mem_append.mpr (Or.inl hw))
    have hposr : ∀ w ∈ r.freeWires, ∃ τ, H.wireType w = some τ ∧
        0 < Shape.totalSize τ.shape :=
      fun w hw => hpos w (List.mem_append.mpr (Or.inr hw))
    rw [Poly.eval_sub, ← ihl hpl ha hposl i, ← ihr hpr hb hposr i]
    exact QTensor.map2_brReadC hm (Term.evalQ_pos σ ha hposl)
      (Term.evalQ_pos σ hb hposr) i
  | neg u ih =>
    intro p q h heval hpos i
    simp only [Term.asCoordPolyMixed?, Option.map_eq_some_iff] at h
    obtain ⟨pu, hpu, hp⟩ := h
    subst hp
    simp only [Term.evalQ, Option.map_eq_some_iff] at heval
    obtain ⟨qu, hqu, hq⟩ := heval
    subst hq
    have hposu : ∀ w ∈ u.freeWires, ∃ τ, H.wireType w = some τ ∧
        0 < Shape.totalSize τ.shape :=
      fun w hw => hpos w (by simpa [Term.freeWires] using hw)
    rw [Poly.eval_neg, ← ih hpu hqu hposu i]
    exact QTensor.map1_brReadC Neg.neg (Term.evalQ_pos σ hqu hposu) i
  | idx u j ih =>
    intro p q h heval hpos i
    obtain ⟨w, hw, hp⟩ := Term.asCoordPolyMixed?_idx_inv h
    subst hw
    subst hp
    simp only [Term.evalQ, Option.bind_eq_bind] at heval
    obtain ⟨qw, hqw, heval⟩ := option_bind_eq_some' heval
    split at heval
    · next e hqs =>
      split at heval
      · next hj =>
        injection heval with heval
        rw [← heval, Poly.eval_var,
          Hypernet.Valuation.entryValM_odd σ i
            (show σ.wireQ w = some qw from hqw) j,
          QTensor.brReadC_scalar rfl]
        rfl
      · cases heval
    · cases heval

theorem atomLeZeroPolysM_sound_entryC {H : Hypernet} (σ : H.Valuation)
    {F : Formula} (hF : Formula.holds σ F)
    (hw : ∀ w ∈ F.freeWires, ∃ τ, H.wireType w = some τ ∧
      0 < Shape.totalSize τ.shape) (i : ℕ) :
    ∀ pa ∈ atomLeZeroPolysM F, QArith.Poly.eval (σ.entryValM i) pa ≤ 0 := by
  intro pa hpa
  match F, hpa with
  | .atom op l r, hpa =>
    simp only [atomLeZeroPolysM] at hpa
    split at hpa
    · exact absurd hpa (List.not_mem_nil)
    · next pl hpl =>
      split at hpa
      · exact absurd hpa (List.not_mem_nil)
      · next pr hpr =>
        obtain ⟨al, ar, hal, har, hrel⟩ := hF
        have hwl : ∀ w ∈ l.freeWires, ∃ τ, H.wireType w = some τ ∧
            0 < Shape.totalSize τ.shape :=
          fun w hw' => hw w (List.mem_append.mpr (Or.inl hw'))
        have hwr : ∀ w ∈ r.freeWires, ∃ τ, H.wireType w = some τ ∧
            0 < Shape.totalSize τ.shape :=
          fun w hw' => hw w (List.mem_append.mpr (Or.inr hw'))
        have hvl := Term.evalQ_asCoordPolyMixed σ hpl hal hwl i
        have hvr := Term.evalQ_asCoordPolyMixed σ hpr har hwr i
        have hscal := QTensor.rel2_brReadC hrel
          (Term.evalQ_pos σ hal hwl) (Term.evalQ_pos σ har hwr) i
        rw [hvl, hvr] at hscal
        match op, hpa, hscal with
        | .le, hpa, hscal =>
          simp only [List.mem_singleton] at hpa
          subst hpa
          rw [Poly.eval_sub]
          have : QArith.Poly.eval (σ.entryValM i) pl
              ≤ QArith.Poly.eval (σ.entryValM i) pr := hscal
          linarith
        | .lt, hpa, hscal =>
          simp only [List.mem_singleton] at hpa
          subst hpa
          rw [Poly.eval_sub]
          have : QArith.Poly.eval (σ.entryValM i) pl
              < QArith.Poly.eval (σ.entryValM i) pr := hscal
          linarith
        | .ge, hpa, hscal =>
          simp only [List.mem_singleton] at hpa
          subst hpa
          rw [Poly.eval_sub]
          have : QArith.Poly.eval (σ.entryValM i) pr
              ≤ QArith.Poly.eval (σ.entryValM i) pl := hscal
          linarith
        | .gt, hpa, hscal =>
          simp only [List.mem_singleton] at hpa
          subst hpa
          rw [Poly.eval_sub]
          have : QArith.Poly.eval (σ.entryValM i) pr
              < QArith.Poly.eval (σ.entryValM i) pl := hscal
          linarith
        | .eq, hpa, hscal =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpa
          have heq : QArith.Poly.eval (σ.entryValM i) pl
              = QArith.Poly.eval (σ.entryValM i) pr := hscal
          rcases hpa with hpa | hpa
          · rw [hpa, Poly.eval_sub]
            linarith
          · rw [hpa, Poly.eval_sub]
            linarith

theorem sound_ax {H : Hypernet} {seq : Sequent}
    (h : seq.pre = seq.post) : seq.semanticallyValid H := by
  intro σ _ hpre
  rw [← h]
  exact hpre

theorem sound_weaken {H : Hypernet} {seq premise : Sequent} {extra : Formula}
    (ih : premise.semanticallyValid H)
    (hpre : seq.pre = .and premise.pre extra)
    (hpost : seq.post = premise.post) : seq.semanticallyValid H := by
  intro σ hadm hpre'
  rw [hpre] at hpre'
  rw [hpost]
  exact ih σ hadm hpre'.1

theorem sound_cut {H : Hypernet} {seq leftPremise rightPremise : Sequent}
    {cutFormula : Formula}
    (ihl : leftPremise.semanticallyValid H)
    (ihr : rightPremise.semanticallyValid H)
    (hpre : seq.pre = leftPremise.pre)
    (hpost : seq.post = rightPremise.post)
    (hcutL : leftPremise.post = cutFormula)
    (hcutR : rightPremise.pre = .and leftPremise.pre cutFormula) :
    seq.semanticallyValid H := by
  intro σ hadm hpre'
  rw [hpre] at hpre'
  rw [hpost]
  apply ihr σ hadm
  rw [hcutR]
  refine ⟨hpre', ?_⟩
  rw [← hcutL]
  exact ihl σ hadm hpre'

theorem sound_andI {H : Hypernet} {seq leftPremise rightPremise : Sequent}
    (ihl : leftPremise.semanticallyValid H)
    (ihr : rightPremise.semanticallyValid H)
    (hpreMatch : leftPremise.pre = rightPremise.pre)
    (hpre : seq.pre = leftPremise.pre)
    (hpost : seq.post = .and leftPremise.post rightPremise.post) :
    seq.semanticallyValid H := by
  intro σ hadm hpre'
  rw [hpre] at hpre'
  rw [hpost]
  refine ⟨ihl σ hadm hpre', ihr σ hadm ?_⟩
  rw [← hpreMatch]
  exact hpre'

theorem sound_andE_left {H : Hypernet} {seq premise : Sequent} {other : Formula}
    (ih : premise.semanticallyValid H)
    (hpre : seq.pre = premise.pre)
    (hpost : premise.post = .and seq.post other) :
    seq.semanticallyValid H := by
  intro σ hadm hpre'
  rw [hpre] at hpre'
  have h := ih σ hadm hpre'
  rw [hpost] at h
  exact h.1

theorem sound_andE_right {H : Hypernet} {seq premise : Sequent} {other : Formula}
    (ih : premise.semanticallyValid H)
    (hpre : seq.pre = premise.pre)
    (hpost : premise.post = .and other seq.post) :
    seq.semanticallyValid H := by
  intro σ hadm hpre'
  rw [hpre] at hpre'
  have h := ih σ hadm hpre'
  rw [hpost] at h
  exact h.2

theorem sound_orI_left {H : Hypernet} {seq premise : Sequent} {other : Formula}
    (ih : premise.semanticallyValid H)
    (hpre : seq.pre = premise.pre)
    (hpost : seq.post = .or premise.post other) :
    seq.semanticallyValid H := by
  intro σ hadm hpre'
  rw [hpre] at hpre'
  rw [hpost]
  exact Or.inl (ih σ hadm hpre')

theorem sound_orI_right {H : Hypernet} {seq premise : Sequent} {other : Formula}
    (ih : premise.semanticallyValid H)
    (hpre : seq.pre = premise.pre)
    (hpost : seq.post = .or other premise.post) :
    seq.semanticallyValid H := by
  intro σ hadm hpre'
  rw [hpre] at hpre'
  rw [hpost]
  exact Or.inr (ih σ hadm hpre')

theorem sound_orE {H : Hypernet} {seq leftPremise rightPremise : Sequent}
    (ihl : leftPremise.semanticallyValid H)
    (ihr : rightPremise.semanticallyValid H)
    (hpostMatch : leftPremise.post = rightPremise.post)
    (hpre : seq.pre = .or leftPremise.pre rightPremise.pre)
    (hpost : seq.post = leftPremise.post) :
    seq.semanticallyValid H := by
  intro σ hadm hpre'
  rw [hpre] at hpre'
  rw [hpost]
  rcases hpre' with h | h
  · exact ihl σ hadm h
  · rw [hpostMatch]
    exact ihr σ hadm h

theorem sound_eqElim {H : Hypernet} {seq eqPremise bodyPremise : Sequent}
    {wire : Wire} {termT termU : Term} {bodyForm : Formula}
    (ihEq : eqPremise.semanticallyValid H)
    (ihBody : bodyPremise.semanticallyValid H)
    (hpre : seq.pre = eqPremise.pre)
    (hpreMatch : eqPremise.pre = bodyPremise.pre)
    (heqPost : eqPremise.post = .atom .eq termT termU)
    (htyEq : ∃ s, termT.bshape H = some s ∧ termU.bshape H = some s)
    (hbodySubT : substituteInFormula bodyForm wire termT bodyPremise.post)
    (hconclSubU : substituteInFormula bodyForm wire termU seq.post) :
    seq.semanticallyValid H := by
  intro σ hadm hpre'
  rw [hpre] at hpre'
  have heq := ihEq σ hadm hpre'
  rw [heqPost] at heq
  obtain ⟨aT, aU, haT, haU, hrel⟩ := heq
  obtain ⟨s, hbT, hbU⟩ := htyEq
  have hsT := Term.evalQ_bshape σ termT s aT hbT haT
  have hsU := Term.evalQ_bshape σ termU s aU hbU haU
  have hteq : aT = aU :=
    QTensor.eq_of_rel2 (fun _ _ h => h) (by rw [hsT, hsU]) hrel
  have hEvEq : Term.evalQ σ termT = Term.evalQ σ termU := by
    rw [haT, haU, hteq]
  have hbody := ihBody σ hadm (by rw [← hpreMatch]; exact hpre')
  rw [hbodySubT] at hbody
  rw [hconclSubU]
  exact (Formula.holds_subst_congr σ hEvEq bodyForm).mp hbody

theorem sound_arithAtom_fold {H : Hypernet} {seq premise : Sequent}
    {termL termR : Term} {b : BowTie}
    (ih : premise.semanticallyValid H)
    (hpre : seq.pre = premise.pre)
    (hprem : atomicCompareZero b termL termR premise.post)
    (hconcl : atomicCompareForm b termL termR seq.post) :
    seq.semanticallyValid H := by
  intro σ hadm hpre'
  rw [hpre] at hpre'
  have hp := ih σ hadm hpre'
  rw [hprem] at hp
  rw [hconcl]
  obtain ⟨d, z, hd, hz, hrel⟩ := hp
  have hzz : z = ⟨[], [0], rfl⟩ := by
    have h' : some (⟨[], [0], rfl⟩ : QTensor) = some z := hz
    injection h' with h'
    exact h'.symm
  subst hzz
  obtain ⟨al, ar, hal, har, hmap⟩ := Term.evalQ_sub_inv σ hd
  exact ⟨al, ar, hal, har, (QTensor.rel2_sub_zero_iff hmap).mp hrel⟩

theorem sound_arithAtom_unfold {H : Hypernet} {seq premise : Sequent}
    {termL termR : Term} {b : BowTie}
    (ih : premise.semanticallyValid H)
    (hpre : seq.pre = premise.pre)
    (hprem : atomicCompareForm b termL termR premise.post)
    (hconcl : atomicCompareZero b termL termR seq.post) :
    seq.semanticallyValid H := by
  intro σ hadm hpre'
  rw [hpre] at hpre'
  have hp := ih σ hadm hpre'
  rw [hprem] at hp
  rw [hconcl]
  obtain ⟨al, ar, hal, har, hrel⟩ := hp
  obtain ⟨d, hmap⟩ := QTensor.map2_defined_of_rel2 hrel (· - ·)
  refine ⟨d, ⟨[], [0], rfl⟩, ?_, rfl, ?_⟩
  · simp only [Term.evalQ, Option.bind_eq_bind, hal, har, Option.bind_some]
    exact hmap
  · exact (QTensor.rel2_sub_zero_iff hmap).mpr hrel

theorem sound_farkas {H : Hypernet} {seq : Sequent}
    {combinationCoeffs conclusion : Term}
    (hshape : ∃ s, conclusion.bshape H = some s)
    (hfin : conclusion.finWires H)
    (hwpos : ∀ w ∈ seq.pre.freeWires ++ conclusion.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
    (hvalid : farkasCombinationValid combinationCoeffs seq.pre conclusion)
    (hpost : seq.post = .atom .le conclusion (.const 0)) :
    seq.semanticallyValid H := by
  intro σ hadm hpre'
  rw [hpost]
  unfold farkasCombinationValid farkasCheck at hvalid
  rw [Bool.or_eq_true, Bool.or_eq_true] at hvalid
  rcases hvalid with (hvalid | hvalid) | hvalid

  · unfold farkasCheckCore at hvalid
    split at hvalid
    · cases hvalid
    · next entries hentries =>
      rw [Bool.and_eq_true] at hvalid
      obtain ⟨hvalid, hsum⟩ := hvalid
      rw [Bool.and_eq_true] at hvalid
      obtain ⟨hcix, hall⟩ := hvalid
      have hsum' := of_decide_eq_true hsum

      obtain ⟨s, hs⟩ := hshape
      have hcw := wire_discipline_of_bshape_fin σ hs hfin hcix
      obtain ⟨qc, hqc⟩ : ∃ qc, Term.evalQ σ conclusion = some qc := by
        by_cases hsnil : s = []
        · subst hsnil
          have hsing : ∀ w ∈ conclusion.freeWires, ∃ qw,
              σ.wireQ w = some qw ∧ SingletonShape qw.shape := by
            intro w hw
            obtain ⟨qw, hqw, hqs⟩ := hcw w hw
            exact ⟨qw, hqw, by
              rcases hqs with h1 | h1
              · exact Or.inl h1
              · exact Or.inl h1⟩
          obtain ⟨qc, hqc, _, _⟩ := Term.evalQ_total_singleton σ conclusion hsing hcix
          exact ⟨qc, hqc⟩
        · obtain ⟨qc, hqc, _, _, _⟩ := Term.evalQ_brRead σ s conclusion hcw hcix
          exact ⟨qc, hqc⟩
      refine ⟨qc, ⟨[], [0], rfl⟩, hqc, rfl, ?_⟩
      apply QTensor.rel2_const_right
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx

      have hposC : ∀ w ∈ conclusion.freeWires, ∀ qw,
          σ.wireQ w = some qw → 0 < Shape.totalSize qw.shape :=
        fun w hw qw hqw => wireQ_pos_of_type_pos σ hqw
          (hwpos w (List.mem_append.mpr (Or.inr hw)))
      have hcr := Term.evalQ_brReadC σ hqc hposC hcix i
      have hx' : qc.entries[i] = qc.brReadC i := by
        rw [QTensor.brReadC_in_range hi, List.getD_eq_getElem _ _ hi]
      show qc.entries[i] ≤ QTensor.scalar ⟨[], [0], rfl⟩
      rw [hx', hcr]
      show QArith.Poly.eval (σ.entryValC i) conclusion.toPoly ≤ 0
      rw [← hsum']
      apply farkas_fold_eval_nonpos
      intro e he
      have h1 := List.all_eq_true.mp hall e he
      rw [Bool.and_eq_true] at h1
      obtain ⟨hle, hany⟩ := h1
      refine ⟨of_decide_eq_true hle, ?_⟩
      obtain ⟨aF, haF, hpa⟩ := List.any_eq_true.mp hany
      rw [Bool.and_eq_true] at hpa
      obtain ⟨haix, hpa⟩ := hpa
      obtain ⟨pa, hpaMem, hpaEq⟩ := List.any_eq_true.mp hpa
      have hpaEq' : pa = e.2.toPoly := of_decide_eq_true hpaEq
      have haHolds := Formula.holds_of_mem_conjunctList σ seq.pre hpre' aF haF
      rw [← hpaEq']
      apply atomLeZeroPolys_sound_entryC σ haHolds ?_ haix i pa hpaMem
      intro w hw
      exact hwpos w (List.mem_append.mpr (Or.inl
        (Formula.freeWires_of_mem_conjunctList seq.pre aF haF w hw)))

  · unfold farkasCheckW at hvalid
    split at hvalid
    · cases hvalid
    · next entries hentries =>
      split at hvalid
      · cases hvalid
      · next pentries hpents =>
        split at hvalid
        · cases hvalid
        · next pc hpc =>
          rw [Bool.and_eq_true] at hvalid
          obtain ⟨hall, hsum⟩ := hvalid
          have hsum' := of_decide_eq_true hsum
          obtain ⟨s, hs⟩ := hshape
          obtain ⟨qc, hqc, -⟩ :=
            Term.evalQ_defined_of_bshape_fin σ conclusion s hs hfin
          have hqcform := Term.evalQ_asCoordPolyIdxW σ hpc hqc
          subst hqcform
          refine ⟨_, ⟨[], [0], rfl⟩, hqc, rfl, ?_⟩
          rw [QTensor.rel2_scalars]
          show QArith.Poly.eval σ.coordValW pc ≤ 0
          rw [← hsum']
          apply farkas_fold_eval_nonpos_polys
          intro e he
          have h1 := List.all_eq_true.mp hall e he
          rw [Bool.and_eq_true] at h1
          obtain ⟨hle, hany⟩ := h1
          refine ⟨of_decide_eq_true hle, ?_⟩
          obtain ⟨aF, haF, hpa⟩ := List.any_eq_true.mp hany
          obtain ⟨pa, hpaMem, hpaEq⟩ := List.any_eq_true.mp hpa
          have hpaEq' : pa = e.2 := of_decide_eq_true hpaEq
          have haHolds := Formula.holds_of_mem_conjunctList σ seq.pre hpre' aF haF
          rw [← hpaEq']
          exact atomLeZeroPolysW_sound σ haHolds pa hpaMem

  · unfold farkasCheckM at hvalid
    split at hvalid
    · cases hvalid
    · next entries hentries =>
      split at hvalid
      · cases hvalid
      · next pentries hpents =>
        split at hvalid
        · cases hvalid
        · next pc hpc =>
          rw [Bool.and_eq_true] at hvalid
          obtain ⟨hall, hsum⟩ := hvalid
          have hsum' := of_decide_eq_true hsum
          obtain ⟨s, hs⟩ := hshape
          obtain ⟨qc, hqc, -⟩ :=
            Term.evalQ_defined_of_bshape_fin σ conclusion s hs hfin
          refine ⟨qc, ⟨[], [0], rfl⟩, hqc, rfl, ?_⟩
          apply QTensor.rel2_const_right
          intro x hx
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
          have hposC : ∀ w ∈ conclusion.freeWires, ∃ τ,
              H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape :=
            fun w hw => hwpos w (List.mem_append.mpr (Or.inr hw))
          have hcr := Term.evalQ_asCoordPolyMixed σ hpc hqc hposC i
          have hx' : qc.entries[i] = qc.brReadC i := by
            rw [QTensor.brReadC_in_range hi, List.getD_eq_getElem _ _ hi]
          show qc.entries[i] ≤ QTensor.scalar ⟨[], [0], rfl⟩
          rw [hx', hcr]
          show QArith.Poly.eval (σ.entryValM i) pc ≤ 0
          rw [← hsum']
          apply farkas_fold_eval_nonpos_polys
          intro e he
          have h1 := List.all_eq_true.mp hall e he
          rw [Bool.and_eq_true] at h1
          obtain ⟨hle, hany⟩ := h1
          refine ⟨of_decide_eq_true hle, ?_⟩
          obtain ⟨aF, haF, hpa⟩ := List.any_eq_true.mp hany
          obtain ⟨pa, hpaMem, hpaEq⟩ := List.any_eq_true.mp hpa
          have hpaEq' : pa = e.2 := of_decide_eq_true hpaEq
          have haHolds := Formula.holds_of_mem_conjunctList σ seq.pre hpre' aF haF
          rw [← hpaEq']
          apply atomLeZeroPolysM_sound_entryC σ haHolds ?_ i pa hpaMem
          intro w hw
          exact hwpos w (List.mem_append.mpr (Or.inl
            (Formula.freeWires_of_mem_conjunctList seq.pre aF haF w hw)))

theorem sound_norm {H : Hypernet} {seq : Sequent} {termL termR : Term}
    (hcanon : polynomialCanonicalEq termL termR)
    (htyEq : termL.bshape H = termR.bshape H)
    (htyDef : ∃ s, termL.bshape H = some s)
    (hfinL : termL.finWires H) (hfinR : termR.finWires H)
    (hpost : seq.post = .atom .eq termL termR) :
    seq.semanticallyValid H := by
  intro σ hadm _
  rw [hpost]
  obtain ⟨s, hsL⟩ := htyDef
  have hsR : termR.bshape H = some s := by
    rw [← htyEq]
    exact hsL
  obtain ⟨hixL, hixR, hcanon'⟩ := hcanon
  have hLw := wire_discipline_of_bshape_fin σ hsL hfinL hixL
  have hRw := wire_discipline_of_bshape_fin σ hsR hfinR hixR
  by_cases hsnil : s = []
  ·
    subst hsnil
    have hLsing : ∀ w ∈ termL.freeWires, ∃ qw,
        σ.wireQ w = some qw ∧ SingletonShape qw.shape := by
      intro w hw
      obtain ⟨qw, hqw, hqs⟩ := hLw w hw
      exact ⟨qw, hqw, by
        rcases hqs with h1 | h1
        · exact Or.inl h1
        · exact Or.inl h1⟩
    have hRsing : ∀ w ∈ termR.freeWires, ∃ qw,
        σ.wireQ w = some qw ∧ SingletonShape qw.shape := by
      intro w hw
      obtain ⟨qw, hqw, hqs⟩ := hRw w hw
      exact ⟨qw, hqw, by
        rcases hqs with h1 | h1
        · exact Or.inl h1
        · exact Or.inl h1⟩
    obtain ⟨qL, hqL, hsingL, hvalL⟩ :=
      Term.evalQ_total_singleton σ termL hLsing hixL
    obtain ⟨qR, hqR, hsingR, hvalR⟩ :=
      Term.evalQ_total_singleton σ termR hRsing hixR
    refine ⟨qL, qR, hqL, hqR, ?_⟩
    rw [QTensor.rel2_singleton hsingL hsingR]
    show qL.scalar = qR.scalar
    rw [hvalL, hvalR, hcanon']
  ·

    obtain ⟨qL, hqL, _, _, heL⟩ := Term.evalQ_brRead σ s termL hLw hixL
    obtain ⟨qR, hqR, _, _, heR⟩ := Term.evalQ_brRead σ s termR hRw hixR
    have hqLs : qL.shape = s := Term.evalQ_bshape σ termL s qL hsL hqL
    have hqRs : qR.shape = s := Term.evalQ_bshape σ termR s qR hsR hqR
    refine ⟨qL, qR, hqL, hqR, ?_⟩
    unfold QTensor.rel2
    rw [if_pos (hqLs.trans hqRs.symm)]
    intro p hp
    obtain ⟨k, hk, hpk⟩ := List.mem_iff_getElem.mp hp
    rw [List.length_zip] at hk
    have hkL : k < qL.entries.length := by omega
    have hkR : k < qR.entries.length := by omega
    have hkS : k < Shape.totalSize s := by
      rw [← hqLs, ← qL.len_eq]
      exact hkL
    have hpair : p = (qL.entries[k]'hkL, qR.entries[k]'hkR) := by
      rw [← hpk, List.getElem_zip]
    rw [hpair]
    show BowTie.holdsQ .eq (qL.entries[k]'hkL) (qR.entries[k]'hkR)
    show qL.entries[k]'hkL = qR.entries[k]'hkR
    have hbrL : qL.brRead k = qL.entries[k]'hkL := by
      rw [QTensor.brRead_pos (by rw [hqLs]; exact hsnil) k,
        List.getD_eq_getElem _ _ hkL]
    have hbrR : qR.brRead k = qR.entries[k]'hkR := by
      rw [QTensor.brRead_pos (by rw [hqRs]; exact hsnil) k,
        List.getD_eq_getElem _ _ hkR]
    rw [← hbrL, ← hbrR, heL k hkS, heR k hkS, hcanon']

theorem affine_evalQ {H : Hypernet} (σ : H.Valuation) {t : Term} {q : QTensor}
    (hq : Term.evalQ σ t = some q) (hsq : SingletonShape q.shape) (c s : ℚ) :
    ∃ qa, Term.evalQ σ (.add (.const c) (.mul (.const s) t)) = some qa ∧
      SingletonShape qa.shape ∧ qa.scalar = c + s * q.scalar := by
  obtain ⟨m, hm, hsm, hvm⟩ :=
    QTensor.map2_singleton (f := (· * ·)) (a := (⟨[], [s], rfl⟩ : QTensor))
      (b := q) (Or.inl rfl) hsq
  obtain ⟨qa, hqa, hsqa, hvqa⟩ :=
    QTensor.map2_singleton (f := (· + ·)) (a := (⟨[], [c], rfl⟩ : QTensor))
      (b := m) (Or.inl rfl) hsm
  refine ⟨qa, ?_, hsqa, ?_⟩
  · simp only [Term.evalQ, Option.bind_eq_bind, hq, Option.bind_some]
    rw [hm]
    simp only [Option.bind_some]
    exact hqa
  · rw [hvqa, hvm]
    rfl

theorem affine_evalQ_inv {H : Hypernet} (σ : H.Valuation) {t : Term} {c s : ℚ}
    {qa : QTensor}
    (h : Term.evalQ σ (.add (.const c) (.mul (.const s) t)) = some qa) :
    ∃ q, Term.evalQ σ t = some q := by
  obtain ⟨c1, m1, hc1, hm1, _⟩ := Term.evalQ_add_inv σ h
  obtain ⟨s1, q, hs1, hq, _⟩ := Term.evalQ_mul_inv σ hm1
  exact ⟨q, hq⟩

theorem sound_convIntro {H : Hypernet} {seq premise : Sequent}
    {term : Term} {simplex : Simplex} {S : ExtensionSet}
    (ih : premise.semanticallyValid H)
    (hpre : seq.pre = premise.pre)
    (htermShape : term.bshape H = some [simplex.complex.ambDim])
    (hhalf : barycentricHalfspaceForm term simplex S premise.post)
    (hpost : seq.post = .inRegion term simplex S) :
    seq.semanticallyValid H := by
  obtain ⟨hSsimp, hd1, a, b, V₀, V₁, hfil, hVa, hVb, hVne, hF⟩ :=
    barycentricHalfspaceBuild_spec hhalf
  subst hSsimp
  intro σ hadm hpre'
  rw [hpre] at hpre'
  have hbar := ih σ hadm hpre'
  rw [hF] at hbar
  obtain ⟨hA, hB⟩ := hbar

  obtain ⟨q, hq⟩ := f4VertexAtom_holds_inv hA
  have hqshape := Term.evalQ_bshape σ term _ q htermShape hq
  have hqsing : SingletonShape q.shape := by
    rw [hqshape, hd1]
    exact Or.inr rfl

  rw [f4VertexAtom_holds_iff hq hqsing] at hA
  rw [f4VertexAtom_holds_iff hq hqsing] at hB

  rw [hpost]
  have hd1' : 0 < S.simplex.complex.ambDim := by omega
  refine ⟨rfl, q, hq, hqshape, ?_⟩
  refine maskRegion_pair_intro hfil hVa hVb hVne hd1 ⟨0, hd1'⟩ ?_ ?_ ?_ ?_
  ·
    intro hexta
    have hcn : S.containsNat a.val = true := by
      rw [ExtensionSet.containsNat_val]
      exact hexta
    rw [if_pos hcn] at hA
    have harith : V₁ / (V₁ - V₀) + -1 / (V₁ - V₀) * q.scalar
        = (V₁ - q.scalar) / (V₁ - V₀) := by
      ring
    show (V₁ - q.scalar) / (V₁ - V₀) ≤ 0
    rw [← harith]
    exact hA
  ·
    intro hexta
    have hcn : S.containsNat a.val = false := by
      rw [ExtensionSet.containsNat_val]
      exact hexta
    rw [hcn] at hA
    have hA' : (0 : ℚ) ≤ V₁ / (V₁ - V₀) + -1 / (V₁ - V₀) * q.scalar := hA
    have harith : V₁ / (V₁ - V₀) + -1 / (V₁ - V₀) * q.scalar
        = (V₁ - q.scalar) / (V₁ - V₀) := by
      ring
    show (0 : ℚ) ≤ (V₁ - q.scalar) / (V₁ - V₀)
    rw [← harith]
    exact hA'
  · intro hextb
    have hcn : S.containsNat b.val = true := by
      rw [ExtensionSet.containsNat_val]
      exact hextb
    rw [if_pos hcn] at hB
    have harith : -V₀ / (V₁ - V₀) + 1 / (V₁ - V₀) * q.scalar
        = (q.scalar - V₀) / (V₁ - V₀) := by
      ring
    show (q.scalar - V₀) / (V₁ - V₀) ≤ 0
    rw [← harith]
    exact hB
  · intro hextb
    have hcn : S.containsNat b.val = false := by
      rw [ExtensionSet.containsNat_val]
      exact hextb
    rw [hcn] at hB
    have hB' : (0 : ℚ) ≤ -V₀ / (V₁ - V₀) + 1 / (V₁ - V₀) * q.scalar := hB
    have harith : -V₀ / (V₁ - V₀) + 1 / (V₁ - V₀) * q.scalar
        = (q.scalar - V₀) / (V₁ - V₀) := by
      ring
    show (0 : ℚ) ≤ (q.scalar - V₀) / (V₁ - V₀)
    rw [← harith]
    exact hB'

theorem sound_convElim {H : Hypernet} {seq premise : Sequent}
    {term : Term} {simplex : Simplex} {S : ExtensionSet}
    (ih : premise.semanticallyValid H)
    (hpre : seq.pre = premise.pre)
    (hpremiseForm : premise.post = .inRegion term simplex S)
    (hhalf : barycentricHalfspaceForm term simplex S seq.post) :
    seq.semanticallyValid H := by
  obtain ⟨hSsimp, hd1, a, b, V₀, V₁, hfil, hVa, hVb, hVne, hF⟩ :=
    barycentricHalfspaceBuild_spec hhalf
  subst hSsimp
  intro σ hadm hpre'
  rw [hpre] at hpre'
  have hreg := ih σ hadm hpre'
  rw [hpremiseForm] at hreg
  obtain ⟨-, q, hq, hqshape, hmask⟩ := hreg
  have hqsing : SingletonShape q.shape := by
    rw [hqshape, hd1]
    exact Or.inr rfl
  have hd1' : 0 < S.simplex.complex.ambDim := by omega
  have hsigns := maskRegion_pair_elim hfil hVa hVb hVne ⟨0, hd1'⟩ hmask

  obtain ⟨hs1, hs2, hs3, hs4⟩ := hsigns
  rw [hF]
  constructor
  ·
    rw [f4VertexAtom_holds_iff hq hqsing]
    have harith : V₁ / (V₁ - V₀) + -1 / (V₁ - V₀) * q.scalar
        = (V₁ - q.scalar) / (V₁ - V₀) := by
      ring
    by_cases hexta : S.contains a = true
    · have hcn : S.containsNat a.val = true := by
        rw [ExtensionSet.containsNat_val]
        exact hexta
      rw [if_pos hcn, harith]
      exact hs1 hexta
    · have hexta' : S.contains a = false := by
        cases h : S.contains a
        · rfl
        · exact absurd h hexta
      have hcn : S.containsNat a.val = false := by
        rw [ExtensionSet.containsNat_val]
        exact hexta'
      rw [hcn]
      show (0 : ℚ) ≤ V₁ / (V₁ - V₀) + -1 / (V₁ - V₀) * q.scalar
      rw [harith]
      exact hs2 hexta'
  ·
    rw [f4VertexAtom_holds_iff hq hqsing]
    have harith : -V₀ / (V₁ - V₀) + 1 / (V₁ - V₀) * q.scalar
        = (q.scalar - V₀) / (V₁ - V₀) := by
      ring
    by_cases hextb : S.contains b = true
    · have hcn : S.containsNat b.val = true := by
        rw [ExtensionSet.containsNat_val]
        exact hextb
      rw [if_pos hcn, harith]
      exact hs3 hextb
    · have hextb' : S.contains b = false := by
        cases h : S.contains b
        · rfl
        · exact absurd h hextb
      have hcn : S.containsNat b.val = false := by
        rw [ExtensionSet.containsNat_val]
        exact hextb'
      rw [hcn]
      show (0 : ℚ) ≤ -V₀ / (V₁ - V₀) + 1 / (V₁ - V₀) * q.scalar
      rw [harith]
      exact hs4 hextb'

theorem sum_indicator_head (n : Nat) (hn : 1 ≤ n) :
    ((List.range n).map (fun i => if i = 0 then (1 : ℚ) else 0)).sum = 1 := by
  cases n with
  | zero => omega
  | succ m =>
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, if_pos rfl,
      List.map_map]
    have hz : ((List.range m).map
        ((fun i => if i = 0 then (1 : ℚ) else 0) ∘ Nat.succ)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      simp [Function.comp]
    rw [hz]
    ring

theorem kernel_evalpt_pair (la lb : List ℚ) (w₀ w₁ : ℚ) (j : Nat) :
    ((List.range ([la, lb] : List (List ℚ)).length).map
      (fun i => (([la, lb] : List (List ℚ)).getD i []).getD j 0 *
        (if i = 0 then w₀ else if i = 1 then w₁ else 0))).sum
      = la.getD j 0 * w₀ + lb.getD j 0 * w₁ := by
  show ((List.range 2).map _).sum = _
  rw [show List.range 2 = [0, 1] from rfl]
  simp

theorem list_sum_filter_support {M : Type*} [AddCommMonoid M]
    {α : Type*} (mask : α → Bool) (f : α → M) :
    ∀ (l : List α), (∀ a ∈ l, mask a = false → f a = 0) →
    (l.map f).sum = ((l.filter (fun a => mask a)).map f).sum := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons hd tl ih =>
    intro hz
    rw [List.map_cons, List.sum_cons, List.filter_cons]
    cases hmask : mask hd with
    | true =>
      simp only [hmask, if_true]
      rw [List.map_cons, List.sum_cons,
        ih (fun a ha hm => hz a (List.mem_cons_of_mem hd ha) hm)]
    | false =>
      simp only [hmask, Bool.false_eq_true, if_false]
      rw [hz hd List.mem_cons_self hmask, zero_add,
        ih (fun a ha hm => hz a (List.mem_cons_of_mem hd ha) hm)]

theorem list_map_sum_eq_fin_sum {M : Type*} [AddCommMonoid M]
    {α : Type*} (f : α → M) :
    ∀ (l : List α), (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  intro l
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.sum_cons, ih]
    show _ = ∑ i : Fin (tl.length + 1), f ((hd :: tl).get i)
    rw [Fin.sum_univ_succ]
    rfl

theorem maskRegion_rat_weights {C : SimpC}
    {mask ext : Fin C.nVertices → Bool} {x : Fin C.ambDim → ℚ}
    (hmask : MaskRegion C mask ext x)
    (hext0 : ∀ v, ext v = false) :
    ∃ qw : Fin ((List.finRange C.nVertices).filter
        (fun v => mask v)).length → ℚ,
      (∀ i, 0 ≤ qw i) ∧ (∑ i, qw i) = 1 ∧
      ∀ j : Fin C.ambDim,
        (∑ i, qw i * C.coord (((List.finRange C.nVertices).filter
          (fun v => mask v)).get i) j) = x j := by
  classical
  obtain ⟨lam, hsupp0, hsum1, hcoords, _, hcore⟩ := hmask
  have hmemL : ∀ i : Fin ((List.finRange C.nVertices).filter
      (fun v => mask v)).length,
      mask (((List.finRange C.nVertices).filter (fun v => mask v)).get i)
        = true :=
    fun i => (List.mem_filter.mp (List.get_mem _ i)).2
  set L := (List.finRange C.nVertices).filter (fun v => mask v) with hL

  set A : Fin L.length → Fin (C.ambDim + 1) → ℚ :=
    fun i => Fin.snoc (fun jn => C.coord (L.get i) jn) 1 with hA
  set bvec : Fin (C.ambDim + 1) → ℚ := Fin.snoc x 1 with hb

  have hlamL : ∀ (F : Fin C.nVertices → ℝ),
      (∀ v, mask v = false → F v = 0) →
      finSum C.nVertices F = ∑ i : Fin L.length, F (L.get i) := by
    intro F hF
    show ((List.finRange C.nVertices).map F).sum = _
    rw [list_sum_filter_support mask F _ (fun a _ hm => hF a hm), ← hL,
      list_map_sum_eq_fin_sum]
  have hcsol : ∀ j, (∑ i, lam (L.get i) * ((A i j : ℚ) : ℝ))
      = ((bvec j : ℚ) : ℝ) := by
    intro j
    induction j using Fin.lastCases with
    | last =>
      simp only [hA, hb, Fin.snoc_last]
      push_cast
      simp only [mul_one]
      rw [← hlamL lam hsupp0]
      exact hsum1
    | cast jn =>
      simp only [hA, hb, Fin.snoc_castSucc]
      rw [← hlamL (fun v => lam v * (C.coord v jn : ℝ))
        (fun v hv => by rw [hsupp0 v hv, zero_mul])]
      exact hcoords jn

  obtain ⟨qw, hqw0, hqwsol⟩ := ConvexRat.exists_nonneg_rat_solution
    A bvec (fun i => lam (L.get i))
    (fun i => hcore (L.get i) (hmemL i) (hext0 (L.get i)))
    hcsol
  refine ⟨qw, hqw0, ?_, ?_⟩
  · have := hqwsol (Fin.last C.ambDim)
    simp only [hA, hb, Fin.snoc_last, mul_one] at this
    exact this
  · intro jn
    have := hqwsol (Fin.castSucc jn)
    simp only [hA, hb, Fin.snoc_castSucc] at this
    exact this

theorem kernel_evalpt_coords {C : SimpC} (Lv : List (Fin C.nVertices))
    (ρ : Nat → ℚ) (qw : Fin Lv.length → ℚ)
    (hρmem : ∀ (i : Nat) (h : i < Lv.length), ρ i = qw ⟨i, h⟩) (j : Nat) :
    ((List.range (Lv.map (fun v => (List.finRange C.ambDim).map
        fun jf => C.coord v jf)).length).map
      (fun i => ((Lv.map (fun v => (List.finRange C.ambDim).map
        fun jf => C.coord v jf)).getD i []).getD j 0 * ρ i)).sum
    = if hj : j < C.ambDim
      then ∑ i : Fin Lv.length, qw i * C.coord (Lv.get i) ⟨j, hj⟩
      else 0 := by
  rw [List.length_map]
  show (∑ i ∈ Finset.range Lv.length,
    ((Lv.map (fun v => (List.finRange C.ambDim).map
      fun jf => C.coord v jf)).getD i []).getD j 0 * ρ i) = _
  rw [← Fin.sum_univ_eq_sum_range]
  have hrow : ∀ i : Fin Lv.length,
      (Lv.map (fun v => (List.finRange C.ambDim).map
        fun jf => C.coord v jf)).getD i.val []
      = (List.finRange C.ambDim).map (fun jf => C.coord (Lv.get i) jf) := by
    intro i
    rw [List.getD_eq_getElem _ _ (by
      rw [List.length_map]
      exact i.isLt), List.getElem_map]
    rw [List.get_eq_getElem]
  split
  · next hj =>
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hρmem i.val i.isLt, Fin.eta, hrow i]
    rw [List.getD_eq_getElem _ _ (by
      rw [List.length_map, List.length_finRange]
      exact hj), List.getElem_map]
    rw [mul_comm]
    congr 1
    congr 1
    apply Fin.ext
    simp
  · next hj =>
    apply Finset.sum_eq_zero
    intro i _
    rw [hrow i, List.getD_eq_default, zero_mul]
    rw [List.length_map, List.length_finRange]
    omega

theorem Term.asCoordPolyIdx?_idx_inv {t : Term} {i : Nat}
    {p : QArith.Poly} (h : Term.asCoordPolyIdx? (.idx t i) = some p) :
    (∃ w, t = .var w) ∧ p = QArith.Poly.var i := by
  cases t with
  | var w =>
    refine ⟨⟨w, rfl⟩, ?_⟩
    simp only [Term.asCoordPolyIdx?] at h
    injection h with h
    exact h.symm
  | const c => cases h
  | add l r => cases h
  | mul l r => cases h
  | sub l r => cases h
  | neg u => cases h
  | idx u i' => cases h

theorem Term.asCoordPolyIdx?_idxFree_of_no_wires :
    ∀ {t : Term} {p : QArith.Poly}, Term.asCoordPolyIdx? t = some p →
    t.freeWires = [] → t.idxFree = true := by
  intro t
  induction t with
  | var w => intro p h _; cases h
  | const c => intro p _ _; rfl
  | add l r ihl ihr =>
    intro p h hfw
    simp only [Term.asCoordPolyIdx?, Option.bind_eq_bind] at h
    obtain ⟨pl, hpl, h⟩ := option_bind_eq_some' h
    obtain ⟨pr, hpr, _⟩ := option_bind_eq_some' h
    show (l.idxFree && r.idxFree) = true
    rw [Bool.and_eq_true]
    exact ⟨ihl hpl (List.append_eq_nil_iff.mp hfw).1,
           ihr hpr (List.append_eq_nil_iff.mp hfw).2⟩
  | mul l r ihl ihr =>
    intro p h hfw
    simp only [Term.asCoordPolyIdx?, Option.bind_eq_bind] at h
    obtain ⟨pl, hpl, h⟩ := option_bind_eq_some' h
    obtain ⟨pr, hpr, _⟩ := option_bind_eq_some' h
    show (l.idxFree && r.idxFree) = true
    rw [Bool.and_eq_true]
    exact ⟨ihl hpl (List.append_eq_nil_iff.mp hfw).1,
           ihr hpr (List.append_eq_nil_iff.mp hfw).2⟩
  | sub l r ihl ihr =>
    intro p h hfw
    simp only [Term.asCoordPolyIdx?, Option.bind_eq_bind] at h
    obtain ⟨pl, hpl, h⟩ := option_bind_eq_some' h
    obtain ⟨pr, hpr, _⟩ := option_bind_eq_some' h
    show (l.idxFree && r.idxFree) = true
    rw [Bool.and_eq_true]
    exact ⟨ihl hpl (List.append_eq_nil_iff.mp hfw).1,
           ihr hpr (List.append_eq_nil_iff.mp hfw).2⟩
  | neg u ih =>
    intro p h hfw
    simp only [Term.asCoordPolyIdx?, Option.map_eq_some_iff] at h
    obtain ⟨pu, hpu, _⟩ := h
    show u.idxFree = true
    exact ih hpu hfw
  | idx u i ih =>
    intro p h hfw
    obtain ⟨⟨w, hw⟩, -⟩ := Term.asCoordPolyIdx?_idx_inv h
    subst hw
    cases hfw

theorem Term.evalQ_asCoordPolyIdx {H : Hypernet} (σ : H.Valuation)
    {w : Wire} {q : QTensor} {n : Nat}
    (hwq : σ.wireQ w = some q) (hqs : q.shape = [n]) :
    ∀ {t : Term} {p : QArith.Poly},
    Term.asCoordPolyIdx? t = some p →
    (∀ w' ∈ t.freeWires, w' = w) →
    t.idxBounded n = true →
    Term.evalQ σ t
      = some ⟨[], [QArith.Poly.eval (fun j => q.entries.getD j 0) p], rfl⟩ := by
  intro t
  induction t with
  | var w' => intro p h _ _; cases h
  | const c =>
    intro p h _ _
    simp only [Term.asCoordPolyIdx?] at h
    injection h with h
    subst h
    rw [QTensor.scalar_mk_congr (Poly.eval_const _ c)]
    rfl
  | add l r ihl ihr =>
    intro p h hws hbd
    simp only [Term.asCoordPolyIdx?, Option.bind_eq_bind] at h
    obtain ⟨pl, hpl, h⟩ := option_bind_eq_some' h
    obtain ⟨pr, hpr, h⟩ := option_bind_eq_some' h
    injection h with h
    subst h
    simp only [Term.idxBounded, Bool.and_eq_true] at hbd
    have hl := ihl hpl
      (fun w' hw' => hws w' (by simp [Term.freeWires, hw'])) hbd.1
    have hr := ihr hpr
      (fun w' hw' => hws w' (by simp [Term.freeWires, hw'])) hbd.2
    rw [QTensor.scalar_mk_congr (Poly.eval_add _ pl pr)]
    show (do QTensor.map2 (· + ·) (← Term.evalQ σ l) (← Term.evalQ σ r)) = _
    rw [hl, hr]
    exact QTensor.map2_scalars _ _ _
  | mul l r ihl ihr =>
    intro p h hws hbd
    simp only [Term.asCoordPolyIdx?, Option.bind_eq_bind] at h
    obtain ⟨pl, hpl, h⟩ := option_bind_eq_some' h
    obtain ⟨pr, hpr, h⟩ := option_bind_eq_some' h
    injection h with h
    subst h
    simp only [Term.idxBounded, Bool.and_eq_true] at hbd
    have hl := ihl hpl
      (fun w' hw' => hws w' (by simp [Term.freeWires, hw'])) hbd.1
    have hr := ihr hpr
      (fun w' hw' => hws w' (by simp [Term.freeWires, hw'])) hbd.2
    rw [QTensor.scalar_mk_congr (Poly.eval_mul _ pl pr)]
    show (do QTensor.map2 (· * ·) (← Term.evalQ σ l) (← Term.evalQ σ r)) = _
    rw [hl, hr]
    exact QTensor.map2_scalars _ _ _
  | sub l r ihl ihr =>
    intro p h hws hbd
    simp only [Term.asCoordPolyIdx?, Option.bind_eq_bind] at h
    obtain ⟨pl, hpl, h⟩ := option_bind_eq_some' h
    obtain ⟨pr, hpr, h⟩ := option_bind_eq_some' h
    injection h with h
    subst h
    simp only [Term.idxBounded, Bool.and_eq_true] at hbd
    have hl := ihl hpl
      (fun w' hw' => hws w' (by simp [Term.freeWires, hw'])) hbd.1
    have hr := ihr hpr
      (fun w' hw' => hws w' (by simp [Term.freeWires, hw'])) hbd.2
    rw [QTensor.scalar_mk_congr (Poly.eval_sub _ pl pr)]
    show (do QTensor.map2 (· - ·) (← Term.evalQ σ l) (← Term.evalQ σ r)) = _
    rw [hl, hr]
    exact QTensor.map2_scalars _ _ _
  | neg u ih =>
    intro p h hws hbd
    simp only [Term.asCoordPolyIdx?, Option.map_eq_some_iff] at h
    obtain ⟨pu, hpu, hp⟩ := h
    subst hp
    have hu := ih hpu (fun w' hw' => hws w' (by
      simpa [Term.freeWires] using hw')) (by
      simpa [Term.idxBounded] using hbd)
    rw [QTensor.scalar_mk_congr (Poly.eval_neg _ pu)]
    show (Term.evalQ σ u).map (QTensor.map1 Neg.neg) = _
    rw [hu]
    rfl
  | idx u i ih =>
    intro p h hws hbd
    obtain ⟨⟨w', hw'⟩, hp⟩ := Term.asCoordPolyIdx?_idx_inv h
    subst hw'
    subst hp
    have hww : w' = w := hws w' (by simp [Term.freeWires])
    subst hww
    simp only [Term.idxBounded, Bool.and_eq_true, decide_eq_true_eq] at hbd
    rw [QTensor.scalar_mk_congr (Poly.eval_var _ i)]
    simp only [Term.evalQ, Option.bind_eq_bind, hwq, Option.bind_some]
    rw [hqs]
    show (if i < n then some
        (⟨[], [q.entries.getD i 0],
          (rfl : [q.entries.getD i 0].length = Shape.totalSize [])⟩ : QTensor)
      else none) = some ⟨[], [q.entries.getD i 0], rfl⟩
    rw [if_pos hbd.1]

theorem sound_bernCone_empty {H : Hypernet} {seq regionPremise : Sequent}
    {termX : Term} {simplex : Simplex} {S : ExtensionSet} {degree : Nat}
    {polynomial : Term} {predicate : Formula}
    (ih : regionPremise.semanticallyValid H)
    (hpre : seq.pre = regionPremise.pre)
    (hregionPost : regionPremise.post = .inRegion termX simplex S)
    (hpolyTie : polynomial.freeWires = [] ∨
      ∃ w, termX = Term.var w ∧ polynomial.freeWires ⊆ [w])
    (hconvex : isExtensionSetEmpty S → isConvexPredicate predicate)
    (hSempty : isExtensionSetEmpty S)
    (hcoeff : allForwardDiffBernCoeffsSatisfyP simplex S degree polynomial
      predicate)
    (hpostApply : applyPredicateToTerm predicate polynomial seq.post) :
    seq.semanticallyValid H := by

  simp only [allForwardDiffBernCoeffsSatisfyP, bernConeCoeffCheck] at hcoeff
  split at hcoeff
  case isFalse => cases hcoeff
  case isTrue hguard =>
  subst hguard
  split at hcoeff
  case isFalse => cases hcoeff
  case isTrue hvlen =>
  split at hcoeff
  case h_1 => cases hcoeff
  case h_2 p hpoly =>
  split at hcoeff
  case isFalse hnixf =>

    split at hcoeff
    case isFalse => cases hcoeff
    case isTrue hgate =>
    obtain ⟨hSb, hbnd⟩ := hgate
    split at hcoeff
    case h_2 => cases hcoeff
    case h_1 table hfd =>

    have hpolyIdx : Term.asCoordPolyIdx? polynomial = some p := by
      have h := hpoly
      simp only [Term.asCoordPoly?] at h
      split at h
      case isTrue hf => exact absurd hf hnixf
      case isFalse => exact h

    have hcv := hconvex hSempty
    unfold isConvexPredicate at hcv
    obtain ⟨cls, hcls⟩ := Option.isSome_iff_exists.mp hcv
    have hconv := satisfiesPredQ_convex hcls

    have hmaskall : ∀ bb ∈ ((List.finRange S.simplex.complex.nVertices).filter
        (fun v => S.simplex.contains v)).map (fun v => S.containsNat v.val),
        bb = false := by
      intro bb hbb
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hbb
      rw [ExtensionSet.containsNat_val]
      exact hSempty v
    intro σ hadm hpre'
    rw [hpre] at hpre'
    have hreg := ih σ hadm hpre'
    rw [hregionPost] at hreg
    obtain ⟨-, q, hq, hqshape, hmask⟩ := hreg
    rw [hpostApply]

    have hwve : ∃ w, termX = Term.var w ∧ polynomial.freeWires ⊆ [w] := by
      rcases hpolyTie with h | h
      · exact absurd
          (Term.asCoordPolyIdx?_idxFree_of_no_wires hpolyIdx h) hnixf
      · exact h
    obtain ⟨w, htX, hsub⟩ := hwve
    rw [htX] at hq
    have hwq : σ.wireQ w = some q := hq

    obtain ⟨qw, hqw0, hqwsum, hqwcoord⟩ :=
      maskRegion_rat_weights hmask hSempty

    obtain ⟨ρ, hρmem, hρnmem⟩ :
        ∃ ρ : Nat → ℚ,
          (∀ (i : Nat) (h : i < ((List.finRange S.simplex.complex.nVertices).filter
            (fun v => S.simplex.contains v)).length), ρ i = qw ⟨i, h⟩) ∧
          ∀ i, ¬ i < ((List.finRange S.simplex.complex.nVertices).filter
            (fun v => S.simplex.contains v)).length → ρ i = 0 := by
      refine ⟨fun i => if h : i < _ then qw ⟨i, h⟩ else 0, ?_, ?_⟩
      · intro i h
        show (if h' : i < _ then qw ⟨i, h'⟩ else 0) = qw ⟨i, h⟩
        split
        · rfl
        · next h' => exact absurd h h'
      · intro i hi
        show (if h' : i < _ then qw ⟨i, h'⟩ else 0) = 0
        split
        · next h' => exact absurd h' hi
        · rfl
    have hρ0 : ∀ v, 0 ≤ ρ v := by
      intro v
      by_cases h : v < ((List.finRange S.simplex.complex.nVertices).filter
        (fun v => S.simplex.contains v)).length
      · rw [hρmem v h]
        exact hqw0 _
      · rw [hρnmem v h]

    have hρsum : ((List.range (((List.finRange S.simplex.complex.nVertices).filter
        (fun v => S.simplex.contains v)).map fun v =>
          (List.finRange S.simplex.complex.ambDim).map
            fun j => S.simplex.complex.coord v j).length).map ρ).sum = 1 := by
      rw [List.length_map]
      show (∑ i ∈ Finset.range ((List.finRange S.simplex.complex.nVertices).filter
        (fun v => S.simplex.contains v)).length, ρ i) = 1
      rw [← Fin.sum_univ_eq_sum_range]
      rw [show (∑ i : Fin ((List.finRange S.simplex.complex.nVertices).filter
          (fun v => S.simplex.contains v)).length, ρ i.val)
          = ∑ i, qw i from
        Finset.sum_congr rfl (fun i _ => by rw [hρmem i.val i.isLt, Fin.eta])]
      exact hqwsum

    have hkern := QArith.fdBernstein_empty_sound _ _ degree p table
      (satisfiesPredQ predicate) hmaskall hfd hcoeff hconv ρ hρ0 hρsum

    have hpteq : QArith.Poly.eval (fun j =>
        ((List.range (((List.finRange S.simplex.complex.nVertices).filter
          (fun v => S.simplex.contains v)).map fun v =>
            (List.finRange S.simplex.complex.ambDim).map
              fun jf => S.simplex.complex.coord v jf).length).map
          (fun i => ((((List.finRange S.simplex.complex.nVertices).filter
            (fun v => S.simplex.contains v)).map fun v =>
              (List.finRange S.simplex.complex.ambDim).map
                fun jf => S.simplex.complex.coord v jf).getD i []).getD j 0
            * ρ i)).sum) p
        = QArith.Poly.eval (fun j => q.entries.getD j 0) p := by
      apply Poly.eval_congr_keys
      intro tm _ ve _
      rw [kernel_evalpt_coords _ ρ qw hρmem ve.1]
      split
      · next hj => exact hqwcoord ⟨ve.1, hj⟩
      · next hj =>
        rw [List.getD_eq_default]
        rw [q.len_eq, hqshape]
        show S.simplex.complex.ambDim * 1 ≤ ve.1
        omega
    rw [hpteq] at hkern

    have heval := Term.evalQ_asCoordPolyIdx σ hwq hqshape hpolyIdx
      (fun w' hw' => by simpa using hsub hw') hbnd
    exact holds_substHole_of_satisfies σ hcls heval (Or.inl rfl)
      (by
        show satisfiesPredQ predicate (QTensor.scalar
          ⟨[], [QArith.Poly.eval (fun j => q.entries.getD j 0) p], rfl⟩) = true
        exact hkern)
  case isTrue hixf =>
  split at hcoeff
  case isTrue => cases hcoeff
  case isFalse hscope =>
  split at hcoeff
  case h_2 => cases hcoeff
  case h_1 table hfd =>

  have hcv := hconvex hSempty
  unfold isConvexPredicate at hcv
  obtain ⟨cls, hcls⟩ := Option.isSome_iff_exists.mp hcv
  have hconv := satisfiesPredQ_convex hcls

  have hmaskall : ∀ bb ∈ ((List.finRange S.simplex.complex.nVertices).filter
      (fun v => S.simplex.contains v)).map (fun v => S.containsNat v.val),
      bb = false := by
    intro bb hbb
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hbb
    rw [ExtensionSet.containsNat_val]
    exact hSempty v
  intro σ hadm hpre'
  rw [hpre] at hpre'
  have hreg := ih σ hadm hpre'
  rw [hregionPost] at hreg
  obtain ⟨-, q, hq, hqshape, hmask⟩ := hreg
  rw [hpostApply]
  by_cases hfw : polynomial.freeWires = []
  ·
    obtain ⟨c, hc⟩ := Term.evalQ?_of_no_wires polynomial hfw hixf
    have hkern := QArith.fdBernstein_empty_sound _ _ degree p table
      (satisfiesPredQ predicate) hmaskall hfd hcoeff hconv
      (fun i => if i = 0 then 1 else 0)
      (fun v => by split <;> norm_num)
      (by
        apply sum_indicator_head
        rw [List.length_map, hvlen]
        omega)

    have heval : ∀ ρpt : Nat → ℚ, QArith.Poly.eval ρpt p = c := by
      intro ρpt
      rw [asCoordPoly?_eval hpoly hixf]
      exact Poly.eval_toPoly_closed hc _
    rw [heval] at hkern
    exact holds_substHole_of_satisfies σ hcls
      (Term.evalQ_of_closed σ polynomial c hc) (Or.inl rfl)
      (by
        show satisfiesPredQ predicate (QTensor.scalar ⟨[], [c], rfl⟩) = true
        exact hkern)
  ·
    have hwve : ∃ w, termX = Term.var w ∧ polynomial.freeWires ⊆ [w] := by
      rcases hpolyTie with h | h
      · exact absurd h hfw
      · exact h
    obtain ⟨w, htX, hsub⟩ := hwve
    rw [htX] at hq
    have hwq : σ.wireQ w = some q := hq
    by_cases hd1 : S.simplex.complex.ambDim = 1
    swap
    ·

      have hvars : QArith.Poly.vars p = [] := by
        rcases not_and_or.mp hscope with h | h
        · exact not_ne_iff.mp h
        · exact absurd (not_ne_iff.mp h) hd1

      have hp_eq : p = polynomial.toPoly := by
        have h := hpoly
        simp only [Term.asCoordPoly?] at h
        split at h
        case isFalse hnf => exact absurd hixf hnf
        case isTrue =>
        split at h
        · next hv =>
          injection h with h
          exact h.symm
        · next x hv =>
          injection h with h
          exfalso
          have hmono := Poly.monos_nil_of_vars_nil (by rw [← h] at hvars; exact hvars)
          have hvnil : QArith.Poly.vars polynomial.toPoly = [] := by
            have hall : ∀ tm ∈ polynomial.toPoly, tm.1 = [] := by
              intro tm htm
              have hmem : (tm.1.map fun ve => (0, ve.2), tm.2)
                  ∈ polynomial.toPoly.map
                    (fun t => (t.1.map fun ve => (0, ve.2), t.2)) :=
                List.mem_map.mpr ⟨tm, htm, rfl⟩
              have := hmono _ hmem
              exact List.map_eq_nil_iff.mp this
            unfold QArith.Poly.vars
            have : (polynomial.toPoly.flatMap fun t => t.1.map (·.1)) = [] := by
              rw [List.flatMap_eq_nil_iff]
              intro tm htm
              rw [hall tm htm]
              rfl
            rw [this]
            rfl
          rw [hv] at hvnil
          cases hvnil
        · cases h
      have hvtoPoly : QArith.Poly.vars polynomial.toPoly = [] := by
        rw [← hp_eq]
        exact hvars
      have hallnil := Poly.monos_nil_of_vars_nil hvtoPoly

      have heval_any : ∀ ρ₁ ρ₂ : Nat → ℚ,
          QArith.Poly.eval ρ₁ polynomial.toPoly
            = QArith.Poly.eval ρ₂ polynomial.toPoly := by
        intro ρ₁ ρ₂
        apply Poly.eval_congr_keys
        intro tm htm ve hve
        rw [hallnil tm htm] at hve
        cases hve

      have hkern := QArith.fdBernstein_empty_sound _ _ degree p table
        (satisfiesPredQ predicate) hmaskall hfd hcoeff hconv
        (fun i => if i = 0 then 1 else 0)
        (fun v => by split <;> norm_num)
        (by
          apply sum_indicator_head
          rw [List.length_map, hvlen]
          omega)
      rw [hp_eq] at hkern

      have hpw : ∀ w' ∈ polynomial.freeWires, ∃ qw, σ.wireQ w' = some qw ∧
          (qw.shape = [] ∨ qw.shape = q.shape) := by
        intro w' hw'
        have hww : w' = w := by simpa using hsub hw'
        subst hww
        exact ⟨q, hwq, Or.inr rfl⟩
      obtain ⟨qp, hqp, hqpj, hqpz, hqpe⟩ :=
        Term.evalQ_brRead σ q.shape polynomial hpw hixf

      have hqnnil : ¬ q.shape = [] := by
        rw [hqshape]
        exact List.cons_ne_nil _ _
      have hqpS : qp.shape = q.shape := by
        rcases hqpj with hnil | hS
        · exfalso
          obtain ⟨w₀, hw₀⟩ := List.exists_mem_of_ne_nil _ hfw
          have hww : w₀ = w := by simpa using hsub hw₀
          subst hww
          exact hqnnil (hqpz hnil w₀ hw₀ q hwq)
        · exact hS

      apply holds_substHole_of_satisfies_entries σ hcls hqp
      intro e he
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
      have hilen : i < Shape.totalSize q.shape := by
        rw [← hqpS, ← qp.len_eq]
        exact hi
      have hbr : qp.brRead i = qp.entries[i] := by
        rw [QTensor.brRead_pos (by rw [hqpS]; exact hqnnil) i,
          List.getD_eq_getElem _ _ hi]
      rw [← hbr, hqpe i hilen]
      rw [heval_any _ (σ.entryVal i)] at hkern
      exact hkern

    have hqsing : SingletonShape q.shape := by
      rw [hqshape, hd1]
      exact Or.inr rfl

    have hpw : ∀ w' ∈ polynomial.freeWires,
        ∃ qw, σ.wireQ w' = some qw ∧ SingletonShape qw.shape := by
      intro w' hw'
      have hww : w' = w := by
        have := hsub hw'
        simpa using this
      subst hww
      exact ⟨q, hwq, hqsing⟩
    obtain ⟨qp, hqp, hsqp, hvqp⟩ := Term.evalQ_total_singleton σ polynomial hpw hixf

    have hvlen2 : ((List.finRange S.simplex.complex.nVertices).filter
        (fun v => S.simplex.contains v)).length = 2 := by
      rw [hvlen, hd1]
    obtain ⟨a, b, hpair⟩ := List.length_eq_two.mp hvlen2
    have hnd : ((List.finRange S.simplex.complex.nVertices).filter
        (fun v => S.simplex.contains v)).Nodup :=
      (List.nodup_finRange _).filter _
    rw [hpair] at hnd
    have hab : a ≠ b := by
      simp only [List.nodup_cons, List.mem_singleton, List.nodup_nil,
        and_true] at hnd
      exact hnd.1
    have hd1' : 0 < S.simplex.complex.ambDim := by omega
    set j0 : Fin S.simplex.complex.ambDim := ⟨0, hd1'⟩ with hj0
    have hjall : ∀ j : Fin S.simplex.complex.ambDim, j = j0 := by
      intro j
      apply Fin.ext
      have := j.isLt
      omega
    set V₀ : ℚ := S.simplex.complex.coord a j0 with hV₀
    set V₁ : ℚ := S.simplex.complex.coord b j0 with hV₁
    have hVa : ∀ j, S.simplex.complex.coord a j = V₀ := fun j => by
      rw [hjall j]
    have hVb : ∀ j, S.simplex.complex.coord b j = V₁ := fun j => by
      rw [hjall j]
    have hVne : V₀ ≠ V₁ := by
      obtain ⟨j', hj'⟩ := S.simplex.complex.distinctVerts a b hab
      rw [hjall j'] at hj'
      exact hj'

    have hsigns := maskRegion_pair_elim hpair hVa hVb hVne j0 hmask
    set x0 : ℚ := q.scalar with hx0
    have hw₀ : 0 ≤ (V₁ - x0) / (V₁ - V₀) := hsigns.2.1 (hSempty a)
    have hw₁ : 0 ≤ (x0 - V₀) / (V₁ - V₀) := hsigns.2.2.2 (hSempty b)
    have hdenne : V₁ - V₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hVne)

    set ρ : Nat → ℚ := fun i => if i = 0 then (V₁ - x0) / (V₁ - V₀)
      else if i = 1 then (x0 - V₀) / (V₁ - V₀) else 0 with hρdef
    have hρ : ∀ v, 0 ≤ ρ v := by
      intro v
      simp only [hρdef]
      split
      · exact hw₀
      · split
        · exact hw₁
        · exact le_refl 0
    have hρ0 : ρ 0 = (V₁ - x0) / (V₁ - V₀) := by simp [hρdef]
    have hρ1 : ρ 1 = (x0 - V₀) / (V₁ - V₀) := by simp [hρdef]
    have hkern := QArith.fdBernstein_empty_sound _ _ degree p table
      (satisfiesPredQ predicate) hmaskall hfd hcoeff hconv ρ hρ
      (by
        rw [List.length_map, hvlen2]
        rw [show List.range 2 = [0, 1] from rfl]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [hρ0, hρ1]
        field_simp
        ring)

    rw [hpair] at hkern
    simp only [List.map_cons, List.map_nil] at hkern
    rw [show ∀ (la lb : List ℚ), (QArith.Poly.eval (fun j =>
        ((List.range ([la, lb] : List (List ℚ)).length).map
          (fun i => (([la, lb] : List (List ℚ)).getD i []).getD j 0 * ρ i)).sum) p)
        = QArith.Poly.eval (fun j => la.getD j 0 * ρ 0 + lb.getD j 0 * ρ 1) p
      from fun la lb => by
        apply Poly.eval_congr_keys
        intro t _ ve _
        exact kernel_evalpt_pair la lb _ _ ve.1] at hkern

    have hpt : ((List.finRange S.simplex.complex.ambDim).map
        (fun j => S.simplex.complex.coord a j)).getD 0 0 * ρ 0 +
        ((List.finRange S.simplex.complex.ambDim).map
          (fun j => S.simplex.complex.coord b j)).getD 0 0 * ρ 1 = x0 := by
      have hfr : (List.finRange S.simplex.complex.ambDim) = [j0] := by
        apply List.ext_getElem
        · rw [List.length_finRange]
          show S.simplex.complex.ambDim = 1
          exact hd1
        · intro n h1 h2
          simp only [List.length_finRange] at h1
          simp only [List.length_cons, List.length_nil] at h2
          have hn : n = 0 := by omega
          subst hn
          rw [List.getElem_finRange]
          show (⟨0, h1⟩ : Fin _) = j0
          apply Fin.ext
          rfl
      rw [hfr]
      simp only [List.map_cons, List.map_nil, List.getD_cons_zero]
      rw [hρ0, hρ1, ← hV₀, ← hV₁]
      field_simp
      ring

    have hevals : QArith.Poly.eval (fun j =>
        ((List.finRange S.simplex.complex.ambDim).map
          (fun j => S.simplex.complex.coord a j)).getD j 0 * ρ 0 +
        ((List.finRange S.simplex.complex.ambDim).map
          (fun j => S.simplex.complex.coord b j)).getD j 0 * ρ 1) p
        = qp.scalar := by
      rw [asCoordPoly?_eval hpoly hixf, hvqp]
      apply Poly.eval_congr_keys
      intro tm htm ve hve
      have hkey : ve.1 ∈ polynomial.freeWires :=
        Term.toPoly_keys polynomial tm htm ve hve
      have hww : ve.1 = w := by
        have := hsub hkey
        simpa using this
      rw [hww, hpt, Hypernet.Valuation.rho_eq σ hwq]
    rw [hevals] at hkern
    exact holds_substHole_of_satisfies σ hcls hqp hsqp hkern

theorem kernel_evalpt_pair_mask (la lb : List ℚ) (m0 m1 : Bool) (u : ℚ)
    (j : Nat) :
    ((List.range ([la, lb] : List (List ℚ)).length).map
      (fun i => (([la, lb] : List (List ℚ)).getD i []).getD j 0 *
        (if ([m0, m1] : List Bool).getD i false then -u else 1 + u))).sum
    = la.getD j 0 * (if m0 then -u else 1 + u)
      + lb.getD j 0 * (if m1 then -u else 1 + u) := by
  show ((List.range 2).map _).sum = _
  rw [show List.range 2 = [0, 1] from rfl]
  simp

theorem sound_bernCone {H : Hypernet} {seq regionPremise : Sequent}
    {termX : Term} {simplex : Simplex} {S : ExtensionSet} {degree : Nat}
    {polynomial : Term} {predicate : Formula}
    (ih : regionPremise.semanticallyValid H)
    (hpre : seq.pre = regionPremise.pre)
    (hregionPost : regionPremise.post = .inRegion termX simplex S)
    (hpolyTie : polynomial.freeWires = [] ∨
      ∃ w, termX = Term.var w ∧ polynomial.freeWires ⊆ [w])
    (hpredShape : (¬ isExtensionSetEmpty S → isConicPredicate predicate)
      ∧ (isExtensionSetEmpty S → isConvexPredicate predicate))
    (hcoeff : allForwardDiffBernCoeffsSatisfyP simplex S degree polynomial
      predicate)
    (hpostApply : applyPredicateToTerm predicate polynomial seq.post) :
    seq.semanticallyValid H := by
  by_cases hSempty : isExtensionSetEmpty S
  · exact sound_bernCone_empty ih hpre hregionPost hpolyTie hpredShape.2
      hSempty hcoeff hpostApply

  simp only [allForwardDiffBernCoeffsSatisfyP, bernConeCoeffCheck] at hcoeff
  split at hcoeff
  case isFalse => cases hcoeff
  case isTrue hguard =>
  subst hguard
  split at hcoeff
  case isFalse => cases hcoeff
  case isTrue hvlen =>
  split at hcoeff
  case h_1 => cases hcoeff
  case h_2 p hpoly =>
  split at hcoeff
  case isFalse hnixf =>

    split at hcoeff
    case isFalse => cases hcoeff
    case isTrue hgate =>
      exact absurd ((ExtensionSet.isEmptyB_iff S).mp hgate.1) hSempty
  case isTrue hixf =>
  split at hcoeff
  case isTrue => cases hcoeff
  case isFalse hscope =>
  split at hcoeff
  case h_2 => cases hcoeff
  case h_1 table hfd =>

  have hcv := hpredShape.1 hSempty
  unfold isConicPredicate at hcv
  obtain ⟨cls, hcls, hconicflag⟩ : ∃ cls, classifyPred predicate = some cls ∧
      cls.conic = true := by
    cases hcp : classifyPred predicate with
    | none => rw [hcp] at hcv; cases hcv
    | some cls =>
      rw [hcp] at hcv
      injection hcv with hcv
      exact ⟨cls, rfl, hcv⟩
  have hconv := satisfiesPredQ_convex hcls
  have hzero := satisfiesPredQ_conic_zero hcls hconicflag
  have hscale := satisfiesPredQ_conic_scale hcls hconicflag
  intro σ hadm hpre'
  rw [hpre] at hpre'
  have hreg := ih σ hadm hpre'
  rw [hregionPost] at hreg
  obtain ⟨-, q, hq, hqshape, hmask⟩ := hreg
  rw [hpostApply]
  by_cases hfw : polynomial.freeWires = []
  ·
    obtain ⟨c, hc⟩ := Term.evalQ?_of_no_wires polynomial hfw hixf
    have hvars : QArith.Poly.vars polynomial.toPoly = [] := by
      unfold QArith.Poly.vars
      have hflat : (polynomial.toPoly.flatMap fun t => t.1.map (·.1)) = [] := by
        rw [List.flatMap_eq_nil_iff]
        intro tm htm
        have hnil : tm.1 = [] := by
          cases htm1 : tm.1 with
          | nil => rfl
          | cons ve rest =>
            exfalso
            have := Term.toPoly_keys polynomial tm htm ve (by rw [htm1]; simp)
            rw [hfw] at this
            cases this
        rw [hnil]
        rfl
      rw [hflat]
      rfl
    have hpc : p = polynomial.toPoly := by
      have h := hpoly
      simp only [Term.asCoordPoly?] at h
      split at h
      case isFalse hnf => exact absurd hixf hnf
      case isTrue =>
      rw [hvars] at h
      injection h with h
      exact h.symm
    have hconst : polynomial.toPoly = QArith.Poly.const c := by
      rw [Term.toPoly_const_form hvars, Poly.eval_toPoly_closed hc]
    rw [hpc, hconst] at hfd
    have hkern := QArith.fdBernstein_sound_const _ _ degree c table
      (satisfiesPredQ predicate) hfd hcoeff
    exact holds_substHole_of_satisfies σ hcls
      (Term.evalQ_of_closed σ polynomial c hc) (Or.inl rfl)
      (by
        show satisfiesPredQ predicate (QTensor.scalar ⟨[], [c], rfl⟩) = true
        exact hkern)
  ·
    have hwve : ∃ w, termX = Term.var w ∧ polynomial.freeWires ⊆ [w] := by
      rcases hpolyTie with h | h
      · exact absurd h hfw
      · exact h
    obtain ⟨w, htX, hsub⟩ := hwve
    rw [htX] at hq
    have hwq : σ.wireQ w = some q := hq
    by_cases hd1 : S.simplex.complex.ambDim = 1
    swap
    ·
      have hvars : QArith.Poly.vars p = [] := by
        rcases not_and_or.mp hscope with h | h
        · exact not_ne_iff.mp h
        · exact absurd (not_ne_iff.mp h) hd1
      have hp_eq : p = polynomial.toPoly := by
        have h := hpoly
        simp only [Term.asCoordPoly?] at h
        split at h
        case isFalse hnf => exact absurd hixf hnf
        case isTrue =>
        split at h
        · next hv =>
          injection h with h
          exact h.symm
        · next x hv =>
          injection h with h
          exfalso
          have hmono := Poly.monos_nil_of_vars_nil
            (by rw [← h] at hvars; exact hvars)
          have hvnil : QArith.Poly.vars polynomial.toPoly = [] := by
            have hall : ∀ tm ∈ polynomial.toPoly, tm.1 = [] := by
              intro tm htm
              have hmem : (tm.1.map fun ve => (0, ve.2), tm.2)
                  ∈ polynomial.toPoly.map
                    (fun t => (t.1.map fun ve => (0, ve.2), t.2)) :=
                List.mem_map.mpr ⟨tm, htm, rfl⟩
              have := hmono _ hmem
              exact List.map_eq_nil_iff.mp this
            unfold QArith.Poly.vars
            have : (polynomial.toPoly.flatMap fun t => t.1.map (·.1)) = [] := by
              rw [List.flatMap_eq_nil_iff]
              intro tm htm
              rw [hall tm htm]
              rfl
            rw [this]
            rfl
          rw [hv] at hvnil
          cases hvnil
        · cases h
      have hvtoPoly : QArith.Poly.vars polynomial.toPoly = [] := by
        rw [← hp_eq]
        exact hvars
      set c₀ : ℚ := QArith.Poly.eval (fun _ => 0) polynomial.toPoly with hc₀
      have hconst : polynomial.toPoly = QArith.Poly.const c₀ :=
        Term.toPoly_const_form hvtoPoly
      rw [hp_eq, hconst] at hfd
      have hkern := QArith.fdBernstein_sound_const _ _ degree c₀ table
        (satisfiesPredQ predicate) hfd hcoeff

      have hpw : ∀ w' ∈ polynomial.freeWires, ∃ qw, σ.wireQ w' = some qw ∧
          (qw.shape = [] ∨ qw.shape = q.shape) := by
        intro w' hw'
        have hww : w' = w := by simpa using hsub hw'
        subst hww
        exact ⟨q, hwq, Or.inr rfl⟩
      obtain ⟨qp, hqp, hqpj, hqpz, hqpe⟩ :=
        Term.evalQ_brRead σ q.shape polynomial hpw hixf
      have hqnnil : ¬ q.shape = [] := by
        rw [hqshape]
        exact List.cons_ne_nil _ _
      have hqpS : qp.shape = q.shape := by
        rcases hqpj with hnil | hS
        · exfalso
          obtain ⟨w₀, hw₀⟩ := List.exists_mem_of_ne_nil _ hfw
          have hww : w₀ = w := by simpa using hsub hw₀
          subst hww
          exact hqnnil (hqpz hnil w₀ hw₀ q hwq)
        · exact hS
      apply holds_substHole_of_satisfies_entries σ hcls hqp
      intro e he
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
      have hilen : i < Shape.totalSize q.shape := by
        rw [← hqpS, ← qp.len_eq]
        exact hi
      have hbr : qp.brRead i = qp.entries[i] := by
        rw [QTensor.brRead_pos (by rw [hqpS]; exact hqnnil) i,
          List.getD_eq_getElem _ _ hi]
      rw [← hbr, hqpe i hilen, hconst, Poly.eval_const]
      exact hkern
    ·
      have hqsing : SingletonShape q.shape := by
        rw [hqshape, hd1]
        exact Or.inr rfl
      have hpw : ∀ w' ∈ polynomial.freeWires,
          ∃ qw, σ.wireQ w' = some qw ∧ SingletonShape qw.shape := by
        intro w' hw'
        have hww : w' = w := by simpa using hsub hw'
        subst hww
        exact ⟨q, hwq, hqsing⟩
      obtain ⟨qp, hqp, hsqp, hvqp⟩ := Term.evalQ_total_singleton σ polynomial hpw hixf

      have hvlen2 : ((List.finRange S.simplex.complex.nVertices).filter
          (fun v => S.simplex.contains v)).length = 2 := by
        rw [hvlen, hd1]
      obtain ⟨a, b, hpair⟩ := List.length_eq_two.mp hvlen2
      have hnd : ((List.finRange S.simplex.complex.nVertices).filter
          (fun v => S.simplex.contains v)).Nodup :=
        (List.nodup_finRange _).filter _
      rw [hpair] at hnd
      have hab : a ≠ b := by
        simp only [List.nodup_cons, List.mem_singleton, List.nodup_nil,
          and_true] at hnd
        exact hnd.1
      have hd1' : 0 < S.simplex.complex.ambDim := by omega
      set j0 : Fin S.simplex.complex.ambDim := ⟨0, hd1'⟩ with hj0
      have hjall : ∀ j : Fin S.simplex.complex.ambDim, j = j0 := by
        intro j
        apply Fin.ext
        have := j.isLt
        omega
      set V₀ : ℚ := S.simplex.complex.coord a j0 with hV₀
      set V₁ : ℚ := S.simplex.complex.coord b j0 with hV₁
      have hVa : ∀ j, S.simplex.complex.coord a j = V₀ := fun j => by
        rw [hjall j]
      have hVb : ∀ j, S.simplex.complex.coord b j = V₁ := fun j => by
        rw [hjall j]
      have hVne : V₀ ≠ V₁ := by
        obtain ⟨j', hj'⟩ := S.simplex.complex.distinctVerts a b hab
        rw [hjall j'] at hj'
        exact hj'
      have hsigns := maskRegion_pair_elim hpair hVa hVb hVne j0 hmask
      set x0 : ℚ := q.scalar with hx0
      have hdenne : V₁ - V₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hVne)

      obtain ⟨v, hv⟩ : ∃ v, S.contains v = true := by
        by_contra hno
        push_neg at hno
        exact hSempty (fun v => by
          have := hno v
          exact Bool.not_eq_true _ ▸ (Bool.eq_false_iff.mpr this))
      have hvmem : v ∈ (List.finRange S.simplex.complex.nVertices).filter
          (fun v => S.simplex.contains v) := by
        apply List.mem_filter.mpr
        exact ⟨List.mem_finRange v, by
          show S.simplex.contains v = true
          exact S.scope v hv⟩
      obtain ⟨v', hv'simp, hv'false⟩ := S.proper
      have hv'mem : v' ∈ (List.finRange S.simplex.complex.nVertices).filter
          (fun v => S.simplex.contains v) := by
        apply List.mem_filter.mpr
        exact ⟨List.mem_finRange v', by
          show S.simplex.contains v' = true
          exact hv'simp⟩
      rw [hpair] at hvmem hv'mem
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hvmem hv'mem

      have hsmask : ((List.finRange S.simplex.complex.nVertices).filter
            (fun v => S.simplex.contains v)).map
            (fun v => S.containsNat v.val)
          = [S.contains a, S.contains b] := by
        rw [hpair]
        simp only [List.map_cons, List.map_nil,
          ExtensionSet.containsNat_val]
      rw [hpair] at hfd
      rw [show ([a, b].map (fun v => S.containsNat v.val))
          = [S.contains a, S.contains b] from by
        simp only [List.map_cons, List.map_nil, ExtensionSet.containsNat_val]]
        at hfd

      have hmaskcase : (S.contains a = true ∧ S.contains b = false) ∨
          (S.contains a = false ∧ S.contains b = true) := by
        rcases hvmem with rfl | rfl <;> rcases hv'mem with rfl | rfl
        · exact absurd hv (by rw [hv'false]; simp)
        · exact Or.inl ⟨hv, hv'false⟩
        · exact Or.inr ⟨hv'false, hv⟩
        · exact absurd hv (by rw [hv'false]; simp)

      set rowA : List ℚ := (List.finRange S.simplex.complex.ambDim).map
        (fun j => S.simplex.complex.coord a j) with hrowA
      set rowB : List ℚ := (List.finRange S.simplex.complex.ambDim).map
        (fun j => S.simplex.complex.coord b j) with hrowB

      have hwA : (V₁ - x0) / (V₁ - V₀) + (x0 - V₀) / (V₁ - V₀) = 1 := by
        field_simp
        ring
      rcases hmaskcase with ⟨hca, hcb⟩ | ⟨hca, hcb⟩
      ·
        set u₀ : ℚ := -((V₁ - x0) / (V₁ - V₀)) with hu₀
        have hlamA : (V₁ - x0) / (V₁ - V₀) ≤ 0 := hsigns.1 hca
        have hu : 0 ≤ u₀ := by
          rw [hu₀]
          linarith
        rw [hca, hcb] at hfd
        have hkern := QArith.fdBernstein_sound_dim1 [rowA, rowB]
          [true, false] degree p table (satisfiesPredQ predicate) u₀
          (Or.inl rfl) hfd hcoeff hu hzero
          (fun a c hc ha => hscale a c hc ha) hconv

        rw [show ([rowA, rowB] : List (List ℚ)).length = 2 from rfl] at hkern
        have hptvals : ∀ j : Nat,
            ((List.range 2).map
              (fun i => (([rowA, rowB] : List (List ℚ)).getD i []).getD j 0 *
                (if ([true, false] : List Bool).getD i false
                 then -u₀ else 1 + u₀))).sum
            = rowA.getD j 0 * ((V₁ - x0) / (V₁ - V₀))
              + rowB.getD j 0 * ((x0 - V₀) / (V₁ - V₀)) := by
          intro j
          rw [show ((List.range 2).map
              (fun i => (([rowA, rowB] : List (List ℚ)).getD i []).getD j 0 *
                (if ([true, false] : List Bool).getD i false
                 then -u₀ else 1 + u₀))).sum
              = rowA.getD j 0 * (if true then -u₀ else 1 + u₀)
                + rowB.getD j 0 * (if false then -u₀ else 1 + u₀) from
            kernel_evalpt_pair_mask rowA rowB true false u₀ j]
          rw [if_pos rfl, if_neg (by simp)]
          congr 1
          · congr 1
            rw [hu₀]
            ring
          · congr 1
            rw [hu₀]
            field_simp
            ring
        have hevals : QArith.Poly.eval (fun j =>
            ((List.range 2).map
              (fun i => (([rowA, rowB] : List (List ℚ)).getD i []).getD j 0 *
                (if ([true, false] : List Bool).getD i false
                 then -u₀ else 1 + u₀))).sum) p
            = qp.scalar := by
          rw [asCoordPoly?_eval hpoly hixf, hvqp]
          apply Poly.eval_congr_keys
          intro tm htm ve hve
          have hkey : ve.1 ∈ polynomial.freeWires :=
            Term.toPoly_keys polynomial tm htm ve hve
          have hww : ve.1 = w := by
            have := hsub hkey
            simpa using this
          rw [hww, hptvals 0]
          rw [hrowA, hrowB]
          have hfr : (List.finRange S.simplex.complex.ambDim) = [j0] := by
            apply List.ext_getElem
            · rw [List.length_finRange]
              show S.simplex.complex.ambDim = 1
              exact hd1
            · intro n h1 h2
              simp only [List.length_finRange] at h1
              simp only [List.length_cons, List.length_nil] at h2
              have hn : n = 0 := by omega
              subst hn
              rw [List.getElem_finRange]
              show (⟨0, h1⟩ : Fin _) = j0
              apply Fin.ext
              rfl
          rw [hfr]
          simp only [List.map_cons, List.map_nil, List.getD_cons_zero]
          rw [← hV₀, ← hV₁, Hypernet.Valuation.rho_eq σ hwq, ← hx0]
          field_simp
          ring
        rw [hevals] at hkern
        exact holds_substHole_of_satisfies σ hcls hqp hsqp hkern
      ·
        set u₀ : ℚ := -((x0 - V₀) / (V₁ - V₀)) with hu₀
        have hlamB : (x0 - V₀) / (V₁ - V₀) ≤ 0 := hsigns.2.2.1 hcb
        have hu : 0 ≤ u₀ := by
          rw [hu₀]
          linarith
        rw [hca, hcb] at hfd
        have hkern := QArith.fdBernstein_sound_dim1 [rowA, rowB]
          [false, true] degree p table (satisfiesPredQ predicate) u₀
          (Or.inr rfl) hfd hcoeff hu hzero
          (fun a c hc ha => hscale a c hc ha) hconv
        rw [show ([rowA, rowB] : List (List ℚ)).length = 2 from rfl] at hkern
        have hptvals : ∀ j : Nat,
            ((List.range 2).map
              (fun i => (([rowA, rowB] : List (List ℚ)).getD i []).getD j 0 *
                (if ([false, true] : List Bool).getD i false
                 then -u₀ else 1 + u₀))).sum
            = rowA.getD j 0 * ((V₁ - x0) / (V₁ - V₀))
              + rowB.getD j 0 * ((x0 - V₀) / (V₁ - V₀)) := by
          intro j
          rw [show ((List.range 2).map
              (fun i => (([rowA, rowB] : List (List ℚ)).getD i []).getD j 0 *
                (if ([false, true] : List Bool).getD i false
                 then -u₀ else 1 + u₀))).sum
              = rowA.getD j 0 * (if false then -u₀ else 1 + u₀)
                + rowB.getD j 0 * (if true then -u₀ else 1 + u₀) from
            kernel_evalpt_pair_mask rowA rowB false true u₀ j]
          rw [if_neg (by simp), if_pos rfl]
          congr 1
          · congr 1
            rw [hu₀]
            field_simp
            ring
          · congr 1
            rw [hu₀]
            ring
        have hevals : QArith.Poly.eval (fun j =>
            ((List.range 2).map
              (fun i => (([rowA, rowB] : List (List ℚ)).getD i []).getD j 0 *
                (if ([false, true] : List Bool).getD i false
                 then -u₀ else 1 + u₀))).sum) p
            = qp.scalar := by
          rw [asCoordPoly?_eval hpoly hixf, hvqp]
          apply Poly.eval_congr_keys
          intro tm htm ve hve
          have hkey : ve.1 ∈ polynomial.freeWires :=
            Term.toPoly_keys polynomial tm htm ve hve
          have hww : ve.1 = w := by
            have := hsub hkey
            simpa using this
          rw [hww, hptvals 0]
          rw [hrowA, hrowB]
          have hfr : (List.finRange S.simplex.complex.ambDim) = [j0] := by
            apply List.ext_getElem
            · rw [List.length_finRange]
              show S.simplex.complex.ambDim = 1
              exact hd1
            · intro n h1 h2
              simp only [List.length_finRange] at h1
              simp only [List.length_cons, List.length_nil] at h2
              have hn : n = 0 := by omega
              subst hn
              rw [List.getElem_finRange]
              show (⟨0, h1⟩ : Fin _) = j0
              apply Fin.ext
              rfl
          rw [hfr]
          simp only [List.map_cons, List.map_nil, List.getD_cons_zero]
          rw [← hV₀, ← hV₁, Hypernet.Valuation.rho_eq σ hwq, ← hx0]
          field_simp
          ring
        rw [hevals] at hkern
        exact holds_substHole_of_satisfies σ hcls hqp hsqp hkern

theorem parseHoleSide_pos {t : Term} {s : ℚ}
    (h : parseHoleSide t = some s) : 0 < s := by
  unfold parseHoleSide at h
  split at h
  · split at h
    · injection h with h
      rw [← h]
      norm_num
    · cases h
  · split at h
    · next hc =>
      injection h with h
      rw [← h]
      exact hc.2
    · cases h
  · split at h
    · next hc =>
      injection h with h
      rw [← h]
      exact hc.2
    · cases h
  · cases h

theorem classifyPredAtom_upClosed_shape {b : BowTie} {tl tr : Term}
    {cls : PredClass}
    (hP : classifyPredAtom (.atom b tl tr) = some cls)
    (hu : cls.upClosed = true) :
    (∃ s c, parseHoleSide tl = some s ∧ tr.evalQ? = some c ∧ b = .ge) ∨
    (∃ s c, parseHoleSide tr = some s ∧ tl.evalQ? = some c ∧ b = .le) := by
  cases hpl : parseHoleSide tl with
  | some s =>
    cases hre : tr.evalQ? with
    | some c =>
      cases b <;> simp only [classifyPredAtom, hpl, hre] at hP
      case ge => exact Or.inl ⟨s, c, rfl, rfl, rfl⟩
      case le =>
        injection hP with hP
        rw [← hP] at hu
        cases hu
      case eq =>
        split at hP
        · injection hP with hP
          rw [← hP] at hu
          cases hu
        · cases hP
      case lt => cases hP
      case gt => cases hP
      case ne => cases hP
    | none =>
      cases hpr : parseHoleSide tr with
      | some s' =>
        cases hle : tl.evalQ? with
        | some c' =>
          cases b <;> simp only [classifyPredAtom, hpl, hre, hpr, hle] at hP
          case le => exact Or.inr ⟨s', c', rfl, rfl, rfl⟩
          case ge =>
            injection hP with hP
            rw [← hP] at hu
            cases hu
          case eq =>
            split at hP
            · injection hP with hP
              rw [← hP] at hu
              cases hu
            · cases hP
          case lt => cases hP
          case gt => cases hP
          case ne => cases hP
        | none =>
          exfalso
          cases b <;>
            simp only [classifyPredAtom, hpl, hre, hpr, hle] at hP <;>
            cases hP
      | none =>
        exfalso
        cases hle : tl.evalQ? <;> cases b <;>
          simp only [classifyPredAtom, hpl, hre, hpr, hle] at hP <;>
          cases hP
  | none =>
    cases hpr : parseHoleSide tr with
    | some s' =>
      cases hle : tl.evalQ? with
      | some c' =>
        cases b <;> simp only [classifyPredAtom, hpl, hpr, hle] at hP
        case le => exact Or.inr ⟨s', c', rfl, rfl, rfl⟩
        case ge =>
          injection hP with hP
          rw [← hP] at hu
          cases hu
        case eq =>
          split at hP
          · injection hP with hP
            rw [← hP] at hu
            cases hu
          · cases hP
        case lt => cases hP
        case gt => cases hP
        case ne => cases hP
      | none =>
        exfalso
        cases b <;>
          simp only [classifyPredAtom, hpl, hpr, hle] at hP <;>
          cases hP
    | none =>
      exfalso
      cases hle : tl.evalQ? <;> cases b <;>
        simp only [classifyPredAtom, hpl, hpr, hle] at hP <;>
        cases hP

theorem satisfiesPredQ_upClosed {P : Formula} {cls : PredClass}
    (hP : classifyPred P = some cls) (hup : cls.upClosed = true) :
    ∀ lo hi : ℚ, lo ≤ hi →
      satisfiesPredQ P lo = true → satisfiesPredQ P hi = true := by
  induction P generalizing cls with
  | and P₁ P₂ ih₁ ih₂ =>
    intro lo hi hle ha
    simp only [classifyPred, Option.bind_eq_bind] at hP
    obtain ⟨c₁, hc₁, hP⟩ := option_bind_eq_some' hP
    obtain ⟨c₂, hc₂, hP⟩ := option_bind_eq_some' hP
    injection hP with hP
    rw [← hP] at hup
    rw [Bool.and_eq_true] at hup
    obtain ⟨ha₁, ha₂⟩ := satisfiesPredQ_and.mp ha
    exact satisfiesPredQ_and.mpr
      ⟨ih₁ hc₁ hup.1 lo hi hle ha₁, ih₂ hc₂ hup.2 lo hi hle ha₂⟩
  | atom b tl tr =>
    intro lo hi hle ha
    rcases classifyPredAtom_upClosed_shape hP hup with
      ⟨s, c, hpl, hre, rfl⟩ | ⟨s, c, hpr, hle', rfl⟩
    · have hs := parseHoleSide_pos hpl
      rw [satisfiesPredQ_orient1_iff hpl hre] at ha ⊢
      show c ≤ s * hi
      have hlo : c ≤ s * lo := ha
      nlinarith
    · have hs := parseHoleSide_pos hpr
      rw [satisfiesPredQ_orient2_iff hpr hle'] at ha ⊢
      show c ≤ s * hi
      have hlo : c ≤ s * lo := ha
      nlinarith
  | inRegion t simplex S => intro _ _ _ _; cases hP
  | or P₁ P₂ _ _ => intro _ _ _ _; cases hP
  | tt => intro _ _ _ _; cases hP
  | ff => intro _ _ _ _; cases hP

theorem QArith.gridAll_mono {p q : ℚ → Bool}
    (hpq : ∀ c, p c = true → q c = true) {t : QArith.FDTable}
    (h : QArith.gridAll p t = true) : QArith.gridAll q t = true := by
  unfold QArith.gridAll at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro row hrow
  have hr := h row hrow
  rw [List.all_eq_true] at hr ⊢
  intro c hc
  exact hpq _ (hr c hc)

theorem cellStrictInteriorBuild_spec {schema : SimpC} {t : Term}
    {k : Fin schema.cells.length} {F : Formula}
    (h : cellStrictInteriorForm schema t k F) :
    schema.ambDim = 1 ∧
    ∃ (a b : Fin schema.nVertices) (V₀ V₁ : ℚ),
      (List.finRange schema.nVertices).filter
        (fun v => (schema.cells.get k).1 v) = [a, b] ∧
      (∀ j, schema.coord a j = V₀) ∧
      (∀ j, schema.coord b j = V₁) ∧
      V₀ ≠ V₁ ∧
      F = .and
        (.atom (if (schema.cells.get k).2 a then .lt else .gt)
          (.add (.const (V₁ / (V₁ - V₀))) (.mul (.const (-1 / (V₁ - V₀))) t))
          (.const 0))
        (.atom (if (schema.cells.get k).2 b then .lt else .gt)
          (.add (.const (-V₀ / (V₁ - V₀))) (.mul (.const (1 / (V₁ - V₀))) t))
          (.const 0)) := by
  simp only [cellStrictInteriorForm, cellStrictInteriorBuild,
    Option.bind_eq_bind] at h
  obtain ⟨lams, hlams, h⟩ := option_bind_eq_some' h
  unfold baryLambdas1D at hlams
  split at hlams
  · next hd1 =>
    refine ⟨hd1, ?_⟩
    split at hlams
    · next a b hfil =>
      simp only [] at hlams
      split at hlams
      · cases hlams
      · next hVne =>
        injection hlams with hlams
        subst hlams
        simp only [List.map_cons, List.map_nil] at h
        injection h with h
        refine ⟨a, b, schema.coord a ⟨0, by omega⟩,
          schema.coord b ⟨0, by omega⟩, hfil, ?_, ?_, ?_, ?_⟩
        · intro j
          have hj : j = ⟨0, by omega⟩ := by
            apply Fin.ext
            have := j.isLt
            omega
          rw [hj]
        · intro j
          have hj : j = ⟨0, by omega⟩ := by
            apply Fin.ext
            have := j.isLt
            omega
          rw [hj]
        · exact hVne
        · rw [← h]
          rfl
    · cases hlams
  · cases hlams

theorem cellOutWitnessBuild_spec {schema : SimpC} {t : Term}
    {k : Fin schema.cells.length} {w : Fin schema.nVertices} {F : Formula}
    (h : cellOutWitnessForm schema t k w F) :
    schema.ambDim = 1 ∧
    (schema.cells.get k).1 w = true ∧
    ∃ (a b : Fin schema.nVertices) (V₀ V₁ : ℚ),
      (List.finRange schema.nVertices).filter
        (fun v => (schema.cells.get k).1 v) = [a, b] ∧
      (∀ j, schema.coord a j = V₀) ∧
      (∀ j, schema.coord b j = V₁) ∧
      V₀ ≠ V₁ ∧
      ((w = a ∧ F = .atom (if (schema.cells.get k).2 a then .gt else .lt)
          (.add (.const (V₁ / (V₁ - V₀))) (.mul (.const (-1 / (V₁ - V₀))) t))
          (.const 0)) ∨
       (w = b ∧ F = .atom (if (schema.cells.get k).2 b then .gt else .lt)
          (.add (.const (-V₀ / (V₁ - V₀))) (.mul (.const (1 / (V₁ - V₀))) t))
          (.const 0))) := by
  simp only [cellOutWitnessForm, cellOutWitnessBuild,
    Option.bind_eq_bind] at h
  obtain ⟨hguard, h⟩ := option_guard_bind_eq_some h
  obtain ⟨lams, hlams, h⟩ := option_bind_eq_some' h
  obtain ⟨entry, hentry, h⟩ := option_bind_eq_some' h
  unfold baryLambdas1D at hlams
  split at hlams
  · next hd1 =>
    refine ⟨hd1, hguard, ?_⟩
    split at hlams
    · next a b hfil =>
      simp only [] at hlams
      split at hlams
      · cases hlams
      · next hVne =>
        injection hlams with hlams
        subst hlams
        have hew : entry.1 = w := by
          have := List.find?_some hentry
          simpa using this
        have hmem := List.mem_of_find?_eq_some hentry
        refine ⟨a, b, schema.coord a ⟨0, by omega⟩,
          schema.coord b ⟨0, by omega⟩, hfil, ?_, ?_, hVne, ?_⟩
        · intro j
          have hj : j = ⟨0, by omega⟩ := by
            apply Fin.ext
            have := j.isLt
            omega
          rw [hj]
        · intro j
          have hj : j = ⟨0, by omega⟩ := by
            apply Fin.ext
            have := j.isLt
            omega
          rw [hj]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with he | he
          · left
            subst he
            have haw : a = w := hew
            injection h with h
            rw [← haw] at h
            refine ⟨haw.symm, ?_⟩
            rw [← h]
            rfl
          · right
            subst he
            have hbw : b = w := hew
            injection h with h
            rw [← hbw] at h
            refine ⟨hbw.symm, ?_⟩
            rw [← h]
            rfl
    · cases hlams
  · cases hlams

theorem maskRegionStrict_pair_intro {C : SimpC}
    {mask ext : Fin C.nVertices → Bool}
    {x : Fin C.ambDim → ℚ} {a b : Fin C.nVertices} {V₀ V₁ : ℚ}
    (hfil : (List.finRange C.nVertices).filter (fun v => mask v) = [a, b])
    (hscope : ∀ v, ext v = true → mask v = true)
    (hVa : ∀ j, C.coord a j = V₀) (hVb : ∀ j, C.coord b j = V₁)
    (hne : V₀ ≠ V₁) (hdim : C.ambDim = 1) (j0 : Fin C.ambDim)
    (hw0t : ext a = true → (V₁ - x j0) / (V₁ - V₀) < 0)
    (hw0f : ext a = false → 0 < (V₁ - x j0) / (V₁ - V₀))
    (hw1t : ext b = true → (x j0 - V₀) / (V₁ - V₀) < 0)
    (hw1f : ext b = false → 0 < (x j0 - V₀) / (V₁ - V₀)) :
    MaskRegionStrict C mask ext x := by
  have hab : a ≠ b := fun hc => hne (by rw [← hVa j0, ← hVb j0, hc])
  obtain ⟨hma, hmb⟩ := mask_true_of_filter_pair hfil
  have hden : (V₁ : ℚ) - V₀ ≠ 0 := sub_ne_zero.mpr hne.symm
  set lam : Fin C.nVertices → ℝ := fun v =>
    if v = a then (((V₁ - x j0) / (V₁ - V₀) : ℚ) : ℝ)
    else if v = b then (((x j0 - V₀) / (V₁ - V₀) : ℚ) : ℝ) else 0 with hlam
  have hzero : ∀ v, mask v = false → lam v = 0 := by
    intro v hv
    rw [hlam]
    simp only []
    rw [if_neg (fun hc => by subst hc; rw [hma] at hv; cases hv),
        if_neg (fun hc => by subst hc; rw [hmb] at hv; cases hv)]
  have hdenR : (V₁ : ℝ) - (V₀ : ℝ) ≠ 0 := by exact_mod_cast hden
  have hsupp : ∀ v, mask v = true → v = a ∨ v = b := by
    intro v hmv
    have hvmem : v ∈ (List.finRange C.nVertices).filter
        (fun v => mask v) := by
      rw [List.mem_filter]
      exact ⟨List.mem_finRange v, hmv⟩
    rw [hfil] at hvmem
    simpa using hvmem
  refine ⟨lam, hzero, ?_, ?_, ?_, ?_⟩
  · rw [finSum_support_pair mask lam a b hfil hzero, hlam]
    simp only [if_pos rfl, if_neg (Ne.symm hab)]
    push_cast
    field_simp
    ring
  · intro j
    have hj : j = j0 := by
      apply Fin.ext
      have h1 := j.isLt
      have h2 := j0.isLt
      omega
    subst hj
    rw [finSum_support_pair mask _ a b hfil
      (fun v hv => by rw [hzero v hv]; ring)]
    rw [hlam]
    simp only [if_pos rfl, if_neg (Ne.symm hab)]
    rw [hVa j, hVb j]
    push_cast
    field_simp
    ring
  · intro v hv
    rw [hlam]
    simp only []
    by_cases hva : v = a
    · subst hva
      rw [if_pos rfl]
      exact_mod_cast hw0t hv
    · by_cases hvb : v = b
      · subst hvb
        rw [if_neg hva, if_pos rfl]
        exact_mod_cast hw1t hv
      · exfalso
        rcases hsupp v (hscope v hv) with h | h
        · exact hva h
        · exact hvb h
  · intro v hmv hv
    rw [hlam]
    simp only []
    by_cases hva : v = a
    · subst hva
      rw [if_pos rfl]
      exact_mod_cast hw0f hv
    · by_cases hvb : v = b
      · subst hvb
        rw [if_neg hva, if_pos rfl]
        exact_mod_cast hw1f hv
      · exfalso
        rcases hsupp v hmv with h | h
        · exact hva h
        · exact hvb h

theorem ERat.allFinQ_entry : ∀ {l : List ERat} {l' : List ℚ},
    ERat.allFinQ l = some l' → ∀ {i : ℕ} {v : ℚ},
      l[i]? = some (.fin v) → l'[i]? = some v := by
  intro l
  induction l with
  | nil =>
    intro l' h i v hi
    simp at hi
  | cons e rest ih =>
    intro l' h i v hi
    cases e with
    | fin q =>
      simp only [ERat.allFinQ] at h
      cases hr : ERat.allFinQ rest with
      | none => rw [hr] at h; cases h
      | some rest' =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi ⊢
          injection hi with hi
        | succ n =>
          simp only [List.getElem?_cons_succ] at hi ⊢
          exact ih hr hi
    | negInf => simp [ERat.allFinQ] at h
    | posInf => simp [ERat.allFinQ] at h

theorem Hypernet.Valuation.wireQ_of_unit_entry {H : Hypernet}
    (σ : H.Valuation) {w : Wire} {τ : TensorType} {v : ℚ}
    (hτ : H.wireType w = some τ) (h1 : Shape.totalSize τ.shape = 1)
    (hread : σ.entryFlat w 0 = some (.fin v)) :
    ∃ q, σ.wireQ w = some q ∧ q.entries = [v] := by
  unfold Hypernet.Valuation.entryFlat at hread
  split at hread
  · cases hread
  · next τ' hτ' =>
    have hττ : τ' = τ := by
      rw [hτ] at hτ'
      injection hτ' with h
      exact h.symm
    subst hττ
    have hlen : (σ w τ' hτ').val.length = 1 := by
      rw [(σ w τ' hτ').property, h1]
    obtain ⟨xe, hxe⟩ := List.length_eq_one_iff.mp hlen
    unfold TensorValue.entryE at hread
    rw [hxe] at hread
    simp only [List.getElem?_cons_zero] at hread
    have hxev : xe.val = ERat.fin v := Option.some.inj hread
    have hval : ERat.allFinQ ((σ w τ' hτ').val.map Subtype.val)
        = some [v] := by
      rw [hxe]
      show ERat.allFinQ [xe.val] = some [v]
      rw [hxev]
      rfl
    unfold Hypernet.Valuation.wireQ
    split
    · next hnone => rw [hτ'] at hnone; cases hnone
    · next τ'' hτ'' =>
      have hττ'' : τ'' = τ' := by
        rw [hτ'] at hτ''
        injection hτ'' with h
        exact h.symm
      subst hττ''
      split
      · next hfnone =>
        exact absurd (hval.symm.trans hfnone) (by simp)
      · next l hlsome =>
        refine ⟨_, rfl, ?_⟩
        show l = [v]
        have := hval.symm.trans hlsome
        injection this with h
        exact h.symm

theorem Hypernet.Valuation.wireQ_of_unit_entryAt0 {H : Hypernet}
    (σ : H.Valuation) {w : Wire} {τ : TensorType} {v : ℚ}
    (hτ : H.wireType w = some τ) (hsh : τ.shape = [1])
    (hread : σ.entryAt w [0] = some (.fin v)) :
    ∃ q, σ.wireQ w = some q ∧ q.entries = [v] := by
  unfold Hypernet.Valuation.entryAt at hread
  split at hread
  · cases hread
  · next τ' hτ' =>
    have hττ : τ' = τ := by
      rw [hτ] at hτ'
      injection hτ' with h
      exact h.symm
    subst hττ
    rw [hsh] at hread
    rw [show Shape.flatten [1] [0] = some 0 from rfl] at hread
    simp only [Option.bind_some] at hread

    have hlen : (σ w τ' hτ').val.length = 1 := by
      rw [(σ w τ' hτ').property, hsh]
      rfl
    obtain ⟨xe, hxe⟩ := List.length_eq_one_iff.mp hlen
    unfold TensorValue.entryE at hread
    rw [hxe] at hread
    simp only [List.getElem?_cons_zero] at hread
    have hxev : xe.val = ERat.fin v := Option.some.inj hread
    have hval : ERat.allFinQ ((σ w τ' hτ').val.map Subtype.val)
        = some [v] := by
      rw [hxe]
      show ERat.allFinQ [xe.val] = some [v]
      rw [hxev]
      rfl
    unfold Hypernet.Valuation.wireQ
    split
    · next hnone => rw [hτ'] at hnone; cases hnone
    · next τ'' hτ'' =>
      have hττ'' : τ'' = τ' := by
        rw [hτ'] at hτ''
        injection hτ'' with h
        exact h.symm
      subst hττ''
      split
      · next hfnone =>
        exact absurd (hval.symm.trans hfnone) (by simp)
      · next l hlsome =>
        refine ⟨_, rfl, ?_⟩
        show l = [v]
        have := hval.symm.trans hlsome
        injection this with h
        exact h.symm

theorem Hypernet.Valuation.wireQ_scalar_entryAt0 {H : Hypernet}
    (σ : H.Valuation) {w : Wire} {q : QTensor} {v : ℚ}
    (hq : σ.wireQ w = some q)
    (hread : σ.entryAt w [0] = some (.fin v))
    (hs : q.shape = [1]) :
    q.scalar = v := by
  obtain ⟨τ, hτ, hsh⟩ := Hypernet.Valuation.wireQ_shape σ hq
  have hτsh : τ.shape = [1] := by
    rw [← hsh]
    exact hs
  obtain ⟨q', hq', hent⟩ :=
    Hypernet.Valuation.wireQ_of_unit_entryAt0 σ hτ hτsh hread
  have hqq : q = q' := by
    rw [hq] at hq'
    injection hq' with h
  subst hqq
  show q.entries.getD 0 0 = v
  rw [hent]
  rfl

theorem holds_eq_var_const {H : Hypernet} (σ : H.Valuation) {o : Wire}
    {q : QTensor} {c : ℚ} (hq : σ.wireQ o = some q)
    (hent : q.entries = [c]) :
    Formula.holds σ (.atom .eq (.var o) (.const c)) := by
  refine ⟨q, ⟨[], [c], rfl⟩, hq, rfl, ?_⟩
  unfold QTensor.rel2
  by_cases hs : q.shape = ([] : Shape)
  · rw [if_pos hs]
    intro p hp
    rw [hent] at hp
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    subst hp
    rfl
  · rw [if_neg hs, if_neg hs, if_pos rfl]
    intro e he
    rw [hent] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    rfl

theorem Formula.holds_chainAnd {H : Hypernet} (σ : H.Valuation) :
    ∀ (l : List Formula), (∀ f ∈ l, Formula.holds σ f) →
      Formula.holds σ (Formula.chainAnd l)
  | [], _ => trivial
  | [f], h => h f (by simp)
  | f :: g :: rest, h =>
    ⟨h f (by simp),
     Formula.holds_chainAnd σ (g :: rest)
       (fun f' hf' => h f' (by simp [List.mem_cons.mp hf']))⟩

theorem holds_cellOneHot {H : Hypernet} (σ : H.Valuation) {schema : SimpC}
    {outputs : List Wire} {k : Fin schema.cells.length} {F : Formula}
    (hbuild : cellOneHotForm schema outputs k F)
    (houts : ∀ o ∈ outputs, ∃ τ, H.wireType o = some τ ∧
      Shape.totalSize τ.shape = 1)
    (hsem : ∀ j : Fin outputs.length,
      σ.entryFlat (outputs.get j) 0
        = some (.fin (if j.val = k.val then 1 else 0))) :
    Formula.holds σ F := by
  simp only [cellOneHotForm, cellOneHotBuild] at hbuild
  split at hbuild
  case isFalse => cases hbuild
  case isTrue harity =>
  injection hbuild with hbuild
  subst hbuild
  have hkl : k.val < outputs.length := by
    rw [harity]
    exact k.isLt
  constructor
  ·
    have hread := hsem ⟨k.val, hkl⟩
    simp only [if_pos rfl] at hread
    have hgetd : outputs.getD k.val 0 = outputs.get ⟨k.val, hkl⟩ := by
      rw [List.getD_eq_getElem _ _ hkl]
      rfl
    obtain ⟨τ, hτ, h1⟩ := houts (outputs.get ⟨k.val, hkl⟩)
      (List.get_mem outputs ⟨k.val, hkl⟩)
    obtain ⟨q, hq, hent⟩ :=
      Hypernet.Valuation.wireQ_of_unit_entry σ hτ h1 hread
    rw [hgetd]
    exact holds_eq_var_const σ hq hent
  ·
    apply Formula.holds_chainAnd
    intro f hf
    obtain ⟨j, hjmem, rfl⟩ := List.mem_map.mp hf
    rw [List.mem_filter] at hjmem
    obtain ⟨hjrange, hjne⟩ := hjmem
    rw [List.mem_range] at hjrange
    have hjne' : j ≠ k.val := by simpa using hjne
    have hread := hsem ⟨j, hjrange⟩
    simp only [if_neg hjne'] at hread
    have hgetd : outputs.getD j 0 = outputs.get ⟨j, hjrange⟩ := by
      rw [List.getD_eq_getElem _ _ hjrange]
      rfl
    obtain ⟨τ, hτ, h1⟩ := houts (outputs.get ⟨j, hjrange⟩)
      (List.get_mem outputs ⟨j, hjrange⟩)
    obtain ⟨q, hq, hent⟩ :=
      Hypernet.Valuation.wireQ_of_unit_entry σ hτ h1 hread
    rw [hgetd]
    exact holds_eq_var_const σ hq hent

theorem sound_cellInInterior {H : Hypernet} {seq premise : Sequent}
    {schema : SimpC} {input : Wire} {outputs : List Wire}
    {whichI : Fin schema.cells.length}
    (ih : premise.semanticallyValid H)
    (happ : PrimApp.cell schema input outputs ∈ H.applications)
    (hinshape : ∃ τ, H.wireType input = some τ ∧
      τ.shape = [schema.ambDim])
    (houts : ∀ o ∈ outputs, ∃ τ, H.wireType o = some τ ∧
      Shape.totalSize τ.shape = 1)
    (hpre : seq.pre = premise.pre)
    (hint : cellStrictInteriorForm schema (.var input) whichI premise.post)
    (hpost : cellOneHotForm schema outputs whichI seq.post) :
    seq.semanticallyValid H := by
  obtain ⟨hd1, a, b, V₀, V₁, hfil, hVa, hVb, hVne, hF⟩ :=
    cellStrictInteriorBuild_spec hint
  intro σ hadm hpre'
  rw [hpre] at hpre'
  have hbar := ih σ hadm hpre'
  rw [hF] at hbar
  obtain ⟨hA, hB⟩ := hbar

  obtain ⟨hdisj, x, hx, kk, hkreg, honehot⟩ := hadm _ happ

  obtain ⟨qa0, qz0, hqa0, hqz0, hrelA⟩ := hA
  obtain ⟨q, hq⟩ := affine_evalQ_inv σ hqa0
  have hwq : σ.wireQ input = some q := hq
  obtain ⟨τin, hτin, hshin⟩ := hinshape
  have hqsh : q.shape = [1] := by
    obtain ⟨τ', hτ', hsh'⟩ := Hypernet.Valuation.wireQ_shape σ hwq
    rw [hτin] at hτ'
    injection hτ' with hττ
    rw [hsh', ← hττ, hshin, hd1]
  have hqsing : SingletonShape q.shape := Or.inr hqsh

  have hd1' : 0 < schema.ambDim := by omega
  have hxtie : q.scalar = x ⟨0, hd1'⟩ := by
    have hr := hx ⟨0, hd1'⟩
    exact Hypernet.Valuation.wireQ_scalar_entryAt0 σ hwq hr hqsh

  obtain ⟨qa, hqa, hsqa, hvqa⟩ :=
    affine_evalQ σ hq hqsing (V₁ / (V₁ - V₀)) (-1 / (V₁ - V₀))
  have hqaeq : qa0 = qa := by
    have h' := hqa0.symm.trans hqa
    injection h'
  subst hqaeq
  have hz : qz0 = ⟨[], [0], rfl⟩ := by
    have h' : some (⟨[], [0], rfl⟩ : QTensor) = some qz0 := hqz0
    injection h' with h'
    exact h'.symm
  subst hz
  have hscalA := (QTensor.rel2_singleton hsqa (Or.inl rfl)).mp hrelA
  rw [hvqa] at hscalA

  obtain ⟨qb0, qzb0, hqb0, hqzb0, hrelB⟩ := hB
  obtain ⟨qb, hqb, hsqb, hvqb⟩ :=
    affine_evalQ σ hq hqsing (-V₀ / (V₁ - V₀)) (1 / (V₁ - V₀))
  have hqbeq : qb0 = qb := by
    have h' := hqb0.symm.trans hqb
    injection h'
  subst hqbeq
  have hzb : qzb0 = ⟨[], [0], rfl⟩ := by
    have h' : some (⟨[], [0], rfl⟩ : QTensor) = some qzb0 := hqzb0
    injection h' with h'
    exact h'.symm
  subst hzb
  have hscalB := (QTensor.rel2_singleton hsqb (Or.inl rfl)).mp hrelB
  rw [hvqb] at hscalB

  have harithA : V₁ / (V₁ - V₀) + -1 / (V₁ - V₀) * q.scalar
      = (V₁ - q.scalar) / (V₁ - V₀) := by ring
  have harithB : -V₀ / (V₁ - V₀) + 1 / (V₁ - V₀) * q.scalar
      = (q.scalar - V₀) / (V₁ - V₀) := by ring
  have hcellWF := schema.cellsWF _ (List.get_mem schema.cells whichI)
  have hstrict : MaskRegionStrict schema
      (schema.cells.get whichI).1 (schema.cells.get whichI).2 x := by
    refine maskRegionStrict_pair_intro hfil
      (fun v hv => hcellWF.2.1 v hv) hVa hVb hVne hd1 ⟨0, hd1'⟩
      ?_ ?_ ?_ ?_
    · intro hexta
      rw [if_pos hexta] at hscalA
      rw [← hxtie, ← harithA]
      exact hscalA
    · intro hexta
      rw [hexta, if_neg Bool.false_ne_true] at hscalA
      rw [← hxtie, ← harithA]
      exact hscalA
    · intro hextb
      rw [if_pos hextb] at hscalB
      rw [← hxtie, ← harithB]
      exact hscalB
    · intro hextb
      rw [hextb, if_neg Bool.false_ne_true] at hscalB
      rw [← hxtie, ← harithB]
      exact hscalB

  have hkI : kk = whichI := by
    by_contra hne'
    exact hdisj whichI kk (fun hc => hne' hc.symm) x hstrict hkreg
  subst hkI
  exact holds_cellOneHot σ hpost houts honehot

theorem sound_cellOut {H : Hypernet} {seq premise : Sequent}
    {schema : SimpC} {input : Wire} {outputs : List Wire}
    {whichJ : Fin schema.cells.length} {wv : Fin schema.nVertices}
    (ih : premise.semanticallyValid H)
    (happ : PrimApp.cell schema input outputs ∈ H.applications)
    (hinshape : ∃ τ, H.wireType input = some τ ∧
      τ.shape = [schema.ambDim])
    (houts : ∀ o ∈ outputs, ∃ τ, H.wireType o = some τ ∧
      Shape.totalSize τ.shape = 1)
    (hpre : seq.pre = premise.pre)
    (hwit : cellOutWitnessForm schema (.var input) whichJ wv premise.post)
    (hpost : cellOutZeroForm schema outputs whichJ seq.post) :
    seq.semanticallyValid H := by
  obtain ⟨hd1, hwmask, a, b, V₀, V₁, hfil, hVa, hVb, hVne, hsel⟩ :=
    cellOutWitnessBuild_spec hwit
  intro σ hadm hpre'
  rw [hpre] at hpre'
  have hbar := ih σ hadm hpre'

  obtain ⟨-, x, hx, kk, hkreg, honehot⟩ := hadm _ happ
  have hd1' : 0 < schema.ambDim := by omega

  have hktie : kk ≠ whichJ := by
    intro hkJ
    rw [hkJ] at hkreg

    have hsigns := maskRegion_pair_elim hfil hVa hVb hVne ⟨0, hd1'⟩ hkreg
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hsigns

    rcases hsel with ⟨hwa, hFsel⟩ | ⟨hwb, hFsel⟩
    ·
      rw [hFsel] at hbar
      obtain ⟨qa0, qz0, hqa0, hqz0, hrelA⟩ := hbar
      obtain ⟨q, hq⟩ := affine_evalQ_inv σ hqa0
      have hwq : σ.wireQ input = some q := hq
      obtain ⟨τin, hτin, hshin⟩ := hinshape
      have hqsh : q.shape = [1] := by
        obtain ⟨τ', hτ', hsh'⟩ := Hypernet.Valuation.wireQ_shape σ hwq
        rw [hτin] at hτ'
        injection hτ' with hττ
        rw [hsh', ← hττ, hshin, hd1]
      have hxtie : q.scalar = x ⟨0, hd1'⟩ :=
        Hypernet.Valuation.wireQ_scalar_entryAt0 σ hwq (hx ⟨0, hd1'⟩) hqsh
      obtain ⟨qa, hqa, hsqa, hvqa⟩ :=
        affine_evalQ σ hq (Or.inr hqsh) (V₁ / (V₁ - V₀)) (-1 / (V₁ - V₀))
      have hqaeq : qa0 = qa := by
        have h' := hqa0.symm.trans hqa
        injection h'
      subst hqaeq
      have hz : qz0 = ⟨[], [0], rfl⟩ := by
        have h' : some (⟨[], [0], rfl⟩ : QTensor) = some qz0 := hqz0
        injection h' with h'
        exact h'.symm
      subst hz
      have hscalA := (QTensor.rel2_singleton hsqa (Or.inl rfl)).mp hrelA
      rw [hvqa] at hscalA
      have harithA : V₁ / (V₁ - V₀) + -1 / (V₁ - V₀) * q.scalar
          = (V₁ - q.scalar) / (V₁ - V₀) := by ring
      cases hext : (schema.cells.get whichJ).2 a with
      | true =>
        rw [if_pos hext] at hscalA
        have hstrict : (0 : ℚ) < V₁ / (V₁ - V₀) + -1 / (V₁ - V₀) * q.scalar :=
          hscalA
        have hweak := hs1 hext
        rw [← hxtie, ← harithA] at hweak
        linarith
      | false =>
        rw [hext, if_neg Bool.false_ne_true] at hscalA
        have hstrict : V₁ / (V₁ - V₀) + -1 / (V₁ - V₀) * q.scalar < 0 :=
          hscalA
        have hweak := hs2 hext
        rw [← hxtie, ← harithA] at hweak
        linarith
    ·
      rw [hFsel] at hbar
      obtain ⟨qb0, qz0, hqb0, hqz0, hrelB⟩ := hbar
      obtain ⟨q, hq⟩ := affine_evalQ_inv σ hqb0
      have hwq : σ.wireQ input = some q := hq
      obtain ⟨τin, hτin, hshin⟩ := hinshape
      have hqsh : q.shape = [1] := by
        obtain ⟨τ', hτ', hsh'⟩ := Hypernet.Valuation.wireQ_shape σ hwq
        rw [hτin] at hτ'
        injection hτ' with hττ
        rw [hsh', ← hττ, hshin, hd1]
      have hxtie : q.scalar = x ⟨0, hd1'⟩ :=
        Hypernet.Valuation.wireQ_scalar_entryAt0 σ hwq (hx ⟨0, hd1'⟩) hqsh
      obtain ⟨qb, hqb, hsqb, hvqb⟩ :=
        affine_evalQ σ hq (Or.inr hqsh) (-V₀ / (V₁ - V₀)) (1 / (V₁ - V₀))
      have hqbeq : qb0 = qb := by
        have h' := hqb0.symm.trans hqb
        injection h'
      subst hqbeq
      have hz : qz0 = ⟨[], [0], rfl⟩ := by
        have h' : some (⟨[], [0], rfl⟩ : QTensor) = some qz0 := hqz0
        injection h' with h'
        exact h'.symm
      subst hz
      have hscalB := (QTensor.rel2_singleton hsqb (Or.inl rfl)).mp hrelB
      rw [hvqb] at hscalB
      have harithB : -V₀ / (V₁ - V₀) + 1 / (V₁ - V₀) * q.scalar
          = (q.scalar - V₀) / (V₁ - V₀) := by ring
      cases hext : (schema.cells.get whichJ).2 b with
      | true =>
        rw [if_pos hext] at hscalB
        have hstrict : (0 : ℚ) < -V₀ / (V₁ - V₀) + 1 / (V₁ - V₀) * q.scalar :=
          hscalB
        have hweak := hs3 hext
        rw [← hxtie, ← harithB] at hweak
        linarith
      | false =>
        rw [hext, if_neg Bool.false_ne_true] at hscalB
        have hstrict : -V₀ / (V₁ - V₀) + 1 / (V₁ - V₀) * q.scalar < 0 :=
          hscalB
        have hweak := hs4 hext
        rw [← hxtie, ← harithB] at hweak
        linarith

  simp only [cellOutZeroForm, cellOutZeroBuild] at hpost
  split at hpost
  case isFalse => cases hpost
  case isTrue harity =>
  injection hpost with hpost
  rw [← hpost]
  have hjl : whichJ.val < outputs.length := by
    rw [harity]
    exact whichJ.isLt
  have hread := honehot ⟨whichJ.val, hjl⟩
  have hne0 : (⟨whichJ.val, hjl⟩ : Fin outputs.length).val ≠ kk.val := by
    intro hc
    exact hktie (Fin.ext hc.symm)
  rw [if_neg hne0] at hread
  have hgetd : outputs.getD whichJ.val 0 = outputs.get ⟨whichJ.val, hjl⟩ := by
    rw [List.getD_eq_getElem _ _ hjl]
    rfl
  obtain ⟨τ, hτ, h1⟩ := houts (outputs.get ⟨whichJ.val, hjl⟩)
    (List.get_mem outputs ⟨whichJ.val, hjl⟩)
  obtain ⟨q, hq, hent⟩ :=
    Hypernet.Valuation.wireQ_of_unit_entry σ hτ h1 hread
  rw [hgetd]
  exact holds_eq_var_const σ hq hent

theorem QTensor.rel2_refl {r : ℚ → ℚ → Prop} (hr : ∀ x, r x x)
    (a : QTensor) : QTensor.rel2 r a a := by
  unfold QTensor.rel2
  rw [if_pos rfl]
  have hzip : ∀ (l : List ℚ), ∀ p ∈ l.zip l, r p.1 p.2 := by
    intro l
    induction l with
    | nil => intro p hp; cases hp
    | cons x xs ih =>
      intro p hp
      rw [List.zip_cons_cons] at hp
      rcases List.mem_cons.mp hp with h | h
      · subst h; exact hr x
      · exact ih p h
  exact hzip a.entries

theorem QTensor.rel2_symm {r : ℚ → ℚ → Prop}
    (hr : ∀ x y, r x y → r y x) {a b : QTensor}
    (h : QTensor.rel2 r a b) : QTensor.rel2 r b a := by
  unfold QTensor.rel2 at h ⊢
  have hswap : ∀ (l1 l2 : List ℚ), ∀ p : ℚ × ℚ, p ∈ l1.zip l2 →
      (p.2, p.1) ∈ l2.zip l1 := by
    intro l1
    induction l1 with
    | nil => intro l2 p hp; simp at hp
    | cons x xs ih =>
      intro l2 p hp
      cases l2 with
      | nil => simp at hp
      | cons y ys =>
        rw [List.zip_cons_cons] at hp ⊢
        rcases List.mem_cons.mp hp with hh | hh
        · subst hh
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih ys p hh)
  by_cases hab : a.shape = b.shape
  · rw [if_pos hab] at h
    rw [if_pos hab.symm]
    intro p hp
    exact hr _ _ (h (p.2, p.1) (hswap b.entries a.entries p hp))
  · rw [if_neg hab] at h
    rw [if_neg (fun hc => hab hc.symm)]
    by_cases hae : a.shape = []
    · rw [if_pos hae] at h
      have hbe : ¬ b.shape = [] := fun hc => hab (hae.trans hc.symm)
      rw [if_neg hbe, if_pos hae]
      intro x hx
      exact hr _ _ (h x hx)
    · rw [if_neg hae] at h
      by_cases hbe : b.shape = []
      · rw [if_pos hbe] at h
        rw [if_pos hbe]
        intro y hy
        exact hr _ _ (h y hy)
      · rw [if_neg hbe] at h
        exact h.elim

/-- Two `rel2` facts at the SAME tensor pair combine pointwise: the
broadcast branch taken is a function of the two shapes alone, so the
quantified domains coincide and the pointwise conjunction lifts.
(Stated for `sound_antisym`; any pointwise combination rides it.) -/
theorem QTensor.rel2_conj {r s t : ℚ → ℚ → Prop}
    (hrst : ∀ x y, r x y → s x y → t x y) {a b : QTensor}
    (hr : QTensor.rel2 r a b) (hs : QTensor.rel2 s a b) :
    QTensor.rel2 t a b := by
  unfold QTensor.rel2 at hr hs ⊢
  by_cases h1 : a.shape = b.shape
  · rw [if_pos h1] at hr hs ⊢
    exact fun p hp => hrst p.1 p.2 (hr p hp) (hs p hp)
  · rw [if_neg h1] at hr hs ⊢
    by_cases h2 : a.shape = []
    · rw [if_pos h2] at hr hs ⊢
      exact fun y hy => hrst _ y (hr y hy) (hs y hy)
    · rw [if_neg h2] at hr hs ⊢
      by_cases h3 : b.shape = []
      · rw [if_pos h3] at hr hs ⊢
        exact fun x hx => hrst x _ (hr x hx) (hs x hx)
      · rw [if_neg h3] at hr hs ⊢
        exact hr.elim

theorem sound_eqRefl {H : Hypernet} {seq : Sequent} {t : Term}
    (htyDef : ∃ s, t.bshape H = some s) (hfin : t.finWires H)
    (hpost : seq.post = .atom .eq t t) :
    seq.semanticallyValid H := by
  intro σ _ _
  rw [hpost]
  obtain ⟨s, hs⟩ := htyDef
  obtain ⟨q, hq, -⟩ := Term.evalQ_defined_of_bshape_fin σ t s hs hfin
  exact ⟨q, q, hq, hq, QTensor.rel2_refl (fun _ => rfl) q⟩

theorem sound_eqSym {H : Hypernet} {seq premise : Sequent} {tT tU : Term}
    (ih : premise.semanticallyValid H)
    (hpre : seq.pre = premise.pre)
    (hpremPost : premise.post = .atom .eq tT tU)
    (hpost : seq.post = .atom .eq tU tT) :
    seq.semanticallyValid H := by
  intro σ hadm hpre'
  rw [hpre] at hpre'
  have h := ih σ hadm hpre'
  rw [hpremPost] at h
  obtain ⟨a, b, ha, hb, hrel⟩ := h
  rw [hpost]
  exact ⟨b, a, hb, ha,
    QTensor.rel2_symm (fun x y (hxy : x = y) => hxy.symm) hrel⟩

/-- Antisym: `≤` and `≥` premise validities at the same term pair force
the equality atom — entrywise `le_antisymm` lifted through `rel2`
(`QTensor.rel2_conj`: both premises constrain the same evaluated pair,
so the broadcast branches align).  Like `sound_eqSym` and unlike
`sound_eqRefl`, no typing pack is needed: the premise atoms only hold
where both sides already evaluate finitely, which is exactly the
evaluation evidence the conclusion atom needs.  Core tier: the
equality-from-inequalities inference has no derivation from the other
rules — provably, since derivable equalities from equality-free
contexts have canonically-equal sides. -/
theorem sound_antisym {H : Hypernet} {seq premiseLe premiseGe : Sequent}
    {tT tU : Term}
    (ihLe : premiseLe.semanticallyValid H)
    (ihGe : premiseGe.semanticallyValid H)
    (hpreLe : seq.pre = premiseLe.pre)
    (hpreGe : seq.pre = premiseGe.pre)
    (hpremLePost : premiseLe.post = .atom .le tT tU)
    (hpremGePost : premiseGe.post = .atom .ge tT tU)
    (hpost : seq.post = .atom .eq tT tU) :
    seq.semanticallyValid H := by
  intro σ hadm hpre'
  have hLe := ihLe σ hadm (by rw [← hpreLe]; exact hpre')
  have hGe := ihGe σ hadm (by rw [← hpreGe]; exact hpre')
  rw [hpremLePost] at hLe
  rw [hpremGePost] at hGe
  obtain ⟨a, b, ha, hb, hle⟩ := hLe
  obtain ⟨a', b', ha', hb', hge⟩ := hGe
  rw [ha] at ha'
  rw [hb] at hb'
  injection ha' with haa
  injection hb' with hbb
  rw [← haa, ← hbb] at hge
  rw [hpost]
  exact ⟨a, b, ha, hb,
    QTensor.rel2_conj
      (fun x y (hxy : x ≤ y) (hyx : y ≤ x) => le_antisymm hxy hyx)
      hle hge⟩

theorem Formula.holds_of_conjGet {H : Hypernet} {σ : H.Valuation} :
    ∀ {π : ConjPath} {Γ d : Formula},
    Γ.conjGet? π = some d → Γ.holds σ → d.holds σ := by
  intro π
  induction π with
  | here =>
    intro Γ d hget hΓ
    simp only [Formula.conjGet?] at hget
    injection hget with h
    exact h ▸ hΓ
  | left p ih =>
    intro Γ d hget hΓ
    cases Γ with
    | and l r =>
      simp only [Formula.conjGet?] at hget
      exact ih hget hΓ.1
    | atom b tl tr => nomatch hget
    | inRegion t Δ S => nomatch hget
    | or l r => nomatch hget
    | tt => nomatch hget
    | ff => nomatch hget
  | right p ih =>
    intro Γ d hget hΓ
    cases Γ with
    | and l r =>
      simp only [Formula.conjGet?] at hget
      exact ih hget hΓ.2
    | atom b tl tr => nomatch hget
    | inRegion t Δ S => nomatch hget
    | or l r => nomatch hget
    | tt => nomatch hget
    | ff => nomatch hget

theorem Formula.holds_conjReplace {H : Hypernet} {σ : H.Valuation} :
    ∀ {π : ConjPath} {Γ Γ' g : Formula},
    Γ.conjReplace? π g = some Γ' → Γ.holds σ → g.holds σ → Γ'.holds σ := by
  intro π
  induction π with
  | here =>
    intro Γ Γ' g hrep hΓ hg
    simp only [Formula.conjReplace?] at hrep
    injection hrep with h
    exact h ▸ hg
  | left p ih =>
    intro Γ Γ' g hrep hΓ hg
    cases Γ with
    | and l r =>
      simp only [Formula.conjReplace?] at hrep
      cases hmap : l.conjReplace? p g with
      | none => rw [hmap] at hrep; nomatch hrep
      | some l' =>
        rw [hmap] at hrep
        injection hrep with h
        rw [← h]
        exact ⟨ih hmap hΓ.1 hg, hΓ.2⟩
    | atom b tl tr => nomatch hrep
    | inRegion t Δ S => nomatch hrep
    | or l r => nomatch hrep
    | tt => nomatch hrep
    | ff => nomatch hrep
  | right p ih =>
    intro Γ Γ' g hrep hΓ hg
    cases Γ with
    | and l r =>
      simp only [Formula.conjReplace?] at hrep
      cases hmap : r.conjReplace? p g with
      | none => rw [hmap] at hrep; nomatch hrep
      | some r' =>
        rw [hmap] at hrep
        injection hrep with h
        rw [← h]
        exact ⟨hΓ.1, ih hmap hΓ.2 hg⟩
    | atom b tl tr => nomatch hrep
    | inRegion t Δ S => nomatch hrep
    | or l r => nomatch hrep
    | tt => nomatch hrep
    | ff => nomatch hrep

theorem Formula.conjGet_of_conjReplace :
    ∀ {π : ConjPath} {Γ Γ' g : Formula},
    Γ.conjReplace? π g = some Γ' → Γ'.conjGet? π = some g := by
  intro π
  induction π with
  | here =>
    intro Γ Γ' g hrep
    simp only [Formula.conjReplace?] at hrep
    injection hrep with h
    rw [← h]
    simp only [Formula.conjGet?]
  | left p ih =>
    intro Γ Γ' g hrep
    cases Γ with
    | and l r =>
      simp only [Formula.conjReplace?] at hrep
      cases hmap : l.conjReplace? p g with
      | none => rw [hmap] at hrep; nomatch hrep
      | some l' =>
        rw [hmap] at hrep
        injection hrep with h
        rw [← h]
        simp only [Formula.conjGet?]
        exact ih hmap
    | atom b tl tr => nomatch hrep
    | inRegion t Δ S => nomatch hrep
    | or l r => nomatch hrep
    | tt => nomatch hrep
    | ff => nomatch hrep
  | right p ih =>
    intro Γ Γ' g hrep
    cases Γ with
    | and l r =>
      simp only [Formula.conjReplace?] at hrep
      cases hmap : r.conjReplace? p g with
      | none => rw [hmap] at hrep; nomatch hrep
      | some r' =>
        rw [hmap] at hrep
        injection hrep with h
        rw [← h]
        simp only [Formula.conjGet?]
        exact ih hmap
    | atom b tl tr => nomatch hrep
    | inRegion t Δ S => nomatch hrep
    | or l r => nomatch hrep
    | tt => nomatch hrep
    | ff => nomatch hrep

theorem Formula.conjReplace_back :
    ∀ {π : ConjPath} {Γ Γ' q g : Formula},
    Γ.conjGet? π = some q → Γ.conjReplace? π g = some Γ' →
    Γ'.conjReplace? π q = some Γ := by
  intro π
  induction π with
  | here =>
    intro Γ Γ' q g hget hrep
    simp only [Formula.conjGet?] at hget
    simp only [Formula.conjReplace?] at hrep ⊢
    injection hget with h1
    rw [h1]
  | left p ih =>
    intro Γ Γ' q g hget hrep
    cases Γ with
    | and l r =>
      simp only [Formula.conjGet?] at hget
      simp only [Formula.conjReplace?] at hrep
      cases hmap : l.conjReplace? p g with
      | none => rw [hmap] at hrep; nomatch hrep
      | some l' =>
        rw [hmap] at hrep
        injection hrep with h
        rw [← h]
        simp only [Formula.conjReplace?]
        rw [ih hget hmap]
        rfl
    | atom b tl tr => nomatch hrep
    | inRegion t Δ S => nomatch hrep
    | or l r => nomatch hrep
    | tt => nomatch hrep
    | ff => nomatch hrep
  | right p ih =>
    intro Γ Γ' q g hget hrep
    cases Γ with
    | and l r =>
      simp only [Formula.conjGet?] at hget
      simp only [Formula.conjReplace?] at hrep
      cases hmap : r.conjReplace? p g with
      | none => rw [hmap] at hrep; nomatch hrep
      | some r' =>
        rw [hmap] at hrep
        injection hrep with h
        rw [← h]
        simp only [Formula.conjReplace?]
        rw [ih hget hmap]
        rfl
    | atom b tl tr => nomatch hrep
    | inRegion t Δ S => nomatch hrep
    | or l r => nomatch hrep
    | tt => nomatch hrep
    | ff => nomatch hrep

theorem Formula.holds_of_forall_conjunct {H : Hypernet} (σ : H.Valuation) :
    ∀ (F : Formula), (∀ a ∈ F.conjunctList, Formula.holds σ a) →
      F.holds σ := by
  intro F
  induction F with
  | and l r ihl ihr =>
    intro h
    exact ⟨ihl (fun a ha => h a (List.mem_append.mpr (Or.inl ha))),
           ihr (fun a ha => h a (List.mem_append.mpr (Or.inr ha)))⟩
  | atom b tl tr => intro h; exact h _ (List.Mem.head _)
  | inRegion t Δ S => intro h; exact h _ (List.Mem.head _)
  | or l r _ _ => intro h; exact h _ (List.Mem.head _)
  | tt => intro _; trivial
  | ff => intro h; exact h _ (List.Mem.head _)

theorem premiseContains_holds {H : Hypernet} {σ : H.Valuation}
    {pre sub : Formula} (hc : premiseContains pre sub)
    (hpre : pre.holds σ) : sub.holds σ :=
  Formula.holds_of_forall_conjunct σ sub (fun a ha =>
    Formula.holds_of_mem_conjunctList σ pre hpre a (hc a ha))

structure PromiseStep where
  seq : Sequent
  supplier : Sequent
  consumer : Sequent
  contract : Formula
  path : ConjPath
  iface : List Wire
  ctx : Formula
  supplierPost : supplier.post = contract
  pathReads : consumer.pre.conjGet? path = some contract
  prePlumb : consumer.pre.conjReplace? path supplier.pre = some seq.pre
  postEq : seq.post = consumer.post
  ctxReads : consumer.pre.conjReplace? path .tt = some ctx
  contractConfined : formulaWiresWithin contract iface
  separation : wiresSeparated supplier.pre ctx seq.post iface

theorem sound_promise {H : Hypernet} (st : PromiseStep)
    (ihs : st.supplier.semanticallyValid H)
    (ihc : st.consumer.semanticallyValid H) :
    st.seq.semanticallyValid H := by
  intro σ hadm hpre
  have hget' : st.seq.pre.conjGet? st.path = some st.supplier.pre :=
    Formula.conjGet_of_conjReplace st.prePlumb
  have hsup : Formula.holds σ st.supplier.pre :=
    Formula.holds_of_conjGet hget' hpre
  have hQ : Formula.holds σ st.contract :=
    st.supplierPost ▸ ihs σ hadm hsup
  have hback : st.seq.pre.conjReplace? st.path st.contract
      = some st.consumer.pre :=
    Formula.conjReplace_back st.pathReads st.prePlumb
  have hcons : Formula.holds σ st.consumer.pre :=
    Formula.holds_conjReplace hback hpre hQ
  exact st.postEq ▸ ihc σ hadm hcons

structure SyzygyStep (H : Hypernet) where
  seq : Sequent
  components : List Sequent
  combination : Term
  conclusion : Term
  preContains : ∀ c ∈ components, premiseContains seq.pre c.pre
  conclShape : ∃ s, conclusion.bshape H = some s
  conclFin : conclusion.finWires H
  wiresPos : ∀ w ∈ seq.pre.freeWires ++ conclusion.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape
  compPostWiresPos : ∀ c ∈ components, ∀ w ∈ c.post.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape
  valid : syzygyCombinationValid combination components seq.pre conclusion
  postForm : syzygyConclusionForm conclusion seq.post

theorem holds_of_syzygyConclusionForm {H : Hypernet} {σ : H.Valuation}
    {conclusion : Term} {F : Formula}
    (hle : Formula.holds σ (.atom .le conclusion (.const 0)))
    (hform : syzygyConclusionForm conclusion F) :
    Formula.holds σ F := by
  rcases hform with hZ | hG | hL
  ·
    rw [hZ]; exact hle
  ·
    obtain ⟨e, hce, hpe⟩ := hG
    rw [hpe]
    rw [hce] at hle
    obtain ⟨a, a0, ha, ha0, hrel⟩ := hle
    have ha0' : a0 = (⟨[], [0], rfl⟩ : QTensor) :=
      (Option.some.inj (show some (⟨[], [0], rfl⟩ : QTensor) = some a0 from ha0)).symm
    subst ha0'
    obtain ⟨bb, hbb, hab⟩ : ∃ bb, Term.evalQ σ e = some bb ∧
        QTensor.map1 Neg.neg bb = a := by
      simpa only [Term.evalQ, Option.map_eq_some_iff] using ha
    subst hab
    refine ⟨bb, ⟨[], [0], rfl⟩, hbb, rfl, ?_⟩
    rw [QTensor.rel2_zero_right]
    rw [QTensor.rel2_zero_right] at hrel
    intro y hy
    have hmem : Neg.neg y ∈ (QTensor.map1 Neg.neg bb).entries :=
      List.mem_map.mpr ⟨y, hy, rfl⟩
    have h1 : (Neg.neg y : ℚ) ≤ 0 := hrel _ hmem
    show (0 : ℚ) ≤ y
    linarith
  ·
    obtain ⟨l, r, hcs, hpl⟩ := hL
    rw [hpl]
    rw [hcs] at hle
    obtain ⟨d, z, hd, hz, hrel⟩ := hle
    have hzz : z = (⟨[], [0], rfl⟩ : QTensor) :=
      (Option.some.inj (show some (⟨[], [0], rfl⟩ : QTensor) = some z from hz)).symm
    subst hzz
    obtain ⟨al, ar, hal, har, hmap⟩ := Term.evalQ_sub_inv σ hd
    exact ⟨al, ar, hal, har, (QTensor.rel2_sub_zero_iff hmap).mp hrel⟩

theorem sound_syzygy {H : Hypernet} (st : SyzygyStep H)
    (hcomps : ∀ c ∈ st.components, c.semanticallyValid H) :
    st.seq.semanticallyValid H := by
  intro σ hadm hpre'
  refine holds_of_syzygyConclusionForm ?_ st.postForm
  have hvalid := st.valid
  unfold syzygyCombinationValid syzygyCheck at hvalid
  rw [Bool.or_eq_true, Bool.or_eq_true] at hvalid
  rcases hvalid with (hvalid | hvalid) | hvalid

  · unfold syzygyCheckCore at hvalid
    split at hvalid
    · cases hvalid
    · next entries hentries =>
      rw [Bool.and_eq_true] at hvalid
      obtain ⟨hvalid, hsum⟩ := hvalid
      rw [Bool.and_eq_true] at hvalid
      obtain ⟨hcix, hall⟩ := hvalid
      have hsum' := of_decide_eq_true hsum

      obtain ⟨s, hs⟩ := st.conclShape
      have hcw := wire_discipline_of_bshape_fin σ hs st.conclFin hcix
      obtain ⟨qc, hqc⟩ : ∃ qc, Term.evalQ σ st.conclusion = some qc := by
        by_cases hsnil : s = []
        · subst hsnil
          have hsing : ∀ w ∈ st.conclusion.freeWires, ∃ qw,
              σ.wireQ w = some qw ∧ SingletonShape qw.shape := by
            intro w hw
            obtain ⟨qw, hqw, hqs⟩ := hcw w hw
            exact ⟨qw, hqw, by
              rcases hqs with h1 | h1
              · exact Or.inl h1
              · exact Or.inl h1⟩
          obtain ⟨qc, hqc, _, _⟩ :=
            Term.evalQ_total_singleton σ st.conclusion hsing hcix
          exact ⟨qc, hqc⟩
        · obtain ⟨qc, hqc, _, _, _⟩ :=
            Term.evalQ_brRead σ s st.conclusion hcw hcix
          exact ⟨qc, hqc⟩
      refine ⟨qc, ⟨[], [0], rfl⟩, hqc, rfl, ?_⟩
      apply QTensor.rel2_const_right
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      have hposC : ∀ w ∈ st.conclusion.freeWires, ∀ qw,
          σ.wireQ w = some qw → 0 < Shape.totalSize qw.shape :=
        fun w hw qw hqw => wireQ_pos_of_type_pos σ hqw
          (st.wiresPos w (List.mem_append.mpr (Or.inr hw)))
      have hcr := Term.evalQ_brReadC σ hqc hposC hcix i
      have hx' : qc.entries[i] = qc.brReadC i := by
        rw [QTensor.brReadC_in_range hi, List.getD_eq_getElem _ _ hi]
      show qc.entries[i] ≤ QTensor.scalar ⟨[], [0], rfl⟩
      rw [hx', hcr]
      show QArith.Poly.eval (σ.entryValC i) st.conclusion.toPoly ≤ 0
      rw [← hsum']
      apply farkas_fold_eval_nonpos
      intro e he
      obtain ⟨l, et⟩ := e
      have h1 := List.all_eq_true.mp hall (l, et) he
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h1
      obtain ⟨hle, hsrc⟩ := h1
      refine ⟨of_decide_eq_true hle, ?_⟩
      rcases hsrc with hcomp | hwire
      ·
        obtain ⟨c, hc, hpa⟩ := List.any_eq_true.mp hcomp
        simp only [Bool.and_eq_true] at hpa
        obtain ⟨hcaix, hpa⟩ := hpa
        obtain ⟨pa, hpaMem, hpaEq⟩ := List.any_eq_true.mp hpa
        have hpaEq' : pa = et.toPoly := of_decide_eq_true hpaEq
        have hcHolds : Formula.holds σ c.post :=
          hcomps c hc σ hadm
            (premiseContains_holds (st.preContains c hc) hpre')
        rw [← hpaEq']
        exact atomLeZeroPolys_sound_entryC σ hcHolds
          (st.compPostWiresPos c hc) hcaix i pa hpaMem
      ·
        obtain ⟨aF, haF, h2⟩ := List.any_eq_true.mp hwire
        simp only [Bool.and_eq_true] at h2
        obtain ⟨⟨-, haix⟩, hpa⟩ := h2
        obtain ⟨pa, hpaMem, hpaEq⟩ := List.any_eq_true.mp hpa
        have hpaEq' : pa = et.toPoly := of_decide_eq_true hpaEq
        have haHolds :=
          Formula.holds_of_mem_conjunctList σ st.seq.pre hpre' aF haF
        rw [← hpaEq']
        apply atomLeZeroPolys_sound_entryC σ haHolds ?_ haix i pa hpaMem
        intro w hw
        exact st.wiresPos w (List.mem_append.mpr (Or.inl
          (Formula.freeWires_of_mem_conjunctList st.seq.pre aF haF w hw)))

  · unfold syzygyCheckW at hvalid
    split at hvalid
    · cases hvalid
    · next entries hentries =>
      split at hvalid
      · cases hvalid
      · next pentries hpents =>
        split at hvalid
        · cases hvalid
        · next pc hpc =>
          rw [Bool.and_eq_true] at hvalid
          obtain ⟨hall, hsum⟩ := hvalid
          have hsum' := of_decide_eq_true hsum
          obtain ⟨s, hs⟩ := st.conclShape
          obtain ⟨qc, hqc, -⟩ :=
            Term.evalQ_defined_of_bshape_fin σ st.conclusion s hs st.conclFin
          have hqcform := Term.evalQ_asCoordPolyIdxW σ hpc hqc
          subst hqcform
          refine ⟨_, ⟨[], [0], rfl⟩, hqc, rfl, ?_⟩
          rw [QTensor.rel2_scalars]
          show QArith.Poly.eval σ.coordValW pc ≤ 0
          rw [← hsum']
          apply farkas_fold_eval_nonpos_polys
          intro e he
          have h1 := List.all_eq_true.mp hall e he
          simp only [Bool.and_eq_true, Bool.or_eq_true] at h1
          obtain ⟨hle, hsrc⟩ := h1
          refine ⟨of_decide_eq_true hle, ?_⟩
          rcases hsrc with hcomp | hwire
          ·
            obtain ⟨c, hc, hpa⟩ := List.any_eq_true.mp hcomp
            obtain ⟨pa, hpaMem, hpaEq⟩ := List.any_eq_true.mp hpa
            have hpaEq' : pa = e.2 := of_decide_eq_true hpaEq
            have hcHolds : Formula.holds σ c.post :=
              hcomps c hc σ hadm
                (premiseContains_holds (st.preContains c hc) hpre')
            rw [← hpaEq']
            exact atomLeZeroPolysW_sound σ hcHolds pa hpaMem
          ·
            obtain ⟨aF, haF, h2⟩ := List.any_eq_true.mp hwire
            simp only [Bool.and_eq_true] at h2
            obtain ⟨-, hpa⟩ := h2
            obtain ⟨pa, hpaMem, hpaEq⟩ := List.any_eq_true.mp hpa
            have hpaEq' : pa = e.2 := of_decide_eq_true hpaEq
            have haHolds :=
              Formula.holds_of_mem_conjunctList σ st.seq.pre hpre' aF haF
            rw [← hpaEq']
            exact atomLeZeroPolysW_sound σ haHolds pa hpaMem

  · unfold syzygyCheckM at hvalid
    split at hvalid
    · cases hvalid
    · next entries hentries =>
      split at hvalid
      · cases hvalid
      · next pentries hpents =>
        split at hvalid
        · cases hvalid
        · next pc hpc =>
          rw [Bool.and_eq_true] at hvalid
          obtain ⟨hall, hsum⟩ := hvalid
          have hsum' := of_decide_eq_true hsum
          obtain ⟨s, hs⟩ := st.conclShape
          obtain ⟨qc, hqc, -⟩ :=
            Term.evalQ_defined_of_bshape_fin σ st.conclusion s hs st.conclFin
          refine ⟨qc, ⟨[], [0], rfl⟩, hqc, rfl, ?_⟩
          apply QTensor.rel2_const_right
          intro x hx
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
          have hposC : ∀ w ∈ st.conclusion.freeWires, ∃ τ,
              H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape :=
            fun w hw => st.wiresPos w (List.mem_append.mpr (Or.inr hw))
          have hcr := Term.evalQ_asCoordPolyMixed σ hpc hqc hposC i
          have hx' : qc.entries[i] = qc.brReadC i := by
            rw [QTensor.brReadC_in_range hi, List.getD_eq_getElem _ _ hi]
          show qc.entries[i] ≤ QTensor.scalar ⟨[], [0], rfl⟩
          rw [hx', hcr]
          show QArith.Poly.eval (σ.entryValM i) pc ≤ 0
          rw [← hsum']
          apply farkas_fold_eval_nonpos_polys
          intro e he
          have h1 := List.all_eq_true.mp hall e he
          simp only [Bool.and_eq_true, Bool.or_eq_true] at h1
          obtain ⟨hle, hsrc⟩ := h1
          refine ⟨of_decide_eq_true hle, ?_⟩
          rcases hsrc with hcomp | hwire
          ·
            obtain ⟨c, hc, hpa⟩ := List.any_eq_true.mp hcomp
            obtain ⟨pa, hpaMem, hpaEq⟩ := List.any_eq_true.mp hpa
            have hpaEq' : pa = e.2 := of_decide_eq_true hpaEq
            have hcHolds : Formula.holds σ c.post :=
              hcomps c hc σ hadm
                (premiseContains_holds (st.preContains c hc) hpre')
            rw [← hpaEq']
            exact atomLeZeroPolysM_sound_entryC σ hcHolds
              (st.compPostWiresPos c hc) i pa hpaMem
          ·
            obtain ⟨aF, haF, h2⟩ := List.any_eq_true.mp hwire
            simp only [Bool.and_eq_true] at h2
            obtain ⟨-, hpa⟩ := h2
            obtain ⟨pa, hpaMem, hpaEq⟩ := List.any_eq_true.mp hpa
            have hpaEq' : pa = e.2 := of_decide_eq_true hpaEq
            have haHolds :=
              Formula.holds_of_mem_conjunctList σ st.seq.pre hpre' aF haF
            rw [← hpaEq']
            apply atomLeZeroPolysM_sound_entryC σ haHolds ?_ i pa hpaMem
            intro w hw
            exact st.wiresPos w (List.mem_append.mpr (Or.inl
              (Formula.freeWires_of_mem_conjunctList st.seq.pre aF haF w hw)))

theorem sound_pConstExact {H : Hypernet} {seq : Sequent} {e₁ e₂ : Term}
    {b : BowTie}
    (hEval : (Formula.atom b e₁ e₂).evalClosed = some true)
    (hpost : seq.post = .atom b e₁ e₂) :
    seq.semanticallyValid H := by
  intro σ _ _
  rw [hpost]
  exact Formula.holds_of_evalClosed_true σ (.atom b e₁ e₂) hEval

theorem sound_pBound {H : Hypernet} {seq : Sequent} {components : List Sequent}
    {combination conclusion : Term}
    (hcomps : ∀ c ∈ components, c.semanticallyValid H)
    (hpreC : ∀ c ∈ components, premiseContains seq.pre c.pre)
    (hshape : ∃ s, conclusion.bshape H = some s)
    (hfin : conclusion.finWires H)
    (hwpos : ∀ w ∈ seq.pre.freeWires ++ conclusion.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
    (hcompPos : ∀ c ∈ components, ∀ w ∈ c.post.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
    (hvalid : syzygyCombinationValid combination components seq.pre conclusion)
    (hform : syzygyConclusionForm conclusion seq.post) :
    seq.semanticallyValid H :=
  sound_syzygy ⟨seq, components, combination, conclusion, hpreC, hshape, hfin,
    hwpos, hcompPos, hvalid, hform⟩ hcomps

private lemma eval_foldr_add_aux (v : Nat → ℚ) {α : Type}
    (g : α → QArith.Poly) (l : List α) (init : QArith.Poly) :
    QArith.Poly.eval v (l.foldr (fun j acc => QArith.Poly.add (g j) acc) init)
    = PsdCert.qlsum (l.map fun j => QArith.Poly.eval v (g j))
      + QArith.Poly.eval v init := by
  induction l with
  | nil => simp [PsdCert.qlsum]
  | cons a t ih => simp [PsdCert.qlsum, ih]; ring

private lemma eval_double_foldr (v : Nat → ℚ) {α β : Type}
    (g : α → β → QArith.Poly) (li : List α) (lj : List β) :
    QArith.Poly.eval v (li.foldr (fun i acc =>
        lj.foldr (fun j acc2 => QArith.Poly.add (g i j) acc2) acc) [])
    = PsdCert.qlsum (li.map fun i =>
        PsdCert.qlsum (lj.map fun j => QArith.Poly.eval v (g i j))) := by
  induction li with
  | nil => simp [PsdCert.qlsum]
  | cons i t ih =>
    rw [List.foldr_cons, eval_foldr_add_aux v (g i) lj, ih]
    rfl

private lemma eval_negQuadFormPoly (v : Nat → ℚ) (a : Nat)
    (M : Fin a → Fin a → ℚ) (ps : List QArith.Poly) :
    QArith.Poly.eval v (PsdCert.negQuadFormPoly a M ps)
    = -(PsdCert.finQSum a fun i => PsdCert.finQSum a fun j =>
        M i j * QArith.Poly.eval v (ps.getD i.val [])
              * QArith.Poly.eval v (ps.getD j.val [])) := by
  rw [PsdCert.negQuadFormPoly, Poly.eval_neg, eval_double_foldr]
  congr 1
  show PsdCert.qlsum _ = PsdCert.qlsum _
  congr 1
  refine List.map_congr_left fun i _ => ?_
  show PsdCert.qlsum _ = PsdCert.qlsum _
  congr 1
  refine List.map_congr_left fun j _ => ?_
  rw [Poly.eval_scale, Poly.eval_mul]
  ring

theorem sound_psdCertOf {H : Hypernet} {seq : Sequent} {a : Nat}
    {M : Fin a → Fin a → ℚ} {ts : List Term} {conclusion : Term}
    (hpsd : ∀ x : Fin a → ℚ, 0 ≤ PsdCert.finQSum a fun i =>
      PsdCert.finQSum a fun j => M i j * x i * x j)
    (hconcl : PsdCert.conclCheck a M ts conclusion = true)
    (hshape : ∃ s, conclusion.bshape H = some s)
    (hfin : conclusion.finWires H)
    (hwpos : ∀ w ∈ conclusion.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
    (hform : syzygyConclusionForm conclusion seq.post) :
    seq.semanticallyValid H := by
  intro σ hadm hpre
  refine holds_of_syzygyConclusionForm ?_ hform
  rw [PsdCert.conclCheck, Bool.or_eq_true] at hconcl
  rcases hconcl with hc | hc

  · rw [PsdCert.conclCheckCore, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true] at hc
    obtain ⟨⟨⟨_hlen, hcix⟩, _htsix⟩, hpoly⟩ := hc
    have hpoly' := of_decide_eq_true hpoly
    obtain ⟨s, hs⟩ := hshape
    have hcw := wire_discipline_of_bshape_fin σ hs hfin hcix
    obtain ⟨qc, hqc⟩ : ∃ qc, Term.evalQ σ conclusion = some qc := by
      by_cases hsnil : s = []
      · subst hsnil
        have hsing : ∀ w ∈ conclusion.freeWires, ∃ qw,
            σ.wireQ w = some qw ∧ SingletonShape qw.shape := by
          intro w hw
          obtain ⟨qw, hqw, hqs⟩ := hcw w hw
          exact ⟨qw, hqw, by
            rcases hqs with h1 | h1
            · exact Or.inl h1
            · exact Or.inl h1⟩
        obtain ⟨qc, hqc, _, _⟩ :=
          Term.evalQ_total_singleton σ conclusion hsing hcix
        exact ⟨qc, hqc⟩
      · obtain ⟨qc, hqc, _, _, _⟩ :=
          Term.evalQ_brRead σ s conclusion hcw hcix
        exact ⟨qc, hqc⟩
    refine ⟨qc, ⟨[], [0], rfl⟩, hqc, rfl, ?_⟩
    apply QTensor.rel2_const_right
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
    have hposC : ∀ w ∈ conclusion.freeWires, ∀ qw,
        σ.wireQ w = some qw → 0 < Shape.totalSize qw.shape :=
      fun w hw qw hqw => wireQ_pos_of_type_pos σ hqw (hwpos w hw)
    have hcr := Term.evalQ_brReadC σ hqc hposC hcix i
    have hx' : qc.entries[i] = qc.brReadC i := by
      rw [QTensor.brReadC_in_range hi, List.getD_eq_getElem _ _ hi]
    show qc.entries[i] ≤ QTensor.scalar ⟨[], [0], rfl⟩
    rw [hx', hcr]
    show QArith.Poly.eval (σ.entryValC i) conclusion.toPoly ≤ 0
    rw [hpoly', eval_negQuadFormPoly]
    exact neg_nonpos.mpr (hpsd fun i' =>
      QArith.Poly.eval (σ.entryValC i) ((ts.map Term.toPoly).getD i'.val []))

  · rw [PsdCert.conclCheckW, Bool.and_eq_true] at hc
    obtain ⟨_hlen, hc⟩ := hc
    cases hpc : conclusion.asCoordPolyIdxW? with
    | none => simp [hpc] at hc
    | some pc =>
      cases hpts : ts.mapM Term.asCoordPolyIdxW? with
      | none => simp [hpc, hpts] at hc
      | some pts =>
        simp only [hpc, hpts] at hc
        have hpc' := of_decide_eq_true hc
        obtain ⟨s, hs⟩ := hshape
        obtain ⟨qc, hqc, -⟩ :=
          Term.evalQ_defined_of_bshape_fin σ conclusion s hs hfin
        have hqcform := Term.evalQ_asCoordPolyIdxW σ hpc hqc
        subst hqcform
        refine ⟨_, ⟨[], [0], rfl⟩, hqc, rfl, ?_⟩
        rw [QTensor.rel2_scalars]
        show QArith.Poly.eval σ.coordValW pc ≤ 0
        rw [hpc', eval_negQuadFormPoly]
        exact neg_nonpos.mpr (hpsd fun i' =>
          QArith.Poly.eval σ.coordValW (pts.getD i'.val []))

theorem sound_psdCertT {H : Hypernet} {seq : Sequent} {a : Nat}
    {A Z : Fin a → Fin a → ℚ} {ts : List Term} {conclusion : Term}
    (hwit : PsdCert.checkT a A Z = true)
    (hconcl : PsdCert.conclCheck a A ts conclusion = true)
    (hshape : ∃ s, conclusion.bshape H = some s)
    (hfin : conclusion.finWires H)
    (hwpos : ∀ w ∈ conclusion.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
    (hform : syzygyConclusionForm conclusion seq.post) :
    seq.semanticallyValid H :=
  sound_psdCertOf (fun x => PsdCert.checkT_quadForm_nonneg hwit x)
    hconcl hshape hfin hwpos hform

theorem sound_psdCertDD {H : Hypernet} {seq : Sequent} {a : Nat}
    {A Z : Fin a → Fin a → ℚ} {ts : List Term} {conclusion : Term}
    (hwit : PsdCert.checkDD a A Z = true)
    (hconcl : PsdCert.conclCheck a A ts conclusion = true)
    (hshape : ∃ s, conclusion.bshape H = some s)
    (hfin : conclusion.finWires H)
    (hwpos : ∀ w ∈ conclusion.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
    (hform : syzygyConclusionForm conclusion seq.post) :
    seq.semanticallyValid H :=
  sound_psdCertOf (fun x => PsdCert.checkDD_quadForm_nonneg hwit x)
    hconcl hshape hfin hwpos hform

theorem sound_psdCertK {H : Hypernet} {seq : Sequent} {m k : Nat}
    {A : Fin (m + k) → Fin (m + k) → ℚ} {N : Fin m → Fin k → ℚ}
    {B : Fin m → Fin m → ℚ} {innerT : Bool} {Z : Fin m → Fin m → ℚ}
    {ts : List Term} {conclusion : Term}
    (hwit : PsdCert.checkK m k A N B innerT Z = true)
    (hconcl : PsdCert.conclCheck (m + k) A ts conclusion = true)
    (hshape : ∃ s, conclusion.bshape H = some s)
    (hfin : conclusion.finWires H)
    (hwpos : ∀ w ∈ conclusion.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
    (hform : syzygyConclusionForm conclusion seq.post) :
    seq.semanticallyValid H :=
  sound_psdCertOf (fun x => PsdCert.checkK_quadForm_nonneg hwit x)
    hconcl hshape hfin hwpos hform

theorem ExtensionSet.interval1D?_spec {S : ExtensionSet} {lo hi : ℚ}
    (h : S.interval1D? = some (lo, hi)) :
    S.simplex.complex.ambDim = 1 ∧
    isExtensionSetEmpty S ∧
    lo < hi ∧
    ∃ (a b : Fin S.simplex.complex.nVertices) (V₀ V₁ : ℚ),
      (List.finRange S.simplex.complex.nVertices).filter
        (fun v => S.simplex.contains v) = [a, b] ∧
      (∀ j, S.simplex.complex.coord a j = V₀) ∧
      (∀ j, S.simplex.complex.coord b j = V₁) ∧
      V₀ ≠ V₁ ∧
      ((V₀ < V₁ ∧ lo = V₀ ∧ hi = V₁) ∨ (V₁ < V₀ ∧ lo = V₁ ∧ hi = V₀)) := by
  unfold ExtensionSet.interval1D? at h
  split at h
  · next hd1 =>
    split at h
    · next hempty =>
      split at h
      · next a b hfil =>
        simp only [] at h
        have hAllJ : ∀ (v : Fin S.simplex.complex.nVertices) (j j' :
            Fin S.simplex.complex.ambDim),
            S.simplex.complex.coord v j = S.simplex.complex.coord v j' := by
          intro v j j'
          have hj : j = j' := by
            apply Fin.ext
            have := j.isLt
            have := j'.isLt
            omega
          rw [hj]
        split at h
        · next hlt =>
          injection h with h
          rw [Prod.mk.injEq] at h
          obtain ⟨hlo, hhi⟩ := h
          refine ⟨hd1, (ExtensionSet.isEmptyB_iff S).mp hempty,
            by rw [← hlo, ← hhi]; exact hlt,
            a, b, _, _, hfil,
            fun j => hAllJ a j ⟨0, by omega⟩,
            fun j => hAllJ b j ⟨0, by omega⟩,
            ne_of_lt hlt, Or.inl ⟨hlt, hlo.symm, hhi.symm⟩⟩
        · split at h
          · next hlt =>
            injection h with h
            rw [Prod.mk.injEq] at h
            obtain ⟨hlo, hhi⟩ := h
            refine ⟨hd1, (ExtensionSet.isEmptyB_iff S).mp hempty,
              by rw [← hlo, ← hhi]; exact hlt,
              a, b, _, _, hfil,
              fun j => hAllJ a j ⟨0, by omega⟩,
              fun j => hAllJ b j ⟨0, by omega⟩,
              (ne_of_lt hlt).symm, Or.inr ⟨hlt, hlo.symm, hhi.symm⟩⟩
          · cases h
      · cases h
    · cases h
  · cases h

theorem interval1D_elim {S : ExtensionSet} {lo hi : ℚ}
    (hint : S.interval1D? = some (lo, hi))
    {x : Fin S.simplex.complex.ambDim → ℚ}
    (hmask : MaskRegion S.simplex.complex S.simplex.contains S.contains x)
    (j0 : Fin S.simplex.complex.ambDim) :
    lo ≤ x j0 ∧ x j0 ≤ hi ∧ lo < hi := by
  obtain ⟨-, hempty, hlohi, a, b, V₀, V₁, hfil, hVa, hVb, hVne, hor⟩ :=
    ExtensionSet.interval1D?_spec hint
  obtain ⟨-, hs2, -, hs4⟩ :=
    maskRegion_pair_elim hfil hVa hVb hVne j0 hmask
  have h2 := hs2 (hempty a)
  have h4 := hs4 (hempty b)
  rcases hor with ⟨hlt, hlo, hhi⟩ | ⟨hlt, hlo, hhi⟩
  · have hnum2 : 0 ≤ V₁ - x j0 := by
      rcases div_nonneg_iff.mp h2 with ⟨hn, -⟩ | ⟨-, hd⟩
      · exact hn
      · linarith
    have hnum4 : 0 ≤ x j0 - V₀ := by
      rcases div_nonneg_iff.mp h4 with ⟨hn, -⟩ | ⟨-, hd⟩
      · exact hn
      · linarith
    subst hlo; subst hhi
    exact ⟨by linarith, by linarith, hlohi⟩
  · have hnum2 : V₁ - x j0 ≤ 0 := by
      rcases div_nonneg_iff.mp h2 with ⟨-, hd⟩ | ⟨hn, -⟩
      · linarith
      · exact hn
    have hnum4 : x j0 - V₀ ≤ 0 := by
      rcases div_nonneg_iff.mp h4 with ⟨-, hd⟩ | ⟨hn, -⟩
      · linarith
      · exact hn
    subst hlo; subst hhi
    exact ⟨by linarith, by linarith, hlohi⟩

theorem interval1D_intro {S : ExtensionSet} {lo hi : ℚ}
    (hint : S.interval1D? = some (lo, hi))
    {x : Fin S.simplex.complex.ambDim → ℚ}
    (j0 : Fin S.simplex.complex.ambDim)
    (hxlo : lo ≤ x j0) (hxhi : x j0 ≤ hi) :
    MaskRegion S.simplex.complex S.simplex.contains S.contains x := by
  obtain ⟨hd1, hempty, -, a, b, V₀, V₁, hfil, hVa, hVb, hVne, hor⟩ :=
    ExtensionSet.interval1D?_spec hint
  refine maskRegion_pair_intro hfil hVa hVb hVne hd1 j0 ?_ ?_ ?_ ?_
  · intro hea; rw [hempty a] at hea; cases hea
  · intro _
    rcases hor with ⟨hlt, hlo, hhi⟩ | ⟨hlt, hlo, hhi⟩
    · subst hlo; subst hhi
      exact div_nonneg_iff.mpr (Or.inl ⟨by linarith, by linarith⟩)
    · subst hlo; subst hhi
      exact div_nonneg_iff.mpr (Or.inr ⟨by linarith, by linarith⟩)
  · intro heb; rw [hempty b] at heb; cases heb
  · intro _
    rcases hor with ⟨hlt, hlo, hhi⟩ | ⟨hlt, hlo, hhi⟩
    · subst hlo; subst hhi
      exact div_nonneg_iff.mpr (Or.inl ⟨by linarith, by linarith⟩)
    · subst hlo; subst hhi
      exact div_nonneg_iff.mpr (Or.inr ⟨by linarith, by linarith⟩)

def ChainInv (ivs : List (ℚ × ℚ)) (lo r : ℚ) : Prop :=
  lo ≤ r ∧
  (r ≤ lo ∨ ∀ x : ℚ, lo ≤ x → x ≤ r → ∃ iv ∈ ivs, iv.1 ≤ x ∧ x ≤ iv.2)

theorem chainInv_extendPass (ivs : List (ℚ × ℚ)) (lo : ℚ) :
    ∀ (sub : List (ℚ × ℚ)), (∀ iv ∈ sub, iv ∈ ivs) →
    ∀ (r : ℚ), ChainInv ivs lo r →
    ChainInv ivs lo (coverExtendPass sub r) := by
  intro sub
  induction sub with
  | nil => intro _ r h; exact h
  | cons iv rest ih =>
    intro hsub r h
    have hiv : iv ∈ ivs := hsub iv List.mem_cons_self
    have hrest : ∀ e ∈ rest, e ∈ ivs :=
      fun e he => hsub e (List.mem_cons_of_mem _ he)
    have hunfold : coverExtendPass (iv :: rest) r
        = coverExtendPass rest (if iv.1 ≤ r ∧ r < iv.2 then iv.2 else r) :=
      rfl
    rw [hunfold]
    refine ih hrest _ ?_
    by_cases hc : iv.1 ≤ r ∧ r < iv.2
    · rw [if_pos hc]
      obtain ⟨hlor, hcov⟩ := h
      refine ⟨le_of_lt (lt_of_le_of_lt hlor hc.2), Or.inr ?_⟩
      intro x hlx hxh
      by_cases hxr : x ≤ r
      · rcases hcov with hrlo | hall
        · exact ⟨iv, hiv, le_trans hc.1 (le_trans hrlo hlx), hxh⟩
        · exact hall x hlx hxr
      · rw [not_le] at hxr
        exact ⟨iv, hiv, le_trans hc.1 (le_of_lt hxr), hxh⟩
    · rw [if_neg hc]
      exact h

theorem chainInv_reach (ivs : List (ℚ × ℚ)) (lo : ℚ) :
    ∀ (n : Nat) (r : ℚ), ChainInv ivs lo r →
    ChainInv ivs lo (coverReach n ivs r) := by
  intro n
  induction n with
  | zero => intro r h; exact h
  | succ n ih =>
    intro r h
    exact ih _ (chainInv_extendPass ivs lo ivs (fun _ hm => hm) r h)

theorem coverChain_covers {ivs : List (ℚ × ℚ)} {lo hi : ℚ} (hlt : lo < hi)
    (hcheck : coverChainCheck ivs lo hi = true) :
    ∀ x : ℚ, lo ≤ x → x ≤ hi → ∃ iv ∈ ivs, iv.1 ≤ x ∧ x ≤ iv.2 := by
  have hreach : hi ≤ coverReach ivs.length ivs lo := by
    unfold coverChainCheck at hcheck
    exact of_decide_eq_true hcheck
  obtain ⟨hlor, hcov⟩ :=
    chainInv_reach ivs lo ivs.length lo ⟨le_refl _, Or.inl (le_refl _)⟩
  rcases hcov with hrlo | hall
  · exact absurd (le_trans hreach hrlo) (not_le.mpr hlt)
  · intro x hlx hxh
    exact hall x hlx (le_trans hxh hreach)

theorem sound_subdivide {H : Hypernet} {seq regionPremise : Sequent}
    {nBranches : Nat} {branchPremise : Fin nBranches → Sequent}
    {termX : Term} {simplex : Simplex} {S : ExtensionSet}
    {branchSimplex : Fin nBranches → Simplex}
    {branchS : Fin nBranches → ExtensionSet}
    {coverCertificate : Term}
    (ihRegion : regionPremise.semanticallyValid H)
    (ihBranch : ∀ k, (branchPremise k).semanticallyValid H)
    (hpre : seq.pre = regionPremise.pre)
    (hregionPost : regionPremise.post = .inRegion termX simplex S)
    (hbranchPre : ∀ k, (branchPremise k).pre
                   = .and regionPremise.pre
                          (.inRegion termX (branchSimplex k) (branchS k)))
    (hbranchPost : ∀ k, (branchPremise k).post = seq.post)
    (hcover : coverInfeasibilityValid termX simplex S nBranches
                branchSimplex branchS coverCertificate) :
    seq.semanticallyValid H := by
  intro σ hadm hpre'
  rw [hpre] at hpre'

  have hreg := ihRegion σ hadm hpre'
  rw [hregionPost] at hreg
  obtain ⟨-, q, hq, hqshape, hmask⟩ := hreg

  unfold coverInfeasibilityValid coverCheck at hcover
  cases hint : S.interval1D? with
  | none => rw [hint] at hcover; cases hcover
  | some lohi =>
    obtain ⟨lo, hi⟩ := lohi
    rw [hint] at hcover
    simp only [Bool.and_eq_true] at hcover
    obtain ⟨⟨-, hall⟩, hchain⟩ := hcover

    obtain ⟨hd1, -⟩ := ExtensionSet.interval1D?_spec hint
    have hd1' : 0 < S.simplex.complex.ambDim := by omega
    obtain ⟨hxlo, hxhi, hlohi⟩ := interval1D_elim hint hmask ⟨0, hd1'⟩

    obtain ⟨iv, hivmem, hivlo, hivhi⟩ :=
      coverChain_covers hlohi hchain _ hxlo hxhi
    obtain ⟨k, -, hkint⟩ := List.mem_filterMap.mp hivmem

    rw [List.all_eq_true] at hall
    have hk' := hall k (List.mem_finRange k)
    rw [Bool.and_eq_true] at hk'
    have htie : (branchS k).simplex = branchSimplex k :=
      of_decide_eq_true hk'.1
    obtain ⟨hbd1, -⟩ := ExtensionSet.interval1D?_spec hkint
    have hbd1' : 0 < (branchS k).simplex.complex.ambDim := by omega

    have hbranchHolds : Formula.holds σ (branchPremise k).pre := by
      rw [hbranchPre k]
      refine ⟨hpre', htie.symm, q, hq, ?_, ?_⟩
      · rw [hqshape, hd1, hbd1]
      · exact interval1D_intro hkint ⟨0, hbd1'⟩ hivlo hivhi
    have hpost := ihBranch k σ hadm hbranchHolds
    rw [hbranchPost k] at hpost
    exact hpost

theorem ERat.allFinQ_getElem? : ∀ {l : List ERat} {l' : List ℚ},
    ERat.allFinQ l = some l' → ∀ {i : ℕ}, i < l'.length →
    l[i]? = some (.fin (l'.getD i 0)) := by
  intro l
  induction l with
  | nil =>
    intro l' h i hi
    simp only [ERat.allFinQ, Option.some.injEq] at h
    subst h
    simp at hi
  | cons hd tl ih =>
    intro l' h i hi
    cases hd with
    | fin a =>
      simp only [ERat.allFinQ] at h
      cases htl : ERat.allFinQ tl with
      | none => rw [htl] at h; cases h
      | some tl' =>
        rw [htl, Option.map_some] at h
        injection h with h
        subst h
        cases i with
        | zero => rfl
        | succ n =>
          simp only [List.getElem?_cons_succ, List.getD_cons_succ]
          exact ih htl (by simpa using hi)
    | negInf => simp [ERat.allFinQ] at h
    | posInf => simp [ERat.allFinQ] at h

theorem Hypernet.Valuation.entryFlat_eq_entryE {H : Hypernet}
    (σ : H.Valuation) {w : Wire} {τ : TensorType}
    (hτ : H.wireType w = some τ) (i : ℕ) :
    σ.entryFlat w i = (σ w τ hτ).entryE i := by
  unfold Hypernet.Valuation.entryFlat
  split
  · next h => rw [hτ] at h; cases h
  · next τ' hτ' =>
    have hττ : τ = τ' := by rw [hτ] at hτ'; injection hτ'
    subst hττ
    rfl

theorem TensorValue.entryE_eq_map_getElem? {τ : TensorType}
    (v : TensorValue τ) (i : ℕ) :
    v.entryE i = (v.val.map Subtype.val)[i]? :=
  (List.getElem?_map ..).symm

theorem Hypernet.Valuation.wireQ_isSome_of_entryFin {H : Hypernet}
    (σ : H.Valuation) {w : Wire} {τ : TensorType}
    (hτ : H.wireType w = some τ)
    (hfin : ∀ i, i < Shape.totalSize τ.shape →
      ∃ q : ℚ, σ.entryFlat w i = some (.fin q)) :
    ∃ qw, σ.wireQ w = some qw := by
  unfold Hypernet.Valuation.wireQ
  split
  · next h => rw [hτ] at h; cases h
  · next τ' hτ' =>
    have hττ : τ = τ' := by rw [hτ] at hτ'; injection hτ'
    subst hττ
    split
    · next hf =>
      exfalso
      have hall : ∀ e ∈ (σ w τ hτ').val.map Subtype.val,
          ∃ q, e = ERat.fin q := by
        intro e he
        obtain ⟨j, hjL, hje⟩ := List.mem_iff_getElem.mp he
        have hLlen : ((σ w τ hτ').val.map Subtype.val).length
            = Shape.totalSize τ.shape := by
          rw [List.length_map]
          exact (σ w τ hτ').property
        have hjts : j < Shape.totalSize τ.shape := hLlen ▸ hjL
        obtain ⟨q, hq⟩ := hfin j hjts
        rw [Hypernet.Valuation.entryFlat_eq_entryE σ hτ' j,
          TensorValue.entryE_eq_map_getElem?,
          List.getElem?_eq_getElem hjL] at hq
        injection hq with hq
        exact ⟨q, by rw [← hje]; exact hq⟩
      obtain ⟨l', hl'⟩ := ERat.allFinQ_of_all_fin _ hall
      rw [hf] at hl'
      cases hl'
    · exact ⟨_, rfl⟩

theorem Hypernet.Valuation.entryFlat_of_wireQ {H : Hypernet}
    (σ : H.Valuation) {w : Wire} {qw : QTensor}
    (hq : σ.wireQ w = some qw) {i : ℕ} (hi : i < qw.entries.length) :
    σ.entryFlat w i = some (.fin (qw.entries.getD i 0)) := by
  unfold Hypernet.Valuation.wireQ at hq
  split at hq
  · cases hq
  · next τ hτ =>
    split at hq
    · cases hq
    · next l hl =>
      injection hq with hq
      subst hq
      rw [Hypernet.Valuation.entryFlat_eq_entryE σ hτ i,
        TensorValue.entryE_eq_map_getElem?]
      exact ERat.allFinQ_getElem? hl hi

theorem QTensor.rel2_const_right_elim {r : ℚ → ℚ → Prop} {q : QTensor}
    {c : ℚ} (h : QTensor.rel2 r q ⟨[], [c], rfl⟩) :
    ∀ x ∈ q.entries, r x c := by
  unfold QTensor.rel2 at h
  by_cases hs : q.shape = []
  · rw [if_pos hs] at h
    have he := QTensor.entries_singleton (q := q) (Or.inl hs)
    intro x hx
    rw [he] at hx h
    rcases List.mem_singleton.mp hx with rfl
    exact h (q.scalar, c) (by simp)
  · rw [if_neg hs, if_neg hs, if_pos rfl] at h
    exact h

theorem QTensor.rel2_const_left_elim {r : ℚ → ℚ → Prop} {q : QTensor}
    {c : ℚ} (h : QTensor.rel2 r ⟨[], [c], rfl⟩ q) :
    ∀ x ∈ q.entries, r c x := by
  unfold QTensor.rel2 at h
  by_cases hs : q.shape = []
  · rw [if_pos hs.symm] at h
    have he := QTensor.entries_singleton (q := q) (Or.inl hs)
    intro x hx
    rw [he] at hx h
    rcases List.mem_singleton.mp hx with rfl
    exact h (c, q.scalar) (by simp)
  · rw [if_neg (fun hh : ([] : Shape) = q.shape => hs hh.symm),
      if_pos rfl] at h
    exact h

theorem QTensor.rel2_of_getD {r : ℚ → ℚ → Prop} {a b : QTensor}
    (hs : a.shape = b.shape)
    (h : ∀ i, i < a.entries.length →
      r (a.entries.getD i 0) (b.entries.getD i 0)) :
    QTensor.rel2 r a b := by
  unfold QTensor.rel2
  rw [if_pos hs]
  intro p hp
  obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hp
  rw [List.length_zip] at hj
  have hlen : a.entries.length = b.entries.length := by
    rw [a.len_eq, b.len_eq, hs]
  have hja : j < a.entries.length := by omega
  have hjb : j < b.entries.length := by omega
  have hval := h j hja
  rw [List.getD_eq_getElem _ _ hja, List.getD_eq_getElem _ _ hjb] at hval
  rw [← hje, List.getElem_zip]
  exact hval

theorem QTensor.map2_constL (f : ℚ → ℚ → ℚ) (c : ℚ) (q : QTensor) :
    ∃ out, QTensor.map2 f ⟨[], [c], rfl⟩ q = some out ∧
      out.shape = q.shape ∧
      out.entries.length = q.entries.length ∧
      ∀ i, i < q.entries.length →
        out.entries.getD i 0 = f c (q.entries.getD i 0) := by
  unfold QTensor.map2
  by_cases hs : q.shape = []
  · rw [dif_pos hs.symm]
    have he := QTensor.entries_singleton (q := q) (Or.inl hs)
    refine ⟨_, rfl, hs.symm, ?_, ?_⟩
    · show (List.zipWith f [c] q.entries).length = q.entries.length
      rw [he]
      rfl
    · intro i hi
      have hlen : q.entries.length = 1 := by rw [he]; rfl
      have hi0 : i = 0 := by omega
      subst hi0
      show (List.zipWith f [c] q.entries).getD 0 0
        = f c (q.entries.getD 0 0)
      rw [he]
      rfl
  · rw [dif_neg (fun hh : ([] : Shape) = q.shape => hs hh.symm),
      if_pos rfl]
    refine ⟨_, rfl, rfl, by simp, ?_⟩
    intro i hi
    show (q.entries.map (f (⟨[], [c], rfl⟩ : QTensor).scalar)).getD i 0
      = f c (q.entries.getD i 0)
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getD_eq_getElem _ _ hi]
    rfl

theorem affineWireTerm_evalQ {H : Hypernet} (σ : H.Valuation) {w : Wire}
    {qw : QTensor} (h : σ.wireQ w = some qw) (off slope : ℚ) :
    ∃ qa, Term.evalQ σ (affineWireTerm off slope w) = some qa ∧
      qa.shape = qw.shape ∧
      qa.entries.length = qw.entries.length ∧
      ∀ i, i < qw.entries.length →
        qa.entries.getD i 0 = off + slope * qw.entries.getD i 0 := by
  obtain ⟨m, hm, hms, hml, hmE⟩ := QTensor.map2_constL (· * ·) slope qw
  obtain ⟨out, ho, hos, hol, hoE⟩ := QTensor.map2_constL (· + ·) off m
  refine ⟨out, ?_, by rw [hos, hms], by rw [hol, hml], ?_⟩
  · show Term.evalQ σ (.add (.const off) (.mul (.const slope) (.var w)))
      = some out
    simp only [Term.evalQ, Option.bind_eq_bind, h, Option.bind_some]
    rw [hm]
    simp only [Option.bind_some]
    exact ho
  · intro i hi
    have him : i < m.entries.length := by rw [hml]; exact hi
    rw [hoE i him, hmE i hi]

theorem lirpa_lower_neg {a α β p : ℚ} (ha : a < 0)
    (h1 : α * a + β ≤ 0) (h2 : β ≤ 0) (hap : a ≤ p) (hp0 : p ≤ 0) :
    α * p + β ≤ 0 := by
  by_contra hc
  rw [not_le] at hc
  have t1 : 0 ≤ (-p) * (-(α * a + β)) :=
    mul_nonneg (by linarith) (by linarith)
  have t2 : 0 ≤ (p - a) * (-β) := mul_nonneg (by linarith) (by linarith)
  have t3 : 0 < (-a) * (α * p + β) := mul_pos (by linarith) hc
  nlinarith [t1, t2, t3]

theorem lirpa_lower_pos {b α β p : ℚ} (hb : 0 < b)
    (h2 : β ≤ 0) (h3 : α * b + β ≤ b) (hp0 : 0 ≤ p) (hpb : p ≤ b) :
    α * p + β ≤ p := by
  by_contra hc
  rw [not_le] at hc
  have t1 : 0 ≤ (b - p) * (-β) := mul_nonneg (by linarith) (by linarith)
  have t2 : 0 ≤ p * (-(α * b + β - b)) :=
    mul_nonneg hp0 (by linarith)
  have t3 : 0 < b * (α * p + β - p) := mul_pos hb (by linarith)
  nlinarith [t1, t2, t3]

theorem lirpa_upper_neg {a γ δ p : ℚ} (ha : a < 0)
    (h1 : 0 ≤ γ * a + δ) (h2 : 0 ≤ δ) (hap : a ≤ p) (hp0 : p ≤ 0) :
    0 ≤ γ * p + δ := by
  by_contra hc
  rw [not_le] at hc
  have t1 : 0 ≤ (-p) * (γ * a + δ) := mul_nonneg (by linarith) h1
  have t2 : 0 ≤ (p - a) * δ := mul_nonneg (by linarith) h2
  have t3 : 0 < (-a) * (-(γ * p + δ)) :=
    mul_pos (by linarith) (by linarith)
  nlinarith [t1, t2, t3]

theorem lirpa_upper_pos {b γ δ p : ℚ} (hb : 0 < b)
    (h2 : 0 ≤ δ) (h3 : b ≤ γ * b + δ) (hp0 : 0 ≤ p) (hpb : p ≤ b) :
    p ≤ γ * p + δ := by
  by_contra hc
  rw [not_le] at hc
  have t1 : 0 ≤ (b - p) * δ := mul_nonneg (by linarith) h2
  have t2 : 0 ≤ p * (γ * b + δ - b) := mul_nonneg hp0 (by linarith)
  have t3 : 0 < b * (p - (γ * p + δ)) := mul_pos hb (by linarith)
  nlinarith [t1, t2, t3]

theorem reluLinked_facts {H : Hypernet} {preact post : Wire}
    (hlink : reluLinked H preact post) (σ : H.Valuation)
    (hadm : σ.Admissible) :
    ∃ qp qy : QTensor,
      σ.wireQ preact = some qp ∧ σ.wireQ post = some qy ∧
      qp.shape = qy.shape ∧ 0 < qp.entries.length ∧
      qp.entries.length = qy.entries.length ∧
      ∀ i, i < qp.entries.length →
        (qp.entries.getD i 0 ≤ 0 ∧ qy.entries.getD i 0 = 0) ∨
        (0 ≤ qp.entries.getD i 0 ∧
          qy.entries.getD i 0 = qp.entries.getD i 0) := by
  obtain ⟨s, hmem, hs⟩ := reluLinked_iff.mp hlink
  have hsem : ∀ i : Fin (Shape.totalSize s), ∃ p y : ℚ,
      σ.entryFlat preact i.val = some (.fin p) ∧
      σ.entryFlat post i.val = some (.fin y) ∧
      ((p ≤ 0 ∧ y = 0) ∨ (0 ≤ p ∧ y = p)) := hadm _ hmem
  obtain ⟨τ, hτp, hτy, hτs⟩ :
      ∃ τ, H.wireType preact = some τ ∧ H.wireType post = some τ ∧
        τ.shape = s := H.typeConsistent _ hmem
  have hts : Shape.totalSize τ.shape = Shape.totalSize s := by rw [hτs]
  obtain ⟨qp, hqp⟩ := σ.wireQ_isSome_of_entryFin hτp (fun i hi => by
    obtain ⟨p, y, hp, -, -⟩ := hsem ⟨i, by omega⟩
    exact ⟨p, hp⟩)
  obtain ⟨qy, hqy⟩ := σ.wireQ_isSome_of_entryFin hτy (fun i hi => by
    obtain ⟨p, y, -, hy, -⟩ := hsem ⟨i, by omega⟩
    exact ⟨y, hy⟩)
  have hqps : qp.shape = τ.shape := by
    obtain ⟨τ', hτ', hsh⟩ := σ.wireQ_shape hqp
    rw [hτp] at hτ'
    injection hτ' with hτ'
    rw [hsh, ← hτ']
  have hqys : qy.shape = τ.shape := by
    obtain ⟨τ', hτ', hsh⟩ := σ.wireQ_shape hqy
    rw [hτy] at hτ'
    injection hτ' with hτ'
    rw [hsh, ← hτ']
  have hplen : qp.entries.length = Shape.totalSize s := by
    rw [qp.len_eq, hqps, hτs]
  have hylen : qy.entries.length = Shape.totalSize s := by
    rw [qy.len_eq, hqys, hτs]
  refine ⟨qp, qy, hqp, hqy, by rw [hqps, hqys], by omega, by omega, ?_⟩
  intro i hi
  obtain ⟨p, y, hp, hy, hcases⟩ := hsem ⟨i, by omega⟩
  have hgp : qp.entries.getD i 0 = p := by
    have h1 := σ.entryFlat_of_wireQ hqp hi
    have h2 := hp.symm.trans h1
    injection h2 with h2
    injection h2 with h2
    exact h2.symm
  have hgy : qy.entries.getD i 0 = y := by
    have h1 := σ.entryFlat_of_wireQ hqy (show i < qy.entries.length by omega)
    have h2 := hy.symm.trans h1
    injection h2 with h2
    injection h2 with h2
    exact h2.symm
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [hgp]; exact h1, by rw [hgy]; exact h2⟩
  · exact Or.inr ⟨by rw [hgp]; exact h1, by rw [hgy, hgp, h2]⟩

theorem sound_reluNN {H : Hypernet} {seq : Sequent} {preact post : Wire}
    (hlink : reluLinked H preact post)
    (hpost : seq.post = .atom .ge (.var post) (.const 0)) :
    seq.semanticallyValid H := by
  intro σ hadm _
  obtain ⟨qp, qy, hqp, hqy, hshape, hpos, hlen, hcase⟩ :=
    reluLinked_facts hlink σ hadm
  rw [hpost]
  refine ⟨qy, ⟨[], [0], rfl⟩, hqy, rfl, ?_⟩
  apply QTensor.rel2_const_right
  intro x hx
  obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hx
  have hjp : j < qp.entries.length := by omega
  have hgd : qy.entries.getD j 0 = x := by
    rw [List.getD_eq_getElem _ _ hj]
    exact hje
  show (0 : ℚ) ≤ x
  rcases hcase j hjp with ⟨-, h2⟩ | ⟨h1, h2⟩
  · rw [← hgd, h2]
  · rw [← hgd, h2]
    exact h1

theorem sound_reluAbove {H : Hypernet} {seq : Sequent} {preact post : Wire}
    (hlink : reluLinked H preact post)
    (hpost : seq.post = .atom .ge (.var post) (.var preact)) :
    seq.semanticallyValid H := by
  intro σ hadm _
  obtain ⟨qp, qy, hqp, hqy, hshape, hpos, hlen, hcase⟩ :=
    reluLinked_facts hlink σ hadm
  rw [hpost]
  refine ⟨qy, qp, hqy, hqp, ?_⟩
  apply QTensor.rel2_of_getD hshape.symm
  intro i hi
  have hip : i < qp.entries.length := by omega
  show qp.entries.getD i 0 ≤ qy.entries.getD i 0
  rcases hcase i hip with ⟨h1, h2⟩ | ⟨-, h2⟩
  · rw [h2]
    exact h1
  · rw [h2]

theorem sound_reluPos {H : Hypernet} {seq premise : Sequent}
    {preact post : Wire}
    (ih : premise.semanticallyValid H)
    (hlink : reluLinked H preact post)
    (hpre : seq.pre = premise.pre)
    (hpremPost : premise.post = .atom .ge (.var preact) (.const 0))
    (hpost : seq.post = .atom .eq (.var post) (.var preact)) :
    seq.semanticallyValid H := by
  intro σ hadm hpre'
  rw [hpre] at hpre'
  have hp := ih σ hadm hpre'
  rw [hpremPost] at hp
  obtain ⟨qp, qy, hqp, hqy, hshape, hpos, hlen, hcase⟩ :=
    reluLinked_facts hlink σ hadm
  obtain ⟨qv, qz, hqv, hqz, hrel⟩ := hp
  have hqvT : qp = qv := Option.some.inj (hqp.symm.trans hqv)
  subst hqvT
  have hqzT : qz = ⟨[], [0], rfl⟩ :=
    (Option.some.inj
      (show some (⟨[], [0], rfl⟩ : QTensor) = some qz from hqz)).symm
  subst hqzT
  have hprem : ∀ x ∈ qp.entries, (0 : ℚ) ≤ x :=
    QTensor.rel2_const_right_elim hrel
  rw [hpost]
  refine ⟨qy, qp, hqy, hqp, ?_⟩
  apply QTensor.rel2_of_getD hshape.symm
  intro i hi
  have hip : i < qp.entries.length := by omega
  have hpge : (0 : ℚ) ≤ qp.entries.getD i 0 := by
    apply hprem
    rw [List.getD_eq_getElem _ _ hip]
    exact List.getElem_mem _
  show qy.entries.getD i 0 = qp.entries.getD i 0
  rcases hcase i hip with ⟨h1, h2⟩ | ⟨-, h2⟩
  · rw [h2, le_antisymm h1 hpge]
  · exact h2

theorem sound_reluNeg {H : Hypernet} {seq premise : Sequent}
    {preact post : Wire}
    (ih : premise.semanticallyValid H)
    (hlink : reluLinked H preact post)
    (hpre : seq.pre = premise.pre)
    (hpremPost : premise.post = .atom .le (.var preact) (.const 0))
    (hpost : seq.post = .atom .eq (.var post) (.const 0)) :
    seq.semanticallyValid H := by
  intro σ hadm hpre'
  rw [hpre] at hpre'
  have hp := ih σ hadm hpre'
  rw [hpremPost] at hp
  obtain ⟨qp, qy, hqp, hqy, hshape, hpos, hlen, hcase⟩ :=
    reluLinked_facts hlink σ hadm
  obtain ⟨qv, qz, hqv, hqz, hrel⟩ := hp
  have hqvT : qp = qv := Option.some.inj (hqp.symm.trans hqv)
  subst hqvT
  have hqzT : qz = ⟨[], [0], rfl⟩ :=
    (Option.some.inj
      (show some (⟨[], [0], rfl⟩ : QTensor) = some qz from hqz)).symm
  subst hqzT
  have hprem : ∀ x ∈ qp.entries, x ≤ (0 : ℚ) :=
    QTensor.rel2_const_right_elim hrel
  rw [hpost]
  refine ⟨qy, ⟨[], [0], rfl⟩, hqy, rfl, ?_⟩
  apply QTensor.rel2_const_right
  intro x hx
  obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hx
  have hjp : j < qp.entries.length := by omega
  have hgd : qy.entries.getD j 0 = x := by
    rw [List.getD_eq_getElem _ _ hj]
    exact hje
  have hple : qp.entries.getD j 0 ≤ 0 := by
    apply hprem
    rw [List.getD_eq_getElem _ _ hjp]
    exact List.getElem_mem _
  show x = (0 : ℚ)
  rcases hcase j hjp with ⟨-, h2⟩ | ⟨h1, h2⟩
  · rw [← hgd, h2]
  · rw [← hgd, h2]
    exact le_antisymm hple h1

theorem sound_lirpa {H : Hypernet}
    {seq lowerPremise upperPremise : Sequent}
    {preact post : Wire} {a b α β γ δ : ℚ}
    (ihl : lowerPremise.semanticallyValid H)
    (ihu : upperPremise.semanticallyValid H)
    (hlink : reluLinked H preact post)
    (hAneg : a < 0) (hBpos : 0 < b)
    (hLower1 : α * a + β ≤ 0) (hLower2 : β ≤ 0) (hLower3 : α * b + β ≤ b)
    (hUpper1 : 0 ≤ γ * a + δ) (hUpper2 : 0 ≤ δ) (hUpper3 : b ≤ γ * b + δ)
    (hpre : seq.pre = lowerPremise.pre)
    (hpreMatch : lowerPremise.pre = upperPremise.pre)
    (hlowerPost : lowerPremise.post = .atom .le (.const a) (.var preact))
    (hupperPost : upperPremise.post = .atom .le (.var preact) (.const b))
    (hpostForm : lirpaConclusionForm preact post α β γ δ seq.post) :
    seq.semanticallyValid H := by
  intro σ hadm hpre'
  rw [hpre] at hpre'
  have hlo := ihl σ hadm hpre'
  rw [hlowerPost] at hlo
  have hup := ihu σ hadm (by rw [← hpreMatch]; exact hpre')
  rw [hupperPost] at hup
  obtain ⟨qp, qy, hqp, hqy, hshape, hposlen, hlen, hcase⟩ :=
    reluLinked_facts hlink σ hadm

  obtain ⟨ca, qv, hca, hqv, hrlo⟩ := hlo
  have hcaT : ca = ⟨[], [a], rfl⟩ :=
    (Option.some.inj
      (show some (⟨[], [a], rfl⟩ : QTensor) = some ca from hca)).symm
  subst hcaT
  have hqvT : qp = qv := Option.some.inj (hqp.symm.trans hqv)
  subst hqvT
  have hloE : ∀ x ∈ qp.entries, a ≤ x :=
    QTensor.rel2_const_left_elim hrlo

  obtain ⟨qv2, cb, hqv2, hcb, hrup⟩ := hup
  have hqv2T : qp = qv2 := Option.some.inj (hqp.symm.trans hqv2)
  subst hqv2T
  have hcbT : cb = ⟨[], [b], rfl⟩ :=
    (Option.some.inj
      (show some (⟨[], [b], rfl⟩ : QTensor) = some cb from hcb)).symm
  subst hcbT
  have hupE : ∀ x ∈ qp.entries, x ≤ b :=
    QTensor.rel2_const_right_elim hrup

  have hpf : seq.post
      = .and (.atom .le (affineWireTerm β α preact) (.var post))
             (.atom .le (.var post) (affineWireTerm δ γ preact)) :=
    hpostForm
  rw [hpf]
  obtain ⟨qaL, hqaL, hsL, hlL, hEL⟩ := affineWireTerm_evalQ σ hqp β α
  obtain ⟨qaU, hqaU, hsU, hlU, hEU⟩ := affineWireTerm_evalQ σ hqp δ γ
  constructor
  ·
    refine ⟨qaL, qy, hqaL, hqy, ?_⟩
    apply QTensor.rel2_of_getD (by rw [hsL, hshape])
    intro i hi
    have hip : i < qp.entries.length := by omega
    have hmem : qp.entries.getD i 0 ∈ qp.entries := by
      rw [List.getD_eq_getElem _ _ hip]
      exact List.getElem_mem _
    have hax := hloE _ hmem
    have hxb := hupE _ hmem
    show qaL.entries.getD i 0 ≤ qy.entries.getD i 0
    rw [hEL i hip]
    rcases hcase i hip with ⟨hple, hy0⟩ | ⟨hpge, hyp⟩
    · rw [hy0]
      have := lirpa_lower_neg hAneg hLower1 hLower2 hax hple
      linarith
    · rw [hyp]
      have := lirpa_lower_pos hBpos hLower2 hLower3 hpge hxb
      linarith
  ·
    refine ⟨qy, qaU, hqy, hqaU, ?_⟩
    apply QTensor.rel2_of_getD (by rw [hsU, ← hshape])
    intro i hi
    have hip : i < qp.entries.length := by omega
    have hmem : qp.entries.getD i 0 ∈ qp.entries := by
      rw [List.getD_eq_getElem _ _ hip]
      exact List.getElem_mem _
    have hax := hloE _ hmem
    have hxb := hupE _ hmem
    show qy.entries.getD i 0 ≤ qaU.entries.getD i 0
    rw [hEU i hip]
    rcases hcase i hip with ⟨hple, hy0⟩ | ⟨hpge, hyp⟩
    · rw [hy0]
      have := lirpa_upper_neg hAneg hUpper1 hUpper2 hax hple
      linarith
    · rw [hyp]
      have := lirpa_upper_pos hBpos hUpper2 hUpper3 hpge hxb
      linarith

mutual

/-- **Soundness.** Every certificate object witnesses the semantic
validity of its sequent. -/
theorem ProofObject.sound {H : Hypernet} {seq : Sequent}
    (pf : ProofObject H seq) : seq.semanticallyValid H :=
  match pf with
  | .mk _ _ _ (.ax _ _ (.mk _ _ h)) => sound_ax h
  | .mk _ _ _ (.weaken _ _ (.mk _ _ _ pproof _ hpre hpost)) =>
      sound_weaken pproof.sound hpre hpost
  | .mk _ _ _ (.cut _ _ (.mk _ _ _ _ lproof _ rproof hpre hpost hcl hcr)) =>
      sound_cut lproof.sound rproof.sound hpre hpost hcl hcr
  | .mk _ _ _ (.andI _ _ (.mk _ _ _ lproof _ rproof hm hpre hpost)) =>
      sound_andI lproof.sound rproof.sound hm hpre hpost
  | .mk _ _ _ (.andE _ _ (.left _ _ _ pproof _ hpre hpost)) =>
      sound_andE_left pproof.sound hpre hpost
  | .mk _ _ _ (.andE _ _ (.right _ _ _ pproof _ hpre hpost)) =>
      sound_andE_right pproof.sound hpre hpost
  | .mk _ _ _ (.orI _ _ (.left _ _ _ pproof _ hpre hpost)) =>
      sound_orI_left pproof.sound hpre hpost
  | .mk _ _ _ (.orI _ _ (.right _ _ _ pproof _ hpre hpost)) =>
      sound_orI_right pproof.sound hpre hpost
  | .mk _ _ _ (.orE _ _ (.mk _ _ _ lproof _ rproof hm hpre hpost)) =>
      sound_orE lproof.sound rproof.sound hm hpre hpost
  | .mk _ _ _ (.eqElim _ _ (.mk _ _ _ eqProof _ bodyProof _ _ _ _
      hpre hm heqPost htyEq hbodyT hconclU)) =>
      sound_eqElim eqProof.sound bodyProof.sound hpre hm heqPost htyEq
        hbodyT hconclU
  | .mk _ _ _ (.convIntro _ _ (.mk _ _ _ pproof _ _ _ hpre hshape
      hhalf hpost)) =>
      sound_convIntro pproof.sound hpre hshape hhalf hpost
  | .mk _ _ _ (.convElim _ _ (.mk _ _ _ pproof _ _ _ hpre hform hhalf)) =>
      sound_convElim pproof.sound hpre hform hhalf
  | .mk _ _ _ (.arithAtom _ _ (.fold _ _ _ pproof _ _ _ _ hpre hz hd)) =>
      sound_arithAtom_fold pproof.sound hpre hz hd
  | .mk _ _ _ (.arithAtom _ _ (.unfold _ _ _ pproof _ _ _ _ hpre hd hz)) =>
      sound_arithAtom_unfold pproof.sound hpre hd hz
  | .mk _ _ _ (.bernCone _ _ (.mk _ _ _ rproof _ simplex S _ poly _
      hpre hregion hpolyTie hpredShape hcoeff hpostApply)) =>
      sound_bernCone rproof.sound hpre hregion hpolyTie hpredShape hcoeff
        hpostApply
  | .mk _ _ _ (.norm _ _ (.mk _ _ _ _ hcanon htyEq htyDef hfinL hfinR
      hpost)) =>
      sound_norm hcanon htyEq htyDef hfinL hfinR hpost
  | .mk _ _ _ (.farkas _ _ (.mk _ _ _ _ _ hshape hfin hwpos hvalid
      hpost)) =>
      sound_farkas hshape hfin hwpos hvalid hpost
  | .mk _ _ _ (.subdivide _ _ (.mk _ _ _ rproof _ _ _ _ _ _ _ bproofs _ _
      hpre hregionPost hbranchPre hbranchPost hcover)) =>
      sound_subdivide rproof.sound (fun k => (bproofs k).sound) hpre
        hregionPost hbranchPre hbranchPost hcover
  | .mk _ _ _ (.lirpa _ _ (.mk _ _ _ lproof _ uproof _ _ _ _ _ _ _ _ _
      hlink hAneg hBpos hL1 hL2 hL3 hU1 hU2 hU3 hpre hpreM hlow hup
      hpostF)) =>
      sound_lirpa lproof.sound uproof.sound hlink hAneg hBpos hL1 hL2 hL3
        hU1 hU2 hU3 hpre hpreM hlow hup hpostF
  | .mk _ _ _ (.reluPos _ _ (.mk _ _ _ pproof _ _ hlink hpre hpp hc)) =>
      sound_reluPos pproof.sound hlink hpre hpp hc
  | .mk _ _ _ (.reluNeg _ _ (.mk _ _ _ pproof _ _ hlink hpre hpp hc)) =>
      sound_reluNeg pproof.sound hlink hpre hpp hc
  | .mk _ _ _ (.reluNN _ _ (.mk _ _ _ _ hlink hc)) =>
      sound_reluNN hlink hc
  | .mk _ _ _ (.reluAbove _ _ (.mk _ _ _ _ hlink hc)) =>
      sound_reluAbove hlink hc
  | .mk _ _ _ (.cellInInterior _ _ (.mk _ _ _ pproof _ _ _ _ happ
      hinshape houts hpre hint hpost)) =>
      sound_cellInInterior pproof.sound happ hinshape houts hpre hint hpost
  | .mk _ _ _ (.cellOut _ _ (.mk _ _ _ pproof _ _ _ _ _ happ
      hinshape houts hpre hwit hpost)) =>
      sound_cellOut pproof.sound happ hinshape houts hpre hwit hpost
  | .mk _ _ _ (.eqRefl _ _ (.mk _ _ _ htyDef hfin hpost)) =>
      sound_eqRefl htyDef hfin hpost
  | .mk _ _ _ (.eqSym _ _ (.mk _ _ _ pproof _ _ hpre hpremPost
      hpost)) =>
      sound_eqSym pproof.sound hpre hpremPost hpost
  | .mk _ _ _ (.promise _ _ (.mk _ seq supplier sproof consumer
      cproof contract path iface ctx hsPost hpath hplumb hpostEq hctx
      hconf hsep)) =>
      sound_promise ⟨seq, supplier, consumer, contract, path, iface, ctx,
        hsPost, hpath, hplumb, hpostEq, hctx, hconf, hsep⟩
        sproof.sound cproof.sound
  | .mk _ _ _ (.syzygy _ _ (.mk _ seq comps cpfs comb concl _
      hpreC hshape hfin hwpos hcompPos hvalid hform)) =>
      sound_syzygy ⟨seq, comps, comb, concl, hpreC, hshape, hfin, hwpos,
        hcompPos, hvalid, hform⟩ cpfs.soundAll
  | .mk _ _ _ (.pConstExact _ _ (.mk _ _ _ _ _ _ hEval hpost)) =>
      sound_pConstExact hEval hpost
  | .mk _ _ _ (.pBound _ _ (.mk _ _ _ cpfs _ _ _
      hpreC hshape hfin hwpos hcompPos hvalid hform)) =>
      sound_pBound cpfs.soundAll hpreC hshape hfin hwpos hcompPos hvalid hform
  | .mk _ _ _ (.psdCertT _ _ (.mk _ _ _ _ _ _ _
      hwit hconcl hshape hfin hwpos hform)) =>
      sound_psdCertT hwit hconcl hshape hfin hwpos hform
  | .mk _ _ _ (.psdCertDD _ _ (.mk _ _ _ _ _ _ _
      hwit hconcl hshape hfin hwpos hform)) =>
      sound_psdCertDD hwit hconcl hshape hfin hwpos hform
  | .mk _ _ _ (.psdCertK _ _ (.mk _ _ _ _ _ _ _ _ _ _ _
      hwit hconcl hshape hfin hwpos hform)) =>
      sound_psdCertK hwit hconcl hshape hfin hwpos hform

termination_by structural pf

theorem ProofSeqList.soundAll {H : Hypernet} {comps : List Sequent}
    (pfs : ProofSeqList H comps) : ∀ c ∈ comps, c.semanticallyValid H :=
  match pfs with
  | .nil _ => fun _ hc => nomatch hc
  | .cons _ _ _ pf pfs => fun c hc =>
      match List.mem_cons.mp hc with
      | Or.inl heq => heq ▸ pf.sound
      | Or.inr hm => pfs.soundAll c hm
termination_by structural pfs
end

theorem check_sound {H : Hypernet} {seq : Sequent} (pf : ProofObject H seq)
    (_hcheck : check pf = true) : seq.semanticallyValid H :=
  pf.sound

mutual

/-- Boolean recognizer for the v0 fragment of the calculus. -/
def ProofObject.v0frag {H : Hypernet} {seq : Sequent}
    (pf : ProofObject H seq) : Bool :=
  match pf with
  | .mk _ _ _ (.ax _ _ _) => true
  | .mk _ _ _ (.weaken _ _ (.mk _ _ _ pproof _ _ _)) => pproof.v0frag
  | .mk _ _ _ (.cut _ _ (.mk _ _ _ _ lproof _ rproof _ _ _ _)) =>
      lproof.v0frag && rproof.v0frag
  | .mk _ _ _ (.andI _ _ (.mk _ _ _ lproof _ rproof _ _ _)) =>
      lproof.v0frag && rproof.v0frag
  | .mk _ _ _ (.andE _ _ (.left _ _ _ pproof _ _ _)) => pproof.v0frag
  | .mk _ _ _ (.andE _ _ (.right _ _ _ pproof _ _ _)) => pproof.v0frag
  | .mk _ _ _ (.orI _ _ (.left _ _ _ pproof _ _ _)) => pproof.v0frag
  | .mk _ _ _ (.orI _ _ (.right _ _ _ pproof _ _ _)) => pproof.v0frag
  | .mk _ _ _ (.orE _ _ (.mk _ _ _ lproof _ rproof _ _ _)) =>
      lproof.v0frag && rproof.v0frag
  | .mk _ _ _ (.eqElim _ _
      (.mk _ _ _ eqProof _ bodyProof _ _ _ _ _ _ _ _ _ _)) =>
      eqProof.v0frag && bodyProof.v0frag
  | .mk _ _ _ (.convIntro _ _ (.mk _ _ _ pproof _ _ _ _ _ _ _)) =>
      pproof.v0frag
  | .mk _ _ _ (.convElim _ _ (.mk _ _ _ pproof _ _ _ _ _ _)) =>
      pproof.v0frag
  | .mk _ _ _ (.arithAtom _ _ (.fold _ _ _ pproof _ _ _ _ _ _ _)) =>
      pproof.v0frag
  | .mk _ _ _ (.arithAtom _ _ (.unfold _ _ _ pproof _ _ _ _ _ _ _)) =>
      pproof.v0frag
  | .mk _ _ _ (.bernCone _ _
      (.mk _ _ _ rproof _ _ _ _ _ _ _ _ _ _ _ _)) =>

      rproof.v0frag
  | .mk _ _ _ (.farkas _ _ _) =>

      true
  | .mk _ _ _ (.norm _ _ _) =>

      true
  | .mk _ _ _ (.subdivide _ _ _) => false
  | .mk _ _ _ (.lirpa _ _ _) => false
  | .mk _ _ _ (.reluPos _ _ _) => false
  | .mk _ _ _ (.reluNeg _ _ _) => false
  | .mk _ _ _ (.reluNN _ _ _) => false
  | .mk _ _ _ (.reluAbove _ _ _) => false
  | .mk _ _ _ (.cellInInterior _ _ _) => false
  | .mk _ _ _ (.cellOut _ _ _) => false

  | .mk _ _ _ (.eqRefl _ _ _) => true
  | .mk _ _ _ (.eqSym _ _ (.mk _ _ _ pproof _ _ _ _ _)) =>
      pproof.v0frag

  | .mk _ _ _ (.promise _ _ (.mk _ _ _ sproof _ cproof _ _ _ _
      _ _ _ _ _ _ _)) =>
      sproof.v0frag && cproof.v0frag
  | .mk _ _ _ (.syzygy _ _ (.mk _ _ _ cpfs _ _ _ _ _ _ _ _ _ _)) =>
      cpfs.v0fragAll

  | .mk _ _ _ (.pConstExact _ _ _) => false
  | .mk _ _ _ (.pBound _ _ _) => false

  | .mk _ _ _ (.psdCertT _ _ _) => false
  | .mk _ _ _ (.psdCertDD _ _ _) => false
  | .mk _ _ _ (.psdCertK _ _ _) => false

termination_by structural pf

def ProofSeqList.v0fragAll {H : Hypernet} {comps : List Sequent}
    (pfs : ProofSeqList H comps) : Bool :=
  match pfs with
  | .nil _ => true
  | .cons _ _ _ pf pfs => pf.v0frag && pfs.v0fragAll
termination_by structural pfs
end

mutual

/-- Soundness restricted to the v0 fragment: a certificate recognized by
`v0frag` witnesses the semantic validity of its sequent. -/
theorem ProofObject.sound_v0 {H : Hypernet} {seq : Sequent}
    (pf : ProofObject H seq) (hfrag : pf.v0frag = true) :
    seq.semanticallyValid H :=
  match pf, hfrag with
  | .mk _ _ _ (.ax _ _ (.mk _ _ h)), _ => sound_ax h
  | .mk _ _ _ (.weaken _ _ (.mk _ _ _ pproof _ hpre hpost)), h => by
      simp only [ProofObject.v0frag] at h
      exact sound_weaken (pproof.sound_v0 h) hpre hpost
  | .mk _ _ _ (.cut _ _ (.mk _ _ _ _ lproof _ rproof hpre hpost hcl hcr)),
      h => by
      simp only [ProofObject.v0frag, Bool.and_eq_true] at h
      exact sound_cut (lproof.sound_v0 h.1) (rproof.sound_v0 h.2)
        hpre hpost hcl hcr
  | .mk _ _ _ (.andI _ _ (.mk _ _ _ lproof _ rproof hm hpre hpost)),
      h => by
      simp only [ProofObject.v0frag, Bool.and_eq_true] at h
      exact sound_andI (lproof.sound_v0 h.1) (rproof.sound_v0 h.2)
        hm hpre hpost
  | .mk _ _ _ (.andE _ _ (.left _ _ _ pproof _ hpre hpost)), h => by
      simp only [ProofObject.v0frag] at h
      exact sound_andE_left (pproof.sound_v0 h) hpre hpost
  | .mk _ _ _ (.andE _ _ (.right _ _ _ pproof _ hpre hpost)), h => by
      simp only [ProofObject.v0frag] at h
      exact sound_andE_right (pproof.sound_v0 h) hpre hpost
  | .mk _ _ _ (.orI _ _ (.left _ _ _ pproof _ hpre hpost)), h => by
      simp only [ProofObject.v0frag] at h
      exact sound_orI_left (pproof.sound_v0 h) hpre hpost
  | .mk _ _ _ (.orI _ _ (.right _ _ _ pproof _ hpre hpost)), h => by
      simp only [ProofObject.v0frag] at h
      exact sound_orI_right (pproof.sound_v0 h) hpre hpost
  | .mk _ _ _ (.orE _ _ (.mk _ _ _ lproof _ rproof hm hpre hpost)),
      h => by
      simp only [ProofObject.v0frag, Bool.and_eq_true] at h
      exact sound_orE (lproof.sound_v0 h.1) (rproof.sound_v0 h.2)
        hm hpre hpost
  | .mk _ _ _ (.eqElim _ _ (.mk _ _ _ eqProof _ bodyProof _ _ _ _
      hpre hm heqPost htyEq hbodyT hconclU)), h => by
      simp only [ProofObject.v0frag, Bool.and_eq_true] at h
      exact sound_eqElim (eqProof.sound_v0 h.1) (bodyProof.sound_v0 h.2)
        hpre hm heqPost htyEq hbodyT hconclU
  | .mk _ _ _ (.convIntro _ _ (.mk _ _ _ pproof _ _ _ hpre hshape
      hhalf hpost)), h => by
      simp only [ProofObject.v0frag] at h
      exact sound_convIntro (pproof.sound_v0 h) hpre hshape hhalf hpost
  | .mk _ _ _ (.convElim _ _ (.mk _ _ _ pproof _ _ _ hpre hform hhalf)),
      h => by
      simp only [ProofObject.v0frag] at h
      exact sound_convElim (pproof.sound_v0 h) hpre hform hhalf
  | .mk _ _ _ (.arithAtom _ _ (.fold _ _ _ pproof _ _ _ _ hpre hz hd)),
      h => by
      simp only [ProofObject.v0frag] at h
      exact sound_arithAtom_fold (pproof.sound_v0 h) hpre hz hd
  | .mk _ _ _ (.arithAtom _ _ (.unfold _ _ _ pproof _ _ _ _ hpre hd hz)),
      h => by
      simp only [ProofObject.v0frag] at h
      exact sound_arithAtom_unfold (pproof.sound_v0 h) hpre hd hz
  | .mk _ _ _ (.bernCone _ _ (.mk _ _ _ rproof _ simplex S _ poly _
      hpre hregion hpolyTie hpredShape hcoeff hpostApply)), h => by
      simp only [ProofObject.v0frag] at h
      exact sound_bernCone (rproof.sound_v0 h) hpre hregion hpolyTie
        hpredShape hcoeff hpostApply
  | .mk _ _ _ (.farkas _ _ (.mk _ _ _ _ _ hshape hfin hwpos hvalid
      hpost)), _ =>
      sound_farkas hshape hfin hwpos hvalid hpost
  | .mk _ _ _ (.norm _ _ (.mk _ _ _ _ hcanon htyEq htyDef hfinL hfinR
      hpost)), _ =>
      sound_norm hcanon htyEq htyDef hfinL hfinR hpost
  | .mk _ _ _ (.subdivide _ _ _), h => by
      simp only [ProofObject.v0frag] at h
      exact Bool.noConfusion h
  | .mk _ _ _ (.lirpa _ _ _), h => by
      simp only [ProofObject.v0frag] at h
      exact Bool.noConfusion h
  | .mk _ _ _ (.reluPos _ _ _), h => by
      simp only [ProofObject.v0frag] at h
      exact Bool.noConfusion h
  | .mk _ _ _ (.reluNeg _ _ _), h => by
      simp only [ProofObject.v0frag] at h
      exact Bool.noConfusion h
  | .mk _ _ _ (.reluNN _ _ _), h => by
      simp only [ProofObject.v0frag] at h
      exact Bool.noConfusion h
  | .mk _ _ _ (.reluAbove _ _ _), h => by
      simp only [ProofObject.v0frag] at h
      exact Bool.noConfusion h
  | .mk _ _ _ (.cellInInterior _ _ _), h => by
      simp only [ProofObject.v0frag] at h
      exact Bool.noConfusion h
  | .mk _ _ _ (.cellOut _ _ _), h => by
      simp only [ProofObject.v0frag] at h
      exact Bool.noConfusion h
  | .mk _ _ _ (.eqRefl _ _ (.mk _ _ _ htyDef hfin hpost)), _ =>
      sound_eqRefl htyDef hfin hpost
  | .mk _ _ _ (.eqSym _ _ (.mk _ _ _ pproof _ _ hpre hpremPost
      hpost)), h => by
      simp only [ProofObject.v0frag] at h
      exact sound_eqSym (pproof.sound_v0 h) hpre hpremPost hpost
  | .mk _ _ _ (.promise _ _ (.mk _ seq supplier sproof consumer
      cproof contract path iface ctx hsPost hpath hplumb hpostEq hctx
      hconf hsep)), h => by
      simp only [ProofObject.v0frag, Bool.and_eq_true] at h
      exact sound_promise ⟨seq, supplier, consumer, contract, path, iface,
        ctx, hsPost, hpath, hplumb, hpostEq, hctx, hconf, hsep⟩
        (sproof.sound_v0 h.1) (cproof.sound_v0 h.2)
  | .mk _ _ _ (.syzygy _ _ (.mk _ seq comps cpfs comb concl _
      hpreC hshape hfin hwpos hcompPos hvalid hform)), h => by
      simp only [ProofObject.v0frag] at h
      exact sound_syzygy ⟨seq, comps, comb, concl, hpreC, hshape, hfin,
        hwpos, hcompPos, hvalid, hform⟩ (cpfs.soundAll_v0 h)
  | .mk _ _ _ (.pConstExact _ _ _), h => by
      simp only [ProofObject.v0frag] at h
      exact Bool.noConfusion h
  | .mk _ _ _ (.pBound _ _ _), h => by
      simp only [ProofObject.v0frag] at h
      exact Bool.noConfusion h
  | .mk _ _ _ (.psdCertT _ _ _), h => by
      simp only [ProofObject.v0frag] at h
      exact Bool.noConfusion h
  | .mk _ _ _ (.psdCertDD _ _ _), h => by
      simp only [ProofObject.v0frag] at h
      exact Bool.noConfusion h
  | .mk _ _ _ (.psdCertK _ _ _), h => by
      simp only [ProofObject.v0frag] at h
      exact Bool.noConfusion h

termination_by structural pf

theorem ProofSeqList.soundAll_v0 {H : Hypernet} {comps : List Sequent}
    (pfs : ProofSeqList H comps) (hall : pfs.v0fragAll = true) :
    ∀ c ∈ comps, c.semanticallyValid H :=
  match pfs, hall with
  | .nil _, _ => fun _ hc => nomatch hc
  | .cons _ _ _ pf pfs, h => fun c hc =>
      have hsplit : pf.v0frag = true ∧ pfs.v0fragAll = true := by
        simpa only [ProofSeqList.v0fragAll, Bool.and_eq_true] using h
      match List.mem_cons.mp hc with
      | Or.inl heq => heq ▸ pf.sound_v0 hsplit.1
      | Or.inr hm => pfs.soundAll_v0 hsplit.2 c hm
termination_by structural pfs
end

theorem check_sound_v0 {H : Hypernet} {seq : Sequent} (pf : ProofObject H seq)
    (hfrag : pf.v0frag = true) : seq.semanticallyValid H :=
  pf.sound_v0 hfrag

end PPLC
