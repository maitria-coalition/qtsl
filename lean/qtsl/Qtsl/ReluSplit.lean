import Qtsl.Soundness
import Qtsl.Decide

/-!
# The ReLU-split rule

Soundness of case-splitting on the sign of a ReLU input: from
`T₊ ▷ Φ ∧ (h ≥ 0) ⊢ Ψ[b := h]` and `T₋ ▷ Φ ∧ (h ≤ 0) ⊢ Ψ[b := 0]`
conclude `Φ ⊢ Ψ`, where `b` marks the occurrences of the ReLU output
wire in `Ψ`.
-/

namespace PPLC

theorem sound_reluSplit {H : Hypernet}
    {seq activePremise inactivePremise : Sequent}
    {preact post marker : Wire} {bodyForm : Formula}
    (ihActive : activePremise.semanticallyValid H)
    (ihInactive : inactivePremise.semanticallyValid H)
    (hlink : reluLinked H preact post)
    (hrank0 : ∃ τ, H.wireType post = some τ ∧ τ.shape = [])
    (hActPre : activePremise.pre
      = .and seq.pre (.atom .ge (.var preact) (.const 0)))
    (hInactPre : inactivePremise.pre
      = .and seq.pre (.atom .le (.var preact) (.const 0)))
    (hActPost : substituteInFormula bodyForm marker (.var preact)
      activePremise.post)
    (hInactPost : substituteInFormula bodyForm marker (.const 0)
      inactivePremise.post)
    (hconcl : substituteInFormula bodyForm marker (.var post) seq.post) :
    seq.semanticallyValid H := by
  intro σ hadm hpre
  obtain ⟨qp, qy, hqp, hqy, hshape, hpos, hlen, hcase⟩ :=
    reluLinked_facts hlink σ hadm

  obtain ⟨τ, hτ, hτs⟩ := hrank0
  have hqys : qy.shape = [] := by
    obtain ⟨τ', hτ', hsh⟩ := σ.wireQ_shape hqy
    rw [hτ] at hτ'
    injection hτ' with hτ'
    rw [hsh, ← hτ', hτs]
  have hqps : qp.shape = [] := hshape.trans hqys
  have hpE : qp.entries = [qp.scalar] :=
    QTensor.entries_singleton (Or.inl hqps)
  have hyE : qy.entries = [qy.scalar] :=
    QTensor.entries_singleton (Or.inl hqys)
  rw [hconcl]

  rcases hcase 0 hpos with ⟨hple, hy0⟩ | ⟨hpge, hyp⟩

  · have hpreI : Formula.holds σ inactivePremise.pre := by
      rw [hInactPre]
      refine ⟨hpre, qp, ⟨[], [0], rfl⟩, hqp, rfl, ?_⟩
      apply QTensor.rel2_const_right
      intro x hx
      rw [hpE] at hx
      rcases List.mem_singleton.mp hx with rfl
      show qp.scalar ≤ 0
      exact hple
    have hbody := ihInactive σ hadm hpreI
    rw [hInactPost] at hbody
    have hyq0 : qy = (⟨[], [0], rfl⟩ : QTensor) := by
      apply QTensor.ext' hqys
      rw [hyE]
      have hs0 : qy.scalar = 0 := hy0
      rw [hs0]
    have hEv : Term.evalQ σ (.const 0) = Term.evalQ σ (.var post) := by
      show some (⟨[], [0], rfl⟩ : QTensor) = σ.wireQ post
      rw [hqy, hyq0]
    exact (Formula.holds_subst_congr σ hEv bodyForm).mp hbody

  · have hpreA : Formula.holds σ activePremise.pre := by
      rw [hActPre]
      refine ⟨hpre, qp, ⟨[], [0], rfl⟩, hqp, rfl, ?_⟩
      apply QTensor.rel2_const_right
      intro x hx
      rw [hpE] at hx
      rcases List.mem_singleton.mp hx with rfl
      show (0 : ℚ) ≤ qp.scalar
      exact hpge
    have hbody := ihActive σ hadm hpreA
    rw [hActPost] at hbody
    have hyqp : qy = qp := by
      apply QTensor.ext' (hshape.symm)
      rw [hpE, hyE]
      have hs' : qy.scalar = qp.scalar := hyp
      rw [hs']
    have hEv : Term.evalQ σ (.var preact) = Term.evalQ σ (.var post) := by
      show σ.wireQ preact = σ.wireQ post
      rw [hqp, hqy, hyqp]
    exact (Formula.holds_subst_congr σ hEv bodyForm).mp hbody

namespace ReluSplitScope

def HSplit : Hypernet where
  wireType := fun w =>
    if w = 0 then some ⟨[2], Dtype.Q⟩
    else if w = 1 then some ⟨[2], Dtype.Q⟩ else none
  applications := [.relu [2] 0 1]
  linearity := by decide
  acyclic := by decide
  typeConsistent := by decide

private def qe (q : ℚ) : Dtype.Q.carrier :=
  ⟨.fin q, ⟨trivial, fun h => nomatch h⟩⟩

def σsplit : HSplit.Valuation := fun w _ h =>
  match w, h with
  | 0, h => (Option.some.inj h) ▸ (⟨[qe 1, qe (-1)], rfl⟩ :
      TensorValue ⟨[2], Dtype.Q⟩)
  | 1, h => (Option.some.inj h) ▸ (⟨[qe 1, qe 0], rfl⟩ :
      TensorValue ⟨[2], Dtype.Q⟩)
  | (_ + 2), h => nomatch h

theorem σsplit_admissible : σsplit.Admissible := by
  intro app happ
  simp only [HSplit, List.mem_cons, List.not_mem_nil, or_false] at happ
  subst happ
  intro i
  have h2 : i.val < 2 := i.isLt
  rcases (by omega : i.val = 0 ∨ i.val = 1) with h | h <;> rw [h]
  · exact ⟨1, 1, rfl, rfl, Or.inr ⟨by norm_num, rfl⟩⟩
  · exact ⟨-1, 0, rfl, rfl, Or.inl ⟨by norm_num, rfl⟩⟩

private abbrev bodyForm₂ : Formula :=
  .or (.atom .eq (.var 2) (.const 0)) (.atom .eq (.var 2) (.var 0))

private abbrev ΨY : Formula :=
  .or (.atom .eq (.var 1) (.const 0)) (.atom .eq (.var 1) (.var 0))

private abbrev ΨH : Formula :=
  .or (.atom .eq (.var 0) (.const 0)) (.atom .eq (.var 0) (.var 0))

private abbrev Ψ0 : Formula :=
  .or (.atom .eq (.const 0) (.const 0)) (.atom .eq (.const 0) (.var 0))

private theorem TplusValid :
    (⟨.and .tt (.atom .ge (.var 0) (.const 0)), ΨH⟩ :
      Sequent).semanticallyValid HSplit := by
  intro σ _ hpre
  obtain ⟨-, a, a', ha, -, -⟩ := hpre
  exact Or.inr ⟨a, a, ha, ha, QTensor.rel2_of_getD rfl (fun i _ => rfl)⟩

private theorem TminusValid :
    (⟨.and .tt (.atom .le (.var 0) (.const 0)), Ψ0⟩ :
      Sequent).semanticallyValid HSplit := by
  intro σ _ _
  exact Or.inl ⟨⟨[], [0], rfl⟩, ⟨[], [0], rfl⟩, rfl, rfl,
    QTensor.rel2_of_getD rfl (fun i _ => rfl)⟩

end ReluSplitScope

theorem reluSplit_rank0_necessary :
    ¬ (∀ (H : Hypernet) (seq activePremise inactivePremise : Sequent)
        (preact post marker : Wire) (bodyForm : Formula),
        activePremise.semanticallyValid H →
        inactivePremise.semanticallyValid H →
        reluLinked H preact post →
        activePremise.pre
          = .and seq.pre (.atom .ge (.var preact) (.const 0)) →
        inactivePremise.pre
          = .and seq.pre (.atom .le (.var preact) (.const 0)) →
        substituteInFormula bodyForm marker (.var preact)
          activePremise.post →
        substituteInFormula bodyForm marker (.const 0)
          inactivePremise.post →
        substituteInFormula bodyForm marker (.var post) seq.post →
        seq.semanticallyValid H) := by
  intro hclaim
  have hlink : reluLinked ReluSplitScope.HSplit 0 1 :=
    reluLinked_iff.mpr ⟨[2], by simp [ReluSplitScope.HSplit], by decide⟩
  have hvalid :=
    hclaim ReluSplitScope.HSplit
      ⟨.tt, ReluSplitScope.ΨY⟩
      ⟨.and .tt (.atom .ge (.var 0) (.const 0)), ReluSplitScope.ΨH⟩
      ⟨.and .tt (.atom .le (.var 0) (.const 0)), ReluSplitScope.Ψ0⟩
      0 1 2 ReluSplitScope.bodyForm₂
      ReluSplitScope.TplusValid ReluSplitScope.TminusValid hlink
      rfl rfl rfl rfl rfl
  have hconcl := hvalid ReluSplitScope.σsplit
    ReluSplitScope.σsplit_admissible trivial

  have hwY : Term.evalQ ReluSplitScope.σsplit (.var 1)
      = some ⟨[2], [1, 0], rfl⟩ := rfl
  have hwH : Term.evalQ ReluSplitScope.σsplit (.var 0)
      = some ⟨[2], [1, -1], rfl⟩ := rfl
  have hwZ : Term.evalQ ReluSplitScope.σsplit (.const 0)
      = some ⟨[], [0], rfl⟩ := rfl
  rcases hconcl with ⟨a, a', ha, ha', hrel⟩ | ⟨a, a', ha, ha', hrel⟩
  ·
    rw [hwY] at ha
    injection ha with ha
    subst ha
    rw [hwZ] at ha'
    injection ha' with ha'
    subst ha'
    have hall := QTensor.rel2_const_right_elim hrel
    have h1 : (1 : ℚ) = 0 := hall 1 (by simp)
    norm_num at h1
  ·
    rw [hwY] at ha
    injection ha with ha
    subst ha
    rw [hwH] at ha'
    injection ha' with ha'
    subst ha'
    unfold QTensor.rel2 at hrel
    rw [if_pos rfl] at hrel
    have h2 : (0 : ℚ) = -1 :=
      hrel ((0 : ℚ), (-1 : ℚ)) (by simp [List.zip])
    norm_num at h2

#print axioms sound_reluSplit
#print axioms reluSplit_rank0_necessary

end PPLC
