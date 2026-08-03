import Qtsl.Soundness
import Qtsl.EvalDemo

/-!
# Soundness capstone for the worked example

The worked-example certificate is proven semantically valid through
`check_sound_v0`: `w₀ ∈ [1,2] ∧ ⊤ ⊢ 1/2 + 2·w₀ ≥ 0` is true in
the model. Non-vacuity is witnessed explicitly: the valuation
`w₀ := 3/2` is admissible and satisfies the premise, so the conclusion
has actual content.
-/

namespace PPLC
namespace SoundnessDemo

open EvalDemo

theorem demoFrag : pfGoal.v0frag = true := by
  decide +kernel

theorem demoValid : seqGoal.semanticallyValid H0 :=
  check_sound_v0 pfGoal demoFrag

def val32 : TensorValue ⟨[1], Dtype.Q⟩ :=
  ⟨[⟨.fin (3/2), ⟨trivial, fun h => nomatch h⟩⟩], rfl⟩

def σ₀ : H0.Valuation := fun w _ h =>
  match w, h with
  | 0, h => (Option.some.inj h) ▸ val32
  | (_ + 1), h => nomatch h

theorem σ₀_admissible : σ₀.Admissible := fun _ happ => nomatch happ

theorem σ₀_read : Term.evalQ σ₀ w0 = some ⟨[1], [3/2], rfl⟩ := rfl

theorem premiseSat : Formula.holds σ₀ seqGoal.pre := by
  refine ⟨⟨rfl, ⟨[1], [3/2], rfl⟩, σ₀_read, rfl, ?_⟩, trivial⟩
  refine ⟨fun _ => (1 : ℝ) / 2, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    cases hv
  · show ((List.finRange 2).map (fun _ => (1 : ℝ) / 2)).sum = 1
    rw [show List.finRange 2 = [0, 1] from rfl]
    norm_num
  · intro j
    have hjv : j.val = 0 := by
      have h := j.isLt
      have he : Sempty.simplex.complex.ambDim = 1 := rfl
      omega
    show ((List.finRange 2).map (fun v => 1 / 2 * (cxB.coord v j : ℝ))).sum
      = (([3/2] : List ℚ).getD j.val 0 : ℝ)
    rw [show List.finRange 2 = [0, 1] from rfl, hjv]
    show (1 : ℝ) / 2 * (cxB.coord (0 : Fin 2) j : ℝ)
      + ((1 : ℝ) / 2 * (cxB.coord (1 : Fin 2) j : ℝ) + 0)
      = (((3 : ℚ) / 2 : ℚ) : ℝ)
    rw [show cxB.coord (0 : Fin 2) j = 1 from rfl,
      show cxB.coord (1 : Fin 2) j = 2 from rfl]
    norm_num
  · intro v hv
    cases hv
  · intro v _ _
    norm_num

theorem conclusionAtWitness : Formula.holds σ₀ seqGoal.post :=
  demoValid σ₀ σ₀_admissible premiseSat

#print axioms demoValid
#print axioms conclusionAtWitness

def rayPoly : QArith.Poly := [([(0, 2)], 1)]

theorem raySweep : (QArith.fdBernstein [[(0 : ℚ)], [1]] [false, true] 2
      rayPoly).map (QArith.gridAll (fun c => decide (0 ≤ c)))
    = some true := by
  decide +kernel

theorem rayCertified (u₀ : ℚ) (hu : 0 ≤ u₀) :
    decide (0 ≤ QArith.Poly.eval (fun j =>
      ((List.range ([[(0 : ℚ)], [1]] : List (List ℚ)).length).map
        fun i => (([[(0 : ℚ)], [1]] : List (List ℚ)).getD i []).getD j 0 *
          (if ([false, true] : List Bool).getD i false
           then -u₀ else 1 + u₀)).sum) rayPoly) = true := by
  have hopt := raySweep
  cases hfd : QArith.fdBernstein [[(0 : ℚ)], [1]] [false, true] 2 rayPoly with
  | none => rw [hfd] at hopt; cases hopt
  | some t =>
    rw [hfd] at hopt
    injection hopt with hgrid
    exact QArith.fdBernstein_sound_dim1 [[(0 : ℚ)], [1]] [false, true] 2
      rayPoly t (fun c => decide (0 ≤ c)) u₀ (Or.inr rfl) hfd hgrid hu
      (by decide)
      (fun a c hc ha => by
        rw [decide_eq_true_eq] at ha ⊢
        exact mul_nonneg hc ha)
      (fun a b l hl hl1 ha hb => by
        rw [decide_eq_true_eq] at ha hb ⊢
        nlinarith)

#print axioms rayCertified

#print axioms ProofObject.sound
#print axioms check_sound

theorem subdivideFragGate : pfSubdivide.v0frag = false := by
  decide +kernel

theorem subdivideValid : seqGoal.semanticallyValid H0 :=
  check_sound pfSubdivide rfl

theorem conclusionAtWitness_subdivide : Formula.holds σ₀ seqGoal.post :=
  subdivideValid σ₀ σ₀_admissible premiseSat

#print axioms subdivideValid
#print axioms conclusionAtWitness_subdivide

theorem reluNNValid : seqReluNN.semanticallyValid HR :=
  check_sound pfReluNN rfl
theorem reluAboveValid : seqReluAbove.semanticallyValid HR :=
  check_sound pfReluAbove rfl
theorem reluPosValid : seqReluPos.semanticallyValid HR :=
  check_sound pfReluPos rfl
theorem reluNegValid : seqReluNeg.semanticallyValid HR :=
  check_sound pfReluNeg rfl
theorem lirpaValid : seqLirpa.semanticallyValid HR :=
  check_sound pfLirpa rfl

private def qe (q : ℚ) : Dtype.Q.carrier :=
  ⟨.fin q, ⟨trivial, fun h => nomatch h⟩⟩

def σQpos : HR.Valuation := fun w _ h =>
  match w, h with
  | 0, h => (Option.some.inj h) ▸ (⟨[qe (1/2)], rfl⟩ :
      TensorValue ⟨[1], Dtype.Q⟩)
  | 1, h => (Option.some.inj h) ▸ (⟨[qe (1/2)], rfl⟩ :
      TensorValue ⟨[1], Dtype.Q⟩)
  | (_ + 2), h => nomatch h

def σQneg : HR.Valuation := fun w _ h =>
  match w, h with
  | 0, h => (Option.some.inj h) ▸ (⟨[qe (-1/2)], rfl⟩ :
      TensorValue ⟨[1], Dtype.Q⟩)
  | 1, h => (Option.some.inj h) ▸ (⟨[qe 0], rfl⟩ :
      TensorValue ⟨[1], Dtype.Q⟩)
  | (_ + 2), h => nomatch h

theorem σQpos_admissible : σQpos.Admissible := by
  intro app happ
  simp only [HR, List.mem_cons, List.not_mem_nil, or_false] at happ
  subst happ
  intro i
  have hi0 : i.val = 0 := by
    have h1 : i.val < 1 := i.isLt
    omega
  rw [hi0]
  exact ⟨1/2, 1/2, rfl, rfl, Or.inr ⟨by norm_num, rfl⟩⟩

theorem σQneg_admissible : σQneg.Admissible := by
  intro app happ
  simp only [HR, List.mem_cons, List.not_mem_nil, or_false] at happ
  subst happ
  intro i
  have hi0 : i.val = 0 := by
    have h1 : i.val < 1 := i.isLt
    omega
  rw [hi0]
  exact ⟨-1/2, 0, rfl, rfl, Or.inl ⟨by norm_num, rfl⟩⟩

theorem reluPosPremiseSat : Formula.holds σQpos seqReluPos.pre := by
  refine ⟨⟨[1], [1/2], rfl⟩, ⟨[], [0], rfl⟩, rfl, rfl, ?_⟩
  apply QTensor.rel2_const_right
  intro z hz
  rcases List.mem_singleton.mp hz with rfl
  show (0 : ℚ) ≤ 1/2
  norm_num

theorem reluPosAtWitness : Formula.holds σQpos seqReluPos.post :=
  reluPosValid σQpos σQpos_admissible reluPosPremiseSat

theorem reluNegPremiseSat : Formula.holds σQneg seqReluNeg.pre := by
  refine ⟨⟨[1], [-1/2], rfl⟩, ⟨[], [0], rfl⟩, rfl, rfl, ?_⟩
  apply QTensor.rel2_const_right
  intro z hz
  rcases List.mem_singleton.mp hz with rfl
  show (-1/2 : ℚ) ≤ 0
  norm_num

theorem reluNegAtWitness : Formula.holds σQneg seqReluNeg.post :=
  reluNegValid σQneg σQneg_admissible reluNegPremiseSat

theorem lirpaBoxSat : Formula.holds σQpos seqLirpa.pre := by
  constructor
  · refine ⟨⟨[], [-1], rfl⟩, ⟨[1], [1/2], rfl⟩, rfl, rfl, ?_⟩
    apply QTensor.rel2_const_left
    intro z hz
    rcases List.mem_singleton.mp hz with rfl
    show (-1 : ℚ) ≤ 1/2
    norm_num
  · refine ⟨⟨[1], [1/2], rfl⟩, ⟨[], [1], rfl⟩, rfl, rfl, ?_⟩
    apply QTensor.rel2_const_right
    intro z hz
    rcases List.mem_singleton.mp hz with rfl
    show (1/2 : ℚ) ≤ 1
    norm_num

theorem lirpaAtWitness : Formula.holds σQpos seqLirpa.post :=
  lirpaValid σQpos σQpos_admissible lirpaBoxSat

#print axioms reluNNValid
#print axioms reluAboveValid
#print axioms reluPosAtWitness
#print axioms reluNegAtWitness
#print axioms lirpaAtWitness

theorem layerValid : seqLayer.semanticallyValid HL :=
  check_sound pfLayer rfl

def σL : HL.Valuation := fun w _ h =>
  match w, h with
  | 0, h => (Option.some.inj h) ▸ (⟨[qe 2], rfl⟩ :
      TensorValue ⟨[], Dtype.Q⟩)
  | 1, h => (Option.some.inj h) ▸ (⟨[qe (-3)], rfl⟩ :
      TensorValue ⟨[], Dtype.Q⟩)
  | 2, h => (Option.some.inj h) ▸ (⟨[qe 2], rfl⟩ :
      TensorValue ⟨[], Dtype.Q⟩)
  | 3, h => (Option.some.inj h) ▸ (⟨[qe 0], rfl⟩ :
      TensorValue ⟨[], Dtype.Q⟩)
  | 4, h => (Option.some.inj h) ▸ (⟨[qe 2, qe 0], rfl⟩ :
      TensorValue ⟨[2], Dtype.Q⟩)
  | (_ + 5), h => nomatch h

theorem σL_admissible : σL.Admissible := by
  intro app happ
  simp only [HL, List.mem_cons, List.not_mem_nil, or_false] at happ
  rcases happ with rfl | rfl | rfl
  ·
    intro i
    have hi0 : i.val = 0 := by
      have h1 : i.val < 1 := i.isLt
      omega
    rw [hi0]
    exact ⟨2, 2, rfl, rfl, Or.inr ⟨by norm_num, rfl⟩⟩
  ·
    intro i
    have hi0 : i.val = 0 := by
      have h1 : i.val < 1 := i.isLt
      omega
    rw [hi0]
    exact ⟨-3, 0, rfl, rfl, Or.inl ⟨by norm_num, rfl⟩⟩
  ·
    intro i j
    have hj0 : j.val = 0 := by
      have h1 : j.val < 1 := j.isLt
      omega
    have hi01 : i.val = 0 ∨ i.val = 1 := by
      have h2 : i.val < 2 := i.isLt
      omega
    have hjeq : j = ⟨0, by decide⟩ := Fin.ext hj0
    subst hjeq
    rcases hi01 with hi | hi
    · have hieq : i = ⟨0, by decide⟩ := Fin.ext hi
      subst hieq
      rfl
    · have hieq : i = ⟨1, by decide⟩ := Fin.ext hi
      subst hieq
      rfl

theorem layerAtWitness : Formula.holds σL seqLayer.post :=
  layerValid σL σL_admissible trivial

#print axioms layerValid
#print axioms layerAtWitness

end SoundnessDemo
end PPLC
