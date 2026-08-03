import Qtsl.Soundness
import Qtsl.Decide
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Expansion warrant for the packaged partial-derivative primitive

`pderiv shape axis` is the formal partial derivative on dense monomial
coefficient tables — a purely syntactic index shift with coefficient
scaling, `out[β] = (β_axis + 1) · in[β + e_axis]` — hence a linear map
on the coefficient tensor. This module discharges the three
packaged-primitive obligations: definitional expansion into core
primitives, derivable typing rule, and derived semantic fact.
-/

namespace PPLC
namespace PderivExpansion

def qelem (q : ℚ) : Dtype.Q.carrier :=
  ⟨.fin q, ⟨trivial, fun h => nomatch h⟩⟩

def qv3 (a b c : ℚ) : TensorValue ⟨[3], Dtype.Q⟩ :=
  ⟨[qelem a, qelem b, qelem c], rfl⟩

private theorem roundOk_finQ (q : ℚ) :
    Dtype.Q.RoundOkE .exact (.fin q) (.fin q) :=
  ⟨rfl, trivial, fun h => nomatch h⟩

private theorem entryAt_eq_entryFlat {H : Hypernet} (σ : H.Valuation)
    {w : Wire} {τ : TensorType} (hτ : H.wireType w = some τ)
    {c : List ℕ} {n : ℕ} (hfl : Shape.flatten τ.shape c = some n) :
    σ.entryAt w c = σ.entryFlat w n := by
  unfold Hypernet.Valuation.entryAt
  split
  · next h => rw [hτ] at h; cases h
  · next τ' hτ' =>
    have hττ : τ = τ' := by rw [hτ] at hτ'; injection hτ'
    subst hττ
    rw [hfl, Hypernet.Valuation.entryFlat_eq_entryE σ hτ' n]
    rfl

def M3 : TensorValue ⟨[3, 3], Dtype.Q⟩ :=
  ⟨[qelem 0, qelem 1, qelem 0,
    qelem 0, qelem 0, qelem 2,
    qelem 0, qelem 0, qelem 0], rfl⟩

def patD : ContractPattern [2, 1] 1 where
  nIndices := 2
  indexExtent := fun _ => 3
  inputBinding := fun i => match i with
    | ⟨0, _⟩ => fun a => match a with
      | ⟨0, _⟩ => ⟨0, by decide⟩
      | ⟨1, _⟩ => ⟨1, by decide⟩
    | ⟨1, _⟩ => fun _ => ⟨1, by decide⟩
  outputBinding := fun _ => ⟨0, by decide⟩

def expTy : Wire → Option TensorType := fun w =>
  if w = 0 then some ⟨[3], Dtype.Q⟩
  else if w = 1 then some ⟨[3, 3], Dtype.Q⟩
  else if w = 2 then some ⟨[3], Dtype.Q⟩
  else none

def pderivExpH : Hypernet where
  wireType := expTy
  applications :=
    [.const ⟨[3, 3], Dtype.Q⟩ M3 1,
     .contract Dtype.Q .exact [1, 0] 2 [2, 1] 1 patD]
  linearity := by decide
  acyclic := by decide
  typeConsistent := by decide +kernel

theorem pderivExpansion_typing :
    pderivExpH.wireType 0 = some ⟨[3], Dtype.Q⟩ ∧
    pderivExpH.wireType 2 = some ⟨[3], Dtype.Q⟩ ∧
    (PrimApp.pderiv [3] 0 0 2).TypeConsistent pderivExpH.wireType :=
  ⟨rfl, rfl, ⟨[3], Dtype.Q⟩, rfl, rfl, rfl⟩

def σd (c₀ c₁ c₂ : ℚ) : pderivExpH.Valuation := fun w _ h =>
  match w, h with
  | 0, h => (Option.some.inj h) ▸ qv3 c₀ c₁ c₂
  | 1, h => (Option.some.inj h) ▸ M3
  | 2, h => (Option.some.inj h) ▸ qv3 c₁ (2 * c₂) 0
  | (_ + 3), h => nomatch h

theorem σd_admissible (c₀ c₁ c₂ : ℚ) : (σd c₀ c₁ c₂).Admissible := by
  intro app happ
  simp only [pderivExpH, List.mem_cons, List.not_mem_nil, or_false] at happ
  rcases happ with rfl | rfl
  ·
    intro i
    rfl
  ·

    intro ν₀ hν₀
    rw [show Shape.positions patD.idxShape
        = [[0,0],[0,1],[0,2],[1,0],[1,1],[1,2],[2,0],[2,1],[2,2]] from by decide]
      at hν₀
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hν₀
    have hmem := hν₀
    have h0 : (0 : ℚ) + (1 * 0) * c₀ + (1 * 1) * c₁ + (1 * 0) * c₂ = c₁ := by ring
    have h1 : (0 : ℚ) + (1 * 0) * c₀ + (1 * 0) * c₁ + (1 * 2) * c₂ = 2 * c₂ := by ring
    have h2 : (0 : ℚ) + (1 * 0) * c₀ + (1 * 0) * c₁ + (1 * 0) * c₂ = 0 := by ring
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | (refine ⟨.fin c₁,
          .fin ((0 : ℚ) + (1 * 0) * c₀ + (1 * 1) * c₁ + (1 * 0) * c₂), rfl, rfl, ?_⟩
         rw [h0]; exact roundOk_finQ c₁)
      | (refine ⟨.fin (2 * c₂),
          .fin ((0 : ℚ) + (1 * 0) * c₀ + (1 * 0) * c₁ + (1 * 2) * c₂), rfl, rfl, ?_⟩
         rw [h1]; exact roundOk_finQ (2 * c₂))
      | (refine ⟨.fin 0,
          .fin ((0 : ℚ) + (1 * 0) * c₀ + (1 * 0) * c₁ + (1 * 0) * c₂), rfl, rfl, ?_⟩
         rw [h2]; exact roundOk_finQ 0)

def derivRel (c₀ c₁ c₂ y₀ y₁ y₂ : ℚ) : Prop :=
  y₀ = c₁ ∧ y₁ = 2 * c₂ ∧ y₂ = 0

theorem pderiv_expansion_complete {c₀ c₁ c₂ y₀ y₁ y₂ : ℚ}
    (h : derivRel c₀ c₁ c₂ y₀ y₁ y₂) :
    ∃ σ : pderivExpH.Valuation, σ.Admissible ∧
      σ.entryFlat 0 0 = some (.fin c₀) ∧
      σ.entryFlat 0 1 = some (.fin c₁) ∧
      σ.entryFlat 0 2 = some (.fin c₂) ∧
      σ.entryFlat 2 0 = some (.fin y₀) ∧
      σ.entryFlat 2 1 = some (.fin y₁) ∧
      σ.entryFlat 2 2 = some (.fin y₂) := by
  obtain ⟨h₀, h₁, h₂⟩ := h
  exact ⟨σd c₀ c₁ c₂, σd_admissible c₀ c₁ c₂, rfl, rfl, rfl,
    by rw [h₀]; rfl, by rw [h₁]; rfl, by rw [h₂]; rfl⟩

theorem pderiv_expansion_sound {c₀ c₁ c₂ y₀ y₁ y₂ : ℚ}
    (σ : pderivExpH.Valuation) (hadm : σ.Admissible)
    (hc0 : σ.entryFlat 0 0 = some (.fin c₀))
    (hc1 : σ.entryFlat 0 1 = some (.fin c₁))
    (hc2 : σ.entryFlat 0 2 = some (.fin c₂))
    (hy0 : σ.entryFlat 2 0 = some (.fin y₀))
    (hy1 : σ.entryFlat 2 1 = some (.fin y₁))
    (hy2 : σ.entryFlat 2 2 = some (.fin y₂)) :
    derivRel c₀ c₁ c₂ y₀ y₁ y₂ := by
  have hconst := hadm _ (show PrimApp.const ⟨[3, 3], Dtype.Q⟩ M3 1
      ∈ pderivExpH.applications from List.Mem.head _)
  have hcontract := hadm _
    (show PrimApp.contract Dtype.Q .exact [1, 0] 2 [2, 1] 1 patD
        ∈ pderivExpH.applications
      from List.Mem.tail _ (List.Mem.head _))

  have hM : ∀ i : ℕ, σ.entryFlat 1 i = M3.entryE i := hconst
  have hM00 : σ.entryAt 1 [0, 0] = some (.fin 0) := by
    rw [entryAt_eq_entryFlat σ (show pderivExpH.wireType 1
      = some ⟨[3, 3], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([3, 3] : Shape) [0, 0] = some 0 by decide),
      hM]
    rfl
  have hM01 : σ.entryAt 1 [0, 1] = some (.fin 1) := by
    rw [entryAt_eq_entryFlat σ (show pderivExpH.wireType 1
      = some ⟨[3, 3], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([3, 3] : Shape) [0, 1] = some 1 by decide),
      hM]
    rfl
  have hM02 : σ.entryAt 1 [0, 2] = some (.fin 0) := by
    rw [entryAt_eq_entryFlat σ (show pderivExpH.wireType 1
      = some ⟨[3, 3], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([3, 3] : Shape) [0, 2] = some 2 by decide),
      hM]
    rfl
  have hM10 : σ.entryAt 1 [1, 0] = some (.fin 0) := by
    rw [entryAt_eq_entryFlat σ (show pderivExpH.wireType 1
      = some ⟨[3, 3], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([3, 3] : Shape) [1, 0] = some 3 by decide),
      hM]
    rfl
  have hM11 : σ.entryAt 1 [1, 1] = some (.fin 0) := by
    rw [entryAt_eq_entryFlat σ (show pderivExpH.wireType 1
      = some ⟨[3, 3], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([3, 3] : Shape) [1, 1] = some 4 by decide),
      hM]
    rfl
  have hM12 : σ.entryAt 1 [1, 2] = some (.fin 2) := by
    rw [entryAt_eq_entryFlat σ (show pderivExpH.wireType 1
      = some ⟨[3, 3], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([3, 3] : Shape) [1, 2] = some 5 by decide),
      hM]
    rfl
  have hM20 : σ.entryAt 1 [2, 0] = some (.fin 0) := by
    rw [entryAt_eq_entryFlat σ (show pderivExpH.wireType 1
      = some ⟨[3, 3], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([3, 3] : Shape) [2, 0] = some 6 by decide),
      hM]
    rfl
  have hM21 : σ.entryAt 1 [2, 1] = some (.fin 0) := by
    rw [entryAt_eq_entryFlat σ (show pderivExpH.wireType 1
      = some ⟨[3, 3], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([3, 3] : Shape) [2, 1] = some 7 by decide),
      hM]
    rfl
  have hM22 : σ.entryAt 1 [2, 2] = some (.fin 0) := by
    rw [entryAt_eq_entryFlat σ (show pderivExpH.wireType 1
      = some ⟨[3, 3], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([3, 3] : Shape) [2, 2] = some 8 by decide),
      hM]
    rfl

  have hc0At : σ.entryAt 0 [0] = some (.fin c₀) := by
    rw [entryAt_eq_entryFlat σ (show pderivExpH.wireType 0
      = some ⟨[3], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([3] : Shape) [0] = some 0 by decide)]
    exact hc0
  have hc1At : σ.entryAt 0 [1] = some (.fin c₁) := by
    rw [entryAt_eq_entryFlat σ (show pderivExpH.wireType 0
      = some ⟨[3], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([3] : Shape) [1] = some 1 by decide)]
    exact hc1
  have hc2At : σ.entryAt 0 [2] = some (.fin c₂) := by
    rw [entryAt_eq_entryFlat σ (show pderivExpH.wireType 0
      = some ⟨[3], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([3] : Shape) [2] = some 2 by decide)]
    exact hc2

  have hrow0 : y₀ = (0 : ℚ) + (1 * 0) * c₀ + (1 * 1) * c₁ + (1 * 0) * c₂ := by
    obtain ⟨eOut, eExact, hOut, hEx, hro⟩ := hcontract [0, 0] (by decide)
    rw [show patD.outCoords [0, 0] = [0] from rfl] at hOut hEx
    have hexval : contractExact σ [1, 0] patD [0] =
        some (.fin ((0 : ℚ) + (1 * 0) * c₀ + (1 * 1) * c₁ + (1 * 0) * c₂)) := by
      unfold contractExact
      rw [show ((Shape.positions patD.idxShape).filter
          (fun ν => decide (patD.outCoords ν = [0])))
          = [[0, 0], [0, 1], [0, 2]] from rfl]
      rw [show (List.finRange ([2, 1] : List Nat).length)
          = [⟨0, by decide⟩, ⟨1, by decide⟩] from rfl]
      simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
        Option.pure_def,
        show (([1, 0] : List Wire).getD ((⟨0, by decide⟩ :
          Fin ([2, 1] : List Nat).length)).val 0) = 1 from rfl,
        show (([1, 0] : List Wire).getD ((⟨1, by decide⟩ :
          Fin ([2, 1] : List Nat).length)).val 0) = 0 from rfl,
      show patD.inCoords [0, 0] ⟨0, by decide⟩ = [0, 0] from rfl,
      show patD.inCoords [0, 0] ⟨1, by decide⟩ = [0] from rfl,
      show patD.inCoords [0, 1] ⟨0, by decide⟩ = [0, 1] from rfl,
      show patD.inCoords [0, 1] ⟨1, by decide⟩ = [1] from rfl,
      show patD.inCoords [0, 2] ⟨0, by decide⟩ = [0, 2] from rfl,
      show patD.inCoords [0, 2] ⟨1, by decide⟩ = [2] from rfl,
        hM00, hM01, hM02, hc0At, hc1At, hc2At]
      rfl
    rw [hexval] at hEx
    have heExact : eExact = .fin ((0 : ℚ) + (1 * 0) * c₀ + (1 * 1) * c₁
        + (1 * 0) * c₂) := (Option.some.inj hEx).symm
    subst heExact
    obtain ⟨heOut, -⟩ := hro
    subst heOut
    have hyAt : σ.entryAt 2 [0] = some (.fin y₀) := by
      rw [entryAt_eq_entryFlat σ (show pderivExpH.wireType 2
        = some ⟨[3], Dtype.Q⟩ from rfl)
        (show Shape.flatten ([3] : Shape) [0] = some 0 by decide)]
      exact hy0
    exact ERat.fin.inj (Option.some.inj (hyAt.symm.trans hOut))

  have hrow1 : y₁ = (0 : ℚ) + (1 * 0) * c₀ + (1 * 0) * c₁ + (1 * 2) * c₂ := by
    obtain ⟨eOut, eExact, hOut, hEx, hro⟩ := hcontract [1, 0] (by decide)
    rw [show patD.outCoords [1, 0] = [1] from rfl] at hOut hEx
    have hexval : contractExact σ [1, 0] patD [1] =
        some (.fin ((0 : ℚ) + (1 * 0) * c₀ + (1 * 0) * c₁ + (1 * 2) * c₂)) := by
      unfold contractExact
      rw [show ((Shape.positions patD.idxShape).filter
          (fun ν => decide (patD.outCoords ν = [1])))
          = [[1, 0], [1, 1], [1, 2]] from rfl]
      rw [show (List.finRange ([2, 1] : List Nat).length)
          = [⟨0, by decide⟩, ⟨1, by decide⟩] from rfl]
      simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
        Option.pure_def,
        show (([1, 0] : List Wire).getD ((⟨0, by decide⟩ :
          Fin ([2, 1] : List Nat).length)).val 0) = 1 from rfl,
        show (([1, 0] : List Wire).getD ((⟨1, by decide⟩ :
          Fin ([2, 1] : List Nat).length)).val 0) = 0 from rfl,
      show patD.inCoords [1, 0] ⟨0, by decide⟩ = [1, 0] from rfl,
      show patD.inCoords [1, 0] ⟨1, by decide⟩ = [0] from rfl,
      show patD.inCoords [1, 1] ⟨0, by decide⟩ = [1, 1] from rfl,
      show patD.inCoords [1, 1] ⟨1, by decide⟩ = [1] from rfl,
      show patD.inCoords [1, 2] ⟨0, by decide⟩ = [1, 2] from rfl,
      show patD.inCoords [1, 2] ⟨1, by decide⟩ = [2] from rfl,
        hM10, hM11, hM12, hc0At, hc1At, hc2At]
      rfl
    rw [hexval] at hEx
    have heExact : eExact = .fin ((0 : ℚ) + (1 * 0) * c₀ + (1 * 0) * c₁
        + (1 * 2) * c₂) := (Option.some.inj hEx).symm
    subst heExact
    obtain ⟨heOut, -⟩ := hro
    subst heOut
    have hyAt : σ.entryAt 2 [1] = some (.fin y₁) := by
      rw [entryAt_eq_entryFlat σ (show pderivExpH.wireType 2
        = some ⟨[3], Dtype.Q⟩ from rfl)
        (show Shape.flatten ([3] : Shape) [1] = some 1 by decide)]
      exact hy1
    exact ERat.fin.inj (Option.some.inj (hyAt.symm.trans hOut))

  have hrow2 : y₂ = (0 : ℚ) + (1 * 0) * c₀ + (1 * 0) * c₁ + (1 * 0) * c₂ := by
    obtain ⟨eOut, eExact, hOut, hEx, hro⟩ := hcontract [2, 0] (by decide)
    rw [show patD.outCoords [2, 0] = [2] from rfl] at hOut hEx
    have hexval : contractExact σ [1, 0] patD [2] =
        some (.fin ((0 : ℚ) + (1 * 0) * c₀ + (1 * 0) * c₁ + (1 * 0) * c₂)) := by
      unfold contractExact
      rw [show ((Shape.positions patD.idxShape).filter
          (fun ν => decide (patD.outCoords ν = [2])))
          = [[2, 0], [2, 1], [2, 2]] from rfl]
      rw [show (List.finRange ([2, 1] : List Nat).length)
          = [⟨0, by decide⟩, ⟨1, by decide⟩] from rfl]
      simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
        Option.pure_def,
        show (([1, 0] : List Wire).getD ((⟨0, by decide⟩ :
          Fin ([2, 1] : List Nat).length)).val 0) = 1 from rfl,
        show (([1, 0] : List Wire).getD ((⟨1, by decide⟩ :
          Fin ([2, 1] : List Nat).length)).val 0) = 0 from rfl,
      show patD.inCoords [2, 0] ⟨0, by decide⟩ = [2, 0] from rfl,
      show patD.inCoords [2, 0] ⟨1, by decide⟩ = [0] from rfl,
      show patD.inCoords [2, 1] ⟨0, by decide⟩ = [2, 1] from rfl,
      show patD.inCoords [2, 1] ⟨1, by decide⟩ = [1] from rfl,
      show patD.inCoords [2, 2] ⟨0, by decide⟩ = [2, 2] from rfl,
      show patD.inCoords [2, 2] ⟨1, by decide⟩ = [2] from rfl,
        hM20, hM21, hM22, hc0At, hc1At, hc2At]
      rfl
    rw [hexval] at hEx
    have heExact : eExact = .fin ((0 : ℚ) + (1 * 0) * c₀ + (1 * 0) * c₁
        + (1 * 0) * c₂) := (Option.some.inj hEx).symm
    subst heExact
    obtain ⟨heOut, -⟩ := hro
    subst heOut
    have hyAt : σ.entryAt 2 [2] = some (.fin y₂) := by
      rw [entryAt_eq_entryFlat σ (show pderivExpH.wireType 2
        = some ⟨[3], Dtype.Q⟩ from rfl)
        (show Shape.flatten ([3] : Shape) [2] = some 2 by decide)]
      exact hy2
    exact ERat.fin.inj (Option.some.inj (hyAt.symm.trans hOut))
  refine ⟨?_, ?_, ?_⟩
  · rw [hrow0]; ring
  · rw [hrow1]; ring
  · rw [hrow2]; ring

theorem pderiv_projection (c₀ c₁ c₂ y₀ y₁ y₂ : ℚ) :
    (∃ σ : pderivExpH.Valuation, σ.Admissible ∧
        σ.entryFlat 0 0 = some (.fin c₀) ∧
        σ.entryFlat 0 1 = some (.fin c₁) ∧
        σ.entryFlat 0 2 = some (.fin c₂) ∧
        σ.entryFlat 2 0 = some (.fin y₀) ∧
        σ.entryFlat 2 1 = some (.fin y₁) ∧
        σ.entryFlat 2 2 = some (.fin y₂)) ↔
    derivRel c₀ c₁ c₂ y₀ y₁ y₂ := by
  constructor
  · rintro ⟨σ, hadm, hc0, hc1, hc2, hy0, hy1, hy2⟩
    exact pderiv_expansion_sound σ hadm hc0 hc1 hc2 hy0 hy1 hy2
  · exact pderiv_expansion_complete

open Polynomial in

noncomputable def toPoly (a b c : ℚ) : Polynomial ℚ :=
  C a + C b * X + C c * X ^ 2

open Polynomial in

theorem derivRel_iff_derivative (c₀ c₁ c₂ y₀ y₁ y₂ : ℚ) :
    derivRel c₀ c₁ c₂ y₀ y₁ y₂ ↔
      toPoly y₀ y₁ y₂ = derivative (toPoly c₀ c₁ c₂) := by
  constructor
  · rintro ⟨rfl, rfl, rfl⟩
    simp [toPoly, map_ofNat]
    ring
  · intro h
    have h0 := congrArg (fun p => Polynomial.coeff p 0) h
    have h1 := congrArg (fun p => Polynomial.coeff p 1) h
    have h2 := congrArg (fun p => Polynomial.coeff p 2) h
    simp [toPoly, coeff_add, coeff_C, coeff_C_mul, coeff_X_pow,
      coeff_one, derivative_add, derivative_C, derivative_X,
      derivative_C_mul, derivative_X_pow] at h0 h1 h2
    exact ⟨by linarith, by linarith, by linarith⟩

theorem pderiv_semOk_canonical_iff {H : Hypernet} (σ : H.Valuation)
    {input output : Wire} :
    PrimApp.SemOk σ (.pderiv [3] 0 input output) ↔
      ∃ qc qy : QTensor,
        σ.wireQ input = some qc ∧ σ.wireQ output = some qy ∧
        derivRel (qc.entries.getD 0 0) (qc.entries.getD 1 0)
          (qc.entries.getD 2 0) (qy.entries.getD 0 0)
          (qy.entries.getD 1 0) (qy.entries.getD 2 0) := by
  constructor
  · intro hsem
    obtain ⟨qc, qy, hqc, hqy, hrel⟩ := hsem (by decide)
    refine ⟨qc, qy, hqc, hqy, ?_, ?_, ?_⟩
    · have h := (hrel [0] (by decide) 0 (by decide)).1 1 (by decide)
      simpa using h
    · have h := (hrel [1] (by decide) 1 (by decide)).1 2 (by decide)
      have h2 : ((([1] : List ℕ).getD 0 0 : ℚ) + 1) = 2 := by
          norm_num [List.getD]
      rw [h2] at h
      exact h
    · exact (hrel [2] (by decide) 2 (by decide)).2 (by decide)
  · rintro ⟨qc, qy, hqc, hqy, h₀, h₁, h₂⟩
    intro _
    refine ⟨qc, qy, hqc, hqy, ?_⟩
    intro β hβ n hn
    have hpos : Shape.positions ([3] : Shape) = [[0], [1], [2]] := by decide
    rw [hpos] at hβ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hβ
    rcases hβ with rfl | rfl | rfl
    · have hn0 : n = 0 := by
        have : (some 0 : Option ℕ) = some n := by
          rw [← hn]; decide
        exact (Option.some.inj this).symm
      subst hn0
      constructor
      · intro m hm
        have hm1 : m = 1 := by
          have : (some 1 : Option ℕ) = some m := by
            rw [← hm]; decide
          exact (Option.some.inj this).symm
        subst hm1
        simpa using h₀
      · intro hnone
        exact absurd hnone (by decide)
    · have hn1 : n = 1 := by
        have : (some 1 : Option ℕ) = some n := by
          rw [← hn]; decide
        exact (Option.some.inj this).symm
      subst hn1
      constructor
      · intro m hm
        have hm2 : m = 2 := by
          have : (some 2 : Option ℕ) = some m := by
            rw [← hm]; decide
          exact (Option.some.inj this).symm
        subst hm2
        have h2 : ((([1] : List ℕ).getD 0 0 : ℚ) + 1) = 2 := by
          norm_num [List.getD]
        rw [h2]
        exact h₁
      · intro hnone
        exact absurd hnone (by decide)
    · have hn2 : n = 2 := by
        have : (some 2 : Option ℕ) = some n := by
          rw [← hn]; decide
        exact (Option.some.inj this).symm
      subst hn2
      constructor
      · intro m hm
        rw [(by decide : Shape.flatten ([3] : Shape)
          (([2] : List ℕ).set 0 (([2] : List ℕ).getD 0 0 + 1)) = none)] at hm
        simp at hm
      · intro _
        exact h₂

private theorem mem_positions_singleton {n β : ℕ} (h : β < n) :
    [β] ∈ Shape.positions [n] := by
  simp only [Shape.positions, List.mem_flatMap]
  exact ⟨β, List.mem_range.mpr h, by simp [Shape.positions]⟩

private theorem flatten_singleton {n β : ℕ} (h : β < n) :
    Shape.flatten ([n] : Shape) [β] = some β := by
  simp [Shape.flatten, h, Shape.totalSize]

private theorem flatten_singleton_none {n β : ℕ} (h : ¬ β < n) :
    Shape.flatten ([n] : Shape) [β] = none := by
  simp [Shape.flatten, h]

private theorem evalQ_idx_var {H : Hypernet} (σ : H.Valuation) {w : Wire}
    {q : QTensor} (hq : σ.wireQ w = some q) {e i : ℕ}
    (hsh : q.shape = [e]) (hi : i < e) :
    Term.evalQ σ (.idx (.var w) i)
      = some ⟨[], [q.entries.getD i 0], rfl⟩ := by
  obtain ⟨qs, qents, qlen⟩ := q
  simp only at hsh
  subst hsh
  simp only [Term.evalQ, hq]
  show (if i < e then _ else none) = _
  rw [if_pos hi]

private theorem evalQ_mul_const_idx {H : Hypernet} (σ : H.Valuation)
    {w : Wire} {q : QTensor} (hq : σ.wireQ w = some q) {e i : ℕ}
    (hsh : q.shape = [e]) (hi : i < e) (k : ℚ) :
    Term.evalQ σ (.mul (.const k) (.idx (.var w) i))
      = some ⟨[], [k * q.entries.getD i 0], rfl⟩ := by
  obtain ⟨qs, qents, qlen⟩ := q
  simp only at hsh
  subst hsh
  simp only [Term.evalQ, hq]
  show ((if i < e then some (⟨[], [qents.getD i 0], rfl⟩ : QTensor)
      else none).bind fun b =>
        QTensor.map2 (fun x1 x2 => x1 * x2) ⟨[], [k], rfl⟩ b) = _
  rw [if_pos hi]
  rfl

private theorem holds_atom_eq_of_evals {H : Hypernet} (σ : H.Valuation)
    {l r : Term} {a b : ℚ}
    (hl : Term.evalQ σ l = some ⟨[], [a], rfl⟩)
    (hr : Term.evalQ σ r = some ⟨[], [b], rfl⟩) (hab : a = b) :
    Formula.holds σ (.atom .eq l r) := by
  refine ⟨⟨[], [a], rfl⟩, ⟨[], [b], rfl⟩, hl, hr, ?_⟩
  simp [QTensor.rel2, BowTie.holdsQ, hab]

theorem pderiv_spFact_holds {H : Hypernet} {n : ℕ} {input output : Wire}
    (happ : PrimApp.pderiv [n] 0 input output ∈ H.applications)
    (σ : H.Valuation) (hadm : σ.Admissible) :
    ((PrimApp.pderiv [n] 0 input output).spFact).holds σ := by
  have hsem := hadm _ happ
  obtain ⟨qc, qy, hqc, hqy, hrel⟩ := hsem (by simp)
  obtain ⟨τ, hτi, hτo, hτs⟩ :
      ∃ τ, H.wireType input = some τ ∧ H.wireType output = some τ ∧
        τ.shape = [n] := H.typeConsistent _ happ
  have hqcs : qc.shape = [n] := by
    obtain ⟨τ', hτ', hsh⟩ := σ.wireQ_shape hqc
    rw [hτi] at hτ'
    injection hτ' with h'
    rw [hsh, ← h', hτs]
  have hqys : qy.shape = [n] := by
    obtain ⟨τ', hτ', hsh⟩ := σ.wireQ_shape hqy
    rw [hτo] at hτ'
    injection hτ' with h'
    rw [hsh, ← h', hτs]
  show Formula.holds σ (Formula.chainAnd _)
  apply Formula.holds_chainAnd
  intro f hf
  obtain ⟨β, hβmem, rfl⟩ := List.mem_map.mp hf
  rw [List.mem_range] at hβmem
  have hrelβ := hrel [β] (mem_positions_singleton hβmem) β
    (flatten_singleton hβmem)
  have hset : ([β] : List ℕ).set 0 (([β] : List ℕ).getD 0 0 + 1)
      = [β + 1] := rfl
  by_cases hb : β + 1 < n
  · rw [if_pos hb]
    have hm := hrelβ.1 (β + 1) (by rw [hset]; exact flatten_singleton hb)
    refine holds_atom_eq_of_evals σ
      (evalQ_idx_var σ hqy hqys hβmem)
      (evalQ_mul_const_idx σ hqc hqcs hb ((β : ℚ) + 1)) ?_
    simpa using hm
  · rw [if_neg hb]
    have h0 := hrelβ.2 (by rw [hset]; exact flatten_singleton_none hb)
    exact holds_atom_eq_of_evals σ
      (evalQ_idx_var σ hqy hqys hβmem)
      (show Term.evalQ σ (.const 0) = some ⟨[], [(0 : ℚ)], rfl⟩ from rfl) h0

#print axioms pderiv_projection
#print axioms derivRel_iff_derivative
#print axioms pderiv_semOk_canonical_iff
#print axioms pderiv_spFact_holds

end PderivExpansion
end PPLC
