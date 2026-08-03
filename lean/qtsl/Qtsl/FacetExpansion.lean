import Qtsl.Soundness
import Qtsl.Decide

/-!
# Expansion warrant for the packaged facet primitive

`facet shape axis hi` restricts a Bernstein or monomial coefficient
table to a facet of its box: the output is the coefficient slab at
coordinate 0 (or extent − 1) along `axis`; for Bernstein tables the
slab is the restricted polynomial's table (`facet_bernstein`). This
module discharges the three obligations of an admissible packaged
primitive: a definitional expansion into core primitives, a typing rule
derivable from the expansion's, and a derived semantic fact proven —
never axiomatized — from the expansion's.
-/

namespace PPLC
namespace FacetExpansion

def qelem (q : ℚ) : Dtype.Q.carrier :=
  ⟨.fin q, ⟨trivial, fun h => nomatch h⟩⟩

def qv2 (a b : ℚ) : TensorValue ⟨[2], Dtype.Q⟩ :=
  ⟨[qelem a, qelem b], rfl⟩

def qv22 (a b c d : ℚ) : TensorValue ⟨[2, 2], Dtype.Q⟩ :=
  ⟨[qelem a, qelem b, qelem c, qelem d], rfl⟩

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

def eFacet (hi : Bool) : TensorValue ⟨[2], Dtype.Q⟩ :=
  ⟨[qelem (if hi then 0 else 1), qelem (if hi then 1 else 0)], rfl⟩

def patF : ContractPattern [1, 2] 1 where
  nIndices := 2
  indexExtent := fun _ => 2
  inputBinding := fun i => match i with
    | ⟨0, _⟩ => fun _ => ⟨0, by decide⟩
    | ⟨1, _⟩ => fun a => match a with
      | ⟨0, _⟩ => ⟨0, by decide⟩
      | ⟨1, _⟩ => ⟨1, by decide⟩
  outputBinding := fun _ => ⟨1, by decide⟩

def expTy : Wire → Option TensorType := fun w =>
  if w = 0 then some ⟨[2, 2], Dtype.Q⟩
  else if w = 1 then some ⟨[2], Dtype.Q⟩
  else if w = 2 then some ⟨[2], Dtype.Q⟩
  else none

def facetExpH (hi : Bool) : Hypernet where
  wireType := expTy
  applications :=
    [.const ⟨[2], Dtype.Q⟩ (eFacet hi) 1,
     .contract Dtype.Q .exact [1, 0] 2 [1, 2] 1 patF]
  linearity := by cases hi <;> decide
  acyclic := by cases hi <;> decide
  typeConsistent := by cases hi <;> decide +kernel

theorem facetExpansion_typing (hi : Bool) :
    (facetExpH hi).wireType 0 = some ⟨[2, 2], Dtype.Q⟩ ∧
    (facetExpH hi).wireType 2 = some ⟨[2], Dtype.Q⟩ ∧
    (PrimApp.facet [2, 2] 0 hi 0 2).TypeConsistent (facetExpH hi).wireType :=
  ⟨rfl, rfl, ⟨[2, 2], Dtype.Q⟩, rfl, rfl, rfl⟩

def σf (hi : Bool) (c₀₀ c₀₁ c₁₀ c₁₁ : ℚ) : (facetExpH hi).Valuation :=
  fun w _ h =>
    match w, h with
    | 0, h => (Option.some.inj h) ▸ qv22 c₀₀ c₀₁ c₁₀ c₁₁
    | 1, h => (Option.some.inj h) ▸ eFacet hi
    | 2, h => (Option.some.inj h) ▸
        qv2 (if hi then c₁₀ else c₀₀) (if hi then c₁₁ else c₀₁)
    | (_ + 3), h => nomatch h

theorem σf_admissible (hi : Bool) (c₀₀ c₀₁ c₁₀ c₁₁ : ℚ) :
    (σf hi c₀₀ c₀₁ c₁₀ c₁₁).Admissible := by
  intro app happ
  simp only [facetExpH, List.mem_cons, List.not_mem_nil, or_false] at happ
  rcases happ with rfl | rfl
  ·
    intro i
    rfl
  ·
    intro ν₀ hν₀
    rw [show Shape.positions patF.idxShape = [[0,0],[0,1],[1,0],[1,1]]
        from by decide] at hν₀
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hν₀
    have hmem := hν₀
    cases hi
    · have h0 : (0 : ℚ) + (1 * 1) * c₀₀ + (1 * 0) * c₁₀ = c₀₀ := by ring
      have h1 : (0 : ℚ) + (1 * 1) * c₀₁ + (1 * 0) * c₁₁ = c₀₁ := by ring
      rcases hmem with rfl | rfl | rfl | rfl <;>
        first
        | (refine ⟨.fin c₀₀,
            .fin ((0 : ℚ) + (1 * 1) * c₀₀ + (1 * 0) * c₁₀), rfl, rfl, ?_⟩
           rw [h0]; exact roundOk_finQ c₀₀)
        | (refine ⟨.fin c₀₁,
            .fin ((0 : ℚ) + (1 * 1) * c₀₁ + (1 * 0) * c₁₁), rfl, rfl, ?_⟩
           rw [h1]; exact roundOk_finQ c₀₁)
    · have h0 : (0 : ℚ) + (1 * 0) * c₀₀ + (1 * 1) * c₁₀ = c₁₀ := by ring
      have h1 : (0 : ℚ) + (1 * 0) * c₀₁ + (1 * 1) * c₁₁ = c₁₁ := by ring
      rcases hmem with rfl | rfl | rfl | rfl <;>
        first
        | (refine ⟨.fin c₁₀,
            .fin ((0 : ℚ) + (1 * 0) * c₀₀ + (1 * 1) * c₁₀), rfl, rfl, ?_⟩
           rw [h0]; exact roundOk_finQ c₁₀)
        | (refine ⟨.fin c₁₁,
            .fin ((0 : ℚ) + (1 * 0) * c₀₁ + (1 * 1) * c₁₁), rfl, rfl, ?_⟩
           rw [h1]; exact roundOk_finQ c₁₁)

def facetRel (hi : Bool) (c₀₀ c₀₁ c₁₀ c₁₁ y₀ y₁ : ℚ) : Prop :=
  match hi with
  | false => y₀ = c₀₀ ∧ y₁ = c₀₁
  | true => y₀ = c₁₀ ∧ y₁ = c₁₁

theorem facet_expansion_complete {hi : Bool} {c₀₀ c₀₁ c₁₀ c₁₁ y₀ y₁ : ℚ}
    (h : facetRel hi c₀₀ c₀₁ c₁₀ c₁₁ y₀ y₁) :
    ∃ σ : (facetExpH hi).Valuation, σ.Admissible ∧
      σ.entryFlat 0 0 = some (.fin c₀₀) ∧
      σ.entryFlat 0 1 = some (.fin c₀₁) ∧
      σ.entryFlat 0 2 = some (.fin c₁₀) ∧
      σ.entryFlat 0 3 = some (.fin c₁₁) ∧
      σ.entryFlat 2 0 = some (.fin y₀) ∧
      σ.entryFlat 2 1 = some (.fin y₁) := by
  cases hi
  · obtain ⟨h₀, h₁⟩ := h
    exact ⟨σf false c₀₀ c₀₁ c₁₀ c₁₁, σf_admissible false c₀₀ c₀₁ c₁₀ c₁₁,
      rfl, rfl, rfl, rfl, by rw [h₀]; rfl, by rw [h₁]; rfl⟩
  · obtain ⟨h₀, h₁⟩ := h
    exact ⟨σf true c₀₀ c₀₁ c₁₀ c₁₁, σf_admissible true c₀₀ c₀₁ c₁₀ c₁₁,
      rfl, rfl, rfl, rfl, by rw [h₀]; rfl, by rw [h₁]; rfl⟩

private theorem contractExact_slab (hi : Bool)
    (σ : (facetExpH hi).Valuation)
    {j : ℕ} (hj : j < 2) {e₀ e₁ a₀ a₁ : ℚ}
    (hE0 : σ.entryAt 1 [0] = some (.fin e₀))
    (hE1 : σ.entryAt 1 [1] = some (.fin e₁))
    (ha0 : σ.entryAt 0 [0, j] = some (.fin a₀))
    (ha1 : σ.entryAt 0 [1, j] = some (.fin a₁)) :
    contractExact σ [1, 0] patF [j] =
      some (.fin ((0 : ℚ) + (1 * e₀) * a₀ + (1 * e₁) * a₁)) := by
  interval_cases j
  · unfold contractExact
    rw [show ((Shape.positions patF.idxShape).filter
        (fun ν => decide (patF.outCoords ν = [0])))
        = [[0, 0], [1, 0]] from rfl]
    rw [show (List.finRange ([1, 2] : List Nat).length)
        = [⟨0, by decide⟩, ⟨1, by decide⟩] from rfl]
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
      Option.pure_def,
      show (([1, 0] : List Wire).getD ((⟨0, by decide⟩ :
        Fin ([1, 2] : List Nat).length)).val 0) = 1 from rfl,
      show (([1, 0] : List Wire).getD ((⟨1, by decide⟩ :
        Fin ([1, 2] : List Nat).length)).val 0) = 0 from rfl,
        show patF.inCoords [0, 0] ⟨0, by decide⟩ = [0] from rfl,
        show patF.inCoords [0, 0] ⟨1, by decide⟩ = [0, 0] from rfl,
        show patF.inCoords [1, 0] ⟨0, by decide⟩ = [1] from rfl,
        show patF.inCoords [1, 0] ⟨1, by decide⟩ = [1, 0] from rfl,
      hE0, hE1, ha0, ha1]
    rfl
  · unfold contractExact
    rw [show ((Shape.positions patF.idxShape).filter
        (fun ν => decide (patF.outCoords ν = [1])))
        = [[0, 1], [1, 1]] from rfl]
    rw [show (List.finRange ([1, 2] : List Nat).length)
        = [⟨0, by decide⟩, ⟨1, by decide⟩] from rfl]
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
      Option.pure_def,
      show (([1, 0] : List Wire).getD ((⟨0, by decide⟩ :
        Fin ([1, 2] : List Nat).length)).val 0) = 1 from rfl,
      show (([1, 0] : List Wire).getD ((⟨1, by decide⟩ :
        Fin ([1, 2] : List Nat).length)).val 0) = 0 from rfl,
        show patF.inCoords [0, 1] ⟨0, by decide⟩ = [0] from rfl,
        show patF.inCoords [0, 1] ⟨1, by decide⟩ = [0, 1] from rfl,
        show patF.inCoords [1, 1] ⟨0, by decide⟩ = [1] from rfl,
        show patF.inCoords [1, 1] ⟨1, by decide⟩ = [1, 1] from rfl,
      hE0, hE1, ha0, ha1]
    rfl

theorem facet_expansion_sound {hi : Bool} {c₀₀ c₀₁ c₁₀ c₁₁ y₀ y₁ : ℚ}
    (σ : (facetExpH hi).Valuation) (hadm : σ.Admissible)
    (hc00 : σ.entryFlat 0 0 = some (.fin c₀₀))
    (hc01 : σ.entryFlat 0 1 = some (.fin c₀₁))
    (hc10 : σ.entryFlat 0 2 = some (.fin c₁₀))
    (hc11 : σ.entryFlat 0 3 = some (.fin c₁₁))
    (hy0 : σ.entryFlat 2 0 = some (.fin y₀))
    (hy1 : σ.entryFlat 2 1 = some (.fin y₁)) :
    facetRel hi c₀₀ c₀₁ c₁₀ c₁₁ y₀ y₁ := by
  have hconst := hadm _ (show PrimApp.const ⟨[2], Dtype.Q⟩ (eFacet hi) 1
      ∈ (facetExpH hi).applications from List.Mem.head _)
  have hcontract := hadm _
    (show PrimApp.contract Dtype.Q .exact [1, 0] 2 [1, 2] 1 patF
        ∈ (facetExpH hi).applications
      from List.Mem.tail _ (List.Mem.head _))
  have hE : ∀ i : ℕ, σ.entryFlat 1 i = (eFacet hi).entryE i := hconst
  have hE0 : σ.entryAt 1 [0] = some (.fin (if hi then 0 else 1)) := by
    rw [entryAt_eq_entryFlat σ (show (facetExpH hi).wireType 1
      = some ⟨[2], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([2] : Shape) [0] = some 0 from rfl), hE]
    cases hi <;> rfl
  have hE1 : σ.entryAt 1 [1] = some (.fin (if hi then 1 else 0)) := by
    rw [entryAt_eq_entryFlat σ (show (facetExpH hi).wireType 1
      = some ⟨[2], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([2] : Shape) [1] = some 1 from rfl), hE]
    cases hi <;> rfl
  have hcAt : ∀ (a j fl : ℕ) (q : ℚ),
      Shape.flatten ([2, 2] : Shape) [a, j] = some fl →
      σ.entryFlat 0 fl = some (.fin q) →
      σ.entryAt 0 [a, j] = some (.fin q) := by
    intro a j fl q hfl hq
    rw [entryAt_eq_entryFlat σ (show (facetExpH hi).wireType 0
      = some ⟨[2, 2], Dtype.Q⟩ from rfl) hfl]
    exact hq
  have hrow : ∀ (j : ℕ) (hj : j < 2) (yj a₀ a₁ : ℚ),
      σ.entryFlat 2 j = some (.fin yj) →
      σ.entryAt 0 [0, j] = some (.fin a₀) →
      σ.entryAt 0 [1, j] = some (.fin a₁) →
      yj = (0 : ℚ) + (1 * (if hi then (0:ℚ) else 1)) * a₀
        + (1 * (if hi then (1:ℚ) else 0)) * a₁ := by
    intro j hj yj a₀ a₁ hyj ha₀ ha₁
    have hν : ([0, j] : List ℕ) ∈ Shape.positions patF.idxShape := by
      have : Shape.positions patF.idxShape = [[0,0],[0,1],[1,0],[1,1]] := rfl
      rw [this]
      interval_cases j <;> simp
    obtain ⟨eOut, eExact, hOut, hEx, hro⟩ := hcontract [0, j] hν
    have houtc : patF.outCoords [0, j] = [j] := by
      show (List.finRange 1).map _ = [j]
      rfl
    rw [houtc] at hOut hEx
    have hexval := contractExact_slab hi σ hj hE0 hE1 ha₀ ha₁
    rw [hexval] at hEx
    have heExact : eExact = .fin ((0 : ℚ)
        + (1 * (if hi then (0:ℚ) else 1)) * a₀
        + (1 * (if hi then (1:ℚ) else 0)) * a₁) :=
      (Option.some.inj hEx).symm
    subst heExact
    obtain ⟨heOut, -⟩ := hro
    subst heOut
    have hyAt : σ.entryAt 2 [j] = some (.fin yj) := by
      rw [entryAt_eq_entryFlat σ (show (facetExpH hi).wireType 2
        = some ⟨[2], Dtype.Q⟩ from rfl)
        (show Shape.flatten ([2] : Shape) [j] = some j by
          simp [Shape.flatten, hj, Shape.totalSize])]
      exact hyj
    exact ERat.fin.inj (Option.some.inj (hyAt.symm.trans hOut))
  have hr0 := hrow 0 (by omega) y₀ c₀₀ c₁₀ hy0
    (hcAt 0 0 0 c₀₀ rfl hc00) (hcAt 1 0 2 c₁₀ rfl hc10)
  have hr1 := hrow 1 (by omega) y₁ c₀₁ c₁₁ hy1
    (hcAt 0 1 1 c₀₁ rfl hc01) (hcAt 1 1 3 c₁₁ rfl hc11)
  cases hi
  · exact ⟨by rw [hr0]; norm_num, by rw [hr1]; norm_num⟩
  · exact ⟨by rw [hr0]; norm_num, by rw [hr1]; norm_num⟩

theorem facet_projection (hi : Bool) (c₀₀ c₀₁ c₁₀ c₁₁ y₀ y₁ : ℚ) :
    (∃ σ : (facetExpH hi).Valuation, σ.Admissible ∧
        σ.entryFlat 0 0 = some (.fin c₀₀) ∧
        σ.entryFlat 0 1 = some (.fin c₀₁) ∧
        σ.entryFlat 0 2 = some (.fin c₁₀) ∧
        σ.entryFlat 0 3 = some (.fin c₁₁) ∧
        σ.entryFlat 2 0 = some (.fin y₀) ∧
        σ.entryFlat 2 1 = some (.fin y₁)) ↔
    facetRel hi c₀₀ c₀₁ c₁₀ c₁₁ y₀ y₁ := by
  constructor
  · rintro ⟨σ, hadm, hc00, hc01, hc10, hc11, hy0, hy1⟩
    exact facet_expansion_sound σ hadm hc00 hc01 hc10 hc11 hy0 hy1
  · exact facet_expansion_complete

def bern1 (a b t : ℚ) : ℚ := a * (1 - t) + b * t

def bern11 (c₀₀ c₀₁ c₁₀ c₁₁ x t : ℚ) : ℚ :=
  c₀₀ * (1 - x) * (1 - t) + c₀₁ * (1 - x) * t
    + c₁₀ * x * (1 - t) + c₁₁ * x * t

theorem facet_bernstein (hi : Bool) (c₀₀ c₀₁ c₁₀ c₁₁ y₀ y₁ : ℚ) :
    facetRel hi c₀₀ c₀₁ c₁₀ c₁₁ y₀ y₁ ↔
      ∀ t : ℚ, bern1 y₀ y₁ t
        = bern11 c₀₀ c₀₁ c₁₀ c₁₁ (if hi then 1 else 0) t := by
  cases hi
  · constructor
    · rintro ⟨h₀, h₁⟩
      intro t
      rw [h₀, h₁]
      show c₀₀ * (1 - t) + c₀₁ * t
        = c₀₀ * (1 - 0) * (1 - t) + c₀₁ * (1 - 0) * t
          + c₁₀ * 0 * (1 - t) + c₁₁ * 0 * t
      ring
    · intro h
      have h0 := h 0
      have h1 := h 1
      simp only [bern1, bern11] at h0 h1
      norm_num at h0 h1
      exact ⟨by linarith, by linarith⟩
  · constructor
    · rintro ⟨h₀, h₁⟩
      intro t
      rw [h₀, h₁]
      show c₁₀ * (1 - t) + c₁₁ * t
        = c₀₀ * (1 - 1) * (1 - t) + c₀₁ * (1 - 1) * t
          + c₁₀ * 1 * (1 - t) + c₁₁ * 1 * t
      ring
    · intro h
      have h0 := h 0
      have h1 := h 1
      simp only [bern1, bern11] at h0 h1
      norm_num at h0 h1
      exact ⟨by linarith, by linarith⟩

theorem facet_semOk_canonical_iff {H : Hypernet} (σ : H.Valuation)
    {hi : Bool} {input output : Wire} :
    PrimApp.SemOk σ (.facet [2, 2] 0 hi input output) ↔
      ∃ qc qy : QTensor,
        σ.wireQ input = some qc ∧ σ.wireQ output = some qy ∧
        facetRel hi (qc.entries.getD 0 0) (qc.entries.getD 1 0)
          (qc.entries.getD 2 0) (qc.entries.getD 3 0)
          (qy.entries.getD 0 0) (qy.entries.getD 1 0) := by
  cases hi
  · constructor
    · intro hsem
      obtain ⟨qc, qy, hqc, hqy, hrel⟩ := hsem (by decide)
      exact ⟨qc, qy, hqc, hqy,
        hrel [0] (by decide) 0 (by decide) 0 (by decide),
        hrel [1] (by decide) 1 (by decide) 1 (by decide)⟩
    · rintro ⟨qc, qy, hqc, hqy, h₀, h₁⟩
      intro _
      refine ⟨qc, qy, hqc, hqy, ?_⟩
      intro γ hγ n hn m hm
      rw [show Shape.positions (([2, 2] : Shape).eraseIdx 0) = [[0], [1]]
          from by decide] at hγ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
      rcases hγ with rfl | rfl
      · have hn0 : n = 0 := (Option.some.inj
          ((by decide : Shape.flatten (([2, 2] : Shape).eraseIdx 0) [0]
              = some 0).symm.trans hn)).symm
        have hm0 : m = 0 := (Option.some.inj
          ((by decide : Shape.flatten ([2, 2] : Shape)
              (([0] : List ℕ).take 0
                ++ [if (false : Bool) then ([2, 2] : Shape).getD 0 0 - 1 else 0]
                ++ ([0] : List ℕ).drop 0) = some 0).symm.trans hm)).symm
        subst hn0; subst hm0
        exact h₀
      · have hn1 : n = 1 := (Option.some.inj
          ((by decide : Shape.flatten (([2, 2] : Shape).eraseIdx 0) [1]
              = some 1).symm.trans hn)).symm
        have hm1 : m = 1 := (Option.some.inj
          ((by decide : Shape.flatten ([2, 2] : Shape)
              (([1] : List ℕ).take 0
                ++ [if (false : Bool) then ([2, 2] : Shape).getD 0 0 - 1 else 0]
                ++ ([1] : List ℕ).drop 0) = some 1).symm.trans hm)).symm
        subst hn1; subst hm1
        exact h₁
  · constructor
    · intro hsem
      obtain ⟨qc, qy, hqc, hqy, hrel⟩ := hsem (by decide)
      exact ⟨qc, qy, hqc, hqy,
        hrel [0] (by decide) 0 (by decide) 2 (by decide),
        hrel [1] (by decide) 1 (by decide) 3 (by decide)⟩
    · rintro ⟨qc, qy, hqc, hqy, h₀, h₁⟩
      intro _
      refine ⟨qc, qy, hqc, hqy, ?_⟩
      intro γ hγ n hn m hm
      rw [show Shape.positions (([2, 2] : Shape).eraseIdx 0) = [[0], [1]]
          from by decide] at hγ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
      rcases hγ with rfl | rfl
      · have hn0 : n = 0 := (Option.some.inj
          ((by decide : Shape.flatten (([2, 2] : Shape).eraseIdx 0) [0]
              = some 0).symm.trans hn)).symm
        have hm2 : m = 2 := (Option.some.inj
          ((by decide : Shape.flatten ([2, 2] : Shape)
              (([0] : List ℕ).take 0
                ++ [if (true : Bool) then ([2, 2] : Shape).getD 0 0 - 1 else 0]
                ++ ([0] : List ℕ).drop 0) = some 2).symm.trans hm)).symm
        subst hn0; subst hm2
        exact h₀
      · have hn1 : n = 1 := (Option.some.inj
          ((by decide : Shape.flatten (([2, 2] : Shape).eraseIdx 0) [1]
              = some 1).symm.trans hn)).symm
        have hm3 : m = 3 := (Option.some.inj
          ((by decide : Shape.flatten ([2, 2] : Shape)
              (([1] : List ℕ).take 0
                ++ [if (true : Bool) then ([2, 2] : Shape).getD 0 0 - 1 else 0]
                ++ ([1] : List ℕ).drop 0) = some 3).symm.trans hm)).symm
        subst hn1; subst hm3
        exact h₁

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

private theorem evalQ_var_rank0 {H : Hypernet} (σ : H.Valuation) {w : Wire}
    {q : QTensor} (hq : σ.wireQ w = some q) (hsh : q.shape = []) :
    Term.evalQ σ (.var w) = some ⟨[], [q.entries.getD 0 0], rfl⟩ := by
  obtain ⟨qs, qents, qlen⟩ := q
  simp only at hsh
  subst hsh
  show σ.wireQ w = _
  rw [hq]
  match qents, qlen with
  | [a], _ => rfl

theorem facet_spFact_holds {H : Hypernet} {n : ℕ} {hi : Bool}
    {input output : Wire}
    (happ : PrimApp.facet [n] 0 hi input output ∈ H.applications)
    (σ : H.Valuation) (hadm : σ.Admissible) :
    ((PrimApp.facet [n] 0 hi input output).spFact).holds σ := by
  by_cases hn : n = 0
  · subst hn
    have hred : (PrimApp.facet [0] 0 hi input output).spFact = .tt := rfl
    rw [hred]
    trivial
  · have hsem := hadm _ happ
    obtain ⟨qc, qy, hqc, hqy, hrel⟩ := hsem (by simp)
    obtain ⟨τ, hτi, hτs, hτo⟩ :
        ∃ τ, H.wireType input = some τ ∧ τ.shape = [n] ∧
          H.wireType output
            = some ⟨([n] : Shape).eraseIdx 0, τ.dtype⟩ :=
      H.typeConsistent _ happ
    have hqcs : qc.shape = [n] := by
      obtain ⟨τ', hτ', hsh⟩ := σ.wireQ_shape hqc
      rw [hτi] at hτ'
      injection hτ' with h'
      rw [hsh, ← h', hτs]
    have hqys : qy.shape = [] := by
      obtain ⟨τ', hτ', hsh⟩ := σ.wireQ_shape hqy
      rw [hτo] at hτ'
      injection hτ' with h'
      rw [hsh, ← h']
      rfl
    have hcoord : (if hi then n - 1 else 0) < n := by
      cases hi
      · show (0 : ℕ) < n
        omega
      · show n - 1 < n
        omega
    have hm : Shape.flatten ([n] : Shape)
        (([] : List ℕ).take 0
          ++ [if hi then ([n] : Shape).getD 0 0 - 1 else 0]
          ++ ([] : List ℕ).drop 0)
        = some (if hi then n - 1 else 0) := by
      show Shape.flatten ([n] : Shape) [if hi then n - 1 else 0] = _
      simp [Shape.flatten, hcoord, Shape.totalSize]
    have hread := hrel [] (by
        show ([] : List ℕ) ∈ Shape.positions (([n] : Shape).eraseIdx 0)
        simp [Shape.positions]) 0 (by
        show Shape.flatten (([n] : Shape).eraseIdx 0) [] = some 0
        rfl) (if hi then n - 1 else 0) hm
    show Formula.holds σ (if n = 0 then .tt else _)
    rw [if_neg hn]
    refine ⟨⟨[], [qy.entries.getD 0 0], rfl⟩,
      ⟨[], [qc.entries.getD (if hi then n - 1 else 0) 0], rfl⟩,
      evalQ_var_rank0 σ hqy hqys,
      evalQ_idx_var σ hqc hqcs hcoord, ?_⟩
    simp [QTensor.rel2, BowTie.holdsQ]
    simpa [List.getD_eq_getElem?_getD] using hread

#print axioms facet_projection
#print axioms facet_bernstein
#print axioms facet_semOk_canonical_iff
#print axioms facet_spFact_holds

end FacetExpansion
end PPLC
