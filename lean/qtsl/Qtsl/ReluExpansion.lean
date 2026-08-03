import Qtsl.Soundness
import Qtsl.Decide

/-!
# Expansion warrant for the packaged ReLU primitive

Discharges the three packaged-primitive obligations for `PrimApp.relu`
at its canonical single-entry rational instance: a definitional
expansion into core primitives, a typing rule derivable from the
expansion's, and a derived semantic fact proven from the expansion's —
never axiomatized.
-/

namespace PPLC
namespace ReluExpansion

def sigmaPM : SimpC where
  nVertices := 3
  ambDim := 1
  coord := fun v _ => if v = 0 then 0 else if v = 1 then 1 else -1
  simplices := [fun v => v == 0, fun v => v == 1, fun v => v == 2,
                fun v => v == 0 || v == 1, fun v => v == 0 || v == 2]
  cells := [(fun v => v == 0 || v == 1, fun v => v == 1),
            (fun v => v == 0 || v == 2, fun v => v == 2)]
  nonempty := by decide
  closure := by decide
  conformity := by decide
  distinctVerts := by decide +kernel
  cellsWF := by decide

def cNeg : Fin sigmaPM.cells.length := ⟨0, by decide⟩

def cPos : Fin sigmaPM.cells.length := ⟨1, by decide⟩

def j0 : Fin sigmaPM.ambDim := ⟨0, by decide⟩

private def v0 : Fin sigmaPM.nVertices := ⟨0, by decide⟩
private def v1 : Fin sigmaPM.nVertices := ⟨1, by decide⟩
private def v2 : Fin sigmaPM.nVertices := ⟨2, by decide⟩

private theorem coordSum {lam : Fin sigmaPM.nVertices → ℝ}
    {x : Fin sigmaPM.ambDim → ℚ}
    (hcoord : ∀ j : Fin sigmaPM.ambDim,
      finSum sigmaPM.nVertices
        (fun v => lam v * (sigmaPM.coord v j : ℝ)) = (x j : ℝ)) :
    lam v1 - lam v2 = (x j0 : ℝ) := by
  have hc : lam v0 * ((0 : ℚ) : ℝ)
      + (lam v1 * ((1 : ℚ) : ℝ) + (lam v2 * ((-1 : ℚ) : ℝ) + 0))
      = (x j0 : ℝ) := hcoord j0
  push_cast at hc
  linarith

theorem maskRegion_cNeg_iff (x : Fin sigmaPM.ambDim → ℚ) :
    MaskRegion sigmaPM (sigmaPM.cells.get cNeg).1 (sigmaPM.cells.get cNeg).2 x
      ↔ x j0 ≤ 0 := by
  constructor
  · rintro ⟨lam, hsupp, hsum, hcoord, hext, hcore⟩
    have h2 : lam v2 = 0 := hsupp v2 (by decide)
    have hx := coordSum hcoord
    have h1 : lam v1 ≤ 0 := hext v1 (by decide)
    have : (x j0 : ℝ) ≤ 0 := by rw [← hx, h2]; linarith
    exact_mod_cast this
  · intro hx
    refine maskRegion_pair_intro (a := v0) (b := v1) (V₀ := 0) (V₁ := 1)
      (by decide) (by decide) (by decide) (by norm_num) (by decide) j0
      ?_ ?_ ?_ ?_
    · intro h; exact absurd h (by decide)
    · intro _
      have : (0 : ℚ) ≤ 1 - x j0 := by linarith
      simpa using this
    · intro _
      simpa using hx
    · intro h; exact absurd h (by decide)

theorem maskRegion_cPos_iff (x : Fin sigmaPM.ambDim → ℚ) :
    MaskRegion sigmaPM (sigmaPM.cells.get cPos).1 (sigmaPM.cells.get cPos).2 x
      ↔ 0 ≤ x j0 := by
  constructor
  · rintro ⟨lam, hsupp, hsum, hcoord, hext, hcore⟩
    have h1 : lam v1 = 0 := hsupp v1 (by decide)
    have hx := coordSum hcoord
    have h2 : lam v2 ≤ 0 := hext v2 (by decide)
    have : (0 : ℝ) ≤ (x j0 : ℝ) := by rw [← hx, h1]; linarith
    exact_mod_cast this
  · intro hx
    refine maskRegion_pair_intro (a := v0) (b := v2) (V₀ := 0) (V₁ := -1)
      (by decide) (by decide) (by decide) (by norm_num) (by decide) j0
      ?_ ?_ ?_ ?_
    · intro h; exact absurd h (by decide)
    · intro _
      have h1 : ((-1 : ℚ) - x j0) / ((-1) - 0) = 1 + x j0 := by ring
      rw [h1]
      linarith
    · intro _
      have h1 : (x j0 - 0) / ((-1 : ℚ) - 0) = -(x j0) := by ring
      rw [h1]
      linarith
    · intro h; exact absurd h (by decide)

theorem maskRegionStrict_cNeg_lt {x : Fin sigmaPM.ambDim → ℚ}
    (h : MaskRegionStrict sigmaPM
      (sigmaPM.cells.get cNeg).1 (sigmaPM.cells.get cNeg).2 x) :
    x j0 < 0 := by
  obtain ⟨lam, hsupp, hsum, hcoord, hext, hcore⟩ := h
  have h2 : lam v2 = 0 := hsupp v2 (by decide)
  have hx := coordSum hcoord
  have h1 : lam v1 < 0 := hext v1 (by decide)
  have : (x j0 : ℝ) < 0 := by rw [← hx, h2]; linarith
  exact_mod_cast this

theorem maskRegionStrict_cPos_lt {x : Fin sigmaPM.ambDim → ℚ}
    (h : MaskRegionStrict sigmaPM
      (sigmaPM.cells.get cPos).1 (sigmaPM.cells.get cPos).2 x) :
    0 < x j0 := by
  obtain ⟨lam, hsupp, hsum, hcoord, hext, hcore⟩ := h
  have h1 : lam v1 = 0 := hsupp v1 (by decide)
  have hx := coordSum hcoord
  have h2 : lam v2 < 0 := hext v2 (by decide)
  have : (0 : ℝ) < (x j0 : ℝ) := by rw [← hx, h1]; linarith
  exact_mod_cast this

theorem sigmaPM_disjoint : sigmaPM.CellIntDisjoint := by
  intro i k hik x hstrict hreg
  match i, k with
  | ⟨0, _⟩, ⟨0, _⟩ => exact hik rfl
  | ⟨1, _⟩, ⟨1, _⟩ => exact hik rfl
  | ⟨0, _⟩, ⟨1, _⟩ =>
    have h1 := maskRegionStrict_cNeg_lt (x := x) hstrict
    have h2 := (maskRegion_cPos_iff x).mp hreg
    exact absurd h2 (by linarith)
  | ⟨1, _⟩, ⟨0, _⟩ =>
    have h1 := maskRegionStrict_cPos_lt (x := x) hstrict
    have h2 := (maskRegion_cNeg_iff x).mp hreg
    exact absurd h2 (by linarith)

def pat0 : ContractPattern [0, 0] 0 where
  nIndices := 0
  indexExtent := Fin.elim0
  inputBinding := fun i => match i with
    | ⟨0, _⟩ => fun a => a.elim0
    | ⟨1, _⟩ => fun a => a.elim0
  outputBinding := Fin.elim0

def expTy : Wire → Option TensorType := fun w =>
  if w = 0 then some ⟨[1], Dtype.Q⟩
  else if w = 1 then some ⟨[1], Dtype.Q⟩
  else if w = 2 then some ⟨[1], Dtype.Q⟩
  else if w = 3 then some ⟨[], Dtype.B⟩
  else if w = 4 then some ⟨[], Dtype.B⟩
  else if w = 5 then some ⟨[], Dtype.Q⟩
  else if w = 6 then some ⟨[], Dtype.Q⟩
  else if w = 7 then some ⟨[], Dtype.Q⟩
  else if w = 8 then some ⟨[1], Dtype.Q⟩
  else none

def reluExpH : Hypernet where
  wireType := expTy
  applications :=
    [.copy 2 0 [1, 2],
     .cell sigmaPM 2 [3, 4],
     .cast Dtype.B Dtype.Q .exact [] 4 5,
     .reshape [] 1 6,
     .contract Dtype.Q .exact [6, 5] 7 [0, 0] 0 pat0,
     .reshape [1] 7 8]
  linearity := by decide
  acyclic := by decide
  typeConsistent := by decide +kernel

theorem reluExpansion_typing :
    reluExpH.wireType 0 = some ⟨[1], Dtype.Q⟩ ∧
    reluExpH.wireType 8 = some ⟨[1], Dtype.Q⟩ ∧
    (PrimApp.relu [1] 0 8).TypeConsistent reluExpH.wireType :=
  ⟨rfl, rfl, ⟨[1], Dtype.Q⟩, rfl, rfl, rfl⟩

def qelem (q : ℚ) : Dtype.Q.carrier :=
  ⟨.fin q, ⟨trivial, fun h => nomatch h⟩⟩

def belem (b : Bool) : Dtype.B.carrier :=
  ⟨.fin (if b then 1 else 0), by
    constructor
    · cases b
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro _
      cases b <;> norm_num⟩

def qv1 (q : ℚ) : TensorValue ⟨[1], Dtype.Q⟩ := ⟨[qelem q], rfl⟩

def qv0 (q : ℚ) : TensorValue ⟨[], Dtype.Q⟩ := ⟨[qelem q], rfl⟩

def bv (b : Bool) : TensorValue ⟨[], Dtype.B⟩ := ⟨[belem b], rfl⟩

def σneg (p : ℚ) : reluExpH.Valuation := fun w _ h =>
  match w, h with
  | 0, h => (Option.some.inj h) ▸ qv1 p
  | 1, h => (Option.some.inj h) ▸ qv1 p
  | 2, h => (Option.some.inj h) ▸ qv1 p
  | 3, h => (Option.some.inj h) ▸ bv true
  | 4, h => (Option.some.inj h) ▸ bv false
  | 5, h => (Option.some.inj h) ▸ qv0 0
  | 6, h => (Option.some.inj h) ▸ qv0 p
  | 7, h => (Option.some.inj h) ▸ qv0 0
  | 8, h => (Option.some.inj h) ▸ qv1 0
  | (_ + 9), h => nomatch h

def σpos (p : ℚ) : reluExpH.Valuation := fun w _ h =>
  match w, h with
  | 0, h => (Option.some.inj h) ▸ qv1 p
  | 1, h => (Option.some.inj h) ▸ qv1 p
  | 2, h => (Option.some.inj h) ▸ qv1 p
  | 3, h => (Option.some.inj h) ▸ bv false
  | 4, h => (Option.some.inj h) ▸ bv true
  | 5, h => (Option.some.inj h) ▸ qv0 1
  | 6, h => (Option.some.inj h) ▸ qv0 p
  | 7, h => (Option.some.inj h) ▸ qv0 p
  | 8, h => (Option.some.inj h) ▸ qv1 p
  | (_ + 9), h => nomatch h

private theorem fin1_eq (j : Fin sigmaPM.ambDim) : j = j0 := by
  apply Fin.ext
  show j.val = 0
  have h1 : j.val < 1 := j.isLt
  omega

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

private theorem roundOk_finQ (q : ℚ) :
    Dtype.Q.RoundOkE .exact (.fin q) (.fin q) :=
  ⟨rfl, trivial, fun h => nomatch h⟩

theorem σneg_admissible {p : ℚ} (hp : p ≤ 0) : (σneg p).Admissible := by
  intro app happ
  simp only [reluExpH, List.mem_cons, List.not_mem_nil, or_false] at happ
  rcases happ with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    intro o ho i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> rfl
  ·
    refine ⟨sigmaPM_disjoint, fun _ => p, ?_, cNeg, ?_, ?_⟩
    · intro j
      rw [fin1_eq j]
      rfl
    · exact (maskRegion_cNeg_iff _).mpr hp
    · intro j
      match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
  ·
    intro i
    have hi0 : i.val = 0 := by
      have h1 : i.val < 1 := i.isLt
      omega
    rw [hi0]
    exact ⟨.fin 0, .fin 0, rfl, rfl, roundOk_finQ 0⟩
  ·
    intro i
    rfl
  ·
    intro ν₀ hν₀
    have hν : ν₀ = [] := List.mem_singleton.mp hν₀
    subst hν
    refine ⟨.fin 0, .fin (0 + (1 * p) * 0), rfl, rfl, ?_⟩
    have : (0 : ℚ) + (1 * p) * 0 = 0 := by ring
    rw [this]
    exact roundOk_finQ 0
  ·
    intro i
    rfl

theorem σpos_admissible {p : ℚ} (hp : 0 ≤ p) : (σpos p).Admissible := by
  intro app happ
  simp only [reluExpH, List.mem_cons, List.not_mem_nil, or_false] at happ
  rcases happ with rfl | rfl | rfl | rfl | rfl | rfl
  · intro o ho i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> rfl
  · refine ⟨sigmaPM_disjoint, fun _ => p, ?_, cPos, ?_, ?_⟩
    · intro j
      rw [fin1_eq j]
      rfl
    · exact (maskRegion_cPos_iff _).mpr hp
    · intro j
      match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
  · intro i
    have hi0 : i.val = 0 := by
      have h1 : i.val < 1 := i.isLt
      omega
    rw [hi0]
    exact ⟨.fin 1, .fin 1, rfl, rfl, roundOk_finQ 1⟩
  · intro i
    rfl
  · intro ν₀ hν₀
    have hν : ν₀ = [] := List.mem_singleton.mp hν₀
    subst hν
    refine ⟨.fin p, .fin (0 + (1 * p) * 1), rfl, rfl, ?_⟩
    have : (0 : ℚ) + (1 * p) * 1 = p := by ring
    rw [this]
    exact roundOk_finQ p
  · intro i
    rfl

def twoCase (p y : ℚ) : Prop := (p ≤ 0 ∧ y = 0) ∨ (0 ≤ p ∧ y = p)

theorem relu_expansion_complete {p y : ℚ} (h : twoCase p y) :
    ∃ σ : reluExpH.Valuation, σ.Admissible ∧
      σ.entryFlat 0 0 = some (.fin p) ∧
      σ.entryFlat 8 0 = some (.fin y) := by
  rcases h with ⟨hp, hy⟩ | ⟨hp, hy⟩
  · exact ⟨σneg p, σneg_admissible hp, rfl, by rw [hy]; exact rfl⟩
  · exact ⟨σpos p, σpos_admissible hp, rfl, by rw [hy]; exact rfl⟩

theorem relu_expansion_sound {p y : ℚ} (σ : reluExpH.Valuation)
    (hadm : σ.Admissible)
    (hp : σ.entryFlat 0 0 = some (.fin p))
    (hy : σ.entryFlat 8 0 = some (.fin y)) :
    twoCase p y := by

  have hcopy := hadm _ (show PrimApp.copy 2 0 [1, 2] ∈ reluExpH.applications
    from List.Mem.head _)
  have hcell := hadm _ (show PrimApp.cell sigmaPM 2 [3, 4] ∈ reluExpH.applications
    from List.Mem.tail _ (List.Mem.head _))
  have hcast := hadm _ (show PrimApp.cast Dtype.B Dtype.Q .exact [] 4 5
      ∈ reluExpH.applications
    from List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hresh1 := hadm _ (show PrimApp.reshape [] 1 6 ∈ reluExpH.applications
    from List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hcontract := hadm _
    (show PrimApp.contract Dtype.Q .exact [6, 5] 7 [0, 0] 0 pat0
        ∈ reluExpH.applications
    from List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _)))))
  have hresh2 := hadm _ (show PrimApp.reshape [1] 7 8 ∈ reluExpH.applications
    from List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))

  have h1read : σ.entryFlat 1 0 = some (.fin p) := by
    rw [hcopy 1 (List.Mem.head _) 0]
    exact hp
  have h2read : σ.entryFlat 2 0 = some (.fin p) := by
    rw [hcopy 2 (List.Mem.tail _ (List.Mem.head _)) 0]
    exact hp

  obtain ⟨-, x, hx, k, hkreg, honehot⟩ := hcell

  have hxp : x j0 = p := by
    have hr : σ.entryFlat 2 0 = some (.fin (x j0)) := by
      rw [← entryAt_eq_entryFlat σ (show reluExpH.wireType 2
        = some ⟨[1], Dtype.Q⟩ from rfl)
        (show Shape.flatten ([1] : Shape) [(j0 : Fin sigmaPM.ambDim).val]
          = some 0 from rfl)]
      exact hx j0
    exact ERat.fin.inj (Option.some.inj (hr.symm.trans h2read))

  have hg : σ.entryFlat 4 0 = some (.fin (if (1 : Fin 2).val = k.val
      then 1 else 0)) := honehot 1

  obtain ⟨eIn, eOut, h4, h5, hro⟩ := hcast ⟨0, by decide⟩
  have heIn : eIn = .fin (if (1 : Fin 2).val = k.val then 1 else 0) :=
    Option.some.inj (h4.symm.trans hg)
  subst heIn
  obtain ⟨heOut, -⟩ := hro
  subst heOut

  have h6read : σ.entryFlat 6 0 = some (.fin p) := by
    rw [hresh1 0]
    exact h1read

  have hcon := hcontract [] (List.mem_singleton.mpr rfl)
  obtain ⟨eOut7, eExact, h7, hex, hro7⟩ := hcon

  have h6at : σ.entryAt (([6, 5] : List Wire).getD ((⟨0, by decide⟩ :
      Fin ([0, 0] : List Nat).length)).val 0)
      (pat0.inCoords [] ⟨0, by decide⟩) = some (.fin p) := by
    rw [show (([6, 5] : List Wire).getD ((⟨0, by decide⟩ :
      Fin ([0, 0] : List Nat).length)).val 0) = 6 from rfl]
    rw [entryAt_eq_entryFlat σ (show reluExpH.wireType 6
      = some ⟨[], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([] : Shape) (pat0.inCoords [] ⟨0, by decide⟩)
        = some 0 from rfl)]
    exact h6read
  have h5at : σ.entryAt (([6, 5] : List Wire).getD ((⟨1, by decide⟩ :
      Fin ([0, 0] : List Nat).length)).val 0)
      (pat0.inCoords [] ⟨1, by decide⟩)
      = some (.fin (if (1 : Fin 2).val = k.val then 1 else 0)) := by
    rw [show (([6, 5] : List Wire).getD ((⟨1, by decide⟩ :
      Fin ([0, 0] : List Nat).length)).val 0) = 5 from rfl]
    rw [entryAt_eq_entryFlat σ (show reluExpH.wireType 5
      = some ⟨[], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([] : Shape) (pat0.inCoords [] ⟨1, by decide⟩)
        = some 0 from rfl)]
    exact h5
  have hexval : contractExact σ [6, 5] pat0 (pat0.outCoords []) =
      some (.fin ((0 : ℚ) + (1 : ℚ) * p *
        (if (1 : Fin 2).val = k.val then 1 else 0))) := by
    unfold contractExact
    rw [show ((Shape.positions pat0.idxShape).filter
      (fun ν => decide (pat0.outCoords ν = pat0.outCoords [])))
      = [[]] from rfl]
    rw [show (List.finRange ([0, 0] : List Nat).length)
      = [⟨0, by decide⟩, ⟨1, by decide⟩] from rfl]
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
      Option.pure_def]
    rw [h6at, h5at]
    rfl
  rw [hexval] at hex
  have heExact : eExact = .fin ((0 : ℚ) + (1 : ℚ) * p *
      (if (1 : Fin 2).val = k.val then 1 else 0)) :=
    (Option.some.inj hex).symm
  subst heExact
  obtain ⟨heOut7, -⟩ := hro7
  subst heOut7

  have h8read : σ.entryFlat 8 0 = some (.fin ((0 : ℚ) + (1 : ℚ) * p *
      (if (1 : Fin 2).val = k.val then 1 else 0))) := by
    rw [hresh2 0]
    rw [entryAt_eq_entryFlat σ (show reluExpH.wireType 7
      = some ⟨[], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([] : Shape) (pat0.outCoords [])
        = some 0 from rfl)] at h7
    exact h7
  have hyv : y = (0 : ℚ) + (1 : ℚ) * p *
      (if (1 : Fin 2).val = k.val then 1 else 0) :=
    ERat.fin.inj (Option.some.inj (hy.symm.trans h8read))

  have hkval : k.val = 0 ∨ k.val = 1 := by
    have h2 : k.val < 2 := k.isLt
    omega
  rcases hkval with hkv | hkv
  ·
    have hkeq : k = cNeg := Fin.ext hkv
    subst hkeq
    left
    have hple : x j0 ≤ 0 := (maskRegion_cNeg_iff x).mp hkreg
    refine ⟨by rw [← hxp]; exact hple, ?_⟩
    have hne : ((1 : Fin 2)).val ≠ cNeg.val := by decide
    rw [hyv, if_neg hne]
    ring
  ·
    have hkeq : k = cPos := Fin.ext hkv
    subst hkeq
    right
    have hpge : 0 ≤ x j0 := (maskRegion_cPos_iff x).mp hkreg
    refine ⟨by rw [← hxp]; exact hpge, ?_⟩
    have heq : ((1 : Fin 2)).val = cPos.val := by decide
    rw [hyv, if_pos heq]
    ring

theorem relu_projection (p y : ℚ) :
    (∃ σ : reluExpH.Valuation, σ.Admissible ∧
        σ.entryFlat 0 0 = some (.fin p) ∧
        σ.entryFlat 8 0 = some (.fin y)) ↔
    ((p ≤ 0 ∧ y = 0) ∨ (0 ≤ p ∧ y = p)) := by
  constructor
  · rintro ⟨σ, hadm, hp, hy⟩
    exact relu_expansion_sound σ hadm hp hy
  · exact relu_expansion_complete

theorem relu_semOk_singleton_iff {H : Hypernet} (σ : H.Valuation)
    {shape : Shape} {input output : Wire}
    (hts : Shape.totalSize shape = 1) :
    PrimApp.SemOk σ (.relu shape input output) ↔
      ∃ p y : ℚ, σ.entryFlat input 0 = some (.fin p) ∧
        σ.entryFlat output 0 = some (.fin y) ∧
        ((p ≤ 0 ∧ y = 0) ∨ (0 ≤ p ∧ y = p)) := by
  constructor
  · intro hsem
    exact hsem ⟨0, by omega⟩
  · intro h i
    have hi : i.val = 0 := by
      have h1 : i.val < Shape.totalSize shape := i.isLt
      omega
    rw [hi]
    exact h

theorem relu_spFact_holds {H : Hypernet} {shape : Shape}
    {input output : Wire}
    (happ : PrimApp.relu shape input output ∈ H.applications)
    (σ : H.Valuation) (hadm : σ.Admissible) :
    ((PrimApp.relu shape input output).spFact).holds σ := by
  by_cases hts : Shape.totalSize shape = 1
  · have hlink : reluLinked H input output :=
      reluLinked_iff.mpr ⟨shape, happ, by omega⟩
    obtain ⟨qp, qy, hqp, hqy, hshape, hpos, hlen, hcase⟩ :=
      reluLinked_facts hlink σ hadm
    obtain ⟨τ, hτi, hτo, hτs⟩ :
        ∃ τ, H.wireType input = some τ ∧ H.wireType output = some τ ∧
          τ.shape = shape := H.typeConsistent _ happ
    have hqps : qp.shape = shape := by
      obtain ⟨τ', hτ', hsh⟩ := σ.wireQ_shape hqp
      rw [hτi] at hτ'
      injection hτ' with h'
      rw [hsh, ← h', hτs]
    have hplen1 : qp.entries.length = 1 := by rw [qp.len_eq, hqps, hts]
    have hylen1 : qy.entries.length = 1 := by omega
    show Formula.holds σ (if Shape.totalSize shape = 1 then _ else _)
    rw [if_pos hts]

    rcases hcase 0 hpos with ⟨hple, hy0⟩ | ⟨hpge, hyp⟩
    ·
      left
      constructor
      · exact ⟨qp, ⟨[], [0], rfl⟩, hqp, rfl, QTensor.rel2_const_right
          (fun z hz => by
            obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hz
            have hj0 : j = 0 := by omega
            subst hj0
            rw [← hje, ← List.getD_eq_getElem _ _ hj]
            exact hple)⟩
      · exact ⟨qy, ⟨[], [0], rfl⟩, hqy, rfl, QTensor.rel2_const_right
          (fun z hz => by
            obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hz
            have hj0 : j = 0 := by omega
            subst hj0
            rw [← hje, ← List.getD_eq_getElem _ _ hj]
            exact hy0)⟩
    ·
      right
      constructor
      · exact ⟨qp, ⟨[], [0], rfl⟩, hqp, rfl, QTensor.rel2_const_right
          (fun z hz => by
            obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hz
            have hj0 : j = 0 := by omega
            subst hj0
            rw [← hje, ← List.getD_eq_getElem _ _ hj]
            exact hpge)⟩
      · exact ⟨qy, qp, hqy, hqp, QTensor.rel2_of_getD hshape.symm
          (fun j hj => by
            have hj0 : j = 0 := by omega
            subst hj0
            exact hyp)⟩
  · show Formula.holds σ (if Shape.totalSize shape = 1 then _ else _)
    rw [if_neg hts]
    trivial

#print axioms relu_projection
#print axioms sigmaPM_disjoint
#print axioms relu_semOk_singleton_iff
#print axioms relu_spFact_holds

end ReluExpansion
end PPLC
