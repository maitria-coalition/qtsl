import Qtsl.ReluExpansion
import Qtsl.SemOkRename

/-!
# Scalar semantic interface of the core primitives

Wire-parametric characterizations of `PrimApp.SemOk` for the
applications the completion theorem's generation construction emits:
scalar constants, scalar products and pair sums (`contract` at two
fixed patterns), pair stacking, copies, exact Boolean-to-rational
casts, scalar-to-vector reshapes, and the two cell schemas — the σ±
complex read as a free Boolean choice at the origin, and its one-cell
restriction `sigmaNN` read as a nonnegativity guard.

The landed expansion modules prove facts of this genre for two fixed
nets at fixed wires; this module states the same semantic interface
with the wires as variables, against typing hypotheses, in both
directions: what an admissible valuation's reads must satisfy, and
which reads assemble into `SemOk`.  The type-consistency dischargers
(`tcConst` …) are the corresponding wire-parametric forms of the
`TypeConsistent` obligations.
-/

namespace PPLC

open ReluExpansion (pat0 sigmaPM cNeg cPos qelem belem qv0 qv1 bv)

/-! ## Reading typed wires -/

/-- Entries beyond a tensor's extent are absent. -/
theorem TensorValue.entryE_none_of_le {τ : TensorType} (t : TensorValue τ)
    {i : ℕ} (h : τ.shape.totalSize ≤ i) : t.entryE i = none := by
  show (t.val[i]?).map Subtype.val = none
  rw [List.getElem?_eq_none (by rw [t.property]; exact h)]
  rfl

/-- The entry read of an in-range index is the indexed carrier value. -/
theorem TensorValue.entryE_of_getElem {τ : TensorType} (t : TensorValue τ)
    {i : ℕ} (h : i < t.val.length) :
    t.entryE i = some (t.val[i]'h).val := by
  show (t.val[i]?).map Subtype.val = _
  rw [List.getElem?_eq_getElem h]
  rfl

/-- A finite-dtype wire always reads a finite rational at every
in-range entry, and the rational carries the dtype's carrier facts. -/
theorem exists_read_fin {H : Hypernet} (σ : H.Valuation) {w : Wire}
    {τ : TensorType} (hw : H.wireType w = some τ)
    (hext : τ.dtype.ext = .fin) {i : ℕ} (hi : i < τ.shape.totalSize) :
    ∃ q : ℚ, σ.entryFlat w i = some (.fin q) ∧ τ.dtype.kind.MemK q ∧
      (τ.dtype.sign = .nn → 0 ≤ q) := by
  have hlen : i < (σ w τ hw).val.length := by
    rw [(σ w τ hw).property]; exact hi
  rw [Hypernet.Valuation.entryFlat_some σ hw i,
    TensorValue.entryE_of_getElem _ hlen]
  have hprop := ((σ w τ hw).val[i]'hlen).property
  rcases hev : ((σ w τ hw).val[i]'hlen).val with _ | q | _
  · rw [hev] at hprop
    have h' : τ.dtype.ext = Ext.ext ∧ τ.dtype.sign = Sign.signed := hprop
    rw [hext] at h'
    exact nomatch h'.1
  · rw [hev] at hprop
    have h' : τ.dtype.kind.MemK q ∧ (τ.dtype.sign = .nn → 0 ≤ q) := hprop
    exact ⟨q, rfl, h'.1, h'.2⟩
  · rw [hev] at hprop
    have h' : τ.dtype.ext = Ext.ext := hprop
    rw [hext] at h'
    exact nomatch h'

/-- A scalar rational wire reads a rational. -/
theorem exists_readQ {H : Hypernet} (σ : H.Valuation) {w : Wire}
    (hw : H.wireType w = some ⟨[], Dtype.Q⟩) :
    ∃ q : ℚ, σ.entryFlat w 0 = some (.fin q) :=
  let ⟨q, hq, _⟩ := exists_read_fin σ hw rfl (by decide)
  ⟨q, hq⟩

/-- A scalar Boolean wire reads `0` or `1`. -/
theorem exists_readB {H : Hypernet} (σ : H.Valuation) {w : Wire}
    (hw : H.wireType w = some ⟨[], Dtype.B⟩) :
    ∃ q : ℚ, (q = 0 ∨ q = 1) ∧ σ.entryFlat w 0 = some (.fin q) :=
  let ⟨q, hq, hmem, _⟩ := exists_read_fin σ hw rfl (by decide)
  ⟨q, hmem, hq⟩

/-- Exact rounding at the rational dtype relates a value to itself. -/
theorem roundOkQ (q : ℚ) : Dtype.Q.RoundOkE .exact (.fin q) (.fin q) :=
  ⟨rfl, trivial, fun h => nomatch h⟩

/-! ## Constants -/

theorem const_scalarQ_semOk_iff {H : Hypernet} (σ : H.Valuation) {w : Wire}
    (hw : H.wireType w = some ⟨[], Dtype.Q⟩) (c : ℚ) :
    (PrimApp.const ⟨[], Dtype.Q⟩ (qv0 c) w).SemOk σ ↔
      σ.entryFlat w 0 = some (.fin c) := by
  constructor
  · intro h
    exact h 0
  · intro h i
    match i with
    | 0 => exact h
    | i + 1 =>
      rw [Hypernet.Valuation.entryFlat_some σ hw,
        TensorValue.entryE_none_of_le _ (Nat.le_add_left 1 i)]
      rfl

/-! ## Scalar product: `contract` at the index-free pattern -/

theorem contract_mul_semOk_iff {H : Hypernet} (σ : H.Valuation)
    {a b c : Wire}
    (ha : H.wireType a = some ⟨[], Dtype.Q⟩)
    (hb : H.wireType b = some ⟨[], Dtype.Q⟩)
    (hc : H.wireType c = some ⟨[], Dtype.Q⟩) {va vb : ℚ}
    (hra : σ.entryFlat a 0 = some (.fin va))
    (hrb : σ.entryFlat b 0 = some (.fin vb)) :
    (PrimApp.contract Dtype.Q .exact [a, b] c [0, 0] 0 pat0).SemOk σ ↔
      σ.entryFlat c 0 = some (.fin (va * vb)) := by
  have haAt : σ.entryAt (([a, b] : List Wire).getD ((⟨0, by decide⟩ :
      Fin ([0, 0] : List Nat).length)).val 0)
      (pat0.inCoords [] ⟨0, by decide⟩) = some (.fin va) := by
    show σ.entryAt a (pat0.inCoords [] ⟨0, by decide⟩) = some (.fin va)
    rw [Hypernet.Valuation.entryAt_some σ ha]
    rw [Hypernet.Valuation.entryFlat_some σ ha] at hra
    exact hra
  have hbAt : σ.entryAt (([a, b] : List Wire).getD ((⟨1, by decide⟩ :
      Fin ([0, 0] : List Nat).length)).val 0)
      (pat0.inCoords [] ⟨1, by decide⟩) = some (.fin vb) := by
    show σ.entryAt b (pat0.inCoords [] ⟨1, by decide⟩) = some (.fin vb)
    rw [Hypernet.Valuation.entryAt_some σ hb]
    rw [Hypernet.Valuation.entryFlat_some σ hb] at hrb
    exact hrb
  have hex : contractExact σ [a, b] pat0 (pat0.outCoords []) =
      some (.fin (0 + 1 * va * vb)) := by
    unfold contractExact
    rw [show ((Shape.positions pat0.idxShape).filter
      (fun ν => decide (pat0.outCoords ν = pat0.outCoords [])))
      = [[]] from rfl]
    rw [show (List.finRange ([0, 0] : List Nat).length)
      = [⟨0, by decide⟩, ⟨1, by decide⟩] from rfl]
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
      Option.pure_def]
    rw [haAt, hbAt]
    rfl
  constructor
  · intro hsem
    obtain ⟨eOut, eEx, hout, hex', hro⟩ := hsem [] (List.mem_singleton.mpr rfl)
    rw [hex] at hex'
    obtain rfl : eEx = .fin (0 + 1 * va * vb) := (Option.some.inj hex').symm
    obtain ⟨rfl, -⟩ := hro
    have hread : σ.entryFlat c 0 = some (.fin (0 + 1 * va * vb)) := by
      rw [Hypernet.Valuation.entryAt_some σ hc] at hout
      rw [Hypernet.Valuation.entryFlat_some σ hc]
      exact hout
    rw [show (0 : ℚ) + 1 * va * vb = va * vb by ring] at hread
    exact hread
  · intro h ν₀ hν₀
    have hν : ν₀ = [] := List.mem_singleton.mp hν₀
    subst hν
    refine ⟨.fin (0 + 1 * va * vb), .fin (0 + 1 * va * vb), ?_, hex, roundOkQ _⟩
    rw [Hypernet.Valuation.entryAt_some σ hc]
    rw [Hypernet.Valuation.entryFlat_some σ hc] at h
    rw [show (0 : ℚ) + 1 * va * vb = va * vb by ring]
    exact h

/-! ## Pair stacking -/

theorem stack_pair_semOk_iff {H : Hypernet} (σ : H.Valuation)
    {a b v : Wire} {va vb : ℚ}
    (hra : σ.entryFlat a 0 = some (.fin va))
    (hrb : σ.entryFlat b 0 = some (.fin vb)) :
    (PrimApp.stack 2 [] [a, b] v).SemOk σ ↔
      (σ.entryFlat v 0 = some (.fin va) ∧
       σ.entryFlat v 1 = some (.fin vb)) := by
  constructor
  · intro hsem
    have h0 := hsem ⟨0, by simp⟩ ⟨0, by decide⟩
    have h1 := hsem ⟨1, by simp⟩ ⟨0, by decide⟩
    exact ⟨h0.trans hra, h1.trans hrb⟩
  · rintro ⟨h0, h1⟩ i j
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => exact h0.trans hra.symm
    | ⟨1, _⟩, ⟨0, _⟩ => exact h1.trans hrb.symm

/-! ## Pair sum: `contract` over one index of extent two -/

/-- Sum a length-two vector to a scalar: one index of extent `2`,
one rank-one input bound to it, rank-zero output. -/
def patSum1 : ContractPattern [1] 0 where
  nIndices := 1
  indexExtent := fun _ => 2
  inputBinding := fun i => match i with
    | ⟨0, _⟩ => fun _ => ⟨0, by decide⟩
  outputBinding := Fin.elim0

theorem contract_sumPair_semOk_iff {H : Hypernet} (σ : H.Valuation)
    {v s : Wire}
    (hv : H.wireType v = some ⟨[2], Dtype.Q⟩)
    (hs : H.wireType s = some ⟨[], Dtype.Q⟩) {v0 v1 : ℚ}
    (hr0 : σ.entryFlat v 0 = some (.fin v0))
    (hr1 : σ.entryFlat v 1 = some (.fin v1)) :
    (PrimApp.contract Dtype.Q .exact [v] s [1] 0 patSum1).SemOk σ ↔
      σ.entryFlat s 0 = some (.fin (v0 + v1)) := by
  have hAt0 : σ.entryAt (([v] : List Wire).getD ((⟨0, by decide⟩ :
      Fin ([1] : List Nat).length)).val 0)
      (patSum1.inCoords [0] ⟨0, by decide⟩) = some (.fin v0) := by
    show σ.entryAt v (patSum1.inCoords [0] ⟨0, by decide⟩) = some (.fin v0)
    rw [Hypernet.Valuation.entryAt_some σ hv]
    rw [Hypernet.Valuation.entryFlat_some σ hv] at hr0
    exact hr0
  have hAt1 : σ.entryAt (([v] : List Wire).getD ((⟨0, by decide⟩ :
      Fin ([1] : List Nat).length)).val 0)
      (patSum1.inCoords [1] ⟨0, by decide⟩) = some (.fin v1) := by
    show σ.entryAt v (patSum1.inCoords [1] ⟨0, by decide⟩) = some (.fin v1)
    rw [Hypernet.Valuation.entryAt_some σ hv]
    rw [Hypernet.Valuation.entryFlat_some σ hv] at hr1
    exact hr1
  have hex : ∀ t : List ℕ, t = [] →
      contractExact σ [v] patSum1 t =
        some (.fin (0 + 1 * v0 + 1 * v1)) := by
    rintro _ rfl
    unfold contractExact
    rw [show ((Shape.positions patSum1.idxShape).filter
      (fun ν => decide (patSum1.outCoords ν = ([] : List ℕ))))
      = [[0], [1]] from rfl]
    rw [show (List.finRange ([1] : List Nat).length)
      = [⟨0, by decide⟩] from rfl]
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
      Option.pure_def]
    rw [hAt0, hAt1]
    rfl
  constructor
  · intro hsem
    obtain ⟨eOut, eEx, hout, hex', hro⟩ :=
      hsem [0] (by simp [show Shape.positions patSum1.idxShape
        = [[0], [1]] from rfl])
    rw [hex _ (show patSum1.outCoords [0] = [] from rfl)] at hex'
    obtain rfl : eEx = .fin (0 + 1 * v0 + 1 * v1) :=
      (Option.some.inj hex').symm
    obtain ⟨rfl, -⟩ := hro
    have hread : σ.entryFlat s 0 = some (.fin (0 + 1 * v0 + 1 * v1)) := by
      rw [Hypernet.Valuation.entryAt_some σ hs] at hout
      rw [Hypernet.Valuation.entryFlat_some σ hs]
      exact hout
    rw [show (0 : ℚ) + 1 * v0 + 1 * v1 = v0 + v1 by ring] at hread
    exact hread
  · intro h ν₀ hν₀
    have hkey : ∀ t : List ℕ, t = [] →
        ∃ eOut eExact,
          σ.entryAt s t = some eOut ∧
          contractExact σ [v] patSum1 t = some eExact ∧
          Dtype.Q.RoundOkE .exact eExact eOut := by
      rintro _ rfl
      refine ⟨.fin (0 + 1 * v0 + 1 * v1), .fin (0 + 1 * v0 + 1 * v1),
        ?_, hex _ rfl, roundOkQ _⟩
      rw [Hypernet.Valuation.entryAt_some σ hs]
      rw [Hypernet.Valuation.entryFlat_some σ hs] at h
      rw [show (0 : ℚ) + 1 * v0 + 1 * v1 = v0 + v1 by ring]
      exact h
    have hν : ν₀ = [0] ∨ ν₀ = [1] := by
      simpa [show Shape.positions patSum1.idxShape = [[0], [1]] from rfl]
        using hν₀
    rcases hν with rfl | rfl
    · exact hkey _ rfl
    · exact hkey _ rfl

/-! ## Copies of a scalar -/

theorem copy_scalarQ_semOk_iff {H : Hypernet} (σ : H.Valuation)
    {src : Wire} {outs : List Wire} (k : ℕ)
    (hsrc : H.wireType src = some ⟨[], Dtype.Q⟩)
    (houts : ∀ o ∈ outs, H.wireType o = some ⟨[], Dtype.Q⟩) {vs : ℚ}
    (hr : σ.entryFlat src 0 = some (.fin vs)) :
    (PrimApp.copy k src outs).SemOk σ ↔
      ∀ o ∈ outs, σ.entryFlat o 0 = some (.fin vs) := by
  constructor
  · intro hsem o ho
    exact (hsem o ho 0).trans hr
  · intro h o ho i
    match i with
    | 0 => exact (h o ho).trans hr.symm
    | i + 1 =>
      rw [Hypernet.Valuation.entryFlat_some σ (houts o ho),
        Hypernet.Valuation.entryFlat_some σ hsrc,
        TensorValue.entryE_none_of_le _ (Nat.le_add_left 1 i),
        TensorValue.entryE_none_of_le _ (Nat.le_add_left 1 i)]

/-! ## Exact Boolean-to-rational cast -/

theorem cast_BQ_semOk_iff {H : Hypernet} (σ : H.Valuation) {i o : Wire}
    {vb : ℚ} (hri : σ.entryFlat i 0 = some (.fin vb)) :
    (PrimApp.cast Dtype.B Dtype.Q .exact [] i o).SemOk σ ↔
      σ.entryFlat o 0 = some (.fin vb) := by
  constructor
  · intro hsem
    obtain ⟨eIn, eOut, h1, h2, hro⟩ := hsem ⟨0, by decide⟩
    obtain rfl : eIn = .fin vb := Option.some.inj (h1.symm.trans hri)
    obtain ⟨rfl, -⟩ := hro
    exact h2
  · intro h idx
    have hidx : idx.val = 0 := Nat.lt_one_iff.mp idx.isLt
    rw [hidx]
    exact ⟨.fin vb, .fin vb, hri, h, rfl, trivial, fun hh => nomatch hh⟩

/-! ## Scalar-to-vector reshape -/

theorem reshape_scalar_semOk_iff {H : Hypernet} (σ : H.Valuation)
    {a b : Wire}
    (ha : H.wireType a = some ⟨[], Dtype.Q⟩)
    (hb : H.wireType b = some ⟨[1], Dtype.Q⟩) {va : ℚ}
    (hr : σ.entryFlat a 0 = some (.fin va)) :
    (PrimApp.reshape [1] a b).SemOk σ ↔
      σ.entryFlat b 0 = some (.fin va) := by
  constructor
  · intro hsem
    exact (hsem 0).trans hr
  · intro h i
    match i with
    | 0 => exact h.trans hr.symm
    | i + 1 =>
      rw [Hypernet.Valuation.entryFlat_some σ hb,
        Hypernet.Valuation.entryFlat_some σ ha,
        TensorValue.entryE_none_of_le _ (Nat.le_add_left 1 i),
        TensorValue.entryE_none_of_le _ (Nat.le_add_left 1 i)]

/-! ## The guard schema: one cell, the nonnegative ray -/

/-- The one-cell restriction of the σ± complex: same vertices, same
simplices, and the single cell is the nonnegative ray `[0, ∞)`. -/
def sigmaNN : SimpC where
  nVertices := 3
  ambDim := 1
  coord := fun v _ => if v = 0 then 0 else if v = 1 then 1 else -1
  simplices := [fun v => v == 0, fun v => v == 1, fun v => v == 2,
                fun v => v == 0 || v == 1, fun v => v == 0 || v == 2]
  cells := [(fun v => v == 0 || v == 2, fun v => v == 2)]
  nonempty := by decide
  closure := by decide
  conformity := by decide
  distinctVerts := by decide +kernel
  cellsWF := by decide

/-- The single `sigmaNN` cell carves exactly the nonnegative ray. -/
theorem maskRegion_sigmaNN_iff (x : Fin sigmaNN.ambDim → ℚ) :
    MaskRegion sigmaNN (sigmaNN.cells.get ⟨0, by decide⟩).1
      (sigmaNN.cells.get ⟨0, by decide⟩).2 x ↔ 0 ≤ x ⟨0, by decide⟩ :=
  ReluExpansion.maskRegion_cPos_iff x

theorem sigmaNN_cellIntDisjoint : sigmaNN.CellIntDisjoint := by
  intro i k hik x hstrict hreg
  exact hik (Fin.ext ((Nat.lt_one_iff.mp i.isLt).trans
    (Nat.lt_one_iff.mp k.isLt).symm))

/-- The guard reading of a one-cell application: admissible exactly on
the nonnegative ray, with the indicator output pinned to `1`. -/
theorem cell_guard_semOk_iff {H : Hypernet} (σ : H.Valuation)
    {s g : Wire}
    (hs : H.wireType s = some ⟨[1], Dtype.Q⟩) {vs : ℚ}
    (hr : σ.entryFlat s 0 = some (.fin vs)) :
    (PrimApp.cell sigmaNN s [g]).SemOk σ ↔
      (0 ≤ vs ∧ σ.entryFlat g 0 = some (.fin 1)) := by
  constructor
  · rintro ⟨-, x, hx, k, hreg, hone⟩
    have hx0 : x ⟨0, by decide⟩ = vs := by
      have hread := hx ⟨0, by decide⟩
      rw [Hypernet.Valuation.entryAt_some σ hs] at hread
      rw [Hypernet.Valuation.entryFlat_some σ hs] at hr
      exact ERat.fin.inj (Option.some.inj (hread.symm.trans hr))
    have hk : k = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp k.isLt)
    subst hk
    refine ⟨?_, ?_⟩
    · rw [← hx0]
      exact (maskRegion_sigmaNN_iff x).mp hreg
    · simpa using hone ⟨0, by simp⟩
  · rintro ⟨hpos, hg⟩
    refine ⟨sigmaNN_cellIntDisjoint, fun _ => vs, ?_,
      ⟨0, by decide⟩, (maskRegion_sigmaNN_iff _).mpr hpos, ?_⟩
    · intro j
      have hj : j = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp j.isLt)
      subst hj
      rw [Hypernet.Valuation.entryAt_some σ hs]
      rw [Hypernet.Valuation.entryFlat_some σ hs] at hr
      exact hr
    · intro j
      have hj : j = ⟨0, by simp⟩ := Fin.ext (Nat.lt_one_iff.mp j.isLt)
      subst hj
      simpa using hg

/-! ## The free-choice reading of the σ± schema at the origin -/

/-- Fed the origin — which both cells contain — the σ± application's
one-hot outputs are exactly the two indicator patterns, freely. -/
theorem cell_freeBit_semOk_iff {H : Hypernet} (σ : H.Valuation)
    {z b0 b1 : Wire}
    (hz : H.wireType z = some ⟨[1], Dtype.Q⟩)
    (hr : σ.entryFlat z 0 = some (.fin 0)) :
    (PrimApp.cell sigmaPM z [b0, b1]).SemOk σ ↔
      ((σ.entryFlat b0 0 = some (.fin 1) ∧
        σ.entryFlat b1 0 = some (.fin 0)) ∨
       (σ.entryFlat b0 0 = some (.fin 0) ∧
        σ.entryFlat b1 0 = some (.fin 1))) := by
  constructor
  · rintro ⟨-, x, hx, k, hreg, hone⟩
    have h0 := hone ⟨0, by simp⟩
    have h1 := hone ⟨1, by simp⟩
    have hk : k.val = 0 ∨ k.val = 1 := by
      have h2 : k.val < 2 := k.isLt
      omega
    rcases hk with hk | hk
    · exact Or.inl ⟨by simpa [hk] using h0, by simpa [hk] using h1⟩
    · exact Or.inr ⟨by simpa [hk] using h0, by simpa [hk] using h1⟩
  · intro h
    refine ⟨ReluExpansion.sigmaPM_disjoint, fun _ => 0, ?_, ?_⟩
    · intro j
      have hj : j = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp j.isLt)
      subst hj
      rw [Hypernet.Valuation.entryAt_some σ hz]
      rw [Hypernet.Valuation.entryFlat_some σ hz] at hr
      exact hr
    · rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · refine ⟨cNeg, (ReluExpansion.maskRegion_cNeg_iff _).mpr le_rfl, ?_⟩
        intro j
        match j with
        | ⟨0, _⟩ =>
          rw [show ((if (0 : ℕ) = (cNeg : Fin sigmaPM.cells.length).val
            then (1 : ℚ) else 0)) = 1 from rfl]
          exact h0
        | ⟨1, _⟩ =>
          rw [show ((if (1 : ℕ) = (cNeg : Fin sigmaPM.cells.length).val
            then (1 : ℚ) else 0)) = 0 from rfl]
          exact h1
      · refine ⟨cPos, (ReluExpansion.maskRegion_cPos_iff _).mpr le_rfl, ?_⟩
        intro j
        match j with
        | ⟨0, _⟩ =>
          rw [show ((if (0 : ℕ) = (cPos : Fin sigmaPM.cells.length).val
            then (1 : ℚ) else 0)) = 0 from rfl]
          exact h0
        | ⟨1, _⟩ =>
          rw [show ((if (1 : ℕ) = (cPos : Fin sigmaPM.cells.length).val
            then (1 : ℚ) else 0)) = 1 from rfl]
          exact h1

/-! ## Type-consistency dischargers -/

theorem tcConstQ {wt : Wire → Option TensorType} {w : Wire} (c : ℚ)
    (hw : wt w = some ⟨[], Dtype.Q⟩) :
    (PrimApp.const ⟨[], Dtype.Q⟩ (qv0 c) w).TypeConsistent wt := hw

theorem tcMul {wt : Wire → Option TensorType} {a b c : Wire}
    (ha : wt a = some ⟨[], Dtype.Q⟩) (hb : wt b = some ⟨[], Dtype.Q⟩)
    (hc : wt c = some ⟨[], Dtype.Q⟩) :
    (PrimApp.contract Dtype.Q .exact [a, b] c [0, 0] 0 pat0).TypeConsistent
      wt := by
  refine ⟨rfl, ?_, ⟨⟨[], Dtype.Q⟩, hc, rfl, rfl⟩, ?_, ?_⟩
  · intro p hp
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨⟨[], Dtype.Q⟩, ha, rfl, rfl⟩
    · exact ⟨⟨[], Dtype.Q⟩, hb, rfl, rfl⟩
  · intro i
    match i with
    | ⟨0, _⟩ => exact fun aIdx => aIdx.elim0
    | ⟨1, _⟩ => exact fun aIdx => aIdx.elim0
  · exact fun aIdx => aIdx.elim0

theorem tcStackPair {wt : Wire → Option TensorType} {a b v : Wire}
    (ha : wt a = some ⟨[], Dtype.Q⟩) (hb : wt b = some ⟨[], Dtype.Q⟩)
    (hv : wt v = some ⟨[2], Dtype.Q⟩) :
    (PrimApp.stack 2 [] [a, b] v).TypeConsistent wt := by
  refine ⟨rfl, ⟨[2], Dtype.Q⟩, hv, rfl, ?_⟩
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact ha
  · exact hb

theorem tcSumPair {wt : Wire → Option TensorType} {v s : Wire}
    (hv : wt v = some ⟨[2], Dtype.Q⟩) (hs : wt s = some ⟨[], Dtype.Q⟩) :
    (PrimApp.contract Dtype.Q .exact [v] s [1] 0 patSum1).TypeConsistent
      wt := by
  refine ⟨rfl, ?_, ⟨⟨[], Dtype.Q⟩, hs, rfl, rfl⟩, ?_, ?_⟩
  · intro p hp
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    subst hp
    exact ⟨⟨[2], Dtype.Q⟩, hv, rfl, rfl⟩
  · intro i
    match i with
    | ⟨0, _⟩ =>
      intro aIdx
      match aIdx with
      | ⟨0, _⟩ => exact ⟨⟨[2], Dtype.Q⟩, hv, rfl⟩
  · exact fun aIdx => aIdx.elim0

theorem tcCopyQ {wt : Wire → Option TensorType} {src : Wire}
    {outs : List Wire}
    (hsrc : wt src = some ⟨[], Dtype.Q⟩)
    (houts : ∀ o ∈ outs, wt o = some ⟨[], Dtype.Q⟩) :
    (PrimApp.copy outs.length src outs).TypeConsistent wt :=
  ⟨rfl, ⟨[], Dtype.Q⟩, hsrc, houts⟩

theorem tcCastBQ {wt : Wire → Option TensorType} {i o : Wire}
    (hi : wt i = some ⟨[], Dtype.B⟩) (ho : wt o = some ⟨[], Dtype.Q⟩) :
    (PrimApp.cast Dtype.B Dtype.Q .exact [] i o).TypeConsistent wt :=
  ⟨hi, ho⟩

theorem tcReshape01 {wt : Wire → Option TensorType} {a b : Wire}
    (ha : wt a = some ⟨[], Dtype.Q⟩) (hb : wt b = some ⟨[1], Dtype.Q⟩) :
    (PrimApp.reshape [1] a b).TypeConsistent wt :=
  ⟨⟨[], Dtype.Q⟩, ha, rfl, hb⟩

theorem tcCellNN {wt : Wire → Option TensorType} {s g : Wire}
    (hs : wt s = some ⟨[1], Dtype.Q⟩) (hg : wt g = some ⟨[], Dtype.B⟩) :
    (PrimApp.cell sigmaNN s [g]).TypeConsistent wt := by
  refine ⟨⟨Dtype.Q, hs⟩, rfl, ?_⟩
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  subst ho
  exact hg

theorem tcCellPM {wt : Wire → Option TensorType} {z b0 b1 : Wire}
    (hz : wt z = some ⟨[1], Dtype.Q⟩)
    (h0 : wt b0 = some ⟨[], Dtype.B⟩)
    (h1 : wt b1 = some ⟨[], Dtype.B⟩) :
    (PrimApp.cell sigmaPM z [b0, b1]).TypeConsistent wt := by
  refine ⟨⟨Dtype.Q, hz⟩, rfl, ?_⟩
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact h0
  · exact h1

/-! ## Axiom receipts (in-package convention: `#print axioms`) -/

#print axioms exists_read_fin
#print axioms const_scalarQ_semOk_iff
#print axioms contract_mul_semOk_iff
#print axioms contract_sumPair_semOk_iff
#print axioms stack_pair_semOk_iff
#print axioms copy_scalarQ_semOk_iff
#print axioms cast_BQ_semOk_iff
#print axioms reshape_scalar_semOk_iff
#print axioms cell_guard_semOk_iff
#print axioms cell_freeBit_semOk_iff

end PPLC
