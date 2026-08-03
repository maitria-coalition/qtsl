import Qtsl.Core.Catalogue
import Qtsl.CoreBridge
import Qtsl.ERat
import Qtsl.Dyadic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# The certificate contract: semantic model and rounding theory

Semantic counterpart of `Qtsl.Core.Catalogue` (which carries
the executable data types). This module interprets the certificate
vocabulary in real and extended-real terms and proves the rounding
theory the float-valued rules rely on:

* `Dtype.iota` / `Dtype.iotaE` — the ℝ/`EReal` embeddings of each
  data type's carrier;
* `Dtype.round`, `Dtype.RoundOkE`, and the rounding theorems
  (`roundE_valid`, `Kind.roundQ_float`, `Dtype.round_rdn_le`,
  `Dtype.le_round_rup`);
* hypernet valuations, exact tensor views (`QTensor`, `wireQ`,
  `Term.evalQ`), formula satisfaction (`Formula.holds`), mask-region
  semantics, and `Sequent.semanticallyValid` — the target of the
  soundness development.
-/

namespace PPLC

noncomputable def Dtype.iota    : (δ : Dtype) → δ.carrier → ℝ :=
  fun _ v => v.val.toRealLossy

noncomputable def Dtype.iotaE (δ : Dtype) (v : δ.carrier) : EReal :=
  v.val.toEReal

theorem Dtype.roundE_valid (δ : Dtype) (r : RoundMode) (q : ℚ) :
    δ.ValueSet (δ.roundE r q) := by

  have hmemK_exact : ∀ (k : Kind), k.fmt? = none →
      ∀ (r' : RoundMode) (q' : ℚ), k.MemK (k.roundQ r' q') := by
    intro k hk r' q'
    cases k
    case bool => show _ = 0 ∨ _ = 1; simp only [Kind.roundQ]; split <;> simp
    case int =>
      show Rat.den _ = 1
      simp only [Kind.roundQ]
      cases r'
      case rdn => exact Rat.den_intCast _
      case rup => exact Rat.den_intCast _
      case rtz => split_ifs <;> exact Rat.den_intCast _
      case rne => exact Rat.den_intCast _
      case exact => exact Rat.den_intCast _
    case rat => trivial
    all_goals simp [Kind.fmt?] at hk

  have hmemK_max : ∀ (k : Kind), k.fmt? = none →
      ∀ (v : ℚ), k.MemK v → k.MemK (max 0 v) := by
    intro k hk v hv
    rcases max_choice 0 v with h | h
    · rw [h]
      cases k
      case bool => exact Or.inl rfl
      case int => show Rat.den 0 = 1; exact Rat.den_ofNat
      case rat => trivial
      all_goals simp [Kind.fmt?] at hk
    · rw [h]; exact hv

  have hmemK_float : ∀ (k : Kind) (fmt : FloatFmt), k.fmt? = some fmt →
      ∀ (r' : RoundMode) (q' : ℚ), k.MemK (k.roundQ r' q') := by
    intro k fmt hk r' q'
    have hrepAny : ∀ (fm : FloatFmt),
        fm.Rep (match r' with
                | .rdn => fm.rdn q' | .rup => fm.rup q' | .rtz => fm.rtz q'
                | .rne => fm.rne q' | .exact => fm.rne q') := by
      intro fm
      cases r'
      case rdn => exact fm.rep_rdn q'
      case rup => exact fm.rep_rup q'
      case rtz => exact fm.rep_rtz q'
      case rne => exact fm.rep_rne q'
      case exact => exact fm.rep_rne q'
    cases k
    case f16 => exact hrepAny FloatFmt.f16
    case bf16 => exact hrepAny FloatFmt.bf16
    case f32 => exact hrepAny FloatFmt.f32
    case f64 => exact hrepAny FloatFmt.f64
    all_goals simp [Kind.fmt?] at hk

  have hmemK_zeroF : ∀ (k : Kind) (fmt : FloatFmt), k.fmt? = some fmt → k.MemK 0 := by
    intro k fmt hk
    cases k
    case f16 => exact FloatFmt.rep_zero _
    case bf16 => exact FloatFmt.rep_zero _
    case f32 => exact FloatFmt.rep_zero _
    case f64 => exact FloatFmt.rep_zero _
    all_goals simp [Kind.fmt?] at hk
  have hmemK_maxF : ∀ (k : Kind) (fmt : FloatFmt), k.fmt? = some fmt →
      ∀ (v : ℚ), k.MemK v → k.MemK (max 0 v) := by
    intro k fmt hk v hv
    rcases max_choice 0 v with h | h
    · rw [h]; exact hmemK_zeroF k fmt hk
    · rw [h]; exact hv
  unfold roundE
  split
  next hf =>

    show δ.kind.MemK _ ∧ (δ.sign = .nn → 0 ≤ _)
    constructor
    · split
      · exact hmemK_max _ hf _ (hmemK_exact _ hf r q)
      · exact hmemK_exact _ hf r q
    · intro hs
      rw [if_pos hs]
      exact le_max_left 0 _
  next fmt hf =>
    split
    next hclamp =>

      exact ⟨hmemK_zeroF _ fmt hf, fun _ => le_refl (0 : ℚ)⟩
    next hclamp =>
      split
      next hpos =>

        show δ.ext = .ext
        exact hpos.1
      next hpos =>
        split
        next hneg =>

          show δ.ext = .ext ∧ δ.sign = .signed
          refine ⟨hneg.1, ?_⟩
          cases hs : δ.sign with
          | signed => rfl
          | nn =>
              exfalso
              have hq0 : q < 0 := by
                have hm := fmt.maxFin_pos
                have h2p : (0:ℚ) < 2 ^ (fmt.eMax - 1) := zpow_pos two_pos _
                rcases hneg.2 with ⟨_, hq⟩ | ⟨_, hq⟩ <;> linarith
              exact hclamp ⟨hs, hq0⟩
        next hneg =>

          show δ.kind.MemK _ ∧ (δ.sign = .nn → 0 ≤ _)
          constructor
          · split
            · exact hmemK_maxF _ fmt hf _ (hmemK_float _ fmt hf r q)
            · exact hmemK_float _ fmt hf r q
          · intro hs
            rw [if_pos hs]
            exact le_max_left 0 _

def Dtype.round   : (δ : Dtype) → RoundMode → ℚ → δ.carrier :=
  fun δ r q => ⟨δ.roundE r q, δ.roundE_valid r q⟩

def Dtype.RoundOkE (δ : Dtype) (r : RoundMode) : ERat → ERat → Prop
  | .fin q, out =>
      (match r with
       | .exact => out = .fin q ∧ δ.ValueSet (.fin q)
       | _ => out = (δ.round r q).val)
  | .negInf, out => out = .negInf
  | .posInf, out => out = .posInf

theorem Kind.roundQ_float {k : Kind} {fmt : FloatFmt} (hk : k.fmt? = some fmt)
    (r : RoundMode) (q : ℚ) :
    k.roundQ r q = (match r with
                    | .rdn => fmt.rdn q | .rup => fmt.rup q | .rtz => fmt.rtz q
                    | .rne => fmt.rne q | .exact => fmt.rne q) := by
  cases k
  case f16 => simp only [Kind.fmt?, Option.some.injEq] at hk; subst hk; rfl
  case bf16 => simp only [Kind.fmt?, Option.some.injEq] at hk; subst hk; rfl
  case f32 => simp only [Kind.fmt?, Option.some.injEq] at hk; subst hk; rfl
  case f64 => simp only [Kind.fmt?, Option.some.injEq] at hk; subst hk; rfl
  all_goals simp [Kind.fmt?] at hk

theorem Dtype.roundE_float {δ : Dtype} {fmt : FloatFmt} (hf : δ.kind.fmt? = some fmt)
    (r : RoundMode) (q : ℚ) :
    δ.roundE r q =
      (if δ.sign = .nn ∧ q < 0 then .fin 0
       else if δ.ext = .ext ∧ ((r = .rup ∧ fmt.maxFin < q) ∨
               (r = .rne ∧ fmt.maxFin + 2 ^ (fmt.eMax - 1) ≤ q)) then .posInf
       else if δ.ext = .ext ∧ ((r = .rdn ∧ q < -fmt.maxFin) ∨
               (r = .rne ∧ q ≤ -(fmt.maxFin + 2 ^ (fmt.eMax - 1)))) then .negInf
       else
         .fin (if δ.sign = .nn then max 0 (δ.kind.roundQ r q)
               else δ.kind.roundQ r q)) := by
  unfold roundE
  rw [hf]

theorem Dtype.round_rdn_le {δ : Dtype} {fmt : FloatFmt} (hf : δ.kind.fmt? = some fmt)
    {q : ℚ} (hnn : δ.sign = .nn → 0 ≤ q) (hfin : δ.ext = .fin → -fmt.maxFin ≤ q) :
    (δ.round .rdn q).val ≤ ERat.fin q := by
  show δ.roundE .rdn q ≤ ERat.fin q
  rw [Dtype.roundE_float hf]
  split_ifs with h1 h2 h3 h4
  · exact ERat.le_fin_fin.mpr (hnn h1.1)
  · rcases h2.2 with ⟨hr, _⟩ | ⟨hr, _⟩ <;> exact absurd hr (by simp)
  · exact ERat.negInf_le _
  · have hlo : -fmt.maxFin ≤ q := by
      cases hext : δ.ext with
      | fin => exact hfin hext
      | ext =>
          by_contra hcon
          exact h3 ⟨hext, Or.inl ⟨rfl, not_le.mp hcon⟩⟩
    rw [Kind.roundQ_float hf]
    exact ERat.le_fin_fin.mpr (max_le (hnn h4) (fmt.rdn_le hlo))
  · have hlo : -fmt.maxFin ≤ q := by
      cases hext : δ.ext with
      | fin => exact hfin hext
      | ext =>
          by_contra hcon
          exact h3 ⟨hext, Or.inl ⟨rfl, not_le.mp hcon⟩⟩
    rw [Kind.roundQ_float hf]
    exact ERat.le_fin_fin.mpr (fmt.rdn_le hlo)

theorem Dtype.le_round_rup {δ : Dtype} {fmt : FloatFmt} (hf : δ.kind.fmt? = some fmt)
    {q : ℚ} (hfin : δ.ext = .fin → q ≤ fmt.maxFin) :
    ERat.fin q ≤ (δ.round .rup q).val := by
  show ERat.fin q ≤ δ.roundE .rup q
  rw [Dtype.roundE_float hf]
  split_ifs with h1 h2 h3 h4
  · exact ERat.le_fin_fin.mpr (le_of_lt h1.2)
  · exact ERat.le_posInf _
  · rcases h3.2 with ⟨hr, _⟩ | ⟨hr, _⟩ <;> exact absurd hr (by simp)
  · have hhi : q ≤ fmt.maxFin := by
      cases hext : δ.ext with
      | fin => exact hfin hext
      | ext =>
          by_contra hcon
          exact h2 ⟨hext, Or.inl ⟨rfl, not_le.mp hcon⟩⟩
    rw [Kind.roundQ_float hf]
    exact ERat.le_fin_fin.mpr (le_trans (fmt.le_rup hhi) (le_max_right 0 _))
  · have hhi : q ≤ fmt.maxFin := by
      cases hext : δ.ext with
      | fin => exact hfin hext
      | ext =>
          by_contra hcon
          exact h2 ⟨hext, Or.inl ⟨rfl, not_le.mp hcon⟩⟩
    rw [Kind.roundQ_float hf]
    exact ERat.le_fin_fin.mpr (fmt.le_rup hhi)

#guard (Dtype.F64.round .rup (2 ^ 2000)).val = ERat.posInf
#guard (Dtype.F64.round .rdn (-(2 ^ 2000))).val = ERat.negInf
#guard (Dtype.F64.round .rtz (2 ^ 2000)).val = ERat.fin FloatFmt.f64.maxFin
#guard ((⟨.f64, .nn, .ext⟩ : Dtype).round .rdn (-1)).val = ERat.fin 0
#guard (Dtype.Q.round .exact (22/7)).val = ERat.fin (22/7)
#guard (Dtype.Z.round .rdn (-7/2)).val = ERat.fin (-4)

namespace Shape

def positions : Shape → List (List ℕ)
  | [] => [[]]
  | s :: rest => (List.range s).flatMap fun i => (positions rest).map (i :: ·)

def flatten : Shape → List ℕ → Option ℕ
  | [], [] => some 0
  | s :: rest, c :: cs =>
      if c < s then (flatten rest cs).map (c * Shape.totalSize rest + ·) else none
  | _, _ => none

def bcastBack (src dst : Shape) (c : List ℕ) : List ℕ :=
  (src.zip (c.drop (dst.length - src.length))).map fun p => if p.1 = 1 then 0 else p.2

end Shape

def Hypernet.Valuation (H : Hypernet) : Type :=
  (w : Wire) → (τ : TensorType) → H.wireType w = some τ → TensorValue τ

namespace Hypernet.Valuation

variable {H : Hypernet} (σ : H.Valuation)

def entryFlat (w : Wire) (i : ℕ) : Option ERat :=
  match h : H.wireType w with
  | none => none
  | some τ => (σ w τ h).entryE i

def entryAt (w : Wire) (c : List ℕ) : Option ERat :=
  match h : H.wireType w with
  | none => none
  | some τ => (Shape.flatten τ.shape c).bind fun i => (σ w τ h).entryE i

end Hypernet.Valuation

def ERat.allFinQ : List ERat → Option (List ℚ)
  | [] => some []
  | .fin q :: rest => (allFinQ rest).map (q :: ·)
  | .negInf :: _ => none
  | .posInf :: _ => none

theorem ERat.allFinQ_length : ∀ (l : List ERat) (l' : List ℚ),
    ERat.allFinQ l = some l' → l'.length = l.length
  | [], l', h => by
      simp only [allFinQ, Option.some.injEq] at h
      simp [← h]
  | .fin q :: rest, l', h => by
      simp only [allFinQ] at h
      cases hr : allFinQ rest with
      | none => rw [hr] at h; simp at h
      | some tail =>
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq] at h
          rw [← h]
          simp [ERat.allFinQ_length rest tail hr]
  | .negInf :: _, _, h => by simp [allFinQ] at h
  | .posInf :: _, _, h => by simp [allFinQ] at h

structure QTensor where
  shape : Shape
  entries : List ℚ
  len_eq : entries.length = Shape.totalSize shape

namespace QTensor

def scalar (t : QTensor) : ℚ := t.entries.getD 0 0

def map2 (f : ℚ → ℚ → ℚ) (a b : QTensor) : Option QTensor :=
  if h : a.shape = b.shape then
    some ⟨a.shape, a.entries.zipWith f b.entries, by
      simp [List.length_zipWith, a.len_eq, b.len_eq, h]⟩
  else if a.shape = [] then
    some ⟨b.shape, b.entries.map (f a.scalar), by simp [b.len_eq]⟩
  else if b.shape = [] then
    some ⟨a.shape, a.entries.map (f · b.scalar), by simp [a.len_eq]⟩
  else none

def map1 (f : ℚ → ℚ) (a : QTensor) : QTensor :=
  ⟨a.shape, a.entries.map f, by simp [a.len_eq]⟩

def rel2 (r : ℚ → ℚ → Prop) (a b : QTensor) : Prop :=
  if a.shape = b.shape then ∀ p ∈ a.entries.zip b.entries, r p.1 p.2
  else if a.shape = [] then ∀ y ∈ b.entries, r a.scalar y
  else if b.shape = [] then ∀ x ∈ a.entries, r x b.scalar
  else False

end QTensor

def Hypernet.Valuation.wireQ {H : Hypernet} (σ : H.Valuation) (w : Wire) :
    Option QTensor :=
  match h : H.wireType w with
  | none => none
  | some τ =>
    match hf : ERat.allFinQ ((σ w τ h).val.map Subtype.val) with
    | none => none
    | some l => some ⟨τ.shape, l, by
        have h1 := ERat.allFinQ_length _ _ hf
        rw [List.length_map] at h1
        exact h1.trans (σ w τ h).property⟩

def Term.evalQ {H : Hypernet} (σ : H.Valuation) : Term → Option QTensor
  | .var w => σ.wireQ w
  | .const c => some ⟨[], [c], rfl⟩
  | .add l r => do QTensor.map2 (· + ·) (← Term.evalQ σ l) (← Term.evalQ σ r)
  | .mul l r => do QTensor.map2 (· * ·) (← Term.evalQ σ l) (← Term.evalQ σ r)
  | .sub l r => do QTensor.map2 (· - ·) (← Term.evalQ σ l) (← Term.evalQ σ r)
  | .neg t => (Term.evalQ σ t).map (QTensor.map1 Neg.neg)
  | .idx t i => do

    let q ← Term.evalQ σ t
    match q.shape with
    | [e] => if i < e then some ⟨[], [q.entries.getD i 0], rfl⟩ else none
    | _ => none

def BowTie.holdsQ : BowTie → ℚ → ℚ → Prop
  | .lt => (· < ·)
  | .le => (· ≤ ·)
  | .eq => (· = ·)
  | .ge => fun a b => b ≤ a
  | .gt => fun a b => b < a
  | .ne => (· ≠ ·)

def finSum (n : ℕ) (f : Fin n → ℝ) : ℝ := ((List.finRange n).map f).sum

def MaskRegion (C : SimpC) (mask ext : Fin C.nVertices → Bool)
    (x : Fin C.ambDim → ℚ) : Prop :=
  ∃ lam : Fin C.nVertices → ℝ,
    (∀ v, mask v = false → lam v = 0) ∧
    finSum C.nVertices lam = 1 ∧
    (∀ j : Fin C.ambDim,
      finSum C.nVertices (fun v => lam v * (C.coord v j : ℝ)) = (x j : ℝ)) ∧
    (∀ v, ext v = true → lam v ≤ 0) ∧
    (∀ v, mask v = true → ext v = false → 0 ≤ lam v)

def MaskRegionStrict (C : SimpC) (mask ext : Fin C.nVertices → Bool)
    (x : Fin C.ambDim → ℚ) : Prop :=
  ∃ lam : Fin C.nVertices → ℝ,
    (∀ v, mask v = false → lam v = 0) ∧
    finSum C.nVertices lam = 1 ∧
    (∀ j : Fin C.ambDim,
      finSum C.nVertices (fun v => lam v * (C.coord v j : ℝ)) = (x j : ℝ)) ∧
    (∀ v, ext v = true → lam v < 0) ∧
    (∀ v, mask v = true → ext v = false → 0 < lam v)

def SimpC.CellIntDisjoint (C : SimpC) : Prop :=
  ∀ i k : Fin C.cells.length, i ≠ k →
    ∀ x : Fin C.ambDim → ℚ,
      MaskRegionStrict C (C.cells.get i).1 (C.cells.get i).2 x →
      ¬ MaskRegion C (C.cells.get k).1 (C.cells.get k).2 x

def Formula.holds {H : Hypernet} (σ : H.Valuation) : Formula → Prop
  | .atom b l r => ∃ a a' : QTensor,
      Term.evalQ σ l = some a ∧ Term.evalQ σ r = some a' ∧
      QTensor.rel2 (BowTie.holdsQ b) a a'
  | .inRegion t simplex S =>
      simplex = S.simplex ∧
      ∃ q : QTensor, Term.evalQ σ t = some q ∧
        q.shape = [S.simplex.complex.ambDim] ∧
        MaskRegion S.simplex.complex S.simplex.contains S.contains
          (fun j => q.entries.getD j.val 0)
  | .and l r => Formula.holds σ l ∧ Formula.holds σ r
  | .or l r => Formula.holds σ l ∨ Formula.holds σ r
  | .tt => True
  | .ff => False

namespace ContractPattern

variable {inputRanks : List Nat} {outputRank : Nat}

def idxShape (pat : ContractPattern inputRanks outputRank) : Shape :=
  List.ofFn pat.indexExtent

def inCoords (pat : ContractPattern inputRanks outputRank)
    (ν : List ℕ) (k : Fin inputRanks.length) : List ℕ :=
  (List.finRange (inputRanks.get k)).map fun a => ν.getD (pat.inputBinding k a).val 0

def outCoords (pat : ContractPattern inputRanks outputRank) (ν : List ℕ) : List ℕ :=
  (List.finRange outputRank).map fun a => ν.getD (pat.outputBinding a).val 0

end ContractPattern

def contractExact {H : Hypernet} (σ : H.Valuation) (inputs : List Wire)
    {inputRanks : List Nat} {outputRank : Nat}
    (pat : ContractPattern inputRanks outputRank) (target : List ℕ) :
    Option ERat := do
  let assigns := (Shape.positions pat.idxShape).filter
    (fun ν => decide (pat.outCoords ν = target))
  let prods ← assigns.mapM fun ν =>
    (List.finRange inputRanks.length).mapM
      (fun k => σ.entryAt (inputs.getD k.val 0) (pat.inCoords ν k))
      >>= ERat.prod?
  ERat.sum? prods

def PrimApp.SemOk {H : Hypernet} (σ : H.Valuation) : PrimApp → Prop
  | .const _ty c out =>
      ∀ i : ℕ, σ.entryFlat out i = c.entryE i
  | .contract δ r inputs output _inputRanks _outputRank pat =>
      ∀ ν₀ ∈ Shape.positions pat.idxShape,
        ∃ eOut eExact,
          σ.entryAt output (pat.outCoords ν₀) = some eOut ∧
          contractExact σ inputs pat (pat.outCoords ν₀) = some eExact ∧
          δ.RoundOkE r eExact eOut
  | .cast _δfrom δto r shape input output =>
      ∀ i : Fin (Shape.totalSize shape),
        ∃ eIn eOut, σ.entryFlat input i.val = some eIn ∧
          σ.entryFlat output i.val = some eOut ∧ δto.RoundOkE r eIn eOut
  | .cell schema input outputs =>

      schema.CellIntDisjoint ∧
      ∃ x : Fin schema.ambDim → ℚ,
        (∀ j : Fin schema.ambDim, σ.entryAt input [j.val] = some (.fin (x j))) ∧
        ∃ k : Fin schema.cells.length,
          MaskRegion schema (schema.cells.get k).1 (schema.cells.get k).2 x ∧
          ∀ j : Fin outputs.length,
            σ.entryFlat (outputs.get j) 0 =
              some (.fin (if j.val = k.val then 1 else 0))
  | .reshape _newShape input output =>
      ∀ i : ℕ, σ.entryFlat output i = σ.entryFlat input i
  | .broadcast toShape input output =>
      ∃ τ, H.wireType input = some τ ∧
        ∀ c ∈ Shape.positions toShape,
          σ.entryAt output c = σ.entryAt input (Shape.bcastBack τ.shape toShape c)
  | .copy _k input outputs =>
      ∀ o ∈ outputs, ∀ i : ℕ, σ.entryFlat o i = σ.entryFlat input i
  | .delete _ => True
  | .swap in1 in2 out1 out2 =>
      (∀ i : ℕ, σ.entryFlat out1 i = σ.entryFlat in2 i) ∧
      (∀ i : ℕ, σ.entryFlat out2 i = σ.entryFlat in1 i)
  | .stack _k shape inputs output =>

      ∀ i : Fin inputs.length, ∀ j : Fin (Shape.totalSize shape),
        σ.entryFlat output (i.val * Shape.totalSize shape + j.val)
          = σ.entryFlat inputs[i] j.val
  | .relu shape input output =>

      ∀ i : Fin (Shape.totalSize shape),
        ∃ p y : ℚ,
          σ.entryFlat input i.val = some (.fin p) ∧
          σ.entryFlat output i.val = some (.fin y) ∧
          ((p ≤ 0 ∧ y = 0) ∨ (0 ≤ p ∧ y = p))
  | .ppoly nvars coeffs inputs output =>

      MonoTable.widthOk coeffs nvars → inputs.length = nvars →
      ∃ xs : List ℚ, ∃ y : ℚ,
        xs.length = inputs.length ∧
        (∀ i (hi : i < inputs.length),
          σ.entryFlat (inputs[i]'hi) 0 = some (.fin (xs.getD i 0))) ∧
        σ.entryFlat output 0 = some (.fin y) ∧
        y = MonoTable.evalQ coeffs xs
  | .pderiv shape axis input output =>

      axis < shape.length →
      ∃ qc qy : QTensor,
        σ.wireQ input = some qc ∧ σ.wireQ output = some qy ∧
        ∀ β ∈ Shape.positions shape, ∀ n, Shape.flatten shape β = some n →
          (∀ m, Shape.flatten shape (β.set axis (β.getD axis 0 + 1)) = some m →
            qy.entries.getD n 0
              = ((β.getD axis 0 : ℚ) + 1) * qc.entries.getD m 0) ∧
          (Shape.flatten shape (β.set axis (β.getD axis 0 + 1)) = none →
            qy.entries.getD n 0 = 0)
  | .facet shape axis hi input output =>

      axis < shape.length →
      ∃ qc qy : QTensor,
        σ.wireQ input = some qc ∧ σ.wireQ output = some qy ∧
        ∀ γ ∈ Shape.positions (shape.eraseIdx axis), ∀ n,
          Shape.flatten (shape.eraseIdx axis) γ = some n →
          ∀ m, Shape.flatten shape
              (γ.take axis ++ [if hi then shape.getD axis 0 - 1 else 0]
                ++ γ.drop axis) = some m →
            qy.entries.getD n 0 = qc.entries.getD m 0

def Hypernet.Valuation.Admissible {H : Hypernet} (σ : H.Valuation) : Prop :=
  ∀ app ∈ H.applications, app.SemOk σ

def Sequent.semanticallyValid (H : Hypernet) (seq : Sequent) : Prop :=
  ∀ σ : H.Valuation, σ.Admissible → seq.pre.holds σ → seq.post.holds σ

end PPLC
