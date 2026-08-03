import Qtsl.Core.Prim
import Qtsl.Core.ERat
import Qtsl.Core.Dyadic
import Qtsl.Core.QArith

/-!
# The certificate contract: computational core

Every definition on the executable checker's path, importing only core
Lean and the other `Core` modules: the certificate data types, the
computational glue, the bounded-computation predicates, the rule
payload structures, and the `Certificate` shape. The semantic
embeddings, rounding theorems, and satisfaction relation live in
`Qtsl.Catalogue`, which imports this module together with
mathlib.
-/

namespace PPLC

inductive Kind where
  | bool
  | int
  | rat
  | f16 | bf16 | f32 | f64
  deriving DecidableEq, Repr

inductive Sign where | nn | signed deriving DecidableEq, Repr
inductive Ext  where | fin | ext   deriving DecidableEq, Repr

structure Dtype where
  kind : Kind
  sign : Sign
  ext  : Ext
  deriving DecidableEq, Repr

namespace Dtype
  def B   : Dtype := ⟨.bool, .nn,     .fin⟩
  def N   : Dtype := ⟨.int,  .nn,     .fin⟩
  def Z   : Dtype := ⟨.int,  .signed, .fin⟩
  def Q   : Dtype := ⟨.rat,  .signed, .fin⟩
  def Qnn : Dtype := ⟨.rat,  .nn,     .fin⟩
  def F64 : Dtype := ⟨.f64,  .signed, .ext⟩
end Dtype

inductive RoundMode where | rne | rtz | rup | rdn | exact
  deriving DecidableEq, Repr

def Kind.MemK : Kind → Rat → Prop
  | .bool => fun q => q = 0 ∨ q = 1
  | .int  => fun q => q.den = 1
  | .rat  => fun _ => True
  | .f16  => FloatFmt.f16.Rep
  | .bf16 => FloatFmt.bf16.Rep
  | .f32  => FloatFmt.f32.Rep
  | .f64  => FloatFmt.f64.Rep

def Kind.fmt? : Kind → Option FloatFmt
  | .f16  => some .f16
  | .bf16 => some .bf16
  | .f32  => some .f32
  | .f64  => some .f64
  | _     => none

def Dtype.ValueSet (δ : Dtype) : ERat → Prop
  | .fin q   => δ.kind.MemK q ∧ (δ.sign = .nn → 0 ≤ q)
  | .negInf  => δ.ext = .ext ∧ δ.sign = .signed
  | .posInf  => δ.ext = .ext

def Dtype.carrier : Dtype → Type := fun δ => { e : ERat // δ.ValueSet e }

def Kind.roundQ : Kind → RoundMode → Rat → Rat
  | .bool, _, q => if q ≤ 0 then 0 else 1
  | .int, r, q =>
      (match r with
       | .rdn => (q.floor : Rat)
       | .rup => (q.ceil : Rat)
       | .rtz => if 0 ≤ q then (q.floor : Rat) else (q.ceil : Rat)
       | .rne => (Prim.roundNQ q : Rat)
       | .exact => (q.floor : Rat))
  | .rat, _, q => q
  | k, r, q => match k.fmt? with
      | some fmt =>
          (match r with
           | .rdn => fmt.rdn q
           | .rup => fmt.rup q
           | .rtz => fmt.rtz q
           | .rne => fmt.rne q
           | .exact => fmt.rne q)
      | none => q

def Dtype.roundE (δ : Dtype) (r : RoundMode) (q : Rat) : ERat :=
  match δ.kind.fmt? with
  | none =>
      .fin (if δ.sign = .nn then max 0 (δ.kind.roundQ r q) else δ.kind.roundQ r q)
  | some fmt =>
      if δ.sign = .nn ∧ q < 0 then .fin 0
      else if δ.ext = .ext ∧ ((r = .rup ∧ fmt.maxFin < q) ∨
              (r = .rne ∧ fmt.maxFin + 2 ^ (fmt.eMax - 1) ≤ q)) then .posInf
      else if δ.ext = .ext ∧ ((r = .rdn ∧ q < -fmt.maxFin) ∨
              (r = .rne ∧ q ≤ -(fmt.maxFin + 2 ^ (fmt.eMax - 1)))) then .negInf
      else
        .fin (if δ.sign = .nn then max 0 (δ.kind.roundQ r q) else δ.kind.roundQ r q)

abbrev Shape := List Nat
def Shape.rank (s : Shape) : Nat := s.length
def Shape.totalSize (s : Shape) : Nat := s.prod

structure TensorType where
  shape : Shape
  dtype : Dtype
  deriving DecidableEq, Repr

def TensorValue (τ : TensorType) : Type :=
  { l : List τ.dtype.carrier // l.length = τ.shape.totalSize }

def TensorValue.entryE {τ : TensorType} (v : TensorValue τ) (i : Nat) : Option ERat :=
  v.val[i]?.map Subtype.val

inductive Primitive where
  | const | contract | cast | cell
  | reshape | broadcast | copy | delete | swap
  | stack
  deriving DecidableEq, Repr

abbrev MonoTable := List (List Nat × Rat)

namespace MonoTable

def widthOk (q : MonoTable) (n : Nat) : Prop := ∀ m ∈ q, m.1.length = n

def widthOkB (q : MonoTable) (n : Nat) : Bool :=
  q.all (fun m => m.1.length == n)

def monoEvalAux (xs : List Rat) : List Nat → Nat → Rat → Rat
  | [], _, acc => acc
  | e :: es, i, acc =>
      (List.range e).foldr (fun _ a => xs.getD i 0 * a)
        (monoEvalAux xs es (i + 1) acc)

def monoEval (xs : List Rat) (m : List Nat × Rat) : Rat :=
  monoEvalAux xs m.1 0 m.2

def evalQ (q : MonoTable) (xs : List Rat) : Rat :=
  q.foldr (fun m acc => monoEval xs m + acc) 0

end MonoTable

structure SimpC where
  nVertices : Nat
  ambDim    : Nat
  coord     : Fin nVertices → Fin ambDim → Rat
  simplices : List (Fin nVertices → Bool)

  cells     : List ((Fin nVertices → Bool) × (Fin nVertices → Bool))

  nonempty      : ∀ s ∈ simplices, ∃ v, s v = true
  closure       : ∀ s ∈ simplices, ∀ v₀, s v₀ = true →
                    (∃ v₁, s v₁ = true ∧ v₁ ≠ v₀) →
                    ∃ s' ∈ simplices, ∀ v, s' v = (s v && decide (v ≠ v₀))
  conformity    : ∀ s₁ ∈ simplices, ∀ s₂ ∈ simplices,
                    (∃ v, s₁ v = true ∧ s₂ v = true) →
                    ∃ s' ∈ simplices, ∀ v, s' v = (s₁ v && s₂ v)
  distinctVerts : ∀ v₁ v₂ : Fin nVertices, v₁ ≠ v₂ →
                    ∃ j, coord v₁ j ≠ coord v₂ j

  cellsWF       : ∀ c ∈ cells, c.1 ∈ simplices ∧
                    (∀ v, c.2 v = true → c.1 v = true) ∧
                    (∃ v, c.1 v = true ∧ c.2 v = false)

structure Simplex where
  complex  : SimpC
  contains : Fin complex.nVertices → Bool
  nonempty : ∃ v, contains v = true

structure ExtensionSet where
  simplex  : Simplex
  contains : Fin simplex.complex.nVertices → Bool
  scope    : ∀ v, contains v = true → simplex.contains v = true
  proper   : ∃ v, simplex.contains v = true ∧ contains v = false

abbrev Wire := Nat

structure ContractPattern (inputRanks : List Nat) (outputRank : Nat) where
  nIndices      : Nat
  indexExtent   : Fin nIndices → Nat
  inputBinding  : (i : Fin inputRanks.length) → Fin (inputRanks.get i) → Fin nIndices
  outputBinding : Fin outputRank → Fin nIndices

inductive PrimApp where
  | const     (ty : TensorType) (c : TensorValue ty) (out : Wire)
  | contract  (δ : Dtype) (r : RoundMode)
              (inputs : List Wire) (output : Wire)
              (inputRanks : List Nat) (outputRank : Nat)
              (pat : ContractPattern inputRanks outputRank)
  | cast      (δfrom δto : Dtype) (r : RoundMode)
              (shape : Shape) (input output : Wire)
  | cell      (schema : SimpC) (input : Wire) (outputs : List Wire)
  | reshape   (newShape : Shape) (input output : Wire)
  | broadcast (toShape : Shape) (input output : Wire)
  | copy      (k : Nat) (input : Wire) (outputs : List Wire)
  | delete    (input : Wire)
  | swap      (in1 in2 out1 out2 : Wire)

  | stack     (k : Nat) (shape : Shape) (inputs : List Wire) (output : Wire)

  | relu      (shape : Shape) (input output : Wire)

  | ppoly     (nvars : Nat) (coeffs : MonoTable)
              (inputs : List Wire) (output : Wire)

  | pderiv    (shape : Shape) (axis : Nat) (input output : Wire)

  | facet     (shape : Shape) (axis : Nat) (hi : Bool) (input output : Wire)

namespace PrimApp

def inputWires : PrimApp → List Wire
  | .const _ _ _              => []
  | .contract _ _ ins _ _ _ _ => ins
  | .cast _ _ _ _ i _         => [i]
  | .cell _ i _               => [i]
  | .reshape _ i _            => [i]
  | .broadcast _ i _          => [i]
  | .copy _ i _               => [i]
  | .delete i                 => [i]
  | .swap i1 i2 _ _           => [i1, i2]
  | .stack _ _ ins _          => ins
  | .relu _ i _               => [i]
  | .ppoly _ _ ins _          => ins
  | .pderiv _ _ i _           => [i]
  | .facet _ _ _ i _          => [i]

def outputWires : PrimApp → List Wire
  | .const _ _ o              => [o]
  | .contract _ _ _ o _ _ _   => [o]
  | .cast _ _ _ _ _ o         => [o]
  | .cell _ _ outs            => outs
  | .reshape _ _ o            => [o]
  | .broadcast _ _ o          => [o]
  | .copy _ _ outs            => outs
  | .delete _                 => []
  | .swap _ _ o1 o2           => [o1, o2]
  | .stack _ _ _ o            => [o]
  | .relu _ _ o               => [o]
  | .ppoly _ _ _ o            => [o]
  | .pderiv _ _ _ o           => [o]
  | .facet _ _ _ _ o          => [o]

end PrimApp

def Shape.broadcastsTo (src dst : Shape) : Prop :=
  src.length ≤ dst.length ∧
  ∀ i : Fin src.length,
    src.getD (src.length - 1 - i.val) 1 = dst.getD (dst.length - 1 - i.val) 1
    ∨ src.getD (src.length - 1 - i.val) 1 = 1

def Linearity (apps : List PrimApp) : Prop :=
  (apps.flatMap PrimApp.inputWires).Nodup ∧
  (apps.flatMap PrimApp.outputWires).Nodup

def Acyclic (apps : List PrimApp) : Prop :=
  ∀ i : Fin apps.length, ∀ w ∈ apps[i].inputWires,
    ∀ j : Fin apps.length, w ∈ apps[j].outputWires → j < i

def PrimApp.TypeConsistent (wt : Wire → Option TensorType) : PrimApp → Prop
  | .const ty _ out => wt out = some ty
  | .contract δ _ inputs output inputRanks outputRank pat =>
      inputs.length = inputRanks.length ∧
      (∀ p ∈ inputs.zip inputRanks,
        ∃ τ, wt p.1 = some τ ∧ τ.dtype = δ ∧ τ.shape.rank = p.2) ∧
      (∃ τ, wt output = some τ ∧ τ.dtype = δ ∧ τ.shape.rank = outputRank) ∧
      (∀ i : Fin inputRanks.length, ∀ a : Fin (inputRanks.get i),
        ∃ τ, wt (inputs.getD i.val 0) = some τ ∧
             τ.shape.getD a.val 0 = pat.indexExtent (pat.inputBinding i a)) ∧
      (∀ a : Fin outputRank,
        ∃ τ, wt output = some τ ∧
             τ.shape.getD a.val 0 = pat.indexExtent (pat.outputBinding a))
  | .cast δfrom δto _ shape input output =>
      wt input = some ⟨shape, δfrom⟩ ∧ wt output = some ⟨shape, δto⟩
  | .cell schema input outputs =>
      (∃ δ, wt input = some ⟨[schema.ambDim], δ⟩) ∧
      outputs.length = schema.cells.length ∧
      (∀ o ∈ outputs, wt o = some ⟨[], Dtype.B⟩)
  | .reshape newShape input output =>
      ∃ τ, wt input = some τ ∧ τ.shape.totalSize = newShape.totalSize ∧
           wt output = some ⟨newShape, τ.dtype⟩
  | .broadcast toShape input output =>
      ∃ τ, wt input = some τ ∧ τ.shape.broadcastsTo toShape ∧
           wt output = some ⟨toShape, τ.dtype⟩
  | .copy k input outputs =>
      outputs.length = k ∧
      ∃ τ, wt input = some τ ∧ ∀ o ∈ outputs, wt o = some τ
  | .delete input => (wt input).isSome
  | .swap in1 in2 out1 out2 =>
      (wt in1).isSome ∧ (wt in2).isSome ∧ wt out1 = wt in2 ∧ wt out2 = wt in1

  | .stack k shape inputs output =>
      inputs.length = k ∧
      ∃ τ, wt output = some τ ∧ τ.shape = k :: shape ∧
        ∀ w ∈ inputs, wt w = some ⟨shape, τ.dtype⟩

  | .relu shape input output =>
      ∃ τ, wt input = some τ ∧ wt output = some τ ∧ τ.shape = shape

  | .ppoly nvars _coeffs inputs output =>
      inputs.length = nvars ∧
      (∀ w ∈ inputs, wt w = some ⟨[], Dtype.Q⟩) ∧
      wt output = some ⟨[], Dtype.Q⟩

  | .pderiv shape _axis input output =>
      ∃ τ, wt input = some τ ∧ wt output = some τ ∧ τ.shape = shape

  | .facet shape axis _hi input output =>
      ∃ τ, wt input = some τ ∧ τ.shape = shape ∧
           wt output = some ⟨shape.eraseIdx axis, τ.dtype⟩

def TypeConsistentAll (wt : Wire → Option TensorType)
    (apps : List PrimApp) : Prop :=
  ∀ app ∈ apps, app.TypeConsistent wt

structure Hypernet where
  wireType       : Wire → Option TensorType
  applications   : List PrimApp
  linearity      : Linearity applications
  acyclic        : Acyclic applications
  typeConsistent : TypeConsistentAll wireType applications

instance : Inhabited Hypernet :=
  ⟨{ wireType := fun _ => none
     applications := []
     linearity := ⟨List.nodup_nil, List.nodup_nil⟩
     acyclic := fun i => i.elim0
     typeConsistent := fun _ h => nomatch h }⟩

inductive Term where
  | var   (w : Wire)
  | const (c : Rat)
  | add   (l r : Term)
  | mul   (l r : Term)
  | sub   (l r : Term)
  | neg   (t : Term)

  | idx   (t : Term) (i : Nat)
  deriving Repr, DecidableEq

inductive BowTie where | lt | le | eq | ge | gt | ne deriving DecidableEq, Repr

inductive Formula where
  | atom     (b : BowTie) (l r : Term)
  | inRegion (t : Term) (simplex : Simplex) (S : ExtensionSet)
  | and      (l r : Formula)
  | or       (l r : Formula)
  | tt
  | ff

abbrev Formula.atomLE (l r : Term) : Formula := .atom .le l r
abbrev Formula.atomLT (l r : Term) : Formula := .atom .lt l r
abbrev Formula.atomEQ (l r : Term) : Formula := .atom .eq l r
abbrev Formula.atomGE (l r : Term) : Formula := .atom .ge l r
abbrev Formula.atomGT (l r : Term) : Formula := .atom .gt l r
abbrev Formula.atomNE (l r : Term) : Formula := .atom .ne l r

instance : DecidableEq SimpC := fun a b => by
  obtain ⟨nv, ad, co, si, ce, _, _, _, _, _⟩ := a
  obtain ⟨nv', ad', co', si', ce', _, _, _, _, _⟩ := b
  refine if h1 : nv = nv' then ?_ else isFalse fun h => h1 (by injection h)
  subst h1
  refine if h2 : ad = ad' then ?_ else isFalse fun h => h2 (by injection h)
  subst h2
  refine if h3 : co = co' then ?_ else isFalse fun h => h3 (by injection h)
  subst h3
  refine if h4 : si = si' then ?_ else isFalse fun h => h4 (by injection h)
  subst h4
  refine if h5 : ce = ce' then ?_ else isFalse fun h => h5 (by injection h)
  subst h5
  exact isTrue rfl

instance : DecidableEq Simplex := fun a b => by
  obtain ⟨c, f, _⟩ := a
  obtain ⟨c', f', _⟩ := b
  refine if h1 : c = c' then ?_ else isFalse fun h => h1 (by injection h)
  subst h1
  refine if h2 : f = f' then ?_ else isFalse fun h => h2 (by injection h)
  subst h2
  exact isTrue rfl

instance : DecidableEq ExtensionSet := fun a b => by
  obtain ⟨s, f, _, _⟩ := a
  obtain ⟨s', f', _, _⟩ := b
  refine if h1 : s = s' then ?_ else isFalse fun h => h1 (by injection h)
  subst h1
  refine if h2 : f = f' then ?_ else isFalse fun h => h2 (by injection h)
  subst h2
  exact isTrue rfl

deriving instance DecidableEq for Formula

def Simplex.containsNat (s : Simplex) (v : Nat) : Bool :=
  if h : v < s.complex.nVertices then s.contains ⟨v, h⟩ else false

def ExtensionSet.containsNat (S : ExtensionSet) (v : Nat) : Bool :=
  if h : v < S.simplex.complex.nVertices then S.contains ⟨v, h⟩ else false

def Formula.chainAnd : List Formula → Formula
  | [] => .tt
  | [f] => f
  | f :: rest => .and f (chainAnd rest)

def Formula.chainOr : List Formula → Formula
  | [] => .ff
  | [f] => f
  | f :: rest => .or f (chainOr rest)

def Term.toPoly : Term → QArith.Poly
  | .var w => QArith.Poly.var w
  | .const c => QArith.Poly.const c
  | .add l r => QArith.Poly.add l.toPoly r.toPoly
  | .mul l r => QArith.Poly.mul l.toPoly r.toPoly
  | .sub l r => QArith.Poly.sub l.toPoly r.toPoly
  | .neg t => QArith.Poly.neg t.toPoly

  | .idx _ _ => QArith.Poly.const 0

def Term.evalQ? : Term → Option Rat
  | .var _ => none
  | .const c => some c
  | .add l r => do pure ((← l.evalQ?) + (← r.evalQ?))
  | .mul l r => do pure ((← l.evalQ?) * (← r.evalQ?))
  | .sub l r => do pure ((← l.evalQ?) - (← r.evalQ?))
  | .neg t => do pure (-(← t.evalQ?))
  | .idx _ _ => none

def BowTie.evalQ : BowTie → Rat → Rat → Bool
  | .lt, x, y => decide (x < y)
  | .le, x, y => decide (x ≤ y)
  | .eq, x, y => decide (x = y)
  | .ge, x, y => decide (y ≤ x)
  | .gt, x, y => decide (y < x)
  | .ne, x, y => decide (¬ x = y)

def Formula.evalClosed : Formula → Option Bool
  | .atom b l r => do pure (b.evalQ (← l.evalQ?) (← r.evalQ?))
  | .inRegion _ _ _ => none
  | .and l r => do pure ((← l.evalClosed) && (← r.evalClosed))
  | .or l r => do pure ((← l.evalClosed) || (← r.evalClosed))
  | .tt => some true
  | .ff => some false

def baryLambdas1D (cx : SimpC) (dContains : Fin cx.nVertices → Bool)
    (t : Term) : Option (List (Fin cx.nVertices × Term)) :=
  if h : cx.ambDim = 1 then
    let j0 : Fin cx.ambDim := ⟨0, by omega⟩
    match (List.finRange cx.nVertices).filter (fun v => dContains v) with
    | [a, b] =>
      let V₀ := cx.coord a j0
      let V₁ := cx.coord b j0
      if V₀ = V₁ then none
      else
        let den := V₁ - V₀
        let lam := fun (c s : Rat) => Term.add (.const c) (.mul (.const s) t)
        some [(a, lam (V₁ / den) (-1 / den)), (b, lam (-V₀ / den) (1 / den))]
    | _ => none
  else none

def Term.freeWires : Term → List Wire
  | .var w => [w]
  | .const _ => []
  | .add l r | .mul l r | .sub l r => l.freeWires ++ r.freeWires
  | .neg t => t.freeWires
  | .idx t _ => t.freeWires

def Term.idxFree : Term → Bool
  | .var _ | .const _ => true
  | .add l r | .mul l r | .sub l r => l.idxFree && r.idxFree
  | .neg t => t.idxFree
  | .idx _ _ => false

def Term.idxBounded (n : Nat) : Term → Bool
  | .var _ | .const _ => true
  | .add l r | .mul l r | .sub l r => l.idxBounded n && r.idxBounded n
  | .neg t => t.idxBounded n
  | .idx t i => decide (i < n) && t.idxBounded n

def Formula.freeWires : Formula → List Wire
  | .atom _ l r => l.freeWires ++ r.freeWires
  | .inRegion t _ _ => t.freeWires
  | .and l r | .or l r => l.freeWires ++ r.freeWires
  | .tt | .ff => []

def Term.type (H : Hypernet) : Term → Option TensorType
  | .var w => H.wireType w
  | .const _ => some ⟨[], Dtype.Q⟩
  | .idx t i =>

    match Term.type H t with
    | some τ =>
      match τ.shape with
      | [e] => if i < e then some ⟨[], τ.dtype⟩ else none
      | _ => none
    | none => none
  | .add l r | .mul l r | .sub l r =>
    match Term.type H l, Term.type H r with
    | some τ₁, some τ₂ => if τ₁ = τ₂ then some τ₁ else none
    | _, _ => none
  | .neg t => Term.type H t

def Formula.WellTyped (H : Hypernet) : Formula → Prop
  | .atom _ l r => ∃ τ, l.type H = some τ ∧ r.type H = some τ
  | .inRegion t simplex S =>
      (∃ τ, t.type H = some τ ∧ τ.shape = [simplex.complex.ambDim]) ∧
      S.simplex = simplex
  | .and l r => l.WellTyped H ∧ r.WellTyped H
  | .or l r  => l.WellTyped H ∧ r.WellTyped H
  | .tt      => True
  | .ff      => True

def Term.bshape (H : Hypernet) : Term → Option Shape
  | .var w => (H.wireType w).map (·.shape)
  | .const _ => some []
  | .add l r | .mul l r | .sub l r =>
    match l.bshape H, r.bshape H with
    | some s₁, some s₂ =>
      if s₁ = s₂ then some s₁
      else if s₁ = [] then some s₂
      else if s₂ = [] then some s₁
      else none
    | _, _ => none
  | .neg t => t.bshape H
  | .idx t i =>

    match t.bshape H with
    | some [e] => if i < e then some [] else none
    | _ => none

def Term.finWires (H : Hypernet) (t : Term) : Prop :=
  ∀ w ∈ t.freeWires, ∃ τ, H.wireType w = some τ ∧ τ.dtype.ext = Ext.fin

def Term.varHead? : Term → Option Wire
  | .var w => some w
  | _ => none

theorem Term.varHead?_eq_some {t : Term} {w : Wire} :
    t.varHead? = some w ↔ t = .var w := by
  cases t <;> simp [Term.varHead?]

structure Sequent where
  pre  : Formula
  post : Formula

def Sequent.wellScoped (H : Hypernet) (seq : Sequent) : Prop :=
  ∀ w, (w ∈ seq.pre.freeWires ∨ w ∈ seq.post.freeWires) → (H.wireType w).isSome

def atomicCompareForm (b : BowTie) (l r : Term) (F : Formula) : Prop :=
  F = .atom b l r

def atomicCompareZero (b : BowTie) (l r : Term) (F : Formula) : Prop :=
  F = .atom b (.sub l r) (.const 0)

def syzygyConclusionForm (conclusion : Term) (F : Formula) : Prop :=
  F = .atom .le conclusion (.const 0)
  ∨ (∃ e, conclusion = .neg e ∧ F = .atom .ge e (.const 0))
  ∨ (∃ l r, conclusion = .sub l r ∧ F = .atom .le l r)

def Term.subst (w : Wire) (t : Term) : Term → Term
  | .var w' => if w' = w then t else .var w'
  | .const c => .const c
  | .add l r => .add (Term.subst w t l) (Term.subst w t r)
  | .mul l r => .mul (Term.subst w t l) (Term.subst w t r)
  | .sub l r => .sub (Term.subst w t l) (Term.subst w t r)
  | .neg u => .neg (Term.subst w t u)
  | .idx u i => .idx (Term.subst w t u) i

def Formula.subst (w : Wire) (t : Term) : Formula → Formula
  | .atom b l r => .atom b (Term.subst w t l) (Term.subst w t r)
  | .inRegion u simplex S => .inRegion (Term.subst w t u) simplex S
  | .and l r => .and (Formula.subst w t l) (Formula.subst w t r)
  | .or l r => .or (Formula.subst w t l) (Formula.subst w t r)
  | .tt => .tt
  | .ff => .ff

def substituteInFormula (F : Formula) (w : Wire) (t : Term) (F' : Formula) : Prop :=
  F' = F.subst w t

def baryCoeffs1D (cx : SimpC) (dContains : Fin cx.nVertices → Bool) :
    Option (List (Fin cx.nVertices × Rat × Rat)) :=
  if h : cx.ambDim = 1 then
    let j0 : Fin cx.ambDim := ⟨0, by omega⟩
    match (List.finRange cx.nVertices).filter (fun v => dContains v) with
    | [a, b] =>
      let V₀ := cx.coord a j0
      let V₁ := cx.coord b j0
      if V₀ = V₁ then none
      else
        let den := V₁ - V₀
        some [(a, V₁ / den, -1 / den), (b, -V₀ / den, 1 / den)]
    | _ => none
  else none

def primAffine (s c : Rat) : Rat × Rat :=
  if c = 0 then
    (if s < 0 then -1 else if s = 0 then 0 else 1, 0)
  else
    let L : Nat := Nat.lcm s.den c.den
    let g : Nat := Int.gcd (s.num * (L / s.den : Nat)) (c.num * (L / c.den : Nat))
    let k : Rat := (L : Rat) / (g : Rat)
    (k * s, k * c)

def f4Lhs (s' c' : Rat) (t : Term) : Term :=
  if c' = 0 then .mul (.const s') t
  else .add (.mul (.const s') t) (.const c')

def f4VertexAtom (inS : Bool) (off slp : Rat) (t : Term) : Formula :=
  let sc := if inS then primAffine slp off else primAffine (-slp) (-off)
  .atom .le (f4Lhs sc.1 sc.2 t) (.const 0)

def barycentricHalfspaceBuild (t : Term) (simplex : Simplex)
    (S : ExtensionSet) : Option Formula := do
  guard (S.simplex = simplex)
  let cs ← baryCoeffs1D simplex.complex simplex.contains
  match cs.map (fun (v, off, slp) =>
    f4VertexAtom (S.containsNat v.val) off slp t) with
  | [x, y] => some (.and x y)
  | _ => none

def barycentricHalfspaceForm (t : Term) (simplex : Simplex)
    (S : ExtensionSet) (F : Formula) : Prop :=
  barycentricHalfspaceBuild t simplex S = some F

def predicateHole : Wire := 4294967295

def applyPredicateToTerm (P : Formula) (arg : Term) (F : Formula) : Prop :=
  F = P.subst predicateHole arg

structure PredClass where
  conic : Bool
  upClosed : Bool
  deriving DecidableEq, Repr

def parseHoleSide : Term → Option Rat
  | .var w => if w = predicateHole then some 1 else none
  | .mul (.const a) (.var w) =>
    if w = predicateHole ∧ 0 < a then some a else none
  | .mul (.var w) (.const a) =>
    if w = predicateHole ∧ 0 < a then some a else none
  | _ => none

def classifyPredAtom : Formula → Option PredClass
  | .atom b l r =>
    let oriented : Option (BowTie × Rat) :=
      match parseHoleSide l, r.evalQ? with
      | some _, some c => some (b, c)
      | _, _ =>
        match parseHoleSide r, l.evalQ? with
        | some _, some c =>
          let b' : BowTie := match b with
            | .lt => .gt | .le => .ge | .ge => .le | .gt => .lt
            | .eq => .eq | .ne => .ne
          some (b', c)
        | _, _ => none
    match oriented with
    | some (.ge, c) => some ⟨c = 0, true⟩
    | some (.le, c) => some ⟨c = 0, false⟩
    | some (.eq, c) => if c = 0 then some ⟨true, false⟩ else none
    | _ => none
  | _ => none

def classifyPred : Formula → Option PredClass
  | .and l r => do
    let a ← classifyPred l
    let b ← classifyPred r
    pure ⟨a.conic && b.conic, a.upClosed && b.upClosed⟩
  | f => classifyPredAtom f

def isConicPredicate (P : Formula) : Prop :=
  (classifyPred P).map (·.conic) = some true
def isConvexPredicate (P : Formula) : Prop :=
  (classifyPred P).isSome
def isUpwardClosedConicPredicate (P : Formula) : Prop :=
  (classifyPred P).map (fun c => c.conic && c.upClosed) = some true

def isExtensionSetEmpty (S : ExtensionSet) : Prop :=
  ∀ v, S.contains v = false

def ExtensionSet.isEmptyB (S : ExtensionSet) : Bool :=
  (List.finRange S.simplex.complex.nVertices).all (fun v => !S.contains v)

theorem ExtensionSet.isEmptyB_iff (S : ExtensionSet) :
    S.isEmptyB = true ↔ isExtensionSetEmpty S := by
  unfold ExtensionSet.isEmptyB isExtensionSetEmpty
  rw [List.all_eq_true]
  constructor
  · intro h v
    simpa using h v (List.mem_finRange v)
  · intro h v _
    rw [h v]
    rfl

def polynomialCanonicalEq (l r : Term) : Prop :=
  l.idxFree = true ∧ r.idxFree = true ∧ l.toPoly = r.toPoly

def satisfiesPredQ (P : Formula) (c : Rat) : Bool :=
  (Formula.subst predicateHole (.const c) P).evalClosed = some true

def Term.asCoordPolyIdx? : Term → Option QArith.Poly
  | .var _ => none
  | .const c => some (QArith.Poly.const c)
  | .add l r =>
    do pure (QArith.Poly.add (← l.asCoordPolyIdx?) (← r.asCoordPolyIdx?))
  | .mul l r =>
    do pure (QArith.Poly.mul (← l.asCoordPolyIdx?) (← r.asCoordPolyIdx?))
  | .sub l r =>
    do pure (QArith.Poly.sub (← l.asCoordPolyIdx?) (← r.asCoordPolyIdx?))
  | .neg t => (Term.asCoordPolyIdx? t).map QArith.Poly.neg
  | .idx (.var _) i => some (QArith.Poly.var i)
  | .idx _ _ => none

def Term.asCoordPoly? (t : Term) : Option QArith.Poly :=
  if t.idxFree then
    let p := t.toPoly
    match QArith.Poly.vars p with
    | [] => some p
    | [_] => some (p.map fun (m, c) => (m.map fun (_, e) => (0, e), c))
    | _ => none
  else
    t.asCoordPolyIdx?

def bernConeCoeffCheck (simplex : Simplex) (S : ExtensionSet) (degree : Nat)
    (polynomial : Term) (predicate : Formula) : Bool :=
  if S.simplex = simplex then
    let cx := simplex.complex
    let verts := (List.finRange cx.nVertices).filter (fun v => simplex.contains v)

    if verts.length = cx.ambDim + 1 then
      match Term.asCoordPoly? polynomial with
      | none => false
      | some p =>
        if polynomial.idxFree then

          if QArith.Poly.vars p ≠ [] ∧ cx.ambDim ≠ 1 then false
          else
            let coords := verts.map fun v =>
              (List.finRange cx.ambDim).map fun j => cx.coord v j
            let smask := verts.map fun v => S.containsNat v.val
            match QArith.fdBernstein coords smask degree p with
            | some table => QArith.gridAll (satisfiesPredQ predicate) table
            | none => false
        else

          if S.isEmptyB ∧ polynomial.idxBounded cx.ambDim then
            let coords := verts.map fun v =>
              (List.finRange cx.ambDim).map fun j => cx.coord v j
            let smask := verts.map fun v => S.containsNat v.val
            match QArith.fdBernstein coords smask degree p with
            | some table => QArith.gridAll (satisfiesPredQ predicate) table
            | none => false
          else false
    else false
  else false

def allForwardDiffBernCoeffsSatisfyP
    (simplex : Simplex) (S : ExtensionSet) (degree : Nat)
    (polynomial : Term) (predicate : Formula) : Prop :=
  bernConeCoeffCheck simplex S degree polynomial predicate = true

def Formula.conjunctList : Formula → List Formula
  | .and l r => l.conjunctList ++ r.conjunctList
  | f => [f]

def atomLeZeroPolys : Formula → List QArith.Poly
  | .atom .le l r => [QArith.Poly.sub l.toPoly r.toPoly]
  | .atom .lt l r => [QArith.Poly.sub l.toPoly r.toPoly]
  | .atom .ge l r => [QArith.Poly.sub r.toPoly l.toPoly]
  | .atom .gt l r => [QArith.Poly.sub r.toPoly l.toPoly]
  | .atom .eq l r => [QArith.Poly.sub l.toPoly r.toPoly,
                      QArith.Poly.sub r.toPoly l.toPoly]
  | _ => []

def farkasEntries : Term → Option (List (Rat × Term))
  | .const c => if c = 0 then some [] else none
  | .add (.mul (.const l) e) rest =>
    (farkasEntries rest).map ((l, e) :: ·)
  | _ => none

def wireCoordKey (w i : Nat) : Nat :=
  if w < i then i * i + w else w * w + w + i

def Term.asCoordPolyIdxW? : Term → Option QArith.Poly
  | .var _ => none
  | .const c => some (QArith.Poly.const c)
  | .add l r =>
    do pure (QArith.Poly.add (← l.asCoordPolyIdxW?) (← r.asCoordPolyIdxW?))
  | .mul l r =>
    do pure (QArith.Poly.mul (← l.asCoordPolyIdxW?) (← r.asCoordPolyIdxW?))
  | .sub l r =>
    do pure (QArith.Poly.sub (← l.asCoordPolyIdxW?) (← r.asCoordPolyIdxW?))
  | .neg t => (Term.asCoordPolyIdxW? t).map QArith.Poly.neg
  | .idx (.var w) i => some (QArith.Poly.var (wireCoordKey w i))
  | .idx _ _ => none

def atomLeZeroPolysW : Formula → List QArith.Poly
  | .atom op l r =>
    match l.asCoordPolyIdxW? with
    | none => []
    | some pl =>
      match r.asCoordPolyIdxW? with
      | none => []
      | some pr =>
        match op with
        | .le | .lt => [QArith.Poly.sub pl pr]
        | .ge | .gt => [QArith.Poly.sub pr pl]
        | .eq => [QArith.Poly.sub pl pr, QArith.Poly.sub pr pl]
        | .ne => []
  | _ => []

def farkasEntriesW : List (Rat × Term) → Option (List (Rat × QArith.Poly))
  | [] => some []
  | (l, e) :: rest =>
    match e.asCoordPolyIdxW?, farkasEntriesW rest with
    | some pe, some prest => some ((l, pe) :: prest)
    | _, _ => none

def farkasCheckW (cc : Term) (premise : Formula) (conclusion : Term) : Bool :=
  match farkasEntries cc with
  | none => false
  | some entries =>
    match farkasEntriesW entries with
    | none => false
    | some pentries =>
      match conclusion.asCoordPolyIdxW? with
      | none => false
      | some pc =>
        let atoms := premise.conjunctList
        pentries.all (fun le =>
          decide (0 ≤ le.1) &&
          atoms.any fun a =>
            (atomLeZeroPolysW a).any fun pa => decide (pa = le.2)) &&
        decide ((pentries.foldr
            (fun le acc => QArith.Poly.add (QArith.Poly.scale le.1 le.2) acc)
            []) = pc)

def Term.asCoordPolyMixed? : Term → Option QArith.Poly
  | .var w => some (QArith.Poly.var (2 * w))
  | .const c => some (QArith.Poly.const c)
  | .add l r =>
    do pure (QArith.Poly.add (← l.asCoordPolyMixed?) (← r.asCoordPolyMixed?))
  | .mul l r =>
    do pure (QArith.Poly.mul (← l.asCoordPolyMixed?) (← r.asCoordPolyMixed?))
  | .sub l r =>
    do pure (QArith.Poly.sub (← l.asCoordPolyMixed?) (← r.asCoordPolyMixed?))
  | .neg t => (Term.asCoordPolyMixed? t).map QArith.Poly.neg
  | .idx (.var w) j => some (QArith.Poly.var (2 * wireCoordKey w j + 1))
  | .idx _ _ => none

def atomLeZeroPolysM : Formula → List QArith.Poly
  | .atom op l r =>
    match l.asCoordPolyMixed? with
    | none => []
    | some pl =>
      match r.asCoordPolyMixed? with
      | none => []
      | some pr =>
        match op with
        | .le | .lt => [QArith.Poly.sub pl pr]
        | .ge | .gt => [QArith.Poly.sub pr pl]
        | .eq => [QArith.Poly.sub pl pr, QArith.Poly.sub pr pl]
        | .ne => []
  | _ => []

def farkasEntriesM : List (Rat × Term) → Option (List (Rat × QArith.Poly))
  | [] => some []
  | (l, e) :: rest =>
    match e.asCoordPolyMixed?, farkasEntriesM rest with
    | some pe, some prest => some ((l, pe) :: prest)
    | _, _ => none

def farkasCheckM (cc : Term) (premise : Formula) (conclusion : Term) : Bool :=
  match farkasEntries cc with
  | none => false
  | some entries =>
    match farkasEntriesM entries with
    | none => false
    | some pentries =>
      match conclusion.asCoordPolyMixed? with
      | none => false
      | some pc =>
        let atoms := premise.conjunctList
        pentries.all (fun le =>
          decide (0 ≤ le.1) &&
          atoms.any fun a =>
            (atomLeZeroPolysM a).any fun pa => decide (pa = le.2)) &&
        decide ((pentries.foldr
            (fun le acc => QArith.Poly.add (QArith.Poly.scale le.1 le.2) acc)
            []) = pc)

def Formula.atomSidesIdxFree : Formula → Bool
  | .atom _ l r => l.idxFree && r.idxFree
  | _ => true

def farkasCheckCore (cc : Term) (premise : Formula) (conclusion : Term) : Bool :=
  match farkasEntries cc with
  | none => false
  | some entries =>
    let atoms := premise.conjunctList
    conclusion.idxFree &&
    entries.all (fun (l, e) =>
      decide (0 ≤ l) &&
      atoms.any fun a =>
        a.atomSidesIdxFree &&
        (atomLeZeroPolys a).any fun pa => decide (pa = e.toPoly)) &&
    decide ((entries.foldr
        (fun (l, e) acc => QArith.Poly.add (QArith.Poly.scale l e.toPoly) acc)
        []) = conclusion.toPoly)

def farkasCheck (cc : Term) (premise : Formula) (conclusion : Term) : Bool :=
  farkasCheckCore cc premise conclusion || farkasCheckW cc premise conclusion ||
  farkasCheckM cc premise conclusion

def farkasCombinationValid (cc : Term) (premise : Formula)
    (conclusion : Term) : Prop :=
  farkasCheck cc premise conclusion = true

inductive ConjPath where
  | here
  | left  (rest : ConjPath)
  | right (rest : ConjPath)
  deriving DecidableEq, Repr

def Formula.conjGet? (f : Formula) : ConjPath → Option Formula
  | .here => some f
  | .left p =>
    match f with
    | .and l _ => l.conjGet? p
    | _ => none
  | .right p =>
    match f with
    | .and _ r => r.conjGet? p
    | _ => none

def Formula.conjReplace? (f : Formula) : ConjPath → Formula → Option Formula
  | .here, g => some g
  | .left p, g =>
    match f with
    | .and l r => (l.conjReplace? p g).map (fun l' => .and l' r)
    | _ => none
  | .right p, g =>
    match f with
    | .and l r => (r.conjReplace? p g).map (fun r' => .and l r')
    | _ => none

def premiseContains (pre sub : Formula) : Prop :=
  ∀ a ∈ sub.conjunctList, a ∈ pre.conjunctList

def formulaWiresWithin (f : Formula) (iface : List Wire) : Prop :=
  ∀ w ∈ f.freeWires, w ∈ iface

def wiresSeparated (left ctx post : Formula) (iface : List Wire) : Prop :=
  ∀ w ∈ left.freeWires,
    (w ∈ ctx.freeWires ∨ w ∈ post.freeWires) → w ∈ iface

def Formula.isEqAtom : Formula → Bool
  | .atom .eq _ _ => true
  | _ => false

def syzygyCheckCore (cc : Term) (components : List Sequent) (premise : Formula)
    (conclusion : Term) : Bool :=
  match farkasEntries cc with
  | none => false
  | some entries =>
    conclusion.idxFree &&
    entries.all (fun (l, e) =>
      decide (0 ≤ l) &&
      ((components.any fun c =>
          c.post.atomSidesIdxFree &&
          ((atomLeZeroPolys c.post).any fun pa => decide (pa = e.toPoly))) ||
       (premise.conjunctList.any fun a =>
          a.isEqAtom && a.atomSidesIdxFree &&
          ((atomLeZeroPolys a).any fun pa => decide (pa = e.toPoly))))) &&
    decide ((entries.foldr
        (fun (l, e) acc => QArith.Poly.add (QArith.Poly.scale l e.toPoly) acc)
        []) = conclusion.toPoly)

def syzygyCheckW (cc : Term) (components : List Sequent) (premise : Formula)
    (conclusion : Term) : Bool :=
  match farkasEntries cc with
  | none => false
  | some entries =>
    match farkasEntriesW entries with
    | none => false
    | some pentries =>
      match conclusion.asCoordPolyIdxW? with
      | none => false
      | some pc =>
        pentries.all (fun le =>
          decide (0 ≤ le.1) &&
          ((components.any fun c =>
              (atomLeZeroPolysW c.post).any fun pa => decide (pa = le.2)) ||
           (premise.conjunctList.any fun a =>
              a.isEqAtom &&
              ((atomLeZeroPolysW a).any fun pa => decide (pa = le.2))))) &&
        decide ((pentries.foldr
            (fun le acc => QArith.Poly.add (QArith.Poly.scale le.1 le.2) acc)
            []) = pc)

def syzygyCheckM (cc : Term) (components : List Sequent) (premise : Formula)
    (conclusion : Term) : Bool :=
  match farkasEntries cc with
  | none => false
  | some entries =>
    match farkasEntriesM entries with
    | none => false
    | some pentries =>
      match conclusion.asCoordPolyMixed? with
      | none => false
      | some pc =>
        pentries.all (fun le =>
          decide (0 ≤ le.1) &&
          ((components.any fun c =>
              (atomLeZeroPolysM c.post).any fun pa => decide (pa = le.2)) ||
           (premise.conjunctList.any fun a =>
              a.isEqAtom &&
              ((atomLeZeroPolysM a).any fun pa => decide (pa = le.2))))) &&
        decide ((pentries.foldr
            (fun le acc => QArith.Poly.add (QArith.Poly.scale le.1 le.2) acc)
            []) = pc)

def syzygyCheck (cc : Term) (components : List Sequent) (premise : Formula)
    (conclusion : Term) : Bool :=
  syzygyCheckCore cc components premise conclusion ||
  syzygyCheckW cc components premise conclusion ||
  syzygyCheckM cc components premise conclusion

def syzygyCombinationValid (cc : Term) (components : List Sequent)
    (premise : Formula) (conclusion : Term) : Prop :=
  syzygyCheck cc components premise conclusion = true

namespace PsdCert

def qlsum (l : List Rat) : Rat := l.foldr (· + ·) 0

def qabs (q : Rat) : Rat := if q < 0 then -q else q

def finQSum (n : Nat) (f : Fin n → Rat) : Rat := qlsum ((List.finRange n).map f)

def mulEntry (n : Nat) (A B : Fin n → Fin n → Rat) (i j : Fin n) : Rat :=
  finQSum n (fun k => A i k * B k j)

def symB (n : Nat) (A : Fin n → Fin n → Rat) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    decide (A i j = A j i)

def upperTriPosDiagB (n : Nat) (Z : Fin n → Fin n → Rat) : Bool :=
  ((List.finRange n).all fun i => (List.finRange n).all fun j =>
    decide (j < i → Z i j = 0)) &&
  ((List.finRange n).all fun i => decide (0 < Z i i))

def checkT (n : Nat) (A Z : Fin n → Fin n → Rat) : Bool :=
  symB n A && upperTriPosDiagB n Z &&
  ((List.finRange n).all fun i => (List.finRange n).all fun j =>
    decide (i < j → mulEntry n A Z i j = 0)) &&
  ((List.finRange n).all fun i => decide (0 < mulEntry n A Z i i))

def congEntry (n : Nat) (A Z : Fin n → Fin n → Rat) (i j : Fin n) : Rat :=
  finQSum n (fun k => Z k i * mulEntry n A Z k j)

def checkDD (n : Nat) (A Z : Fin n → Fin n → Rat) : Bool :=
  symB n A && upperTriPosDiagB n Z &&
  ((List.finRange n).all fun i =>
    decide (finQSum n (fun j => if j = i then 0 else qabs (congEntry n A Z i j))
            < congEntry n A Z i i))

def kernelExt (m k : Nat) (N : Fin m → Fin k → Rat) (a : Fin m)
    (j : Fin (m + k)) : Rat :=
  if h : j.val < m then (if a.val = j.val then 1 else 0)
  else N a ⟨j.val - m, by have := j.isLt; omega⟩

def checkK (m k : Nat) (A : Fin (m + k) → Fin (m + k) → Rat)
    (N : Fin m → Fin k → Rat) (B : Fin m → Fin m → Rat)
    (innerT : Bool) (Z : Fin m → Fin m → Rat) : Bool :=
  ((List.finRange (m + k)).all fun i => (List.finRange (m + k)).all fun j =>
    decide (A i j = qlsum ((List.finRange m).map fun a =>
      qlsum ((List.finRange m).map fun b =>
        kernelExt m k N a i * B a b * kernelExt m k N b j)))) &&
  (if innerT then checkT m B Z else checkDD m B Z)

def negQuadFormPoly (n : Nat) (M : Fin n → Fin n → Rat)
    (ps : List QArith.Poly) : QArith.Poly :=
  QArith.Poly.neg ((List.finRange n).foldr (fun i acc =>
    (List.finRange n).foldr (fun j acc2 =>
      QArith.Poly.add (QArith.Poly.scale (M i j)
        (QArith.Poly.mul (ps.getD i.val []) (ps.getD j.val []))) acc2) acc) [])

def conclCheckCore (n : Nat) (M : Fin n → Fin n → Rat) (ts : List Term)
    (conclusion : Term) : Bool :=
  decide (ts.length = n) &&
  conclusion.idxFree && ts.all Term.idxFree &&
  decide (conclusion.toPoly = negQuadFormPoly n M (ts.map Term.toPoly))

def conclCheckW (n : Nat) (M : Fin n → Fin n → Rat) (ts : List Term)
    (conclusion : Term) : Bool :=
  decide (ts.length = n) &&
  (match conclusion.asCoordPolyIdxW?, ts.mapM Term.asCoordPolyIdxW? with
   | some pc, some pts => decide (pc = negQuadFormPoly n M pts)
   | _, _ => false)

def conclCheck (n : Nat) (M : Fin n → Fin n → Rat) (ts : List Term)
    (conclusion : Term) : Bool :=
  conclCheckCore n M ts conclusion || conclCheckW n M ts conclusion

end PsdCert

def ExtensionSet.interval1D? (S : ExtensionSet) : Option (Rat × Rat) :=
  if h : S.simplex.complex.ambDim = 1 then
    if S.isEmptyB then
      match (List.finRange S.simplex.complex.nVertices).filter
          (fun v => S.simplex.contains v) with
      | [a, b] =>
        let j0 : Fin S.simplex.complex.ambDim := ⟨0, by omega⟩
        let V₀ := S.simplex.complex.coord a j0
        let V₁ := S.simplex.complex.coord b j0
        if V₀ < V₁ then some (V₀, V₁)
        else if V₁ < V₀ then some (V₁, V₀)
        else none
      | _ => none
    else none
  else none

def coverExtendPass (ivs : List (Rat × Rat)) (r : Rat) : Rat :=
  ivs.foldl (fun r iv => if iv.1 ≤ r ∧ r < iv.2 then iv.2 else r) r

def coverReach : Nat → List (Rat × Rat) → Rat → Rat
  | 0, _, r => r
  | n + 1, ivs, r => coverReach n ivs (coverExtendPass ivs r)

def coverChainCheck (ivs : List (Rat × Rat)) (lo hi : Rat) : Bool :=
  decide (hi ≤ coverReach ivs.length ivs lo)

def coverCheck (simplex : Simplex) (S : ExtensionSet) (nBranches : Nat)
    (branchSimplex : Fin nBranches → Simplex)
    (branchS : Fin nBranches → ExtensionSet) : Bool :=
  match S.interval1D? with
  | none => false
  | some (lo, hi) =>
    decide (S.simplex = simplex) &&
    ((List.finRange nBranches).all fun k =>
      decide ((branchS k).simplex = branchSimplex k) &&
      ((branchS k).interval1D?).isSome) &&
    coverChainCheck
      ((List.finRange nBranches).filterMap fun k => (branchS k).interval1D?)
      lo hi

def coverInfeasibilityValid
    (_termX : Term) (simplex : Simplex) (S : ExtensionSet)
    (nBranches : Nat)
    (branchSimplex : Fin nBranches → Simplex)
    (branchS : Fin nBranches → ExtensionSet)
    (_coverCert : Term) : Prop :=
  coverCheck simplex S nBranches branchSimplex branchS = true

def affineWireTerm (offset slope : Rat) (w : Wire) : Term :=
  .add (.const offset) (.mul (.const slope) (.var w))

def lirpaConclusionForm
    (preact post : Wire) (α β γ δ : Rat) (F : Formula) : Prop :=
  F = .and (.atom .le (affineWireTerm β α preact) (.var post))
           (.atom .le (.var post) (affineWireTerm δ γ preact))

def cellStrictInteriorBuild (schema : SimpC) (t : Term)
    (k : Fin schema.cells.length) : Option Formula := do
  let c := schema.cells[k.val]'(k.isLt)
  let lams ← baryLambdas1D schema c.1 t
  match lams.map (fun (v, lt) =>
    Formula.atom (if c.2 v then .lt else .gt) lt (.const 0)) with
  | [x, y] => some (.and x y)
  | _ => none

def cellStrictInteriorForm (schema : SimpC) (t : Term)
    (k : Fin schema.cells.length) (F : Formula) : Prop :=
  cellStrictInteriorBuild schema t k = some F

def cellOneHotBuild (schema : SimpC) (outputs : List Wire)
    (k : Fin schema.cells.length) : Option Formula :=
  if outputs.length = schema.cells.length then
    let bk := Formula.atom .eq (.var (outputs.getD k.val 0)) (.const 1)
    let others := ((List.range outputs.length).filter (· ≠ k.val)).map
      fun j => Formula.atom .eq (.var (outputs.getD j 0)) (.const 0)
    some (.and bk (Formula.chainAnd others))
  else none

def cellOneHotForm (schema : SimpC) (outputs : List Wire)
    (k : Fin schema.cells.length) (F : Formula) : Prop :=
  cellOneHotBuild schema outputs k = some F

def cellOutWitnessBuild (schema : SimpC) (t : Term)
    (k : Fin schema.cells.length) (w : Fin schema.nVertices) :
    Option Formula := do
  let c := schema.cells[k.val]'(k.isLt)
  guard (c.1 w = true)
  let lams ← baryLambdas1D schema c.1 t
  let entry ← lams.find? fun p => decide (p.1 = w)
  some (.atom (if c.2 w then .gt else .lt) entry.2 (.const 0))

def cellOutWitnessForm (schema : SimpC) (t : Term)
    (k : Fin schema.cells.length) (w : Fin schema.nVertices)
    (F : Formula) : Prop :=
  cellOutWitnessBuild schema t k w = some F

def cellOutZeroBuild (schema : SimpC) (outputs : List Wire)
    (k : Fin schema.cells.length) : Option Formula :=
  if outputs.length = schema.cells.length then
    some (.atom .eq (.var (outputs.getD k.val 0)) (.const 0))
  else none

def cellOutZeroForm (schema : SimpC) (outputs : List Wire)
    (k : Fin schema.cells.length) (F : Formula) : Prop :=
  cellOutZeroBuild schema outputs k = some F

def PrimApp.isReluAt (preact post : Wire) : PrimApp → Bool
  | .relu s i o =>
      decide (i = preact) && decide (o = post) &&
      decide (0 < Shape.totalSize s)
  | _ => false

def reluLinked (H : Hypernet) (preact post : Wire) : Prop :=
  H.applications.any (PrimApp.isReluAt preact post) = true

theorem PrimApp.isReluAt_iff {preact post : Wire} {a : PrimApp} :
    PrimApp.isReluAt preact post a = true ↔
      ∃ s, a = .relu s preact post ∧ 0 < Shape.totalSize s := by
  cases a with
  | relu s i o =>
    simp only [PrimApp.isReluAt, Bool.and_eq_true, decide_eq_true_eq,
      PrimApp.relu.injEq]
    constructor
    · rintro ⟨⟨rfl, rfl⟩, hs⟩
      exact ⟨s, ⟨rfl, rfl, rfl⟩, hs⟩
    · rintro ⟨s', ⟨rfl, rfl, rfl⟩, hs⟩
      exact ⟨⟨rfl, rfl⟩, hs⟩
  | const ty c out =>
    simp only [PrimApp.isReluAt, Bool.false_eq_true, false_iff]
    rintro ⟨s, h, -⟩; exact PrimApp.noConfusion h
  | contract δ r ins out irs orank pat =>
    simp only [PrimApp.isReluAt, Bool.false_eq_true, false_iff]
    rintro ⟨s, h, -⟩; exact PrimApp.noConfusion h
  | cast δf δt r sh i o =>
    simp only [PrimApp.isReluAt, Bool.false_eq_true, false_iff]
    rintro ⟨s, h, -⟩; exact PrimApp.noConfusion h
  | cell sch i os =>
    simp only [PrimApp.isReluAt, Bool.false_eq_true, false_iff]
    rintro ⟨s, h, -⟩; exact PrimApp.noConfusion h
  | reshape ns i o =>
    simp only [PrimApp.isReluAt, Bool.false_eq_true, false_iff]
    rintro ⟨s, h, -⟩; exact PrimApp.noConfusion h
  | broadcast ts i o =>
    simp only [PrimApp.isReluAt, Bool.false_eq_true, false_iff]
    rintro ⟨s, h, -⟩; exact PrimApp.noConfusion h
  | copy k i os =>
    simp only [PrimApp.isReluAt, Bool.false_eq_true, false_iff]
    rintro ⟨s, h, -⟩; exact PrimApp.noConfusion h
  | delete i =>
    simp only [PrimApp.isReluAt, Bool.false_eq_true, false_iff]
    rintro ⟨s, h, -⟩; exact PrimApp.noConfusion h
  | swap i1 i2 o1 o2 =>
    simp only [PrimApp.isReluAt, Bool.false_eq_true, false_iff]
    rintro ⟨s, h, -⟩; exact PrimApp.noConfusion h
  | stack k sh ins o =>
    simp only [PrimApp.isReluAt, Bool.false_eq_true, false_iff]
    rintro ⟨s, h, -⟩; exact PrimApp.noConfusion h
  | ppoly n q ins o =>
    simp only [PrimApp.isReluAt, Bool.false_eq_true, false_iff]
    rintro ⟨s, h, -⟩; exact PrimApp.noConfusion h
  | pderiv sh ax i o =>
    simp only [PrimApp.isReluAt, Bool.false_eq_true, false_iff]
    rintro ⟨s, h, -⟩; exact PrimApp.noConfusion h
  | facet sh ax hi i o =>
    simp only [PrimApp.isReluAt, Bool.false_eq_true, false_iff]
    rintro ⟨s, h, -⟩; exact PrimApp.noConfusion h

theorem reluLinked_iff {H : Hypernet} {preact post : Wire} :
    reluLinked H preact post ↔
      ∃ s, PrimApp.relu s preact post ∈ H.applications ∧
        0 < Shape.totalSize s := by
  unfold reluLinked
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a, ha, hp⟩
    obtain ⟨s, rfl, hs⟩ := PrimApp.isReluAt_iff.mp hp
    exact ⟨s, ha, hs⟩
  · rintro ⟨s, hmem, hs⟩
    exact ⟨_, hmem, PrimApp.isReluAt_iff.mpr ⟨s, rfl, hs⟩⟩

inductive RuleTag where

  | ax | weaken | cut | andI | andE | orI | orE | eqElim

  | convIntro | convElim

  | arithAtom

  | bernCone

  | norm | farkas | subdivide | lirpa
  | reluPos | reluNeg | reluNN | reluAbove
  | cellInInterior | cellOut

  | eqRefl | eqSym

  | promise | syzygy

  | pConstExact | pBound

  | psdCertT | psdCertDD | psdCertK
  deriving DecidableEq, Repr

mutual

inductive ProofObject : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent) (rule : RuleTag)
       (payload : RuleData H seq rule) : ProofObject H seq

inductive RuleData : Hypernet → Sequent → RuleTag → Type where
  | ax             (H : Hypernet) (seq : Sequent) : PAxData H seq             → RuleData H seq .ax
  | weaken         (H : Hypernet) (seq : Sequent) : PWeakenData H seq         → RuleData H seq .weaken
  | cut            (H : Hypernet) (seq : Sequent) : PCutData H seq            → RuleData H seq .cut
  | andI           (H : Hypernet) (seq : Sequent) : PAndIData H seq           → RuleData H seq .andI
  | andE           (H : Hypernet) (seq : Sequent) : PAndEData H seq           → RuleData H seq .andE
  | orI            (H : Hypernet) (seq : Sequent) : POrIData H seq            → RuleData H seq .orI
  | orE            (H : Hypernet) (seq : Sequent) : POrEData H seq            → RuleData H seq .orE
  | eqElim         (H : Hypernet) (seq : Sequent) : PEqElimData H seq         → RuleData H seq .eqElim
  | convIntro      (H : Hypernet) (seq : Sequent) : PConvIntroData H seq      → RuleData H seq .convIntro
  | convElim       (H : Hypernet) (seq : Sequent) : PConvElimData H seq       → RuleData H seq .convElim
  | arithAtom      (H : Hypernet) (seq : Sequent) : PArithAtomData H seq      → RuleData H seq .arithAtom
  | bernCone       (H : Hypernet) (seq : Sequent) : PBernConeData H seq       → RuleData H seq .bernCone
  | norm           (H : Hypernet) (seq : Sequent) : PNormData H seq           → RuleData H seq .norm
  | farkas         (H : Hypernet) (seq : Sequent) : PFarkasData H seq         → RuleData H seq .farkas
  | subdivide      (H : Hypernet) (seq : Sequent) : PSubdivideData H seq      → RuleData H seq .subdivide
  | lirpa          (H : Hypernet) (seq : Sequent) : PLiRPAData H seq          → RuleData H seq .lirpa
  | reluPos        (H : Hypernet) (seq : Sequent) : PReLUPosData H seq        → RuleData H seq .reluPos
  | reluNeg        (H : Hypernet) (seq : Sequent) : PReLUNegData H seq        → RuleData H seq .reluNeg
  | reluNN         (H : Hypernet) (seq : Sequent) : PReLUNNData H seq         → RuleData H seq .reluNN
  | reluAbove      (H : Hypernet) (seq : Sequent) : PReLUAboveData H seq      → RuleData H seq .reluAbove
  | cellInInterior (H : Hypernet) (seq : Sequent) : PCellInIntData H seq      → RuleData H seq .cellInInterior
  | cellOut        (H : Hypernet) (seq : Sequent) : PCellOutData H seq        → RuleData H seq .cellOut
  | eqRefl         (H : Hypernet) (seq : Sequent) : PEqReflData H seq         → RuleData H seq .eqRefl
  | eqSym          (H : Hypernet) (seq : Sequent) : PEqSymData H seq          → RuleData H seq .eqSym
  | promise        (H : Hypernet) (seq : Sequent) : PPromiseData H seq        → RuleData H seq .promise
  | syzygy         (H : Hypernet) (seq : Sequent) : PSyzygyData H seq         → RuleData H seq .syzygy
  | pConstExact    (H : Hypernet) (seq : Sequent) : PConstExactData H seq     → RuleData H seq .pConstExact
  | pBound         (H : Hypernet) (seq : Sequent) : PBoundData H seq          → RuleData H seq .pBound
  | psdCertT       (H : Hypernet) (seq : Sequent) : PPsdCertTData H seq       → RuleData H seq .psdCertT
  | psdCertDD      (H : Hypernet) (seq : Sequent) : PPsdCertDDData H seq      → RuleData H seq .psdCertDD
  | psdCertK       (H : Hypernet) (seq : Sequent) : PPsdCertKData H seq       → RuleData H seq .psdCertK

inductive PAxData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (preEqPost : seq.pre = seq.post) : PAxData H seq

inductive PWeakenData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (premise : Sequent) (premiseProof : ProofObject H premise)
       (extra : Formula)
       (preEq  : seq.pre  = .and premise.pre extra)
       (postEq : seq.post = premise.post)
       : PWeakenData H seq

inductive PCutData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (cutFormula : Formula)
       (leftPremise  : Sequent) (leftProof  : ProofObject H leftPremise)
       (rightPremise : Sequent) (rightProof : ProofObject H rightPremise)
       (preEq    : seq.pre  = leftPremise.pre)
       (postEq   : seq.post = rightPremise.post)
       (cutLeft  : leftPremise.post = cutFormula)
       (cutRight : rightPremise.pre = .and leftPremise.pre cutFormula)
       : PCutData H seq

inductive PAndIData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (leftPremise  : Sequent) (leftProof  : ProofObject H leftPremise)
       (rightPremise : Sequent) (rightProof : ProofObject H rightPremise)
       (preMatch : leftPremise.pre = rightPremise.pre)
       (preEq    : seq.pre  = leftPremise.pre)
       (postEq   : seq.post = .and leftPremise.post rightPremise.post)
       : PAndIData H seq

inductive PAndEData : Hypernet → Sequent → Type where
  | left  (H : Hypernet) (seq : Sequent)
          (premise : Sequent) (premiseProof : ProofObject H premise)
          (other : Formula)
          (preEq  : seq.pre = premise.pre)
          (postEq : premise.post = .and seq.post other)
          : PAndEData H seq
  | right (H : Hypernet) (seq : Sequent)
          (premise : Sequent) (premiseProof : ProofObject H premise)
          (other : Formula)
          (preEq  : seq.pre = premise.pre)
          (postEq : premise.post = .and other seq.post)
          : PAndEData H seq

inductive POrIData : Hypernet → Sequent → Type where
  | left  (H : Hypernet) (seq : Sequent)
          (premise : Sequent) (premiseProof : ProofObject H premise)
          (other : Formula)
          (preEq  : seq.pre = premise.pre)
          (postEq : seq.post = .or premise.post other)
          : POrIData H seq
  | right (H : Hypernet) (seq : Sequent)
          (premise : Sequent) (premiseProof : ProofObject H premise)
          (other : Formula)
          (preEq  : seq.pre = premise.pre)
          (postEq : seq.post = .or other premise.post)
          : POrIData H seq

inductive POrEData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (leftPremise  : Sequent) (leftProof  : ProofObject H leftPremise)
       (rightPremise : Sequent) (rightProof : ProofObject H rightPremise)
       (postMatch : leftPremise.post = rightPremise.post)
       (preEq     : seq.pre  = .or leftPremise.pre rightPremise.pre)
       (postEq    : seq.post = leftPremise.post)
       : POrEData H seq

inductive PEqElimData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (eqPremise   : Sequent) (eqProof   : ProofObject H eqPremise)
       (bodyPremise : Sequent) (bodyProof : ProofObject H bodyPremise)
       (wire : Wire) (termT termU : Term) (bodyForm : Formula)
       (preEq     : seq.pre = eqPremise.pre)
       (preMatch  : eqPremise.pre = bodyPremise.pre)
       (eqPost    : eqPremise.post = .atom .eq termT termU)
       (tyEq      : ∃ s, termT.bshape H = some s ∧ termU.bshape H = some s)
       (bodySubT  : substituteInFormula bodyForm wire termT bodyPremise.post)
       (conclSubU : substituteInFormula bodyForm wire termU seq.post)
       : PEqElimData H seq

inductive PEqReflData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (term : Term)
       (tyDef  : ∃ s, term.bshape H = some s)
       (fin    : term.finWires H)
       (postEq : seq.post = .atom .eq term term)
       : PEqReflData H seq

inductive PEqSymData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (premise : Sequent) (premiseProof : ProofObject H premise)
       (termT termU : Term)
       (preEq       : seq.pre = premise.pre)
       (premisePost : premise.post = .atom .eq termT termU)
       (postEq      : seq.post = .atom .eq termU termT)
       : PEqSymData H seq

inductive PConvIntroData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (premise : Sequent) (premiseProof : ProofObject H premise)
       (term : Term) (simplex : Simplex) (S : ExtensionSet)
       (preEq     : seq.pre = premise.pre)
       (termShape : term.bshape H = some [simplex.complex.ambDim])
       (halfspace : barycentricHalfspaceForm term simplex S premise.post)
       (postEq    : seq.post = .inRegion term simplex S)
       : PConvIntroData H seq

inductive PConvElimData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (premise : Sequent) (premiseProof : ProofObject H premise)
       (term : Term) (simplex : Simplex) (S : ExtensionSet)
       (preEq       : seq.pre = premise.pre)
       (premiseForm : premise.post = .inRegion term simplex S)
       (halfspace   : barycentricHalfspaceForm term simplex S seq.post)
       : PConvElimData H seq

inductive PArithAtomData : Hypernet → Sequent → Type where
  | fold   (H : Hypernet) (seq : Sequent)
           (premise : Sequent) (premiseProof : ProofObject H premise)
           (termL termR : Term) (b : BowTie)
           (notNE          : b ≠ .ne)
           (preEq          : seq.pre = premise.pre)
           (premiseIsZero  : atomicCompareZero b termL termR premise.post)
           (conclIsDirect  : atomicCompareForm b termL termR seq.post)
           : PArithAtomData H seq
  | unfold (H : Hypernet) (seq : Sequent)
           (premise : Sequent) (premiseProof : ProofObject H premise)
           (termL termR : Term) (b : BowTie)
           (notNE           : b ≠ .ne)
           (preEq           : seq.pre = premise.pre)
           (premiseIsDirect : atomicCompareForm b termL termR premise.post)
           (conclIsZero     : atomicCompareZero b termL termR seq.post)
           : PArithAtomData H seq

inductive PBernConeData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (regionPremise : Sequent) (regionProof : ProofObject H regionPremise)
       (termX : Term) (simplex : Simplex) (S : ExtensionSet)
       (degree : Nat) (polynomial : Term) (predicate : Formula)
       (preEq      : seq.pre = regionPremise.pre)
       (regionPost : regionPremise.post = .inRegion termX simplex S)
       (polyTie    : polynomial.freeWires = []
                     ∨ ∃ w, termX = Term.var w ∧ polynomial.freeWires ⊆ [w])
       (predShape  : (¬ isExtensionSetEmpty S → isConicPredicate predicate)
                     ∧ (isExtensionSetEmpty S → isConvexPredicate predicate))
       (coefficients : allForwardDiffBernCoeffsSatisfyP simplex S degree
                         polynomial predicate)
       (postApply  : applyPredicateToTerm predicate polynomial seq.post)
       : PBernConeData H seq

inductive PNormData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (termL termR : Term)
       (canonEq : polynomialCanonicalEq termL termR)

       (tyEq   : termL.bshape H = termR.bshape H)
       (tyDef  : ∃ s, termL.bshape H = some s)
       (finL   : termL.finWires H)
       (finR   : termR.finWires H)
       (postEq  : seq.post = .atom .eq termL termR)
       : PNormData H seq

inductive PFarkasData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (combinationCoeffs : Term)
       (conclusion : Term)

       (denBoundLog2 : Nat)
       (conclShape : ∃ s, conclusion.bshape H = some s)
       (conclFin   : conclusion.finWires H)

       (wiresPos : ∀ w ∈ seq.pre.freeWires ++ conclusion.freeWires,
                     ∃ τ, H.wireType w = some τ ∧
                       0 < Shape.totalSize τ.shape)
       (valid  : farkasCombinationValid combinationCoeffs seq.pre conclusion)
       (postEq : seq.post = .atom .le conclusion (.const 0))
       : PFarkasData H seq

inductive PSubdivideData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (regionPremise : Sequent) (regionProof : ProofObject H regionPremise)
       (termX : Term) (simplex : Simplex) (S : ExtensionSet)
       (nBranches : Nat)
       (branchSimplex : Fin nBranches → Simplex)
       (branchS       : Fin nBranches → ExtensionSet)
       (branchPremise : Fin nBranches → Sequent)
       (branchProof   : (k : Fin nBranches) → ProofObject H (branchPremise k))
       (coverCertificate : Term)

       (denBoundLog2 : Nat)
       (preEq      : seq.pre = regionPremise.pre)
       (regionPost : regionPremise.post = .inRegion termX simplex S)
       (branchPre  : ∀ k, (branchPremise k).pre
                          = .and regionPremise.pre
                                 (.inRegion termX (branchSimplex k) (branchS k)))
       (branchPost : ∀ k, (branchPremise k).post = seq.post)
       (coverValid : coverInfeasibilityValid termX simplex S nBranches
                       branchSimplex branchS coverCertificate)
       : PSubdivideData H seq

inductive PLiRPAData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (lowerPremise : Sequent) (lowerProof : ProofObject H lowerPremise)
       (upperPremise : Sequent) (upperProof : ProofObject H upperPremise)
       (preact post : Wire) (a b α β γ δ : Rat)

       (denBoundLog2 : Nat)
       (link : reluLinked H preact post)
       (hAneg   : a < 0)
       (hBpos   : 0 < b)
       (hLower1 : α * a + β ≤ 0)
       (hLower2 : β ≤ 0)
       (hLower3 : α * b + β ≤ b)
       (hUpper1 : 0 ≤ γ * a + δ)
       (hUpper2 : 0 ≤ δ)
       (hUpper3 : b ≤ γ * b + δ)
       (preEq     : seq.pre = lowerPremise.pre)
       (preMatch  : lowerPremise.pre = upperPremise.pre)
       (lowerPost : lowerPremise.post = .atom .le (.const a) (.var preact))
       (upperPost : upperPremise.post = .atom .le (.var preact) (.const b))
       (postForm  : lirpaConclusionForm preact post α β γ δ seq.post)
       : PLiRPAData H seq

inductive PReLUPosData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (premise : Sequent) (premiseProof : ProofObject H premise)
       (preact post : Wire)
       (link : reluLinked H preact post)
       (preEq       : seq.pre = premise.pre)
       (premisePost : premise.post = .atom .ge (.var preact) (.const 0))
       (conclPost   : seq.post     = .atom .eq (.var post) (.var preact))
       : PReLUPosData H seq

inductive PReLUNegData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (premise : Sequent) (premiseProof : ProofObject H premise)
       (preact post : Wire)
       (link : reluLinked H preact post)
       (preEq       : seq.pre = premise.pre)
       (premisePost : premise.post = .atom .le (.var preact) (.const 0))
       (conclPost   : seq.post     = .atom .eq (.var post) (.const 0))
       : PReLUNegData H seq

inductive PReLUNNData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (preact post : Wire)
       (link : reluLinked H preact post)
       (conclPost : seq.post = .atom .ge (.var post) (.const 0))
       : PReLUNNData H seq

inductive PReLUAboveData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (preact post : Wire)
       (link : reluLinked H preact post)
       (conclPost : seq.post = .atom .ge (.var post) (.var preact))
       : PReLUAboveData H seq

inductive PCellInIntData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (premise : Sequent) (premiseProof : ProofObject H premise)
       (schema : SimpC) (input : Wire) (outputs : List Wire)
       (whichI : Fin schema.cells.length)
       (appInH : PrimApp.cell schema input outputs ∈ H.applications)
       (inputShape : ∃ τ, H.wireType input = some τ ∧
                       τ.shape = [schema.ambDim])
       (outputsScalar : ∀ o ∈ outputs, ∃ τ, H.wireType o = some τ ∧
                          Shape.totalSize τ.shape = 1)
       (preEq  : seq.pre = premise.pre)
       (interiorPremise : cellStrictInteriorForm schema (.var input) whichI
                            premise.post)
       (postOneHot : cellOneHotForm schema outputs whichI seq.post)
       : PCellInIntData H seq

inductive PCellOutData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (premise : Sequent) (premiseProof : ProofObject H premise)
       (schema : SimpC) (input : Wire) (outputs : List Wire)
       (whichJ : Fin schema.cells.length)
       (witnessVertex : Fin schema.nVertices)
       (appInH : PrimApp.cell schema input outputs ∈ H.applications)
       (inputShape : ∃ τ, H.wireType input = some τ ∧
                       τ.shape = [schema.ambDim])
       (outputsScalar : ∀ o ∈ outputs, ∃ τ, H.wireType o = some τ ∧
                          Shape.totalSize τ.shape = 1)
       (preEq  : seq.pre = premise.pre)
       (outWitness : cellOutWitnessForm schema (.var input) whichJ
                       witnessVertex premise.post)
       (postZero : cellOutZeroForm schema outputs whichJ seq.post)
       : PCellOutData H seq

inductive PPromiseData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (supplier : Sequent) (supplierProof : ProofObject H supplier)
       (consumer : Sequent) (consumerProof : ProofObject H consumer)
       (contract : Formula)
       (path : ConjPath)
       (iface : List Wire)
       (ctx : Formula)
       (supplierPost : supplier.post = contract)
       (pathReads : consumer.pre.conjGet? path = some contract)
       (prePlumb : consumer.pre.conjReplace? path supplier.pre = some seq.pre)
       (postEq : seq.post = consumer.post)
       (ctxReads : consumer.pre.conjReplace? path .tt = some ctx)
       (contractConfined : formulaWiresWithin contract iface)
       (separation : wiresSeparated supplier.pre ctx seq.post iface)
       : PPromiseData H seq

inductive PSyzygyData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (components : List Sequent)
       (componentProofs : ProofSeqList H components)
       (combination : Term)
       (conclusion : Term)
       (denBoundLog2 : Nat)
       (preContains : ∀ c ∈ components, premiseContains seq.pre c.pre)
       (conclShape : ∃ s, conclusion.bshape H = some s)
       (conclFin   : conclusion.finWires H)
       (wiresPos : ∀ w ∈ seq.pre.freeWires ++ conclusion.freeWires,
                     ∃ τ, H.wireType w = some τ ∧
                       0 < Shape.totalSize τ.shape)
       (compPostWiresPos : ∀ c ∈ components, ∀ w ∈ c.post.freeWires,
                     ∃ τ, H.wireType w = some τ ∧
                       0 < Shape.totalSize τ.shape)
       (valid : syzygyCombinationValid combination components seq.pre conclusion)
       (postForm : syzygyConclusionForm conclusion seq.post)
       : PSyzygyData H seq

inductive PConstExactData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (e₁ e₂ : Term) (b : BowTie)
       (notNE : b ≠ .ne)
       (evalTrue : (Formula.atom b e₁ e₂).evalClosed = some true)
       (postEq : seq.post = .atom b e₁ e₂)
       : PConstExactData H seq

inductive PBoundData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (components : List Sequent)
       (componentProofs : ProofSeqList H components)
       (combination : Term)
       (conclusion : Term)
       (denBoundLog2 : Nat)
       (preContains : ∀ c ∈ components, premiseContains seq.pre c.pre)
       (conclShape : ∃ s, conclusion.bshape H = some s)
       (conclFin   : conclusion.finWires H)
       (wiresPos : ∀ w ∈ seq.pre.freeWires ++ conclusion.freeWires,
                     ∃ τ, H.wireType w = some τ ∧
                       0 < Shape.totalSize τ.shape)
       (compPostWiresPos : ∀ c ∈ components, ∀ w ∈ c.post.freeWires,
                     ∃ τ, H.wireType w = some τ ∧
                       0 < Shape.totalSize τ.shape)
       (valid : syzygyCombinationValid combination components seq.pre conclusion)
       (postForm : syzygyConclusionForm conclusion seq.post)
       : PBoundData H seq

inductive PPsdCertTData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (n : Nat) (A Z : Fin n → Fin n → Rat)
       (ts : List Term) (conclusion : Term)
       (witness : PsdCert.checkT n A Z = true)
       (concl : PsdCert.conclCheck n A ts conclusion = true)
       (conclShape : ∃ s, conclusion.bshape H = some s)
       (conclFin   : conclusion.finWires H)
       (wiresPos : ∀ w ∈ conclusion.freeWires,
                     ∃ τ, H.wireType w = some τ ∧
                       0 < Shape.totalSize τ.shape)
       (postForm : syzygyConclusionForm conclusion seq.post)
       : PPsdCertTData H seq

inductive PPsdCertDDData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (n : Nat) (A Z : Fin n → Fin n → Rat)
       (ts : List Term) (conclusion : Term)
       (witness : PsdCert.checkDD n A Z = true)
       (concl : PsdCert.conclCheck n A ts conclusion = true)
       (conclShape : ∃ s, conclusion.bshape H = some s)
       (conclFin   : conclusion.finWires H)
       (wiresPos : ∀ w ∈ conclusion.freeWires,
                     ∃ τ, H.wireType w = some τ ∧
                       0 < Shape.totalSize τ.shape)
       (postForm : syzygyConclusionForm conclusion seq.post)
       : PPsdCertDDData H seq

inductive PPsdCertKData : Hypernet → Sequent → Type where
  | mk (H : Hypernet) (seq : Sequent)
       (m k : Nat)
       (A : Fin (m + k) → Fin (m + k) → Rat)
       (N : Fin m → Fin k → Rat) (B : Fin m → Fin m → Rat)
       (innerT : Bool) (Z : Fin m → Fin m → Rat)
       (ts : List Term) (conclusion : Term)
       (witness : PsdCert.checkK m k A N B innerT Z = true)
       (concl : PsdCert.conclCheck (m + k) A ts conclusion = true)
       (conclShape : ∃ s, conclusion.bshape H = some s)
       (conclFin   : conclusion.finWires H)
       (wiresPos : ∀ w ∈ conclusion.freeWires,
                     ∃ τ, H.wireType w = some τ ∧
                       0 < Shape.totalSize τ.shape)
       (postForm : syzygyConclusionForm conclusion seq.post)
       : PPsdCertKData H seq

inductive ProofSeqList : Hypernet → List Sequent → Type where
  | nil  (H : Hypernet) : ProofSeqList H []
  | cons (H : Hypernet) (seq : Sequent) (rest : List Sequent)
         (pf : ProofObject H seq) (pfs : ProofSeqList H rest)
         : ProofSeqList H (seq :: rest)

end

def check {H : Hypernet} {seq : Sequent} (_pf : ProofObject H seq) : Bool :=
  true

def spCellDisjunct (schema : SimpC) (input : Wire) (outputs : List Wire)
    (i : Fin schema.cells.length) : Formula :=
  let c := schema.cells[i.val]'(i.isLt)
  have hmem : c ∈ schema.cells := List.getElem_mem i.isLt
  have hwf := schema.cellsWF c hmem
  let sVal : Simplex :=
    ⟨schema, c.1, schema.nonempty c.1 hwf.1⟩
  let ext : ExtensionSet :=
    ⟨sVal, c.2, hwf.2.1, hwf.2.2⟩
  match cellOneHotBuild schema outputs i with
  | some oneHot => .and (.inRegion (.var input) sVal ext) oneHot
  | none => .tt

def MonoTable.monoTermAux (inputs : List Wire) : List Nat → Nat → Term → Term
  | [], _, acc => acc
  | e :: es, i, acc =>
      (List.range e).foldr
        (fun _ a => Term.mul (Term.var (inputs.getD i 0)) a)
        (MonoTable.monoTermAux inputs es (i + 1) acc)

def MonoTable.monoTerm (inputs : List Wire) (m : List Nat × Rat) : Term :=
  MonoTable.monoTermAux inputs m.1 0 (Term.const m.2)

def MonoTable.term (q : MonoTable) (inputs : List Wire) : Term :=
  q.foldr (fun m acc => Term.add (MonoTable.monoTerm inputs m) acc)
    (Term.const 0)

def PrimApp.spFact : PrimApp → Formula
  | .const _ _ _ => .tt
  | .contract _ r ins out _ outputRank pat =>
    if r = RoundMode.exact ∧ pat.nIndices = 0 ∧ outputRank = 0 then
      .atom .eq (.var out)
        (ins.foldr (fun w acc => .mul (.var w) acc) (.const 1))
    else .tt
  | .cast δfrom δto r _ input output =>
    if δfrom = δto ∧ r = RoundMode.exact then
      .atom .eq (.var output) (.var input)
    else .tt
  | .cell schema input outputs =>
    if outputs.length = schema.cells.length then
      match (List.finRange schema.cells.length).map
          (spCellDisjunct schema input outputs) with
      | [] => .tt
      | ds => Formula.chainOr ds
    else .tt
  | .reshape _ _ _ => .tt
  | .broadcast _ _ _ => .tt
  | .copy _ input outputs =>
    Formula.chainAnd (outputs.map fun o => .atom .eq (.var o) (.var input))
  | .delete _ => .tt
  | .swap in1 in2 out1 out2 =>
    .and (.atom .eq (.var out1) (.var in2))
         (.atom .eq (.var out2) (.var in1))
  | .stack k shape inputs output =>

    if inputs.length = k ∧ shape = [] then
      Formula.chainAnd ((List.range k).map fun i =>
        .atom .eq (.idx (.var output) i) (.var (inputs.getD i 0)))
    else .tt
  | .relu shape input output =>

    if Shape.totalSize shape = 1 then
      .or (.and (.atom .le (.var input) (.const 0))
                (.atom .eq (.var output) (.const 0)))
          (.and (.atom .ge (.var input) (.const 0))
                (.atom .eq (.var output) (.var input)))
    else .tt
  | .ppoly nvars coeffs inputs output =>

    if MonoTable.widthOkB coeffs nvars && inputs.length == nvars then
      .atom .eq (.var output) (MonoTable.term coeffs inputs)
    else .tt
  | .pderiv shape axis input output =>

    match shape, axis with
    | [n], 0 =>
      Formula.chainAnd ((List.range n).map fun β =>
        if β + 1 < n then
          .atom .eq (.idx (.var output) β)
            (.mul (.const ((β : Rat) + 1)) (.idx (.var input) (β + 1)))
        else
          .atom .eq (.idx (.var output) β) (.const 0))
    | _, _ => .tt
  | .facet shape axis hi input output =>

    match shape, axis with
    | [n], 0 =>
      if n = 0 then .tt
      else .atom .eq (.var output)
        (.idx (.var input) (if hi then n - 1 else 0))
    | _, _ => .tt

def Hypernet.spConjunction (H : Hypernet) : Formula :=
  H.applications.foldr (fun a acc => .and a.spFact acc) .tt

structure Certificate where
  hypernet : Hypernet
  goalPre  : Formula
  goalPost : Formula

  holeFresh : (hypernet.wireType predicateHole).isNone
  proof : ProofObject hypernet
            ⟨.and goalPre hypernet.spConjunction, goalPost⟩

end PPLC
