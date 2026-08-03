import Qtsl.Core.Catalogue

/-!
# Plates: symbolic-extent syntax (the plated layer)

The hypernet language extended with **plates as symbolic extents**: a plate is
container-level data — a declared index variable — plus the license for
wire shapes and contraction-pattern index extents to mention it where
they now carry literal extents. No eleventh box, no membrane syntax.

Design facts realized here, mirroring the plate design's lift table:

* `const` carries a literal core `TensorType`/`TensorValue` — **the
  refusal**: a literal tensor has finitely many entries, so no symbolic
  extent is utterable in a literal's shape. This single refusal is what
  makes equivariance (T-NAT, `Qtsl.Plate.TNat`) a theorem of the grammar.
* `reshape` carries a literal `Shape` and its typing clause demands a
  literal input shape (a deliberate v1 refusal — totalSize equality
  over symbolic extents is polynomial identity in ℕ[ι], machinery with
  zero demand).
* `cell` is plate-free in v1: the design's mapped form (plate-axis prefix
  π) cannot instantiate into the *current* base `PrimApp.cell` typing,
  which demands input shape exactly `[schema.ambDim]` — the mapped-cell
  row is a known base-language seam.
* extent equality demands in typing clauses are **syntactic** (`SExtent`
  has decidable equality): conservative, never unsound — a
  ι-vs-literal coincidence at some σ is deliberately excluded, which is
  a completeness loss only (T-PLATE needs typing facts at *every* σ).

The `plates` field of `PlatedHypernet` is advisory (a
count-bound hint): assignments σ quantify over all of
`Nat → Nat`, so de Bruijn scoping is never load-bearing for the
theorems. Everything here is mathlib-free, like the `Core` it extends.
-/

namespace PPLC
namespace Plate

/-- A symbolic extent: a literal, or a declared plate variable. -/
inductive SExtent where
  | lit  (n : Nat)
  | pvar (v : Nat)
  deriving DecidableEq, Repr

/-- Instantiation of one extent at an assignment σ. -/
def SExtent.inst (σ : Nat → Nat) : SExtent → Nat
  | .lit n  => n
  | .pvar v => σ v

@[simp] theorem SExtent.inst_lit (σ : Nat → Nat) (n : Nat) :
    (SExtent.lit n).inst σ = n := rfl

@[simp] theorem SExtent.inst_pvar (σ : Nat → Nat) (v : Nat) :
    (SExtent.pvar v).inst σ = σ v := rfl

/-- Symbolic shapes: lists of symbolic extents. -/
abbrev SShape := List SExtent

namespace SShape

/-- Instantiation of a symbolic shape. -/
def inst (σ : Nat → Nat) (s : SShape) : Shape :=
  s.map (SExtent.inst σ)

/-- All-literal embedding of a core shape. -/
def lift (s : Shape) : SShape := s.map .lit

/-- No occurrence of the plate variable `v`. -/
def noVar (s : SShape) (v : Nat) : Prop := ∀ e ∈ s, e ≠ SExtent.pvar v

/-- Entirely literal (plate-free along every plate variable). -/
def plateFree (s : SShape) : Prop := ∀ e ∈ s, ∃ n, e = SExtent.lit n

theorem plateFree.noVar {s : SShape} (h : s.plateFree) (v : Nat) :
    s.noVar v := by
  intro e he
  obtain ⟨n, rfl⟩ := h e he
  intro hcon
  exact SExtent.noConfusion hcon

theorem lift_plateFree (s : Shape) : (lift s).plateFree := by
  intro e he
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp he
  exact ⟨n, rfl⟩

@[simp] theorem inst_length (σ : Nat → Nat) (s : SShape) :
    (s.inst σ).length = s.length := by
  simp [SShape.inst]

@[simp] theorem inst_nil (σ : Nat → Nat) : SShape.inst σ [] = [] := rfl

@[simp] theorem inst_cons (σ : Nat → Nat) (e : SExtent) (s : SShape) :
    SShape.inst σ (e :: s) = e.inst σ :: s.inst σ := rfl

/-- S1: instantiation is a homomorphism on shapes. -/
theorem inst_append (σ : Nat → Nat) (s t : SShape) :
    (s ++ t).inst σ = s.inst σ ++ t.inst σ := by
  simp [SShape.inst]

@[simp] theorem lift_inst (σ : Nat → Nat) (s : Shape) :
    (lift s).inst σ = s := by
  induction s with
  | nil => rfl
  | cons n t ih => simpa [lift, inst] using ih

@[simp] theorem lift_length (s : Shape) : (lift s).length = s.length := by
  simp [lift]

end SShape

set_option linter.unnecessarySimpa false in
/-- getD commutes with map when the default is mapped too. -/
theorem getD_map_comm {α β : Type} (f : α → β) (l : List α)
    (n : Nat) (d : α) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  induction l generalizing n with
  | nil => simp [List.getD]
  | cons a t ih =>
    cases n with
    | zero => simp [List.getD]
    | succ m => simpa [List.getD] using ih m

/-- S1 (extents): syntactic equality is sound at every σ. -/
theorem SExtent.instEq_of_syn (σ : Nat → Nat) {e e' : SExtent}
    (h : e = e') : e.inst σ = e'.inst σ := by
  rw [h]

/-- Symbolic tensor types. -/
structure STensorType where
  shape : SShape
  dtype : Dtype
  deriving DecidableEq, Repr

namespace STensorType

def inst (σ : Nat → Nat) (τ : STensorType) : TensorType :=
  ⟨τ.shape.inst σ, τ.dtype⟩

def lift (τ : TensorType) : STensorType := ⟨.lift τ.shape, τ.dtype⟩

@[simp] theorem inst_shape (σ : Nat → Nat) (τ : STensorType) :
    (τ.inst σ).shape = τ.shape.inst σ := rfl

@[simp] theorem inst_dtype (σ : Nat → Nat) (τ : STensorType) :
    (τ.inst σ).dtype = τ.dtype := rfl

@[simp] theorem lift_inst (σ : Nat → Nat) (τ : TensorType) :
    (STensorType.lift τ).inst σ = τ := by
  cases τ with
  | mk s d => simp [lift, inst]

end STensorType

/-- The symbolic trailing-axis broadcast relation: extent equality read
syntactically, **literal 1 only** in the widening slot — a plate
variable is never assumed to be 1 (conservative, sound; the m2 mutant
locus). -/
def SShape.broadcastsToS (src dst : SShape) : Prop :=
  src.length ≤ dst.length ∧
  ∀ i : Fin src.length,
    src.getD (src.length - 1 - i.val) (.lit 1)
      = dst.getD (dst.length - 1 - i.val) (.lit 1)
    ∨ src.getD (src.length - 1 - i.val) (.lit 1) = .lit 1

/-- S2: the lifting lemma at the broadcast corner, now against the core
relation (supersedes the probe's structural mirror): a symbolic
trailing-axis compatibility fact instantiates to `Shape.broadcastsTo`
at every assignment σ. -/
theorem SShape.broadcastsToS_inst (σ : Nat → Nat) {src dst : SShape}
    (h : src.broadcastsToS dst) :
    Shape.broadcastsTo (src.inst σ) (dst.inst σ) := by
  obtain ⟨hlen, hax⟩ := h
  refine ⟨by simpa using hlen, ?_⟩
  intro i
  have hi : i.val < src.length := by
    simpa using i.isLt
  have hsrc :
      (src.inst σ).getD ((src.inst σ).length - 1 - i.val) 1
        = SExtent.inst σ (src.getD (src.length - 1 - i.val) (.lit 1)) := by
    have := getD_map_comm (SExtent.inst σ) src
      (src.length - 1 - i.val) (.lit 1)
    simpa [SShape.inst] using this
  have hdst :
      (dst.inst σ).getD ((dst.inst σ).length - 1 - i.val) 1
        = SExtent.inst σ (dst.getD (dst.length - 1 - i.val) (.lit 1)) := by
    have := getD_map_comm (SExtent.inst σ) dst
      (dst.length - 1 - i.val) (.lit 1)
    simpa [SShape.inst] using this
  rcases hax ⟨i.val, hi⟩ with heq | hone
  · left
    rw [hsrc, hdst]
    exact SExtent.instEq_of_syn σ heq
  · right
    rw [hsrc, hone]
    rfl

/-- A contraction pattern over symbolic index extents (S3): the core
`ContractPattern` with `indexExtent` valued in `SExtent`; bindings are
untouched (they are combinatorial data, extent-free). -/
structure SContractPattern (inputRanks : List Nat) (outputRank : Nat) where
  nIndices      : Nat
  indexExtent   : Fin nIndices → SExtent
  inputBinding  : (i : Fin inputRanks.length) → Fin (inputRanks.get i) → Fin nIndices
  outputBinding : Fin outputRank → Fin nIndices

def SContractPattern.inst (σ : Nat → Nat) {ir : List Nat} {orank : Nat}
    (pat : SContractPattern ir orank) : ContractPattern ir orank where
  nIndices      := pat.nIndices
  indexExtent   := fun j => (pat.indexExtent j).inst σ
  inputBinding  := pat.inputBinding
  outputBinding := pat.outputBinding

@[simp] theorem SContractPattern.inst_nIndices (σ : Nat → Nat)
    {ir : List Nat} {orank : Nat} (pat : SContractPattern ir orank) :
    (pat.inst σ).nIndices = pat.nIndices := rfl

/-- The ten boxes over the extended extent alphabet, per the plate
design's lift table. `const` and `reshape` deliberately carry *literal*
(core-language) data — the refusals. -/
inductive SPrimApp where
  | const     (ty : TensorType) (c : TensorValue ty) (out : Wire)
  | contract  (δ : Dtype) (r : RoundMode)
              (inputs : List Wire) (output : Wire)
              (inputRanks : List Nat) (outputRank : Nat)
              (pat : SContractPattern inputRanks outputRank)
  | cast      (δfrom δto : Dtype) (r : RoundMode)
              (shape : SShape) (input output : Wire)
  | cell      (schema : SimpC) (input : Wire) (outputs : List Wire)
  | reshape   (newShape : Shape) (input output : Wire)
  | broadcast (toShape : SShape) (input output : Wire)
  | copy      (k : Nat) (input : Wire) (outputs : List Wire)
  | delete    (input : Wire)
  | swap      (in1 in2 out1 out2 : Wire)
  | stack     (k : Nat) (shape : SShape) (inputs : List Wire) (output : Wire)

namespace SPrimApp

/-- Instantiation into the core `PrimApp` (S4): replace every symbolic
extent by its value; wires and combinatorial data untouched. -/
def inst (σ : Nat → Nat) : SPrimApp → PrimApp
  | .const ty c out => .const ty c out
  | .contract δ r ins out ir orank pat =>
      .contract δ r ins out ir orank (pat.inst σ)
  | .cast δf δt r shape i o => .cast δf δt r (shape.inst σ) i o
  | .cell schema i outs => .cell schema i outs
  | .reshape ns i o => .reshape ns i o
  | .broadcast ts i o => .broadcast (ts.inst σ) i o
  | .copy k i outs => .copy k i outs
  | .delete i => .delete i
  | .swap a b c d => .swap a b c d
  | .stack k shape ins o => .stack k (shape.inst σ) ins o

def inputWiresS : SPrimApp → List Wire
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

def outputWiresS : SPrimApp → List Wire
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

/-- S4: instantiation preserves the wire structure (graph-level
homomorphism), input side. -/
@[simp] theorem inst_inputWires (σ : Nat → Nat) (a : SPrimApp) :
    (a.inst σ).inputWires = a.inputWiresS := by
  cases a <;> rfl

/-- S4: instantiation preserves the wire structure, output side. -/
@[simp] theorem inst_outputWires (σ : Nat → Nat) (a : SPrimApp) :
    (a.inst σ).outputWires = a.outputWiresS := by
  cases a <;> rfl

/-- The lifted typing table (S6), one clause per box, extent equality
syntactic throughout. See the module docstring for the three refusals
(`const`, `reshape`, plate-free `cell`). -/
def TypeConsistentS (swt : Wire → Option STensorType) : SPrimApp → Prop
  | .const ty _ out => swt out = some (STensorType.lift ty)
  | .contract δ _ inputs output inputRanks outputRank pat =>
      inputs.length = inputRanks.length ∧
      (∀ p ∈ inputs.zip inputRanks,
        ∃ τ, swt p.1 = some τ ∧ τ.dtype = δ ∧ τ.shape.length = p.2) ∧
      (∃ τ, swt output = some τ ∧ τ.dtype = δ ∧
            τ.shape.length = outputRank) ∧
      (∀ i : Fin inputRanks.length, ∀ a : Fin (inputRanks.get i),
        ∃ τ, swt (inputs.getD i.val 0) = some τ ∧
             τ.shape.getD a.val (.lit 0)
               = pat.indexExtent (pat.inputBinding i a)) ∧
      (∀ a : Fin outputRank,
        ∃ τ, swt output = some τ ∧
             τ.shape.getD a.val (.lit 0)
               = pat.indexExtent (pat.outputBinding a))
  | .cast δfrom δto _ shape input output =>
      swt input = some ⟨shape, δfrom⟩ ∧ swt output = some ⟨shape, δto⟩
  | .cell schema input outputs =>
      (∃ δ, swt input = some ⟨[.lit schema.ambDim], δ⟩) ∧
      outputs.length = schema.cells.length ∧
      (∀ o ∈ outputs, swt o = some ⟨[], Dtype.B⟩)
  | .reshape newShape input output =>
      ∃ s : Shape, ∃ δ, swt input = some ⟨SShape.lift s, δ⟩ ∧
           s.totalSize = newShape.totalSize ∧
           swt output = some ⟨SShape.lift newShape, δ⟩
  | .broadcast toShape input output =>
      ∃ τ, swt input = some τ ∧ τ.shape.broadcastsToS toShape ∧
           swt output = some ⟨toShape, τ.dtype⟩
  | .copy k input outputs =>
      outputs.length = k ∧
      ∃ τ, swt input = some τ ∧ ∀ o ∈ outputs, swt o = some τ
  | .delete input => (swt input).isSome
  | .swap in1 in2 out1 out2 =>
      (swt in1).isSome ∧ (swt in2).isSome ∧
      swt out1 = swt in2 ∧ swt out2 = swt in1
  | .stack k shape inputs output =>
      inputs.length = k ∧
      ∃ τ, swt output = some τ ∧ τ.shape = .lit k :: shape ∧
        ∀ w ∈ inputs, swt w = some ⟨shape, τ.dtype⟩

end SPrimApp

/-- Linearity over the plated syntax (core formula, symbolic wires). -/
def LinearityS (apps : List SPrimApp) : Prop :=
  (apps.flatMap SPrimApp.inputWiresS).Nodup ∧
  (apps.flatMap SPrimApp.outputWiresS).Nodup

/-- Acyclicity over the plated syntax (core formula). -/
def AcyclicS (apps : List SPrimApp) : Prop :=
  ∀ i : Fin apps.length, ∀ w ∈ apps[i].inputWiresS,
    ∀ j : Fin apps.length, w ∈ apps[j].outputWiresS → j < i

def TypeConsistentAllS (swt : Wire → Option STensorType)
    (apps : List SPrimApp) : Prop :=
  ∀ app ∈ apps, app.TypeConsistentS swt

/-- A plated hypernet: the core record over the extended extent
alphabet, plus the (advisory) plate-declaration count. A plate-free
plated hypernet is a hypernet, byte for byte; the
instantiation into the core `Hypernet` lives in `Qtsl.Plate.TPlate`. -/
structure PlatedHypernet where
  /-- Number of declared plate variables. Advisory (a
  count-bound hint): never consumed by typing or semantics —
  assignments quantify over all of `Nat → Nat`. -/
  plates : Nat
  wireTypeS      : Wire → Option STensorType
  applications   : List SPrimApp
  linearity      : LinearityS applications
  acyclic        : AcyclicS applications
  typeConsistent : TypeConsistentAllS wireTypeS applications

end Plate
end PPLC
