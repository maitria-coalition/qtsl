import Qtsl.PpolyExpansion
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Lattice

/-!
# The denotation class of the primitive calculus

The interface denotation of a hypernet, as a relation: with input and
output ports designated, a hypernet denotes the set of input/output
tuples reachable by an admissible valuation (`Hypernet.DenotRel`).
The denotation is genuinely relational: `cell` semantics admits every
containing cell on a shared boundary, and a point contained in no
listed cell has no admissible valuation at all, so the relation is
multivalued on boundaries and partial wherever a case analysis is
non-exhaustive.

This module defines the target class of the calculus's completion
theorem — the statement that fixed the primitive count at ten — and
states both of its directions precisely.

* `PieceData`, `PieceData.graph`, `IsPiecewisePolyRel` — finite unions
  of graphs of rational-coefficient polynomial maps restricted to
  basic closed pieces (finite conjunctions of polynomial inequalities
  `0 ≤ q`).  This is the finitary, ℚ-pinned stratum of the
  ω-semialgebraic morphism class: countable unions of exactly this
  piece data carve the ω-semialgebraic sets (`SuFunctor.StateSpace`,
  in the semantic-universe development).
* `Hypernet.DenotRel` — the interface denotation.
* The fragment carve `Hypernet.TenBoxOnly`, `Hypernet.ExactBQ`: the
  ten core boxes only, Boolean/rational dtypes, exact rounding.  The
  carve is forced, not stylistic: an integer `cast` under a directed
  rounding mode denotes a floor-class staircase, whose graph is a
  countable — and not finite — union of polynomial pieces, so the
  unrestricted calculus lands in the countably-piecewise
  (ω-semialgebraic) stratum, and the finite-piecewise completion
  statement is exactly the exact-⟨B,Q⟩ fragment's.
* `PrimitiveBasisSound`, `PrimitiveBasisComplete` — the two directions
  of the completion statement, as named propositions.  Soundness:
  every fragment hypernet's denotation lies in the class.  Its
  interface-closure hypothesis (`Hypernet.InterfaceClosed`) is
  load-bearing: leaving a consumed-but-never-produced wire off the
  input interface existentially projects the relation, and projections
  over ℚ escape the class (the image of `z ↦ z²` carves the rational
  squares, which no finite list of polynomial sign conditions cuts
  out).  Completeness: every class member is denoted by some fragment
  hypernet.

The full proofs are staged — list-and-renumbering algebra on the
soundness side, a general polynomial elaborator on the completeness
side — and the two canonical strata are proven here end to end
against the landed expansion nets, as machine-checked instances:

* `denotRel_ppoly_canonical` — the polynomial stratum: the canonical
  polynomial net (`const`/`contract`/`stack`) denotes the graph of its
  polynomial, a one-piece class element.
* `denotRel_relu` — the piecewise stratum: the ReLU core expansion
  (`copy`/`cell`/`cast`/`reshape`/`contract`) denotes the two-piece
  class element `{0 ≤ x ↦ x} ∪ {x ≤ 0 ↦ 0}`: one `cell`, two closed
  pieces, and the boundary overlap at `0` on which the two graphs
  agree — multivaluedness degenerating to agreement exactly because
  the pieces are closed and the piece maps coincide there.

The negative half of the completion story — the nine-box calculus
without `stack` cannot carry cross-wire sums (the packing gap) — has
its own mechanization lineage in the design record; this module owns
the positive half's statement and its first machine-checked instances.
-/

namespace PPLC

open MvPolynomial

/-! ## The class: finite unions of polynomial graphs over basic closed pieces -/

/-- One piece of a piecewise-polynomial relation: a basic closed piece
(the conjunction of `0 ≤ q` over `conds`) together with the polynomial
map defined on it.  All coefficients are pinned to ℚ — a piece is
finite, exactly-transmissible data. -/
structure PieceData (d m : ℕ) : Type where
  /-- The carving conditions; the piece is their conjunction, each read
  as `0 ≤ q(x)`.  Equations enter as pairs `q, -q`. -/
  conds : List (MvPolynomial (Fin d) ℚ)
  /-- The polynomial map the relation takes on this piece. -/
  val : Fin m → MvPolynomial (Fin d) ℚ

/-- The graph of a piece: inputs satisfying the carving, paired with
the piece map's values. -/
def PieceData.graph {d m : ℕ} (P : PieceData d m) :
    Set ((Fin d → ℚ) × (Fin m → ℚ)) :=
  { xy | (∀ q ∈ P.conds, 0 ≤ eval xy.1 q) ∧
         ∀ j, xy.2 j = eval xy.1 (P.val j) }

/-- The denotation class: finite unions of graphs of ℚ-polynomial maps
restricted to basic closed ℚ-carved pieces. -/
def IsPiecewisePolyRel {d m : ℕ}
    (R : Set ((Fin d → ℚ) × (Fin m → ℚ))) : Prop :=
  ∃ Ps : List (PieceData d m), R = ⋃ P ∈ Ps, P.graph

namespace IsPiecewisePolyRel

theorem of_eq_graph {d m : ℕ} {R : Set ((Fin d → ℚ) × (Fin m → ℚ))}
    (P : PieceData d m) (h : R = P.graph) : IsPiecewisePolyRel R := by
  refine ⟨[P], ?_⟩
  rw [h]
  ext z
  constructor
  · intro hz
    exact Set.mem_iUnion₂.mpr ⟨P, List.mem_cons_self .., hz⟩
  · intro hz
    obtain ⟨Q, hQ, hzQ⟩ := Set.mem_iUnion₂.mp hz
    rw [List.mem_singleton.mp hQ] at hzQ
    exact hzQ

theorem of_eq_graph_union {d m : ℕ} {R : Set ((Fin d → ℚ) × (Fin m → ℚ))}
    (P Q : PieceData d m) (h : R = P.graph ∪ Q.graph) :
    IsPiecewisePolyRel R := by
  refine ⟨[P, Q], ?_⟩
  rw [h]
  ext z
  constructor
  · rintro (hz | hz)
    · exact Set.mem_iUnion₂.mpr ⟨P, List.mem_cons_self .., hz⟩
    · exact Set.mem_iUnion₂.mpr
        ⟨Q, List.mem_cons_of_mem _ (List.mem_cons_self ..), hz⟩
  · intro hz
    obtain ⟨T, hT, hzT⟩ := Set.mem_iUnion₂.mp hz
    rcases List.mem_cons.mp hT with rfl | hT'
    · exact Or.inl hzT
    · rw [List.mem_singleton.mp hT'] at hzT
      exact Or.inr hzT

theorem empty (d m : ℕ) :
    IsPiecewisePolyRel (∅ : Set ((Fin d → ℚ) × (Fin m → ℚ))) := by
  refine ⟨[], ?_⟩
  ext z
  simp

theorem union {d m : ℕ} {R S : Set ((Fin d → ℚ) × (Fin m → ℚ))}
    (hR : IsPiecewisePolyRel R) (hS : IsPiecewisePolyRel S) :
    IsPiecewisePolyRel (R ∪ S) := by
  obtain ⟨Ps, rfl⟩ := hR
  obtain ⟨Qs, rfl⟩ := hS
  refine ⟨Ps ++ Qs, ?_⟩
  ext z
  constructor
  · rintro (hz | hz)
    · obtain ⟨P, hP, hzP⟩ := Set.mem_iUnion₂.mp hz
      exact Set.mem_iUnion₂.mpr ⟨P, List.mem_append_left _ hP, hzP⟩
    · obtain ⟨Q, hQ, hzQ⟩ := Set.mem_iUnion₂.mp hz
      exact Set.mem_iUnion₂.mpr ⟨Q, List.mem_append_right _ hQ, hzQ⟩
  · intro hz
    obtain ⟨P, hP, hzP⟩ := Set.mem_iUnion₂.mp hz
    rcases List.mem_append.mp hP with h | h
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨P, h, hzP⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨P, h, hzP⟩)

/-- Total polynomial maps are in the class: a single piece with no
carving conditions. -/
theorem polyGraph {d m : ℕ} (g : Fin m → MvPolynomial (Fin d) ℚ) :
    IsPiecewisePolyRel { xy : (Fin d → ℚ) × (Fin m → ℚ) |
      ∀ j, xy.2 j = eval xy.1 (g j) } := by
  refine of_eq_graph ⟨[], g⟩ ?_
  ext z
  constructor
  · intro hz
    exact ⟨fun q hq => absurd hq List.not_mem_nil, hz⟩
  · intro hz
    exact hz.2

end IsPiecewisePolyRel

/-! ## The interface denotation -/

/-- The interface denotation of a hypernet: input and output ports
designated as wires (each read at its first entry), the relation of
port tuples reachable by an admissible valuation. -/
def Hypernet.DenotRel (H : Hypernet) (d m : ℕ)
    (ins : Fin d → Wire) (outs : Fin m → Wire) :
    Set ((Fin d → ℚ) × (Fin m → ℚ)) :=
  { xy | ∃ σ : H.Valuation, σ.Admissible ∧
      (∀ i, σ.entryFlat (ins i) 0 = some (.fin (xy.1 i))) ∧
      (∀ j, σ.entryFlat (outs j) 0 = some (.fin (xy.2 j))) }

/-! ## The fragment: ten boxes, Boolean/rational dtypes, exact rounding -/

/-- The ten primitive boxes; the packaged symbols are views, not
members of the basis. -/
def PrimApp.isTenBox : PrimApp → Bool
  | .const .. | .contract .. | .cast .. | .cell .. | .reshape ..
  | .broadcast .. | .copy .. | .delete .. | .swap .. | .stack .. => true
  | .relu .. | .ppoly .. | .pderiv .. | .facet .. => false

/-- Boolean or exact-rational dtype. -/
def Dtype.isBQ : Dtype → Bool
  | ⟨.bool, .nn, .fin⟩ => true
  | ⟨.rat, .signed, .fin⟩ => true
  | _ => false

/-- Exact rounding mode. -/
def RoundMode.isExact : RoundMode → Bool
  | .exact => true
  | _ => false

/-- Per-application fragment check: payload dtypes Boolean/rational,
rounding exact.  Structural boxes carry no dtype or rounding payload
and pass; the packaged symbols are excluded by `isTenBox`, not here. -/
def PrimApp.exactBQ : PrimApp → Bool
  | .const ty _ _ => ty.dtype.isBQ
  | .contract δ r _ _ _ _ _ => δ.isBQ && r.isExact
  | .cast δfrom δto r _ _ _ => δfrom.isBQ && δto.isBQ && r.isExact
  | .cell .. | .reshape .. | .broadcast .. | .copy .. | .delete ..
  | .swap .. | .stack .. => true
  | .relu .. | .ppoly .. | .pderiv .. | .facet .. => true

/-- The hypernet is built from the ten primitive boxes only. -/
def Hypernet.TenBoxOnly (H : Hypernet) : Prop :=
  ∀ app ∈ H.applications, app.isTenBox = true

/-- The hypernet computes in the exact ⟨B,Q⟩ fragment: Boolean and
rational dtypes, exact rounding everywhere. -/
def Hypernet.ExactBQ (H : Hypernet) : Prop :=
  ∀ app ∈ H.applications, app.exactBQ = true

/-- A scalar rational port: typed, rational dtype, a single entry. -/
def Hypernet.ScalarQPort (H : Hypernet) (w : Wire) : Prop :=
  ∃ τ, H.wireType w = some τ ∧ τ.dtype = Dtype.Q ∧ τ.shape.totalSize = 1

/-- Wires produced by some application. -/
def Hypernet.producedWires (H : Hypernet) : List Wire :=
  H.applications.flatMap PrimApp.outputWires

/-- Wires consumed by some application. -/
def Hypernet.consumedWires (H : Hypernet) : List Wire :=
  H.applications.flatMap PrimApp.inputWires

/-- Interface closure: the input ports are distinct unproduced wires,
and every consumed-but-never-produced wire is an input port.  Without
this, the denotation existentially projects over an unpinned graph
input, and projections over ℚ escape the piecewise-polynomial class. -/
def Hypernet.InterfaceClosed (H : Hypernet) {d : ℕ}
    (ins : Fin d → Wire) : Prop :=
  Function.Injective ins ∧
  (∀ i, ins i ∉ H.producedWires) ∧
  (∀ w ∈ H.consumedWires, w ∉ H.producedWires → ∃ i, ins i = w)

/-! ## The completion statement, both directions

Stated as named propositions; the full proofs are staged, and the
instances below prove the two canonical strata end to end. -/

/-- **Soundness of the primitive basis** (the containment direction of
the completion statement): every exact-⟨B,Q⟩ ten-box hypernet with a
closed scalar-rational interface denotes a finite union of polynomial
graphs over basic closed pieces. -/
def PrimitiveBasisSound : Prop :=
  ∀ (H : Hypernet) (d m : ℕ) (ins : Fin d → Wire) (outs : Fin m → Wire),
    H.TenBoxOnly → H.ExactBQ → H.InterfaceClosed ins →
    (∀ i, H.ScalarQPort (ins i)) → (∀ j, H.ScalarQPort (outs j)) →
    IsPiecewisePolyRel (H.DenotRel d m ins outs)

/-- **Completeness of the primitive basis** (the generation direction
of the completion statement): every finite union of polynomial graphs
over basic closed pieces is the denotation of some exact-⟨B,Q⟩ ten-box
hypernet. -/
def PrimitiveBasisComplete : Prop :=
  ∀ (d m : ℕ) (Ps : List (PieceData d m)),
    ∃ (H : Hypernet) (ins : Fin d → Wire) (outs : Fin m → Wire),
      H.TenBoxOnly ∧ H.ExactBQ ∧
      (∀ i, H.ScalarQPort (ins i)) ∧ (∀ j, H.ScalarQPort (outs j)) ∧
      H.DenotRel d m ins outs = ⋃ P ∈ Ps, P.graph

/-! ## Instances: the polynomial stratum -/

private theorem fin1_zero (i : Fin 1) : i = 0 :=
  Fin.ext (Nat.lt_one_iff.mp i.isLt)

private theorem evalX1 (x : Fin 1 → ℚ) :
    eval x (X 0 : MvPolynomial (Fin 1) ℚ) = x 0 := by
  simp

private theorem evalNegX1 (x : Fin 1 → ℚ) :
    eval x (-X 0 : MvPolynomial (Fin 1) ℚ) = -(x 0) := by
  simp

/-- The canonical polynomial table evaluates to its polynomial. -/
private theorem evalQ_qCanon (p : ℚ) :
    MonoTable.evalQ PpolyExpansion.qCanon [p] = 3 + 2 * p := by
  show (3 : ℚ) + (p * 2 + 0) = 3 + 2 * p
  ring

/-- The canonical polynomial net denotes the graph of its polynomial:
a one-piece element of the denotation class, machine-checked from the
net's admissible valuations. -/
theorem denotRel_ppoly_canonical :
    PpolyExpansion.ppolyExpH.DenotRel 1 1 ![0] ![6]
      = PieceData.graph ⟨[], ![C 3 + C 2 * X 0]⟩ := by
  ext ⟨x, y⟩
  simp only [Hypernet.DenotRel, PieceData.graph, Set.mem_setOf_eq]
  constructor
  · rintro ⟨σ, hadm, hin, hout⟩
    have hy : y 0 = MonoTable.evalQ PpolyExpansion.qCanon [x 0] :=
      (PpolyExpansion.ppoly_projection (x 0) (y 0)).mp
        ⟨σ, hadm, hin 0, hout 0⟩
    refine ⟨fun q hq => absurd hq List.not_mem_nil, fun j => ?_⟩
    rw [fin1_zero j]
    show y 0 = eval x (C 3 + C 2 * X 0)
    rw [hy, evalQ_qCanon]
    simp [eval_C]
  · rintro ⟨-, hval⟩
    have h0 : y 0 = eval x (C 3 + C 2 * X 0) := hval 0
    have hy : y 0 = MonoTable.evalQ PpolyExpansion.qCanon [x 0] := by
      rw [evalQ_qCanon, h0]
      simp [eval_C]
    obtain ⟨σ, hadm, hp, hq⟩ := PpolyExpansion.ppoly_expansion_complete hy
    exact ⟨σ, hadm,
      fun i => by rw [fin1_zero i]; exact hp,
      fun j => by rw [fin1_zero j]; exact hq⟩

/-- The polynomial-stratum instance of the completion statement's
generation direction. -/
theorem isPiecewisePolyRel_ppoly_canonical :
    IsPiecewisePolyRel (PpolyExpansion.ppolyExpH.DenotRel 1 1 ![0] ![6]) :=
  .of_eq_graph _ denotRel_ppoly_canonical

/-! ## Instances: the piecewise stratum -/

/-- The ReLU core expansion denotes the two-piece class element:
`x` on the nonnegative piece, `0` on the nonpositive piece, the graphs
agreeing on the shared boundary.  The first machine-checked piecewise
instance of the completion statement: one `cell`, two closed pieces. -/
theorem denotRel_relu :
    ReluExpansion.reluExpH.DenotRel 1 1 ![0] ![8]
      = PieceData.graph ⟨[X 0], ![X 0]⟩
        ∪ PieceData.graph ⟨[-X 0], ![0]⟩ := by
  ext ⟨x, y⟩
  simp only [Hypernet.DenotRel, PieceData.graph, Set.mem_union,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨σ, hadm, hin, hout⟩
    rcases (ReluExpansion.relu_projection (x 0) (y 0)).mp
        ⟨σ, hadm, hin 0, hout 0⟩ with ⟨hple, hy0⟩ | ⟨hpge, hyp⟩
    · refine Or.inr ⟨fun q hq => ?_, fun j => ?_⟩
      · rw [List.mem_singleton.mp hq, evalNegX1]
        linarith
      · rw [fin1_zero j]
        show y 0 = eval x (0 : MvPolynomial (Fin 1) ℚ)
        rw [map_zero]
        exact hy0
    · refine Or.inl ⟨fun q hq => ?_, fun j => ?_⟩
      · rw [List.mem_singleton.mp hq, evalX1]
        exact hpge
      · rw [fin1_zero j]
        show y 0 = eval x (X 0 : MvPolynomial (Fin 1) ℚ)
        rw [evalX1]
        exact hyp
  · rintro (⟨hconds, hval⟩ | ⟨hconds, hval⟩)
    · have hx : (0 : ℚ) ≤ x 0 := by
        have h := hconds (X 0) (List.mem_cons_self ..)
        rwa [evalX1] at h
      have hy : y 0 = x 0 := by
        have h : y 0 = eval x (X 0 : MvPolynomial (Fin 1) ℚ) := hval 0
        rwa [evalX1] at h
      obtain ⟨σ, hadm, hp, hq⟩ :=
        ReluExpansion.relu_expansion_complete (Or.inr ⟨hx, hy⟩)
      exact ⟨σ, hadm,
        fun i => by rw [fin1_zero i]; exact hp,
        fun j => by rw [fin1_zero j]; exact hq⟩
    · have hx : x 0 ≤ 0 := by
        have h := hconds (-X 0) (List.mem_cons_self ..)
        rw [evalNegX1] at h
        linarith
      have hy : y 0 = 0 := by
        have h : y 0 = eval x (0 : MvPolynomial (Fin 1) ℚ) := hval 0
        rwa [map_zero] at h
      obtain ⟨σ, hadm, hp, hq⟩ :=
        ReluExpansion.relu_expansion_complete (Or.inl ⟨hx, hy⟩)
      exact ⟨σ, hadm,
        fun i => by rw [fin1_zero i]; exact hp,
        fun j => by rw [fin1_zero j]; exact hq⟩

/-- The piecewise-stratum instance of the completion statement's
generation direction. -/
theorem isPiecewisePolyRel_relu :
    IsPiecewisePolyRel (ReluExpansion.reluExpH.DenotRel 1 1 ![0] ![8]) :=
  .of_eq_graph_union _ _ denotRel_relu

/-! ## Fragment receipts for the instance nets

These make the two instances honest witnesses of the completeness
statement's matrix: both nets are ten-box-only, exact-⟨B,Q⟩, with
scalar rational ports. -/

theorem ppolyExpH_tenBoxOnly : PpolyExpansion.ppolyExpH.TenBoxOnly := by
  intro app h
  fin_cases h <;> rfl

theorem ppolyExpH_exactBQ : PpolyExpansion.ppolyExpH.ExactBQ := by
  intro app h
  fin_cases h <;> rfl

theorem reluExpH_tenBoxOnly : ReluExpansion.reluExpH.TenBoxOnly := by
  intro app h
  fin_cases h <;> rfl

theorem reluExpH_exactBQ : ReluExpansion.reluExpH.ExactBQ := by
  intro app h
  fin_cases h <;> rfl

theorem ppolyExpH_ports :
    PpolyExpansion.ppolyExpH.ScalarQPort 0 ∧
    PpolyExpansion.ppolyExpH.ScalarQPort 6 :=
  ⟨⟨⟨[], Dtype.Q⟩, rfl, rfl, rfl⟩, ⟨⟨[], Dtype.Q⟩, rfl, rfl, rfl⟩⟩

theorem reluExpH_ports :
    ReluExpansion.reluExpH.ScalarQPort 0 ∧
    ReluExpansion.reluExpH.ScalarQPort 8 :=
  ⟨⟨⟨[1], Dtype.Q⟩, rfl, rfl, rfl⟩, ⟨⟨[1], Dtype.Q⟩, rfl, rfl, rfl⟩⟩

#print axioms denotRel_ppoly_canonical
#print axioms isPiecewisePolyRel_ppoly_canonical
#print axioms denotRel_relu
#print axioms isPiecewisePolyRel_relu
#print axioms ppolyExpH_tenBoxOnly
#print axioms ppolyExpH_exactBQ
#print axioms reluExpH_tenBoxOnly
#print axioms reluExpH_exactBQ
#print axioms ppolyExpH_ports
#print axioms reluExpH_ports
#print axioms IsPiecewisePolyRel.union
#print axioms IsPiecewisePolyRel.polyGraph

end PPLC
