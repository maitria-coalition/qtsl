import Qtsl.Catalogue

/-!
# Flavored cell schemas: tensor-simplicial and full-semialgebraic

The core `cell` box takes an abstract `SimpC` schema, and its semantic
well-formedness conjunct `SimpC.CellIntDisjoint` quantifies over real
barycentric weights — not checkable from the schema data by any finite
scan. This module gives the schema two concrete finitely-presented
flavors under which that side condition becomes cheap or free:

1. **Tensor-simplicial** (`CellSchemaTS`): a partition of the flat
   ambient dimensions into clusters — the data is a total function
   `Fin D → Fin m`, the total-function form of a dtype-nat partition
   tensor — with one `SimpC` per cluster; cells are Cartesian products
   of per-cluster cells. `CellSchemaTS.product_exclusion` reduces the
   product-level exclusion to per-cluster exclusion: the certificate
   burden collapses from quadratic in the (exponentially many) product
   cells to additive in the clusters, and library cluster species carry
   once-proved exclusion lemmas (zero certificate bytes; cite the
   species).
2. **Full-semialgebraic** (`CellSchemaSA`): a finite list of
   dimension-1-codomain, cell-free hypernets over the host wire type;
   cells are weak-sign combinations `σ : Fin k → Bool` (`true = ⊕`).
   `sign_exclusion` makes the exclusion a theorem of the presentation —
   uniform in the presenting functions, no geometry, no certificate
   bytes.

## The sign convention: weak two-way signs, not classical three-way

The classical sign-condition decomposition `{-,0,+}^k` keeps the
topological interior-disjointness *property* — wall cells (some
`σ i = 0`) have empty ambient interior, so interiors remain disjoint —
but kills the cheap syntactic *proxy*: the exclusion form used here
(strict-in-one-cell excludes weak-in-another, obtained by strictifying
the defining inequalities) either forces wall cells to strictify to the
empty system (vacuous freight) or, under a relative-interior reading of
"strict", makes the syntactic lemma false, demanding a topological
reformulation. Weak signs `{⊕,⊖}^k` are the convention where proxy and
property coincide definitionally: walls `f i x = 0` belong weakly to
both adjacent cells, and strict-interior rules are sound-by-
unavailability at walls — the hemicontinuous boundary convention the
core `cell` box already has, and exactly `ReluExpansion.sigmaPM`'s two
cells at `k = 1`. `sign_exclusion` is accordingly stated as the
syntactic strict-weak exclusion, with the strict-strict corollary
beside it. (If wall cells are ever wanted first-class, they are
derivable as intersections of adjacent weak cells — a downstream
refinement, not a schema change.)

## Witness economy: emptiness is the schema-side certificate

Nonemptiness of a cell discharges at each use site — the consumer's own
input point checks `k` strict signs — so the schema carries no witness-
point slot. Emptiness is what discharges *downstream universal proof
obligations* (a branch over an empty cell is vacuous), so the optional
schema slot is a per-cell emptiness marker (`CellSchemaSA.prunedEmpty`):
existentials discharge at use, universals want pruning at the schema.
The certificate payload backing a marker is checker-side data; its Lean
consumption form is `CellSchemaSA.EmptyCellOk`.

Definitional expansions of both flavors into the core `cell` box, and
the adequacy theorems tying the direct semantics below to admissible
valuations of those expansions, are the companion development; this
module is deliberately independent of the soundness spine.
-/

namespace PPLC

/-- Strict mask-region membership implies weak membership. -/
theorem MaskRegionStrict.maskRegion {C : SimpC}
    {mask ext : Fin C.nVertices → Bool} {x : Fin C.ambDim → ℚ}
    (h : MaskRegionStrict C mask ext x) : MaskRegion C mask ext x := by
  obtain ⟨lam, hsupp, hsum, hcoord, hext, hcore⟩ := h
  exact ⟨lam, hsupp, hsum, hcoord,
    fun v hv => le_of_lt (hext v hv),
    fun v hm he => le_of_lt (hcore v hm he)⟩

/-! ## Flavor 1: tensor-simplicial -/

/-- The flat ambient positions belonging to cluster `c`, in ascending
flat order (`List.finRange` is ascending and `filter` preserves order). -/
def clusterDims {D m : ℕ} (part : Fin D → Fin m) (c : Fin m) :
    List (Fin D) :=
  (List.finRange D).filter (fun p => part p == c)

/-- A tensor-simplicial cell schema: a partition of the `D` flat ambient
dimensions into `m` clusters (the total-function form of a dtype-nat
partition tensor), and one simplicial complex per cluster whose ambient
dimension is the cluster's size. Cells are Cartesian products of
per-cluster cells; the product cell list is derived, never stored. -/
structure CellSchemaTS where
  /-- flat ambient dimension of the host wire type (its total size). -/
  D : ℕ
  /-- number of clusters. -/
  m : ℕ
  /-- the partition: flat position `p` belongs to cluster `part p`. -/
  part : Fin D → Fin m
  /-- the per-cluster simplicial complexes. -/
  complexes : Fin m → SimpC
  /-- each cluster's complex lives in ambient dimension = cluster size. -/
  dimsMatch : ∀ c, (complexes c).ambDim = (clusterDims part c).length

namespace CellSchemaTS

variable (T : CellSchemaTS)

/-- Projection of an ambient point to cluster `c`'s coordinates, in
ascending flat order. -/
def proj (c : Fin T.m) (x : Fin T.D → ℚ) :
    Fin (T.complexes c).ambDim → ℚ :=
  fun j => x ((clusterDims T.part c).get (Fin.cast (T.dimsMatch c) j))

/-- A product-cell index: one cell choice per cluster. (The box-level
flat output index is the mixed-radix flattening of this tuple; that
bookkeeping belongs to the definitional expansion, not to the
semantics.) -/
def CellIdx : Type :=
  (c : Fin T.m) → Fin (T.complexes c).cells.length

/-- Weak membership in the product cell `κ`: weak membership in every
cluster's chosen cell. -/
def Mem (κ : T.CellIdx) (x : Fin T.D → ℚ) : Prop :=
  ∀ c : Fin T.m,
    MaskRegion (T.complexes c)
      ((T.complexes c).cells.get (κ c)).1
      ((T.complexes c).cells.get (κ c)).2 (T.proj c x)

/-- Strict membership in the product cell `κ`: strict membership in
every cluster's chosen cell. Componentwise strictness is the honest
relative interior — the relative interior of a product of convex sets
is the product of the relative interiors. -/
def MemStrict (κ : T.CellIdx) (x : Fin T.D → ℚ) : Prop :=
  ∀ c : Fin T.m,
    MaskRegionStrict (T.complexes c)
      ((T.complexes c).cells.get (κ c)).1
      ((T.complexes c).cells.get (κ c)).2 (T.proj c x)

theorem MemStrict.mem {T : CellSchemaTS} {κ : T.CellIdx}
    {x : Fin T.D → ℚ} (h : T.MemStrict κ x) : T.Mem κ x :=
  fun c => (h c).maskRegion

/-- The flavored strict-vs-weak exclusion property, mirroring
`SimpC.CellIntDisjoint` at the product level. -/
def CellIntDisjoint : Prop :=
  ∀ κ ν : T.CellIdx, κ ≠ ν →
    ∀ x : Fin T.D → ℚ, T.MemStrict κ x → ¬ T.Mem ν x

/-- **Product exclusion**: per-cluster exclusion implies product-cell
exclusion. Distinct product cells differ at some cluster `c`; strict
membership gives strict membership at `c`, weak membership gives weak
membership at `c`, and cluster `c`'s exclusion refutes. The proof is
uniform in the schema data — which is the whole point: the certificate
burden for the product schema is per-cluster only (additive), never
per-product-cell-pair (exponential). -/
theorem product_exclusion
    (h : ∀ c, (T.complexes c).CellIntDisjoint) : T.CellIntDisjoint := by
  intro κ ν hκν x hs hw
  obtain ⟨c, hc⟩ := Function.ne_iff.mp hκν
  exact h c (κ c) (ν c) hc (T.proj c x) (hs c) (hw c)

/-- Strict-strict corollary: distinct product cells have disjoint
(relative) interiors. -/
theorem strict_exclusion
    (h : ∀ c, (T.complexes c).CellIntDisjoint)
    {κ ν : T.CellIdx} (hκν : κ ≠ ν) (x : Fin T.D → ℚ)
    (hs : T.MemStrict κ x) : ¬ T.MemStrict ν x :=
  fun hn => T.product_exclusion h κ ν hκν x hs hn.mem

end CellSchemaTS

/-! ## Flavor 2: full-semialgebraic -/

/-- Whether a primitive application is a `cell` box. -/
def PrimApp.usesCell : PrimApp → Bool
  | .cell _ _ _ => true
  | _ => false

/-- A hypernet is cell-free when none of its applications is a `cell`
box. Semantically this makes the presenting functions deterministic
(no boundary nondeterminism imported into the presenters, so sign
fibers are honest semialgebraic regions); structurally it makes the
schema-in-hypernet recursion well-founded on sight (one stratum). -/
def Hypernet.CellFree (H : Hypernet) : Prop :=
  ∀ app ∈ H.applications, app.usesCell = false

/-- Signed reading of a scalar: `⊕` (`true`) reads `y`, `⊖` (`false`)
reads `-y`; both memberships below are weak in `signVal`, so the walls
`y = 0` belong to both adjacent cells.

THE SIGN-CONVENTION LOCUS: a flip to classical three-way `{-,0,+}`
signs is a localized edit to this definition (a three-valued sign type)
and the two membership predicates below — and `sign_exclusion` becomes
false for wall cells under it (see the module docstring), which is the
reason for the weak two-way convention. -/
def signVal (s : Bool) (y : ℚ) : ℚ :=
  if s then y else -y

theorem signVal_not (s : Bool) (y : ℚ) :
    signVal (!s) y = -(signVal s y) := by
  cases s <;> simp [signVal]

/-- Weak membership of a value vector `y` (the presenting functions'
outputs at some ambient point) in the sign cell `σ`. Stated at the
value-vector level: the exclusion below is uniform in the presenting
functions, and the adequacy development instantiates `y` with the
spliced hypernets' output values — the per-valuation reading, which
survives even relational presenters. -/
def SignMem {k : ℕ} (y : Fin k → ℚ) (σ : Fin k → Bool) : Prop :=
  ∀ i, 0 ≤ signVal (σ i) (y i)

/-- Strict membership of a value vector in the sign cell `σ`: the
cell's interior, away from every wall. -/
def SignMemStrict {k : ℕ} (y : Fin k → ℚ) (σ : Fin k → Bool) : Prop :=
  ∀ i, 0 < signVal (σ i) (y i)

theorem SignMemStrict.signMem {k : ℕ} {y : Fin k → ℚ}
    {σ : Fin k → Bool} (h : SignMemStrict y σ) : SignMem y σ :=
  fun i => le_of_lt (h i)

/-- **Sign exclusion**: distinct weak-sign cells satisfy the syntactic
strict-vs-weak exclusion — uniformly in the presenting functions, no
geometry, no certificate bytes. The exclusion side condition of the
cell typing rule is a theorem of this presentation. -/
theorem sign_exclusion {k : ℕ} {y : Fin k → ℚ} {σ τ : Fin k → Bool}
    (hστ : σ ≠ τ) (hs : SignMemStrict y σ) : ¬ SignMem y τ := by
  intro hw
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hστ
  have hτi : τ i = !σ i := by
    cases hσ : σ i <;> cases hτ : τ i <;> simp_all
  have h1 := hs i
  have h2 := hw i
  rw [hτi, signVal_not] at h2
  linarith

/-- Strict-strict corollary: distinct sign cells have disjoint
interiors (ambient interiors — sign cells of a full roster are
full-dimensional wherever nonempty). -/
theorem sign_exclusion_strict {k : ℕ} {y : Fin k → ℚ}
    {σ τ : Fin k → Bool} (hστ : σ ≠ τ) (hs : SignMemStrict y σ) :
    ¬ SignMemStrict y τ :=
  fun ht => sign_exclusion hστ hs ht.signMem

/-- A full-semialgebraic cell schema over host wire type
`⟨hostShape, Q⟩`: `k` presenting hypernets, each cell-free, with a
designated input wire of the host type and a designated rank-1 scalar
output wire. Cells are the weak-sign combinations `Fin k → Bool`
(full roster of `2^k` unless pruned); the cell roster is implicit —
the presentation stays linear in `k`.

`prunedEmpty` marks sign vectors carrying an *emptiness* certificate
(checker-side payload): with the full roster (`prunedEmpty = fun _ =>
false`, the default) coverage is free by sign totality; each pruned
cell owes an emptiness certificate (or an explicit domain-invariant
citation) to keep coverage honest. No nonemptiness witness slot exists
by design — see the module docstring's witness-economy note. -/
structure CellSchemaSA where
  /-- shape of the host wire type (dtype `Q`). -/
  hostShape : Shape
  /-- number of presenting functions; the full cell roster is `2^k`. -/
  k : ℕ
  /-- the presenting hypernets. -/
  funs : Fin k → Hypernet
  /-- designated domain wire of each presenter. -/
  inWire : Fin k → Wire
  /-- designated scalar output wire of each presenter. -/
  outWire : Fin k → Wire
  /-- each presenter consumes the host wire type. -/
  domOk : ∀ i, (funs i).wireType (inWire i) = some ⟨hostShape, Dtype.Q⟩
  /-- each presenter produces a rank-1 scalar (`⟨[1], Q⟩`, matching the
  core `cell` box's rank-1 input convention). -/
  codOk : ∀ i, (funs i).wireType (outWire i) = some ⟨[1], Dtype.Q⟩
  /-- presenters are cell-free (deterministic; one stratum). -/
  cellFree : ∀ i, (funs i).CellFree
  /-- sign vectors marked as empty (certificate-backed pruning);
  default: none — the full roster. -/
  prunedEmpty : (Fin k → Bool) → Bool := fun _ => false

namespace CellSchemaSA

/-- Weak membership relative to a value vector `y` for the presenters'
outputs (the adequacy development ties `y` to admissible valuations of
the spliced presenters). -/
def MemVia (S : CellSchemaSA) (y : Fin S.k → ℚ)
    (σ : Fin S.k → Bool) : Prop :=
  SignMem y σ

/-- Strict membership relative to a value vector. -/
def MemViaStrict (S : CellSchemaSA) (y : Fin S.k → ℚ)
    (σ : Fin S.k → Bool) : Prop :=
  SignMemStrict y σ

/-- The consumption form of the emptiness certificates: no admitted
value vector lies weakly in a pruned cell. A consumer holding
`EmptyCellOk` at its evaluation point ex-falsos every branch over a
pruned cell. -/
def EmptyCellOk (S : CellSchemaSA) (y : Fin S.k → ℚ) : Prop :=
  ∀ σ, S.prunedEmpty σ = true → ¬ SignMem y σ

/-- Schema-level sign exclusion. -/
theorem sign_exclusion (S : CellSchemaSA) {y : Fin S.k → ℚ}
    {σ τ : Fin S.k → Bool} (hστ : σ ≠ τ)
    (hs : S.MemViaStrict y σ) : ¬ S.MemVia y τ :=
  PPLC.sign_exclusion hστ hs

end CellSchemaSA

/-! ## The tagged sum -/

/-- A cell schema in one of its three presentation flavors. The raw
`SimpC` form remains the elaboration target and the one semantic ground
truth; the flavors are presentations under which the exclusion side
condition is cheap (tensor-simplicial: per-cluster) or free
(full-semialgebraic: `sign_exclusion`). -/
inductive CellSchema where
  | raw (C : SimpC)
  | tensorSimplicial (T : CellSchemaTS)
  | semialgebraic (S : CellSchemaSA)

/-- The wire-format flavor tag: `0` raw, `1` tensor-simplicial, `2`
full-semialgebraic (legacy rows with no tag read as `0`). -/
def CellSchema.flavorTag : CellSchema → ℕ
  | .raw _ => 0
  | .tensorSimplicial _ => 1
  | .semialgebraic _ => 2

#print axioms CellSchemaTS.product_exclusion
#print axioms sign_exclusion

end PPLC
