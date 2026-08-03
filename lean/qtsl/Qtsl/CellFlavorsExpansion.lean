import Qtsl.CellFlavorsDemo

/-!
# Expansions and adequacy for flavored cell schemas (A1–A3)

Companion development to `Qtsl.CellFlavors`, discharging the design memo's
three adequacy obligations under `Qtsl.ReluExpansion`'s packaged-primitive
discipline — a definitional expansion into core primitives, a typing rule
derivable from the expansion's, and derived semantic facts proven from the
expansion's, never axiomatized. The raw `SimpC`/`MaskRegion` semantics
remains the one semantic ground truth; everything here lowers *to* it.

Two strata, mirroring the discipline's own precedent (ReluExpansion
discharges "at its canonical single-entry rational instance"):

1. **Value level, fully general in the schema data.**
   - The SA sign-to-`MaskRegion` dictionary at general `k`
     (`signMem_iff_lowering`, `signMemStrict_iff_lowering`): sign-cell
     membership and interior coincide with per-coordinate `sigmaPM`
     mask-region membership of the lowering — extending the earlier `k = 1`
     lemmas (`maskRegion_c{Neg,Pos}_iff` and strict companions).
   - The TS one-hot product readout (`indicator_prod_eq`): the product of
     per-cluster indicators is the product-cell indicator — the box-level
     bookkeeping of the per-cluster lowering. (The TS membership
     coincidence itself, `CellSchemaTS.mem_iff_lowering`, is definitional
     *by design*: L1 defined the direct semantics as the lowering's
     per-cluster form; the named statement exists for citation.)
   - A3: exclusion transported across the lowering
     (`sign_exclusion_lowered`; the TS analogue is L1's
     `product_exclusion` verbatim, since the TS direct semantics *is* the
     lowered form), and the consumer-form determination lemmas
     (`CellSchemaTS.interior_determines`, `sign_interior_determines`) —
     the dischargeable-premise payoff HCellInterior consumes: a point
     strictly inside cell κ forces any one-hot cell of the box to be κ.

2. **Hypernet level, at the canonical instance** — the planar quadrant
   fan, ONE hypernet (`quadExpH`) read as both flavors: `quadrantsTS`'s
   expansion and `quadrantsSA`'s expansion coincide (shared
   const+contract projection front end — the memo's F5: no gather
   primitive — shared per-cluster/per-presenter `sigmaPM` boxes, shared
   one-hot product rows); only the output indexing differs, and
   `sigmaCell` mediates. `quadExp_projection` (TS) and
   `quadExp_projection_sa` (SA) are the A1 statements;
   `quadExp_typing` carries A2's interface facts (the side-condition
   lifts are L1's `product_exclusion`/`sign_exclusion`, already proved).

A fully generic hypernet-level A1 (arbitrary schema → generically built
hypernet) is deliberately a successor leg: it is generic hypernet
synthesis, not adequacy.
-/

namespace PPLC
namespace CellFlavorsExpansion

open ReluExpansion CellFlavorsDemo

/-! ## Local helpers (re-proofs of `ReluExpansion`'s private lemmas) -/

private def w0 : Fin sigmaPM.nVertices := ⟨0, by decide⟩
private def w1 : Fin sigmaPM.nVertices := ⟨1, by decide⟩
private def w2 : Fin sigmaPM.nVertices := ⟨2, by decide⟩

private theorem fin1_eq (j : Fin sigmaPM.ambDim) : j = j0 := by
  apply Fin.ext
  show j.val = 0
  have h1 : j.val < 1 := j.isLt
  omega

private theorem roundOk_finQ (q : ℚ) :
    Dtype.Q.RoundOkE .exact (.fin q) (.fin q) :=
  ⟨rfl, trivial, fun h => nomatch h⟩

private theorem roundOk_finB {q : ℚ} (h : q = 0 ∨ q = 1) :
    Dtype.B.RoundOkE .exact (.fin q) (.fin q) :=
  ⟨rfl, h, fun _ => by rcases h with rfl | rfl <;> norm_num⟩

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

/-! ## The strict `sigmaPM` dictionary entries

F2's weak iffs (`maskRegion_c{Neg,Pos}_iff`) already have strict
*forward* directions (`maskRegionStrict_c{Neg,Pos}_lt`); these complete
them to iffs, via `maskRegionStrict_pair_intro` with the same vertex
pairs as the weak intros. -/

theorem maskRegionStrict_cNeg_iff (x : Fin sigmaPM.ambDim → ℚ) :
    MaskRegionStrict sigmaPM
      (sigmaPM.cells.get cNeg).1 (sigmaPM.cells.get cNeg).2 x
      ↔ x j0 < 0 := by
  constructor
  · exact maskRegionStrict_cNeg_lt
  · intro hx
    refine maskRegionStrict_pair_intro (a := w0) (b := w1) (V₀ := 0) (V₁ := 1)
      (by decide) (by decide) (by decide) (by decide) (by norm_num) (by decide)
      j0 ?_ ?_ ?_ ?_
    · intro h; exact absurd h (by decide)
    · intro _
      have : (0 : ℚ) < 1 - x j0 := by linarith
      simpa using this
    · intro _
      simpa using hx
    · intro h; exact absurd h (by decide)

theorem maskRegionStrict_cPos_iff (x : Fin sigmaPM.ambDim → ℚ) :
    MaskRegionStrict sigmaPM
      (sigmaPM.cells.get cPos).1 (sigmaPM.cells.get cPos).2 x
      ↔ 0 < x j0 := by
  constructor
  · exact maskRegionStrict_cPos_lt
  · intro hx
    refine maskRegionStrict_pair_intro (a := w0) (b := w2) (V₀ := 0) (V₁ := -1)
      (by decide) (by decide) (by decide) (by decide) (by norm_num) (by decide)
      j0 ?_ ?_ ?_ ?_
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

/-! ## The sign-to-cell dictionary, unified over the sign -/

/-- The `sigmaPM` cell selected by a weak sign: `⊕` (`true`) selects
`cPos` (`{x ≥ 0}`), `⊖` (`false`) selects `cNeg` (`{x ≤ 0}`). THE
DICTIONARY LOCUS: this is the single point where sign vectors meet the
core box's cell roster. -/
def sigmaCell (s : Bool) : Fin sigmaPM.cells.length :=
  if s then cPos else cNeg

theorem maskRegion_sigmaCell_iff (s : Bool) (x : Fin sigmaPM.ambDim → ℚ) :
    MaskRegion sigmaPM
      (sigmaPM.cells.get (sigmaCell s)).1 (sigmaPM.cells.get (sigmaCell s)).2 x
      ↔ 0 ≤ signVal s (x j0) := by
  cases s
  · rw [show sigmaCell false = cNeg from rfl, maskRegion_cNeg_iff]
    simp [signVal]
  · rw [show sigmaCell true = cPos from rfl, maskRegion_cPos_iff]
    simp [signVal]

theorem maskRegionStrict_sigmaCell_iff (s : Bool) (x : Fin sigmaPM.ambDim → ℚ) :
    MaskRegionStrict sigmaPM
      (sigmaPM.cells.get (sigmaCell s)).1 (sigmaPM.cells.get (sigmaCell s)).2 x
      ↔ 0 < signVal s (x j0) := by
  cases s
  · rw [show sigmaCell false = cNeg from rfl, maskRegionStrict_cNeg_iff]
    simp [signVal]
  · rw [show sigmaCell true = cPos from rfl, maskRegionStrict_cPos_iff]
    simp [signVal]

/-! ## A1 (SA flavor, value level): the dictionary at general k -/

/-- **A1 (SA, weak)**: sign-cell membership coincides with the
`MaskRegion` semantics of the lowering — one `sigmaPM` box per
presenting function, cell selected by `sigmaCell`. The earlier `k = 1`
lemmas are the single-coordinate case. -/
theorem signMem_iff_lowering {k : ℕ} (y : Fin k → ℚ) (σ : Fin k → Bool) :
    SignMem y σ ↔
      ∀ i, MaskRegion sigmaPM
        (sigmaPM.cells.get (sigmaCell (σ i))).1
        (sigmaPM.cells.get (sigmaCell (σ i))).2 (fun _ => y i) := by
  constructor
  · intro h i
    exact (maskRegion_sigmaCell_iff (σ i) (fun _ => y i)).mpr (h i)
  · intro h i
    exact (maskRegion_sigmaCell_iff (σ i) (fun _ => y i)).mp (h i)

/-- **A1 (SA, strict)**: sign-cell interior coincides with the strict
`MaskRegion` semantics of the lowering. -/
theorem signMemStrict_iff_lowering {k : ℕ} (y : Fin k → ℚ) (σ : Fin k → Bool) :
    SignMemStrict y σ ↔
      ∀ i, MaskRegionStrict sigmaPM
        (sigmaPM.cells.get (sigmaCell (σ i))).1
        (sigmaPM.cells.get (sigmaCell (σ i))).2 (fun _ => y i) := by
  constructor
  · intro h i
    exact (maskRegionStrict_sigmaCell_iff (σ i) (fun _ => y i)).mpr (h i)
  · intro h i
    exact (maskRegionStrict_sigmaCell_iff (σ i) (fun _ => y i)).mp (h i)

/-- Schema-level face of the weak dictionary. -/
theorem _root_.PPLC.CellSchemaSA.memVia_iff_lowering (S : CellSchemaSA)
    (y : Fin S.k → ℚ) (σ : Fin S.k → Bool) :
    S.MemVia y σ ↔
      ∀ i, MaskRegion sigmaPM
        (sigmaPM.cells.get (sigmaCell (σ i))).1
        (sigmaPM.cells.get (sigmaCell (σ i))).2 (fun _ => y i) :=
  signMem_iff_lowering y σ

/-- Schema-level face of the strict dictionary. -/
theorem _root_.PPLC.CellSchemaSA.memViaStrict_iff_lowering (S : CellSchemaSA)
    (y : Fin S.k → ℚ) (σ : Fin S.k → Bool) :
    S.MemViaStrict y σ ↔
      ∀ i, MaskRegionStrict sigmaPM
        (sigmaPM.cells.get (sigmaCell (σ i))).1
        (sigmaPM.cells.get (sigmaCell (σ i))).2 (fun _ => y i) :=
  signMemStrict_iff_lowering y σ

/-! ## A1 (TS flavor, value level) -/

/-- **A1 (TS, weak)**: product-cell membership coincides with the
per-cluster `MaskRegion` conjunction of the lowering. `Iff.rfl`, and
honestly so: L1 *defined* the direct semantics as the lowering's
per-cluster form — this named statement exists so downstream work cites
adequacy rather than a definitional unfold. The non-definitional TS
content is the readout bookkeeping (`indicator_prod_eq`) and the
hypernet-level instance below. -/
theorem _root_.PPLC.CellSchemaTS.mem_iff_lowering (T : CellSchemaTS)
    (κ : T.CellIdx) (x : Fin T.D → ℚ) :
    T.Mem κ x ↔
      ∀ c, MaskRegion (T.complexes c)
        ((T.complexes c).cells.get (κ c)).1
        ((T.complexes c).cells.get (κ c)).2 (T.proj c x) :=
  Iff.rfl

/-- **A1 (TS, strict)**: product-cell interior coincides with the strict
per-cluster conjunction — see `mem_iff_lowering`'s docstring. -/
theorem _root_.PPLC.CellSchemaTS.memStrict_iff_lowering (T : CellSchemaTS)
    (κ : T.CellIdx) (x : Fin T.D → ℚ) :
    T.MemStrict κ x ↔
      ∀ c, MaskRegionStrict (T.complexes c)
        ((T.complexes c).cells.get (κ c)).1
        ((T.complexes c).cells.get (κ c)).2 (T.proj c x) :=
  Iff.rfl

/-- **The one-hot product readout**: the product of per-cluster
indicators is the product-cell indicator. This is the semantic content
of the TS expansion's product `contract` rows — each cluster's box
one-hots some cell, and multiplying the chosen indicators one-hots the
product cell exactly at the tuple of hot cells. -/
theorem indicator_prod_eq {m : ℕ} {n : Fin m → ℕ}
    (κ k : (c : Fin m) → Fin (n c)) :
    ((List.finRange m).map (fun c => if κ c = k c then (1 : ℚ) else 0)).prod
      = if κ = k then 1 else 0 := by
  by_cases h : κ = k
  · subst h
    rw [if_pos rfl]
    refine List.prod_eq_one ?_
    intro a ha
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp ha
    rw [if_pos rfl]
  · rw [if_neg h]
    obtain ⟨c, hc⟩ := Function.ne_iff.mp h
    refine List.prod_eq_zero ?_
    exact List.mem_map.mpr ⟨c, List.mem_finRange c, by rw [if_neg hc]⟩

/-! ## A3: exclusion transport and the consumer-form determination -/

/-- **A3 (SA)**: strict-vs-weak exclusion of distinct sign cells, stated
against the lowered `MaskRegion` form — the flavored exclusion holds of
the lowering's semantics, so HCellInterior instantiated at an SA schema
has a sound premise in either vocabulary. (The TS analogue needs no new
theorem: the TS direct semantics IS the lowered form, so L1's
`CellSchemaTS.product_exclusion` is already the lowered-level
exclusion.) -/
theorem sign_exclusion_lowered {k : ℕ} {y : Fin k → ℚ} {σ τ : Fin k → Bool}
    (hστ : σ ≠ τ)
    (hs : ∀ i, MaskRegionStrict sigmaPM
      (sigmaPM.cells.get (sigmaCell (σ i))).1
      (sigmaPM.cells.get (sigmaCell (σ i))).2 (fun _ => y i)) :
    ¬ ∀ i, MaskRegion sigmaPM
      (sigmaPM.cells.get (sigmaCell (τ i))).1
      (sigmaPM.cells.get (sigmaCell (τ i))).2 (fun _ => y i) := fun hw =>
  sign_exclusion hστ ((signMemStrict_iff_lowering y σ).mpr hs)
    ((signMem_iff_lowering y τ).mpr hw)

/-- **A3 consumer form (TS)**: under the flavored exclusion, a point
strictly inside product cell κ forces any weakly-containing cell — in
particular the expansion's one-hot cell — to be κ. This is the
dischargeable premise HCellInterior wants: strict membership determines
the box's output. -/
theorem _root_.PPLC.CellSchemaTS.interior_determines {T : CellSchemaTS}
    (hd : T.CellIntDisjoint) {κ ν : T.CellIdx} {x : Fin T.D → ℚ}
    (hs : T.MemStrict κ x) (hw : T.Mem ν x) : ν = κ := by
  by_contra hne
  exact hd κ ν (fun h => hne h.symm) x hs hw

/-- **A3 consumer form (SA)**: a value vector strictly inside sign cell
σ forces any weakly-containing sign cell to be σ — no disjointness
hypothesis at all: `sign_exclusion` is free. -/
theorem sign_interior_determines {k : ℕ} {y : Fin k → ℚ}
    {σ τ : Fin k → Bool} (hs : SignMemStrict y σ) (hw : SignMem y τ) :
    τ = σ := by
  by_contra hne
  exact sign_exclusion (fun h => hne h.symm) hs hw

/-! ## The canonical instance: the planar quadrant fan, expanded

One hypernet, both flavors. The TS reading: `quadrantsTS` (D = 2 flat
dimensions, identity partition into two singleton clusters, `sigmaPM`
per cluster). The SA reading: `quadrantsSA` (k = 2 coordinate-projection
presenters over the `[2]`-Q host wire). Their expansions coincide
because a singleton-cluster projection and a coordinate presenter are
the same const+contract front end (F5), and the per-box/per-product
stages are identical; `sigmaCell` mediates the output indexings. -/

/-- The "ij,j→i" matrix-vector contraction pattern: index i (extent 1)
on the matrix's first axis and the output, index j (extent 2) shared by
the matrix's second axis and the vector. -/
def projPat : ContractPattern [2, 1] 1 where
  nIndices := 2
  indexExtent := fun i => match i with
    | ⟨0, _⟩ => 1
    | ⟨1, _⟩ => 2
  inputBinding := fun i => match i with
    | ⟨0, _⟩ => fun a => a
    | ⟨1, _⟩ => fun _ => ⟨1, by decide⟩
  outputBinding := fun _ => ⟨0, by decide⟩

/-- The first-coordinate selection matrix `(1 0)`, as a `[1,2]` tensor
constant (F5: coordinate projection = 0/1 `const` + one `contract` row;
no gather primitive). -/
def Pmat0 : TensorValue ⟨[1, 2], Dtype.Q⟩ := ⟨[qelem 1, qelem 0], rfl⟩

/-- The second-coordinate selection matrix `(0 1)`. -/
def Pmat1 : TensorValue ⟨[1, 2], Dtype.Q⟩ := ⟨[qelem 0, qelem 1], rfl⟩

/-- Wire table shared by the coordinate presenters: 0 the `[2]`-Q input,
1 the selection matrix, 2 the `[1]`-Q output — rank-1, per the ratified
`codOk` convention, feeding a `sigmaPM` box directly. -/
def projTy : Wire → Option TensorType := fun w =>
  if w = 0 then some ⟨[2], Dtype.Q⟩
  else if w = 1 then some ⟨[1, 2], Dtype.Q⟩
  else if w = 2 then some ⟨[1], Dtype.Q⟩
  else none

/-- The first-coordinate presenter: `f₀(x) = x₀`. -/
def projNet0 : Hypernet where
  wireType := projTy
  applications := [.const ⟨[1, 2], Dtype.Q⟩ Pmat0 1,
                   .contract Dtype.Q .exact [1, 0] 2 [2, 1] 1 projPat]
  linearity := by decide
  acyclic := by decide
  typeConsistent := by decide +kernel

/-- The second-coordinate presenter: `f₁(x) = x₁`. -/
def projNet1 : Hypernet where
  wireType := projTy
  applications := [.const ⟨[1, 2], Dtype.Q⟩ Pmat1 1,
                   .contract Dtype.Q .exact [1, 0] 2 [2, 1] 1 projPat]
  linearity := by decide
  acyclic := by decide
  typeConsistent := by decide +kernel

/-- The planar quadrant fan as a full-semialgebraic schema: two
coordinate-projection presenters over the `[2]`-Q host wire; the four
sign cells are the four (closed) quadrants, walls shared weakly —
the same cells as `quadrantsTS`. -/
def quadrantsSA : CellSchemaSA where
  hostShape := [2]
  k := 2
  funs := fun c => match c with
    | ⟨0, _⟩ => projNet0
    | ⟨1, _⟩ => projNet1
  inWire := fun _ => 0
  outWire := fun _ => 2
  domOk := fun c => match c with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  codOk := fun c => match c with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  cellFree := fun c => match c with
    | ⟨0, _⟩ => by
        intro app happ
        simp only [projNet0, List.mem_cons, List.not_mem_nil, or_false] at happ
        rcases happ with rfl | rfl <;> rfl
    | ⟨1, _⟩ => by
        intro app happ
        simp only [projNet1, List.mem_cons, List.not_mem_nil, or_false] at happ
        rcases happ with rfl | rfl <;> rfl

/-- The `quadrantsSA` exclusion, free — A2's side condition for the SA
reading, discharged with zero certificate bytes. -/
theorem quadrantsSA_exclusion {y : Fin quadrantsSA.k → ℚ}
    {σ τ : Fin quadrantsSA.k → Bool} (hστ : σ ≠ τ)
    (hs : quadrantsSA.MemViaStrict y σ) : ¬ quadrantsSA.MemVia y τ :=
  quadrantsSA.sign_exclusion hστ hs

/-- Wire table of the shared expansion. 0: input; 1–2: input copies;
3–4: selection matrices; 5–6: projected coordinates (rank-1, feeding the
boxes directly); 7–10: box outputs (scalar B, the core convention);
11–14: their Q casts; 15–22: product fan-out copies; 23–26: one-hot
products; 27–30: the Boolean outputs, flat index `2·κ₀ + κ₁` = the
binary sign index. -/
def quadTy : Wire → Option TensorType := fun w =>
  if w ≤ 2 then some ⟨[2], Dtype.Q⟩
  else if w ≤ 4 then some ⟨[1, 2], Dtype.Q⟩
  else if w ≤ 6 then some ⟨[1], Dtype.Q⟩
  else if w ≤ 10 then some ⟨[], Dtype.B⟩
  else if w ≤ 26 then some ⟨[], Dtype.Q⟩
  else if w ≤ 30 then some ⟨[], Dtype.B⟩
  else none

/-- **The shared expansion of the quadrant fan** — `quadrantsTS`'s
tensor-simplicial lowering and `quadrantsSA`'s full-semialgebraic
lowering, which coincide at this instance. All within the ten boxes.
The product-row wiring (rows 23–26: which copy of which indicator
feeds which output) is the M2 mutant locus. -/
def quadExpH : Hypernet where
  wireType := quadTy
  applications :=
    [.copy 2 0 [1, 2],
     .const ⟨[1, 2], Dtype.Q⟩ Pmat0 3,
     .const ⟨[1, 2], Dtype.Q⟩ Pmat1 4,
     .contract Dtype.Q .exact [3, 1] 5 [2, 1] 1 projPat,
     .contract Dtype.Q .exact [4, 2] 6 [2, 1] 1 projPat,
     .cell sigmaPM 5 [7, 8],
     .cell sigmaPM 6 [9, 10],
     .cast Dtype.B Dtype.Q .exact [] 7 11,
     .cast Dtype.B Dtype.Q .exact [] 8 12,
     .cast Dtype.B Dtype.Q .exact [] 9 13,
     .cast Dtype.B Dtype.Q .exact [] 10 14,
     .copy 2 11 [15, 16],
     .copy 2 12 [17, 18],
     .copy 2 13 [19, 20],
     .copy 2 14 [21, 22],
     .contract Dtype.Q .exact [15, 19] 23 [0, 0] 0 pat0,
     .contract Dtype.Q .exact [16, 21] 24 [0, 0] 0 pat0,
     .contract Dtype.Q .exact [17, 20] 25 [0, 0] 0 pat0,
     .contract Dtype.Q .exact [18, 22] 26 [0, 0] 0 pat0,
     .cast Dtype.Q Dtype.B .exact [] 23 27,
     .cast Dtype.Q Dtype.B .exact [] 24 28,
     .cast Dtype.Q Dtype.B .exact [] 25 29,
     .cast Dtype.Q Dtype.B .exact [] 26 30]
  linearity := by decide
  acyclic := by decide +kernel
  typeConsistent := by decide +kernel

/-- **A2 at the instance**: the expansion presents the flavored
interface — input wire of the host type `⟨[2], Q⟩`, four scalar-Boolean
outputs (the core box's output convention), and each presenter's output
rank-1 Q (the ratified `codOk`), so the presenters feed their boxes
directly. The typing side conditions of the internal boxes discharge by
`sigmaPM_disjoint` (a species citation), and the flavored side
conditions lift by L1's `CellSchemaTS.product_exclusion` /
`sign_exclusion` — A2's derivability, with the well-formedness fields of
`quadExpH` itself (`by decide`) as the component typing rules. -/
theorem quadExp_typing :
    quadExpH.wireType 0 = some ⟨[2], Dtype.Q⟩ ∧
    (∀ w ∈ [27, 28, 29, 30], quadExpH.wireType w = some ⟨[], Dtype.B⟩) ∧
    (∀ i, (quadrantsSA.funs i).wireType (quadrantsSA.outWire i)
      = some ⟨[1], Dtype.Q⟩) :=
  ⟨rfl, by decide, quadrantsSA.codOk⟩

/-! ## The completeness valuation -/

/-- The cluster-0 projection of the quadrant fan is the first
coordinate. -/
theorem quadrants_proj_zero (x : Fin 2 → ℚ) :
    quadrantsTS.proj (0 : Fin 2) x = fun _ => x 0 := by
  funext j
  match j with
  | ⟨0, _⟩ => rfl

/-- The cluster-1 projection of the quadrant fan is the second
coordinate. -/
theorem quadrants_proj_one (x : Fin 2 → ℚ) :
    quadrantsTS.proj (1 : Fin 2) x = fun _ => x 1 := by
  funext j
  match j with
  | ⟨0, _⟩ => rfl

/-- A `[2]`-vector tensor value. -/
def qv2 (a b : ℚ) : TensorValue ⟨[2], Dtype.Q⟩ := ⟨[qelem a, qelem b], rfl⟩

/-- A Boolean carrier element from a rational known to be 0 or 1. -/
def belemI (q : ℚ) (h : q = 0 ∨ q = 1) : Dtype.B.carrier :=
  ⟨.fin q, h, fun _ => by rcases h with rfl | rfl <;> norm_num⟩

/-- A scalar-Boolean tensor value from a rational known to be 0 or 1. -/
def bvI (q : ℚ) (h : q = 0 ∨ q = 1) : TensorValue ⟨[], Dtype.B⟩ :=
  ⟨[belemI q h], rfl⟩

/-- The one-hot indicator: `1` exactly at the hot index. THE
COMPLETENESS ONE-HOT LOCUS (mutant M3). -/
def indQ (j : ℕ) (k : Fin 2) : ℚ := if j = k.val then 1 else 0

theorem indQ_mem (j : ℕ) (k : Fin 2) : indQ j k = 0 ∨ indQ j k = 1 := by
  unfold indQ
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem indQ_mul_mem (a b : ℕ) (k k' : Fin 2) :
    indQ a k * indQ b k' = 0 ∨ indQ a k * indQ b k' = 1 := by
  rcases indQ_mem a k with h | h <;> rcases indQ_mem b k' with h' | h' <;>
    rw [h, h'] <;> norm_num

/-- The completeness valuation: input `x` on wires 0–2, the selection
matrices, the projected coordinates, one-hot indicators at the chosen
per-cluster cells `k0, k1`, and their products downstream. -/
def quadVal (x : Fin 2 → ℚ) (k0 k1 : Fin 2) : quadExpH.Valuation := fun w _ h =>
  match w, h with
  | 0, h => (Option.some.inj h) ▸ qv2 (x 0) (x 1)
  | 1, h => (Option.some.inj h) ▸ qv2 (x 0) (x 1)
  | 2, h => (Option.some.inj h) ▸ qv2 (x 0) (x 1)
  | 3, h => (Option.some.inj h) ▸ Pmat0
  | 4, h => (Option.some.inj h) ▸ Pmat1
  | 5, h => (Option.some.inj h) ▸ qv1 (x 0)
  | 6, h => (Option.some.inj h) ▸ qv1 (x 1)
  | 7, h => (Option.some.inj h) ▸ bvI (indQ 0 k0) (indQ_mem 0 k0)
  | 8, h => (Option.some.inj h) ▸ bvI (indQ 1 k0) (indQ_mem 1 k0)
  | 9, h => (Option.some.inj h) ▸ bvI (indQ 0 k1) (indQ_mem 0 k1)
  | 10, h => (Option.some.inj h) ▸ bvI (indQ 1 k1) (indQ_mem 1 k1)
  | 11, h => (Option.some.inj h) ▸ qv0 (indQ 0 k0)
  | 12, h => (Option.some.inj h) ▸ qv0 (indQ 1 k0)
  | 13, h => (Option.some.inj h) ▸ qv0 (indQ 0 k1)
  | 14, h => (Option.some.inj h) ▸ qv0 (indQ 1 k1)
  | 15, h => (Option.some.inj h) ▸ qv0 (indQ 0 k0)
  | 16, h => (Option.some.inj h) ▸ qv0 (indQ 0 k0)
  | 17, h => (Option.some.inj h) ▸ qv0 (indQ 1 k0)
  | 18, h => (Option.some.inj h) ▸ qv0 (indQ 1 k0)
  | 19, h => (Option.some.inj h) ▸ qv0 (indQ 0 k1)
  | 20, h => (Option.some.inj h) ▸ qv0 (indQ 0 k1)
  | 21, h => (Option.some.inj h) ▸ qv0 (indQ 1 k1)
  | 22, h => (Option.some.inj h) ▸ qv0 (indQ 1 k1)
  | 23, h => (Option.some.inj h) ▸ qv0 (indQ 0 k0 * indQ 0 k1)
  | 24, h => (Option.some.inj h) ▸ qv0 (indQ 0 k0 * indQ 1 k1)
  | 25, h => (Option.some.inj h) ▸ qv0 (indQ 1 k0 * indQ 0 k1)
  | 26, h => (Option.some.inj h) ▸ qv0 (indQ 1 k0 * indQ 1 k1)
  | 27, h => (Option.some.inj h) ▸ bvI (indQ 0 k0 * indQ 0 k1) (indQ_mul_mem 0 0 k0 k1)
  | 28, h => (Option.some.inj h) ▸ bvI (indQ 0 k0 * indQ 1 k1) (indQ_mul_mem 0 1 k0 k1)
  | 29, h => (Option.some.inj h) ▸ bvI (indQ 1 k0 * indQ 0 k1) (indQ_mul_mem 1 0 k0 k1)
  | 30, h => (Option.some.inj h) ▸ bvI (indQ 1 k0 * indQ 1 k1) (indQ_mul_mem 1 1 k0 k1)
  | (_ + 31), h => nomatch h

theorem quadVal_admissible {x : Fin 2 → ℚ} {k0 k1 : Fin 2}
    (h0 : MaskRegion sigmaPM
      (sigmaPM.cells.get k0).1 (sigmaPM.cells.get k0).2 (fun _ => x 0))
    (h1 : MaskRegion sigmaPM
      (sigmaPM.cells.get k1).1 (sigmaPM.cells.get k1).2 (fun _ => x 1)) :
    (quadVal x k0 k1).Admissible := by
  intro app happ
  simp only [quadExpH, List.mem_cons, List.not_mem_nil, or_false] at happ
  rcases happ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- copy 2 0 [1, 2]
    intro o ho i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> rfl
  · -- const Pmat0 3
    intro i
    rfl
  · -- const Pmat1 4
    intro i
    rfl
  · -- contract [3, 1] → 5 (projection 0)
    intro ν₀ hν₀
    rw [show Shape.positions projPat.idxShape = [[0, 0], [0, 1]] from rfl] at hν₀
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hν₀
    rcases hν₀ with rfl | rfl
    · refine ⟨.fin (x 0), .fin ((0 + (1 * 1) * (x 0)) + (1 * 0) * (x 1)), rfl, rfl, ?_⟩
      rw [show ((0 : ℚ) + (1 * 1) * (x 0)) + (1 * 0) * (x 1) = x 0 from by ring]
      exact roundOk_finQ (x 0)
    · refine ⟨.fin (x 0), .fin ((0 + (1 * 1) * (x 0)) + (1 * 0) * (x 1)), rfl, rfl, ?_⟩
      rw [show ((0 : ℚ) + (1 * 1) * (x 0)) + (1 * 0) * (x 1) = x 0 from by ring]
      exact roundOk_finQ (x 0)
  · -- contract [4, 2] → 6 (projection 1)
    intro ν₀ hν₀
    rw [show Shape.positions projPat.idxShape = [[0, 0], [0, 1]] from rfl] at hν₀
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hν₀
    rcases hν₀ with rfl | rfl
    · refine ⟨.fin (x 1), .fin ((0 + (1 * 0) * (x 0)) + (1 * 1) * (x 1)), rfl, rfl, ?_⟩
      rw [show ((0 : ℚ) + (1 * 0) * (x 0)) + (1 * 1) * (x 1) = x 1 from by ring]
      exact roundOk_finQ (x 1)
    · refine ⟨.fin (x 1), .fin ((0 + (1 * 0) * (x 0)) + (1 * 1) * (x 1)), rfl, rfl, ?_⟩
      rw [show ((0 : ℚ) + (1 * 0) * (x 0)) + (1 * 1) * (x 1) = x 1 from by ring]
      exact roundOk_finQ (x 1)
  · -- cell sigmaPM 5 [7, 8]
    refine ⟨sigmaPM_disjoint, fun _ => x 0, ?_, k0, h0, ?_⟩
    · intro j
      rw [fin1_eq j]
      rfl
    · intro j
      match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
  · -- cell sigmaPM 6 [9, 10]
    refine ⟨sigmaPM_disjoint, fun _ => x 1, ?_, k1, h1, ?_⟩
    · intro j
      rw [fin1_eq j]
      rfl
    · intro j
      match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
  · -- cast B→Q 7 → 11
    intro i
    have h1' : i.val < 1 := i.isLt
    have hi0 : i.val = 0 := by omega
    rw [hi0]
    exact ⟨.fin (indQ 0 k0), .fin (indQ 0 k0), rfl, rfl, roundOk_finQ _⟩
  · -- cast B→Q 8 → 12
    intro i
    have h1' : i.val < 1 := i.isLt
    have hi0 : i.val = 0 := by omega
    rw [hi0]
    exact ⟨.fin (indQ 1 k0), .fin (indQ 1 k0), rfl, rfl, roundOk_finQ _⟩
  · -- cast B→Q 9 → 13
    intro i
    have h1' : i.val < 1 := i.isLt
    have hi0 : i.val = 0 := by omega
    rw [hi0]
    exact ⟨.fin (indQ 0 k1), .fin (indQ 0 k1), rfl, rfl, roundOk_finQ _⟩
  · -- cast B→Q 10 → 14
    intro i
    have h1' : i.val < 1 := i.isLt
    have hi0 : i.val = 0 := by omega
    rw [hi0]
    exact ⟨.fin (indQ 1 k1), .fin (indQ 1 k1), rfl, rfl, roundOk_finQ _⟩
  · -- copy 11 [15, 16]
    intro o ho i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> rfl
  · -- copy 12 [17, 18]
    intro o ho i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> rfl
  · -- copy 13 [19, 20]
    intro o ho i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> rfl
  · -- copy 14 [21, 22]
    intro o ho i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> rfl
  · -- contract [15, 19] → 23
    intro ν₀ hν₀
    have hν : ν₀ = [] := List.mem_singleton.mp hν₀
    subst hν
    refine ⟨.fin (indQ 0 k0 * indQ 0 k1), .fin (0 + (1 * indQ 0 k0) * indQ 0 k1),
      rfl, rfl, ?_⟩
    rw [show (0 : ℚ) + (1 * indQ 0 k0) * indQ 0 k1 = indQ 0 k0 * indQ 0 k1 from by ring]
    exact roundOk_finQ _
  · -- contract [16, 21] → 24
    intro ν₀ hν₀
    have hν : ν₀ = [] := List.mem_singleton.mp hν₀
    subst hν
    refine ⟨.fin (indQ 0 k0 * indQ 1 k1), .fin (0 + (1 * indQ 0 k0) * indQ 1 k1),
      rfl, rfl, ?_⟩
    rw [show (0 : ℚ) + (1 * indQ 0 k0) * indQ 1 k1 = indQ 0 k0 * indQ 1 k1 from by ring]
    exact roundOk_finQ _
  · -- contract [17, 20] → 25
    intro ν₀ hν₀
    have hν : ν₀ = [] := List.mem_singleton.mp hν₀
    subst hν
    refine ⟨.fin (indQ 1 k0 * indQ 0 k1), .fin (0 + (1 * indQ 1 k0) * indQ 0 k1),
      rfl, rfl, ?_⟩
    rw [show (0 : ℚ) + (1 * indQ 1 k0) * indQ 0 k1 = indQ 1 k0 * indQ 0 k1 from by ring]
    exact roundOk_finQ _
  · -- contract [18, 22] → 26
    intro ν₀ hν₀
    have hν : ν₀ = [] := List.mem_singleton.mp hν₀
    subst hν
    refine ⟨.fin (indQ 1 k0 * indQ 1 k1), .fin (0 + (1 * indQ 1 k0) * indQ 1 k1),
      rfl, rfl, ?_⟩
    rw [show (0 : ℚ) + (1 * indQ 1 k0) * indQ 1 k1 = indQ 1 k0 * indQ 1 k1 from by ring]
    exact roundOk_finQ _
  · -- cast Q→B 23 → 27
    intro i
    have h1' : i.val < 1 := i.isLt
    have hi0 : i.val = 0 := by omega
    rw [hi0]
    exact ⟨.fin (indQ 0 k0 * indQ 0 k1), .fin (indQ 0 k0 * indQ 0 k1), rfl, rfl,
      roundOk_finB (indQ_mul_mem 0 0 k0 k1)⟩
  · -- cast Q→B 24 → 28
    intro i
    have h1' : i.val < 1 := i.isLt
    have hi0 : i.val = 0 := by omega
    rw [hi0]
    exact ⟨.fin (indQ 0 k0 * indQ 1 k1), .fin (indQ 0 k0 * indQ 1 k1), rfl, rfl,
      roundOk_finB (indQ_mul_mem 0 1 k0 k1)⟩
  · -- cast Q→B 25 → 29
    intro i
    have h1' : i.val < 1 := i.isLt
    have hi0 : i.val = 0 := by omega
    rw [hi0]
    exact ⟨.fin (indQ 1 k0 * indQ 0 k1), .fin (indQ 1 k0 * indQ 0 k1), rfl, rfl,
      roundOk_finB (indQ_mul_mem 1 0 k0 k1)⟩
  · -- cast Q→B 26 → 30
    intro i
    have h1' : i.val < 1 := i.isLt
    have hi0 : i.val = 0 := by omega
    rw [hi0]
    exact ⟨.fin (indQ 1 k0 * indQ 1 k1), .fin (indQ 1 k0 * indQ 1 k1), rfl, rfl,
      roundOk_finB (indQ_mul_mem 1 1 k0 k1)⟩

/-! ## A1 at the instance -/

/-- Completeness: weak membership in the product cell yields an
admissible valuation of the expansion, input `x`, outputs one-hot at
the mixed-radix index of κ. -/
theorem quadExp_complete {x : Fin 2 → ℚ} {κ : quadrantsTS.CellIdx}
    (hmem : quadrantsTS.Mem κ x) :
    ∃ σ : quadExpH.Valuation, σ.Admissible ∧
      (∀ j : Fin 2, σ.entryFlat 0 j.val = some (.fin (x j))) ∧
      (∀ j : Fin 4, σ.entryFlat (27 + j.val) 0
        = some (.fin (if j.val = 2 * (κ (0 : Fin 2)).val + (κ (1 : Fin 2)).val then 1 else 0))) := by
  have h0 := hmem (0 : Fin 2)
  have h1 := hmem (1 : Fin 2)
  rw [quadrants_proj_zero] at h0
  rw [quadrants_proj_one] at h1
  refine ⟨quadVal x (κ (0 : Fin 2)) (κ (1 : Fin 2)), quadVal_admissible h0 h1, ?_, ?_⟩
  · intro j
    match j with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  · intro j
    have hlt0 : (κ (0 : Fin 2)).val < 2 := (κ (0 : Fin 2)).isLt
    have hlt1 : (κ (1 : Fin 2)).val < 2 := (κ (1 : Fin 2)).isLt
    have e0 : (κ (0 : Fin 2)).val = 0 ∨ (κ (0 : Fin 2)).val = 1 := by omega
    have e1 : (κ (1 : Fin 2)).val = 0 ∨ (κ (1 : Fin 2)).val = 1 := by omega
    match j with
    | ⟨0, _⟩ =>
      show some (ERat.fin (indQ 0 (κ (0 : Fin 2)) * indQ 0 (κ (1 : Fin 2))))
          = some (ERat.fin (if (0 : ℕ) = 2 * (κ (0 : Fin 2)).val + (κ (1 : Fin 2)).val then 1 else 0))
      rcases e0 with h | h <;> rcases e1 with h' | h' <;> simp [indQ, h, h']
    | ⟨1, _⟩ =>
      show some (ERat.fin (indQ 0 (κ (0 : Fin 2)) * indQ 1 (κ (1 : Fin 2))))
          = some (ERat.fin (if (1 : ℕ) = 2 * (κ (0 : Fin 2)).val + (κ (1 : Fin 2)).val then 1 else 0))
      rcases e0 with h | h <;> rcases e1 with h' | h' <;> simp [indQ, h, h']
    | ⟨2, _⟩ =>
      show some (ERat.fin (indQ 1 (κ (0 : Fin 2)) * indQ 0 (κ (1 : Fin 2))))
          = some (ERat.fin (if (2 : ℕ) = 2 * (κ (0 : Fin 2)).val + (κ (1 : Fin 2)).val then 1 else 0))
      rcases e0 with h | h <;> rcases e1 with h' | h' <;> simp [indQ, h, h']
    | ⟨3, _⟩ =>
      show some (ERat.fin (indQ 1 (κ (0 : Fin 2)) * indQ 1 (κ (1 : Fin 2))))
          = some (ERat.fin (if (3 : ℕ) = 2 * (κ (0 : Fin 2)).val + (κ (1 : Fin 2)).val then 1 else 0))
      rcases e0 with h | h <;> rcases e1 with h' | h' <;> simp [indQ, h, h']

/-- Soundness: an admissible valuation of the expansion with input `x`
and outputs one-hot at the mixed-radix index of κ certifies weak
membership in the product cell κ. The ReluExpansion chase, at scale:
decompose admissibility, compute the contract rows, consume the cell
arms' hot indices, and let the one-hot equations at the four outputs
force the hot tuple to be κ. -/
theorem quadExp_sound {x : Fin 2 → ℚ} {κ : quadrantsTS.CellIdx}
    (σ : quadExpH.Valuation) (hadm : σ.Admissible)
    (hin : ∀ j : Fin 2, σ.entryFlat 0 j.val = some (.fin (x j)))
    (hout : ∀ j : Fin 4, σ.entryFlat (27 + j.val) 0
      = some (.fin (if j.val = 2 * (κ (0 : Fin 2)).val + (κ (1 : Fin 2)).val then 1 else 0))) :
    quadrantsTS.Mem κ x := by
  simp only [Hypernet.Valuation.Admissible, quadExpH, List.forall_mem_cons] at hadm
  obtain ⟨hc0, hP0, hP1, hpj0, hpj1, hcl0, hcl1, hb0, hb1, hb2, hb3,
    hcp0, hcp1, hcp2, hcp3, hpr0, hpr1, hpr2, hpr3, hq0, hq1, hq2, hq3, -⟩ := hadm
  -- input copies
  have h1r : ∀ i : ℕ, σ.entryFlat 1 i = σ.entryFlat 0 i := hc0 1 (by decide)
  have h2r : ∀ i : ℕ, σ.entryFlat 2 i = σ.entryFlat 0 i := hc0 2 (by decide)
  -- projection 0: wire 5 carries x 0
  have ha3_00 : σ.entryAt (([3, 1] : List Wire).getD
      ((⟨0, by decide⟩ : Fin ([2, 1] : List ℕ).length)).val 0)
      (projPat.inCoords [0, 0] ⟨0, by decide⟩) = some (.fin 1) := by
    rw [show (([3, 1] : List Wire).getD
      ((⟨0, by decide⟩ : Fin ([2, 1] : List ℕ).length)).val 0) = 3 from rfl]
    rw [entryAt_eq_entryFlat σ (show quadExpH.wireType 3 = some ⟨[1, 2], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([1, 2] : Shape) (projPat.inCoords [0, 0] ⟨0, by decide⟩)
        = some 0 from rfl)]
    exact hP0 0
  have ha1_00 : σ.entryAt (([3, 1] : List Wire).getD
      ((⟨1, by decide⟩ : Fin ([2, 1] : List ℕ).length)).val 0)
      (projPat.inCoords [0, 0] ⟨1, by decide⟩) = some (.fin (x 0)) := by
    rw [show (([3, 1] : List Wire).getD
      ((⟨1, by decide⟩ : Fin ([2, 1] : List ℕ).length)).val 0) = 1 from rfl]
    rw [entryAt_eq_entryFlat σ (show quadExpH.wireType 1 = some ⟨[2], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([2] : Shape) (projPat.inCoords [0, 0] ⟨1, by decide⟩)
        = some 0 from rfl)]
    exact (h1r 0).trans (hin 0)
  have ha3_01 : σ.entryAt (([3, 1] : List Wire).getD
      ((⟨0, by decide⟩ : Fin ([2, 1] : List ℕ).length)).val 0)
      (projPat.inCoords [0, 1] ⟨0, by decide⟩) = some (.fin 0) := by
    rw [show (([3, 1] : List Wire).getD
      ((⟨0, by decide⟩ : Fin ([2, 1] : List ℕ).length)).val 0) = 3 from rfl]
    rw [entryAt_eq_entryFlat σ (show quadExpH.wireType 3 = some ⟨[1, 2], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([1, 2] : Shape) (projPat.inCoords [0, 1] ⟨0, by decide⟩)
        = some 1 from rfl)]
    exact hP0 1
  have ha1_01 : σ.entryAt (([3, 1] : List Wire).getD
      ((⟨1, by decide⟩ : Fin ([2, 1] : List ℕ).length)).val 0)
      (projPat.inCoords [0, 1] ⟨1, by decide⟩) = some (.fin (x 1)) := by
    rw [show (([3, 1] : List Wire).getD
      ((⟨1, by decide⟩ : Fin ([2, 1] : List ℕ).length)).val 0) = 1 from rfl]
    rw [entryAt_eq_entryFlat σ (show quadExpH.wireType 1 = some ⟨[2], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([2] : Shape) (projPat.inCoords [0, 1] ⟨1, by decide⟩)
        = some 1 from rfl)]
    exact (h1r 1).trans (hin 1)
  have hex5 : contractExact σ [3, 1] projPat (projPat.outCoords [0, 0])
      = some (.fin ((0 + (1 * 1) * (x 0)) + (1 * 0) * (x 1))) := by
    unfold contractExact
    rw [show ((Shape.positions projPat.idxShape).filter
      (fun ν => decide (projPat.outCoords ν = projPat.outCoords [0, 0])))
      = [[0, 0], [0, 1]] from rfl]
    rw [show (List.finRange ([2, 1] : List ℕ).length)
      = [⟨0, by decide⟩, ⟨1, by decide⟩] from rfl]
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.pure_def]
    rw [ha3_00, ha1_00, ha3_01, ha1_01]
    rfl
  obtain ⟨eO5, eE5, h5out, h5ex, h5ro⟩ := hpj0 [0, 0] (by decide)
  have heE5 : eE5 = .fin ((0 + (1 * 1) * (x 0)) + (1 * 0) * (x 1)) :=
    Option.some.inj (h5ex.symm.trans hex5)
  subst heE5
  obtain ⟨heO5, -⟩ := h5ro
  subst heO5
  rw [show ((0 : ℚ) + (1 * 1) * (x 0)) + (1 * 0) * (x 1) = x 0 from by ring] at h5out
  -- projection 1: wire 6 carries x 1
  have ha4_00 : σ.entryAt (([4, 2] : List Wire).getD
      ((⟨0, by decide⟩ : Fin ([2, 1] : List ℕ).length)).val 0)
      (projPat.inCoords [0, 0] ⟨0, by decide⟩) = some (.fin 0) := by
    rw [show (([4, 2] : List Wire).getD
      ((⟨0, by decide⟩ : Fin ([2, 1] : List ℕ).length)).val 0) = 4 from rfl]
    rw [entryAt_eq_entryFlat σ (show quadExpH.wireType 4 = some ⟨[1, 2], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([1, 2] : Shape) (projPat.inCoords [0, 0] ⟨0, by decide⟩)
        = some 0 from rfl)]
    exact hP1 0
  have ha2_00 : σ.entryAt (([4, 2] : List Wire).getD
      ((⟨1, by decide⟩ : Fin ([2, 1] : List ℕ).length)).val 0)
      (projPat.inCoords [0, 0] ⟨1, by decide⟩) = some (.fin (x 0)) := by
    rw [show (([4, 2] : List Wire).getD
      ((⟨1, by decide⟩ : Fin ([2, 1] : List ℕ).length)).val 0) = 2 from rfl]
    rw [entryAt_eq_entryFlat σ (show quadExpH.wireType 2 = some ⟨[2], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([2] : Shape) (projPat.inCoords [0, 0] ⟨1, by decide⟩)
        = some 0 from rfl)]
    exact (h2r 0).trans (hin 0)
  have ha4_01 : σ.entryAt (([4, 2] : List Wire).getD
      ((⟨0, by decide⟩ : Fin ([2, 1] : List ℕ).length)).val 0)
      (projPat.inCoords [0, 1] ⟨0, by decide⟩) = some (.fin 1) := by
    rw [show (([4, 2] : List Wire).getD
      ((⟨0, by decide⟩ : Fin ([2, 1] : List ℕ).length)).val 0) = 4 from rfl]
    rw [entryAt_eq_entryFlat σ (show quadExpH.wireType 4 = some ⟨[1, 2], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([1, 2] : Shape) (projPat.inCoords [0, 1] ⟨0, by decide⟩)
        = some 1 from rfl)]
    exact hP1 1
  have ha2_01 : σ.entryAt (([4, 2] : List Wire).getD
      ((⟨1, by decide⟩ : Fin ([2, 1] : List ℕ).length)).val 0)
      (projPat.inCoords [0, 1] ⟨1, by decide⟩) = some (.fin (x 1)) := by
    rw [show (([4, 2] : List Wire).getD
      ((⟨1, by decide⟩ : Fin ([2, 1] : List ℕ).length)).val 0) = 2 from rfl]
    rw [entryAt_eq_entryFlat σ (show quadExpH.wireType 2 = some ⟨[2], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([2] : Shape) (projPat.inCoords [0, 1] ⟨1, by decide⟩)
        = some 1 from rfl)]
    exact (h2r 1).trans (hin 1)
  have hex6 : contractExact σ [4, 2] projPat (projPat.outCoords [0, 0])
      = some (.fin ((0 + (1 * 0) * (x 0)) + (1 * 1) * (x 1))) := by
    unfold contractExact
    rw [show ((Shape.positions projPat.idxShape).filter
      (fun ν => decide (projPat.outCoords ν = projPat.outCoords [0, 0])))
      = [[0, 0], [0, 1]] from rfl]
    rw [show (List.finRange ([2, 1] : List ℕ).length)
      = [⟨0, by decide⟩, ⟨1, by decide⟩] from rfl]
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.pure_def]
    rw [ha4_00, ha2_00, ha4_01, ha2_01]
    rfl
  obtain ⟨eO6, eE6, h6out, h6ex, h6ro⟩ := hpj1 [0, 0] (by decide)
  have heE6 : eE6 = .fin ((0 + (1 * 0) * (x 0)) + (1 * 1) * (x 1)) :=
    Option.some.inj (h6ex.symm.trans hex6)
  subst heE6
  obtain ⟨heO6, -⟩ := h6ro
  subst heO6
  rw [show ((0 : ℚ) + (1 * 0) * (x 0)) + (1 * 1) * (x 1) = x 1 from by ring] at h6out
  -- cell arms: hot indices with their regions
  obtain ⟨-, x5, hx5, k0, hreg0, hhot0⟩ := hcl0
  obtain ⟨-, x6, hx6, k1, hreg1, hhot1⟩ := hcl1
  have hx50 : x5 j0 = x 0 :=
    ERat.fin.inj (Option.some.inj ((hx5 j0).symm.trans h5out))
  have hx61 : x6 j0 = x 1 :=
    ERat.fin.inj (Option.some.inj ((hx6 j0).symm.trans h6out))
  have hreg0' : MaskRegion sigmaPM
      (sigmaPM.cells.get k0).1 (sigmaPM.cells.get k0).2 (fun _ => x 0) := by
    have hfx : x5 = fun _ => x 0 := funext fun j => by rw [fin1_eq j]; exact hx50
    rwa [hfx] at hreg0
  have hreg1' : MaskRegion sigmaPM
      (sigmaPM.cells.get k1).1 (sigmaPM.cells.get k1).2 (fun _ => x 1) := by
    have hfx : x6 = fun _ => x 1 := funext fun j => by rw [fin1_eq j]; exact hx61
    rwa [hfx] at hreg1
  have h7 : σ.entryFlat 7 0 = some (.fin (if (0 : ℕ) = k0.val then 1 else 0)) :=
    hhot0 ⟨0, by decide⟩
  have h8 : σ.entryFlat 8 0 = some (.fin (if (1 : ℕ) = k0.val then 1 else 0)) :=
    hhot0 ⟨1, by decide⟩
  have h9 : σ.entryFlat 9 0 = some (.fin (if (0 : ℕ) = k1.val then 1 else 0)) :=
    hhot1 ⟨0, by decide⟩
  have h10 : σ.entryFlat 10 0 = some (.fin (if (1 : ℕ) = k1.val then 1 else 0)) :=
    hhot1 ⟨1, by decide⟩
  -- casts B→Q: wires 11–14
  obtain ⟨eI11, eO11, h11in, h11out, h11ro⟩ := hb0 ⟨0, by decide⟩
  have heI11 : eI11 = .fin (if (0 : ℕ) = k0.val then 1 else 0) :=
    Option.some.inj (h11in.symm.trans h7)
  subst heI11
  obtain ⟨heO11, -⟩ := h11ro
  subst heO11
  obtain ⟨eI12, eO12, h12in, h12out, h12ro⟩ := hb1 ⟨0, by decide⟩
  have heI12 : eI12 = .fin (if (1 : ℕ) = k0.val then 1 else 0) :=
    Option.some.inj (h12in.symm.trans h8)
  subst heI12
  obtain ⟨heO12, -⟩ := h12ro
  subst heO12
  obtain ⟨eI13, eO13, h13in, h13out, h13ro⟩ := hb2 ⟨0, by decide⟩
  have heI13 : eI13 = .fin (if (0 : ℕ) = k1.val then 1 else 0) :=
    Option.some.inj (h13in.symm.trans h9)
  subst heI13
  obtain ⟨heO13, -⟩ := h13ro
  subst heO13
  obtain ⟨eI14, eO14, h14in, h14out, h14ro⟩ := hb3 ⟨0, by decide⟩
  have heI14 : eI14 = .fin (if (1 : ℕ) = k1.val then 1 else 0) :=
    Option.some.inj (h14in.symm.trans h10)
  subst heI14
  obtain ⟨heO14, -⟩ := h14ro
  subst heO14
  -- copies: wires 15–22
  have h15 : σ.entryFlat 15 0 = some (.fin (if (0 : ℕ) = k0.val then 1 else 0)) := by
    exact (hcp0 15 (by decide) 0).trans h11out
  have h16 : σ.entryFlat 16 0 = some (.fin (if (0 : ℕ) = k0.val then 1 else 0)) := by
    exact (hcp0 16 (by decide) 0).trans h11out
  have h17 : σ.entryFlat 17 0 = some (.fin (if (1 : ℕ) = k0.val then 1 else 0)) := by
    exact (hcp1 17 (by decide) 0).trans h12out
  have h18 : σ.entryFlat 18 0 = some (.fin (if (1 : ℕ) = k0.val then 1 else 0)) := by
    exact (hcp1 18 (by decide) 0).trans h12out
  have h19 : σ.entryFlat 19 0 = some (.fin (if (0 : ℕ) = k1.val then 1 else 0)) := by
    exact (hcp2 19 (by decide) 0).trans h13out
  have h20 : σ.entryFlat 20 0 = some (.fin (if (0 : ℕ) = k1.val then 1 else 0)) := by
    exact (hcp2 20 (by decide) 0).trans h13out
  have h21 : σ.entryFlat 21 0 = some (.fin (if (1 : ℕ) = k1.val then 1 else 0)) := by
    exact (hcp3 21 (by decide) 0).trans h14out
  have h22 : σ.entryFlat 22 0 = some (.fin (if (1 : ℕ) = k1.val then 1 else 0)) := by
    exact (hcp3 22 (by decide) 0).trans h14out
  -- product rows: wires 23–26 carry indicator products
  have hprod : ∀ (wa wb wo : Wire)
      (_ : PrimApp.SemOk σ (.contract Dtype.Q .exact [wa, wb] wo [0, 0] 0 pat0))
      (a b : ℚ)
      (_ : σ.entryAt (([wa, wb] : List Wire).getD
        ((⟨0, by decide⟩ : Fin ([0, 0] : List ℕ).length)).val 0)
        (pat0.inCoords [] ⟨0, by decide⟩) = some (.fin a))
      (_ : σ.entryAt (([wa, wb] : List Wire).getD
        ((⟨1, by decide⟩ : Fin ([0, 0] : List ℕ).length)).val 0)
        (pat0.inCoords [] ⟨1, by decide⟩) = some (.fin b)),
      σ.entryAt wo (pat0.outCoords []) = some (.fin (0 + (1 * a) * b)) := by
    intro wa wb wo hsem a b hA hB
    obtain ⟨eO, eE, hOut, hEx, hRo⟩ := hsem [] (List.mem_singleton.mpr rfl)
    have hexv : contractExact σ [wa, wb] pat0 (pat0.outCoords [])
        = some (.fin (0 + (1 * a) * b)) := by
      unfold contractExact
      rw [show ((Shape.positions pat0.idxShape).filter
        (fun ν => decide (pat0.outCoords ν = pat0.outCoords []))) = [[]] from rfl]
      rw [show (List.finRange ([0, 0] : List ℕ).length)
        = [⟨0, by decide⟩, ⟨1, by decide⟩] from rfl]
      simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.pure_def]
      rw [hA, hB]
      rfl
    have heE : eE = .fin (0 + (1 * a) * b) := Option.some.inj (hEx.symm.trans hexv)
    subst heE
    obtain ⟨heO, -⟩ := hRo
    subst heO
    exact hOut
  have hat : ∀ (w : Wire) (v : ℚ), σ.entryFlat w 0 = some (.fin v) →
      quadExpH.wireType w = some ⟨[], Dtype.Q⟩ →
      ∀ (c : List ℕ), Shape.flatten ([] : Shape) c = some 0 →
      σ.entryAt w c = some (.fin v) := by
    intro w v hw hty c hfl
    rw [entryAt_eq_entryFlat σ hty hfl]
    exact hw
  have h23 : σ.entryAt 23 (pat0.outCoords []) = some (.fin (0 +
      (1 * (if (0 : ℕ) = k0.val then (1:ℚ) else 0)) * (if (0 : ℕ) = k1.val then (1:ℚ) else 0))) :=
    hprod 15 19 23 hpr0 _ _
      (hat 15 _ h15 rfl _ rfl) (hat 19 _ h19 rfl _ rfl)
  have h24 : σ.entryAt 24 (pat0.outCoords []) = some (.fin (0 +
      (1 * (if (0 : ℕ) = k0.val then (1:ℚ) else 0)) * (if (1 : ℕ) = k1.val then (1:ℚ) else 0))) :=
    hprod 16 21 24 hpr1 _ _
      (hat 16 _ h16 rfl _ rfl) (hat 21 _ h21 rfl _ rfl)
  have h25 : σ.entryAt 25 (pat0.outCoords []) = some (.fin (0 +
      (1 * (if (1 : ℕ) = k0.val then (1:ℚ) else 0)) * (if (0 : ℕ) = k1.val then (1:ℚ) else 0))) :=
    hprod 17 20 25 hpr2 _ _
      (hat 17 _ h17 rfl _ rfl) (hat 20 _ h20 rfl _ rfl)
  have h26 : σ.entryAt 26 (pat0.outCoords []) = some (.fin (0 +
      (1 * (if (1 : ℕ) = k0.val then (1:ℚ) else 0)) * (if (1 : ℕ) = k1.val then (1:ℚ) else 0))) :=
    hprod 18 22 26 hpr3 _ _
      (hat 18 _ h18 rfl _ rfl) (hat 22 _ h22 rfl _ rfl)
  -- through the final casts, equate with the one-hot hypothesis
  rw [entryAt_eq_entryFlat σ (show quadExpH.wireType 23 = some ⟨[], Dtype.Q⟩ from rfl)
    (show Shape.flatten ([] : Shape) (pat0.outCoords []) = some 0 from rfl)] at h23
  rw [entryAt_eq_entryFlat σ (show quadExpH.wireType 24 = some ⟨[], Dtype.Q⟩ from rfl)
    (show Shape.flatten ([] : Shape) (pat0.outCoords []) = some 0 from rfl)] at h24
  rw [entryAt_eq_entryFlat σ (show quadExpH.wireType 25 = some ⟨[], Dtype.Q⟩ from rfl)
    (show Shape.flatten ([] : Shape) (pat0.outCoords []) = some 0 from rfl)] at h25
  rw [entryAt_eq_entryFlat σ (show quadExpH.wireType 26 = some ⟨[], Dtype.Q⟩ from rfl)
    (show Shape.flatten ([] : Shape) (pat0.outCoords []) = some 0 from rfl)] at h26
  obtain ⟨eI27, eO27, h27in, h27out, h27ro⟩ := hq0 ⟨0, by decide⟩
  have heI27 : eI27 = _ := Option.some.inj (h27in.symm.trans h23)
  subst heI27
  obtain ⟨heO27, -⟩ := h27ro
  subst heO27
  obtain ⟨eI28, eO28, h28in, h28out, h28ro⟩ := hq1 ⟨0, by decide⟩
  have heI28 : eI28 = _ := Option.some.inj (h28in.symm.trans h24)
  subst heI28
  obtain ⟨heO28, -⟩ := h28ro
  subst heO28
  obtain ⟨eI29, eO29, h29in, h29out, h29ro⟩ := hq2 ⟨0, by decide⟩
  have heI29 : eI29 = _ := Option.some.inj (h29in.symm.trans h25)
  subst heI29
  obtain ⟨heO29, -⟩ := h29ro
  subst heO29
  obtain ⟨eI30, eO30, h30in, h30out, h30ro⟩ := hq3 ⟨0, by decide⟩
  have heI30 : eI30 = _ := Option.some.inj (h30in.symm.trans h26)
  subst heI30
  obtain ⟨heO30, -⟩ := h30ro
  subst heO30
  have hval27 := ERat.fin.inj (Option.some.inj (h27out.symm.trans (hout ⟨0, by decide⟩)))
  have hval28 := ERat.fin.inj (Option.some.inj (h28out.symm.trans (hout ⟨1, by decide⟩)))
  have hval29 := ERat.fin.inj (Option.some.inj (h29out.symm.trans (hout ⟨2, by decide⟩)))
  have hval30 := ERat.fin.inj (Option.some.inj (h30out.symm.trans (hout ⟨3, by decide⟩)))
  -- the one-hot equations force the hot tuple to be κ
  have hlt0 : (κ (0 : Fin 2)).val < 2 := (κ (0 : Fin 2)).isLt
  have hlt1 : (κ (1 : Fin 2)).val < 2 := (κ (1 : Fin 2)).isLt
  have hltk0 : k0.val < 2 := k0.isLt
  have hltk1 : k1.val < 2 := k1.isLt
  have e : k0.val = (κ (0 : Fin 2)).val ∧ k1.val = (κ (1 : Fin 2)).val := by
    rcases (by omega : k0.val = 0 ∨ k0.val = 1) with h | h <;>
    rcases (by omega : k1.val = 0 ∨ k1.val = 1) with h' | h' <;>
    rcases (by omega : (κ (0 : Fin 2)).val = 0 ∨ (κ (0 : Fin 2)).val = 1) with g | g <;>
    rcases (by omega : (κ (1 : Fin 2)).val = 0 ∨ (κ (1 : Fin 2)).val = 1) with g' | g' <;>
      simp [h, h', g, g'] at hval27 hval28 hval29 hval30 ⊢
  have hk0e : k0 = κ (0 : Fin 2) := Fin.ext e.1
  have hk1e : k1 = κ (1 : Fin 2) := Fin.ext e.2
  subst hk0e
  subst hk1e
  intro c
  match c with
  | ⟨0, _⟩ =>
    show MaskRegion sigmaPM
      (sigmaPM.cells.get (κ (0 : Fin 2))).1 (sigmaPM.cells.get (κ (0 : Fin 2))).2 (quadrantsTS.proj (0 : Fin 2) x)
    rw [quadrants_proj_zero]
    exact hreg0'
  | ⟨1, _⟩ =>
    show MaskRegion sigmaPM
      (sigmaPM.cells.get (κ (1 : Fin 2))).1 (sigmaPM.cells.get (κ (1 : Fin 2))).2 (quadrantsTS.proj (1 : Fin 2) x)
    rw [quadrants_proj_one]
    exact hreg1'

/-- **A1 at the instance (TS reading)**: an admissible valuation of the
shared expansion with input `x` and outputs one-hot at κ's mixed-radix
index exists **iff** `x` is weakly in the product cell κ — the flavored
membership coincides with the semantics of the lowering. -/
theorem quadExp_projection (x : Fin 2 → ℚ) (κ : quadrantsTS.CellIdx) :
    (∃ σ : quadExpH.Valuation, σ.Admissible ∧
        (∀ j : Fin 2, σ.entryFlat 0 j.val = some (.fin (x j))) ∧
        (∀ j : Fin 4, σ.entryFlat (27 + j.val) 0
          = some (.fin (if j.val = 2 * (κ (0 : Fin 2)).val + (κ (1 : Fin 2)).val then 1 else 0))))
      ↔ quadrantsTS.Mem κ x := by
  constructor
  · rintro ⟨σ, hadm, hin, hout⟩
    exact quadExp_sound σ hadm hin hout
  · exact quadExp_complete

/-- The two flavored readings of the quadrant fan agree: product-cell
membership at the `sigmaCell` tuple is sign membership of the
coordinate vector — the value vector of `quadrantsSA`'s presenters IS
the coordinate vector. -/
theorem quadrantsTS_mem_iff_signMem (x : Fin 2 → ℚ) (s : Fin 2 → Bool) :
    quadrantsTS.Mem (fun c => sigmaCell (s c)) x ↔ SignMem x s := by
  constructor
  · intro h i
    match i with
    | ⟨0, _⟩ =>
      have h0 := h (0 : Fin 2)
      rw [quadrants_proj_zero] at h0
      exact (maskRegion_sigmaCell_iff (s 0) (fun _ => x 0)).mp h0
    | ⟨1, _⟩ =>
      have h1 := h (1 : Fin 2)
      rw [quadrants_proj_one] at h1
      exact (maskRegion_sigmaCell_iff (s 1) (fun _ => x 1)).mp h1
  · intro h c
    match c with
    | ⟨0, _⟩ =>
      show MaskRegion sigmaPM
        (sigmaPM.cells.get (sigmaCell (s 0))).1
        (sigmaPM.cells.get (sigmaCell (s 0))).2 (quadrantsTS.proj (0 : Fin 2) x)
      rw [quadrants_proj_zero]
      exact (maskRegion_sigmaCell_iff (s 0) (fun _ => x 0)).mpr (h 0)
    | ⟨1, _⟩ =>
      show MaskRegion sigmaPM
        (sigmaPM.cells.get (sigmaCell (s 1))).1
        (sigmaPM.cells.get (sigmaCell (s 1))).2 (quadrantsTS.proj (1 : Fin 2) x)
      rw [quadrants_proj_one]
      exact (maskRegion_sigmaCell_iff (s 1) (fun _ => x 1)).mpr (h 1)

/-- **A1 at the instance (SA reading)**: the same hypernet, the same
iff, read through the sign dictionary — an admissible valuation with
outputs one-hot at the binary sign index exists iff the coordinate
vector is weakly in the sign cell. One expansion, two flavors. -/
theorem quadExp_projection_sa (x : Fin 2 → ℚ) (s : Fin 2 → Bool) :
    (∃ σ : quadExpH.Valuation, σ.Admissible ∧
        (∀ j : Fin 2, σ.entryFlat 0 j.val = some (.fin (x j))) ∧
        (∀ j : Fin 4, σ.entryFlat (27 + j.val) 0
          = some (.fin (if j.val = 2 * (sigmaCell (s 0)).val + (sigmaCell (s 1)).val
            then 1 else 0))))
      ↔ SignMem x s :=
  (quadExp_projection x (fun c => sigmaCell (s c))).trans
    (quadrantsTS_mem_iff_signMem x s)

#print axioms signMem_iff_lowering
#print axioms signMemStrict_iff_lowering
#print axioms indicator_prod_eq
#print axioms sign_exclusion_lowered
#print axioms PPLC.CellSchemaTS.interior_determines
#print axioms sign_interior_determines
#print axioms quadExp_typing
#print axioms quadExp_projection
#print axioms quadExp_projection_sa

end CellFlavorsExpansion
end PPLC
