import Qtsl.Catalogue
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin

/-! # Contraction rows: the einsum-lowering theorem, once, generally

The toolkit meets tensor contraction twice: as the `contract` box (the
book's Definition contraction-pattern, mechanized here as
`ContractPattern` with `contractExact` its exact evaluator), and as
*contraction rows* in the relational engine — an index map and an
output set stored as data, the summation definitional.  The two are one
definition at two strata; this module machine-checks that sentence.

**The row-form definition** (the Hypernets chapter, §Relational
kinship: contraction rows): over a semiring
`S`, a tensor indexed by an extent family `A : ι → ℕ` is a finite
function `(∀ i, Fin (A i)) → S`; the tensor product of a family is the
(lazy) pointwise product; the contraction of `T` along `a : ι → κ` with
output set `O` sends an output assignment `v` to the sum, over
assignments `w` of the non-output axes, of `T (i ↦ (v ∪ w)(a i))`.  The
extent family `B : κ → ℕ` is *induced* on the image of `a`
(`B (a i) = A i` — determined, not chosen) and is data only on the
broadcast axes `O \ im a`; the γ side condition (`[M] = im a ∪ O`)
makes the value-relevant free choice — an axis nobody reads, summed —
unrepresentable rather than discouraged.

**The statements.**

* `contractRaw_tprod_eq_einsumS` (T-A, the einsum-lowering theorem):
  for every `ContractPattern`, the row contraction of the lazy tensor
  product along the induced row computes the pattern's semiring
  semantics `einsumS`, at every row-form output coordinate.  Unconditional:
  a dead index degenerates identically on both sides.
* `NoDeadIndex.inducedRow_gamma` (T-γ): a pattern with no dead index
  induces a γ-satisfying row — einsum lowerings never emit the
  degenerate case on either side.
* `einsumS_dead_index` (T-B, γ's value-relevance receipt): a dead index
  scales the pattern's value by its extent, `|B(m)| • 1_S` — the
  would-be third case of the row-form definition, exhibited.
* `contractRaw_broadcast_const` (T-C): the contraction is constant
  along broadcast axes — extent data there is shape-relevant,
  value-irrelevant.
* `Row.extent_determined` (T-D): two γ-rows sharing `(a, O)` have equal
  extents away from the broadcast axes — determined, not chosen.
* `einsumS_diag_vanish` (T-F): at output coordinates that do not factor
  through a non-injective output binding, the eager box semantics is 0.
* `einsumS_eq_contract_of_injective`: with an injective output binding
  every pattern output coordinate is a row-form coordinate — the einsum
  tensor is recovered whole from the row.
* `contractExact_eq_einsumS` (T-E, the executable tie, ℚ locus): the
  catalogue's exact evaluator computes `einsumS` wherever the input
  reads are finite rationals.
* `SemOk_contract_iff` (T-G, the admissibility interface) and
  `Hypernet.Valuation.Admissible.contract_char` (T-H): the semantic
  universe consumes hypernets through θ's wall over `Admissible`
  (`SuFunctor.HypernetInclusion`, `mem_admRegion_iff`), and `Admissible`
  is the ∀-clause over `PrimApp.SemOk`; the contract arm of that clause
  is characterized, through T-E and T-A, as: every output read is a
  rounding of the row contraction of the lazy tensor product of the
  input tensors.  SU wall → `Admissible` → `SemOk` → `einsumS` →
  `contractRaw ∘ tprod` — the dependency chain by which the Hypernets
  chapter's relational-kinship section is consumed from above.
-/

namespace PPLC

/-! ## The row-form tensor definition, semiring-generic -/

namespace HouseTensor

variable {S : Type*}

/-- The tensor of the row-form definition, over a semiring: a finite function
`[∏ i, A i] → S`.  The index type generalizes the slide's `[N]`; the
finite-sequence form is the sigma instance used by `tprod`. -/
abbrev Tensor {ι : Type*} (A : ι → ℕ) (S : Type*) : Type _ :=
  (∀ i, Fin (A i)) → S

/-- The tensor product of a finite family, as the (lazy) pointwise
product over the flattened index set `Σ k, Fin (r k)`. -/
def tprod [CommSemiring S] {K : ℕ} {r : Fin K → ℕ}
    {A : ∀ k : Fin K, Fin (r k) → ℕ}
    (T : ∀ k : Fin K, Tensor (A k) S) :
    Tensor (fun p : (k : Fin K) × Fin (r k) => A p.1 p.2) S :=
  fun v => ∏ k : Fin K, T k fun a => v ⟨k, a⟩

/-- The contraction-row formula: at an output assignment `v` (on the
output axes `O`), sum over assignments `w` of the remaining axes of the
tensor read at `(v ∪ w) ∘ a`.  Stated for arbitrary `(a, O, B)` with
the induced-extent compatibility; γ is *not* a hypothesis of the
formula — it is row well-formedness (`Row`), and `einsumS_dead_index`
exhibits what its absence would cost. -/
def contractRaw [CommSemiring S] {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] {A : ι → ℕ}
    (a : ι → κ) (O : Finset κ) (B : κ → ℕ)
    (compat : ∀ i, B (a i) = A i) (T : Tensor A S) :
    Tensor (fun m : {x : κ // x ∈ O} => B m.val) S :=
  fun v => ∑ w : ∀ m : {x : κ // x ∉ O}, Fin (B m.val),
    T fun i => Fin.cast (compat i)
      (if h : a i ∈ O then v ⟨a i, h⟩ else w ⟨a i, h⟩)

/-- A contraction row: index map and output set as data, extents
induced on the image and free only on the broadcast axes, with the γ
side condition structural — the case that would silently scale a value
is unrepresentable in rows. -/
structure Row {ι κ : Type*} (A : ι → ℕ) where
  a : ι → κ
  O : Finset κ
  B : κ → ℕ
  compat : ∀ i, B (a i) = A i
  gamma : ∀ m, m ∉ O → ∃ i, a i = m

/-- The contraction of a tensor along a row. -/
def Row.contract [CommSemiring S] {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] {A : ι → ℕ} (R : Row (κ := κ) A) (T : Tensor A S) :
    Tensor (fun m : {x : κ // x ∈ R.O} => R.B m.val) S :=
  contractRaw R.a R.O R.B R.compat T

/-- T-C, broadcast constancy: the contraction reads its output
assignment only at axes hit by the index map, so it is constant along
the broadcast axes `O \ im a` — extent data there is shape-relevant but
value-irrelevant. -/
theorem contractRaw_broadcast_const [CommSemiring S] {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ] {A : ι → ℕ}
    (a : ι → κ) (O : Finset κ) (B : κ → ℕ)
    (compat : ∀ i, B (a i) = A i) (T : Tensor A S)
    (v v' : ∀ m : {x : κ // x ∈ O}, Fin (B m.val))
    (h : ∀ (m : κ) (hm : m ∈ O), (∃ i, a i = m) → v ⟨m, hm⟩ = v' ⟨m, hm⟩) :
    contractRaw a O B compat T v = contractRaw a O B compat T v' := by
  unfold contractRaw
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  funext i
  congr 1
  by_cases hi : a i ∈ O
  · rw [dif_pos hi, dif_pos hi, h (a i) hi ⟨i, rfl⟩]
  · rw [dif_neg hi, dif_neg hi]

/-- T-D, extent determination: two γ-rows sharing the index map and
output set have equal extents everywhere except possibly on the
broadcast axes `O \ im a` — `B` is determined (by `compat` on the
image, which γ extends to every summed axis), not chosen. -/
theorem Row.extent_determined {ι κ : Type*} {A : ι → ℕ}
    (R R' : Row (κ := κ) A) (ha : R.a = R'.a) (_hO : R.O = R'.O)
    (m : κ) (hm : m ∉ R.O ∨ ∃ i, R.a i = m) : R.B m = R'.B m := by
  have himage : ∀ i, R.B (R.a i) = R'.B (R.a i) := fun i => by
    rw [R.compat i, ← R'.compat i, ha]
  rcases hm with hm | ⟨i, hi⟩
  · obtain ⟨i, hi⟩ := R.gamma m hm
    rw [← hi]; exact himage i
  · rw [← hi]; exact himage i

end HouseTensor

/-! ## The pattern semantics, semiring-generic

`ContractPattern` is the mechanized catalogue's own einsum vocabulary
(the book's Definition contraction-pattern); `einsumS` is its semantics
over an arbitrary commutative semiring — the formula
`out[c] = ∑_{ν : νβ₀ = c} ∏ₘ inₘ[νβₘ]`, of which `contractExact` is the
exact-`ℚ` evaluator (tie: `contractExact_eq_einsumS`). -/

namespace ContractPattern

open HouseTensor

variable {inputRanks : List Nat} {outputRank : Nat}
variable {S : Type*} [CommSemiring S]

/-- The semiring semantics of a contraction pattern: sum over full
index assignments compatible with the output coordinate, of the
product of the input reads. -/
def einsumS (pat : ContractPattern inputRanks outputRank)
    (T : ∀ k : Fin inputRanks.length,
      Tensor (fun a : Fin (inputRanks.get k) =>
        pat.indexExtent (pat.inputBinding k a)) S) :
    Tensor (fun j : Fin outputRank => pat.indexExtent (pat.outputBinding j)) S :=
  fun c => ∑ ν : ∀ i, Fin (pat.indexExtent i),
    if ∀ j, ν (pat.outputBinding j) = c j then
      ∏ k, T k fun a => ν (pat.inputBinding k a)
    else 0

/-- The row's index map induced by a pattern: the copairing of the
input bindings on the flattened factor-axis set. -/
def inducedMap (pat : ContractPattern inputRanks outputRank) :
    ((k : Fin inputRanks.length) × Fin (inputRanks.get k)) → Fin pat.nIndices :=
  fun p => pat.inputBinding p.1 p.2

/-- The row's output set induced by a pattern: the image of the output
binding. -/
def outSet (pat : ContractPattern inputRanks outputRank) :
    Finset (Fin pat.nIndices) :=
  Finset.image pat.outputBinding Finset.univ

theorem outputBinding_mem_outSet (pat : ContractPattern inputRanks outputRank)
    (j : Fin outputRank) : pat.outputBinding j ∈ pat.outSet :=
  Finset.mem_image_of_mem _ (Finset.mem_univ j)

/-- No dead index: every index is hit by an input or by the output —
the well-formedness under which einsum lowers to a γ-row. -/
def NoDeadIndex (pat : ContractPattern inputRanks outputRank) : Prop :=
  ∀ i : Fin pat.nIndices,
    (∃ (k : Fin inputRanks.length) (a : Fin (inputRanks.get k)),
      pat.inputBinding k a = i) ∨ ∃ j, pat.outputBinding j = i

/-- T-γ: a no-dead-index pattern induces a γ-satisfying row — the
lowering emits only representable rows. -/
theorem NoDeadIndex.inducedRow_gamma {pat : ContractPattern inputRanks outputRank}
    (h : pat.NoDeadIndex) :
    ∀ m, m ∉ pat.outSet → ∃ p, pat.inducedMap p = m := by
  intro m hm
  rcases h m with ⟨k, a, hk⟩ | ⟨j, hj⟩
  · exact ⟨⟨k, a⟩, hk⟩
  · exact absurd (hj ▸ pat.outputBinding_mem_outSet j) hm

/-- The γ-row induced by a no-dead-index pattern. -/
def NoDeadIndex.inducedRow {pat : ContractPattern inputRanks outputRank}
    (h : pat.NoDeadIndex) :
    Row (κ := Fin pat.nIndices)
      (fun p : (k : Fin inputRanks.length) × Fin (inputRanks.get k) =>
        pat.indexExtent (pat.inputBinding p.1 p.2)) where
  a := pat.inducedMap
  O := pat.outSet
  B := pat.indexExtent
  compat := fun _ => rfl
  gamma := h.inducedRow_gamma

/-- **T-A, the einsum-lowering theorem**: the row contraction of the
lazy tensor product along the induced row computes the pattern's
semantics, at every row-form output coordinate.  Unconditional — γ and
output-binding injectivity govern representability and coordinate
coverage (T-γ, `einsumS_eq_contract_of_injective`), never this
equality: a dead index degenerates identically on both sides. -/
theorem contractRaw_tprod_eq_einsumS
    (pat : ContractPattern inputRanks outputRank)
    (T : ∀ k : Fin inputRanks.length,
      Tensor (fun a : Fin (inputRanks.get k) =>
        pat.indexExtent (pat.inputBinding k a)) S)
    (w : ∀ m : {x : Fin pat.nIndices // x ∈ pat.outSet}, Fin (pat.indexExtent m.val)) :
    contractRaw pat.inducedMap pat.outSet pat.indexExtent (fun _ => rfl)
        (tprod T) w
      = pat.einsumS T fun j => w ⟨pat.outputBinding j, pat.outputBinding_mem_outSet j⟩ := by
  classical
  unfold contractRaw einsumS
  rw [← Finset.sum_filter]
  refine Finset.sum_bij'
    (i := fun w' _ => fun m : Fin pat.nIndices =>
      if h : m ∈ pat.outSet then w ⟨m, h⟩ else w' ⟨m, h⟩)
    (j := fun ν _ => fun m : {x : Fin pat.nIndices // x ∉ pat.outSet} => ν m.val)
    ?_ ?_ ?_ ?_ ?_
  · -- membership: the glued assignment satisfies the output constraint
    intro w' _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩
    simp only [dif_pos (pat.outputBinding_mem_outSet j)]
  · -- membership: restriction lands in the summation domain
    intro ν _
    exact Finset.mem_univ _
  · -- left inverse: restrict ∘ glue = id
    intro w' _
    funext m
    simp only [dif_neg m.prop]
  · -- right inverse: glue ∘ restrict = id on the constrained set
    intro ν hν
    have hc : ∀ j, ν (pat.outputBinding j)
        = w ⟨pat.outputBinding j, pat.outputBinding_mem_outSet j⟩ :=
      (Finset.mem_filter.mp hν).2
    funext m
    by_cases h : m ∈ pat.outSet
    · simp only [dif_pos h]
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
      subst hj
      exact (hc j).symm
    · simp only [dif_neg h]
  · -- summands agree
    intro w' _
    unfold tprod
    exact Finset.prod_congr rfl fun k _ => rfl

/-- T-F, diagonal vanishing: at an output coordinate that does not
factor through the output binding, the eager pattern semantics is 0 —
the box's diagonal-write behavior off the factorable locus (the
relational rendering reaches only the factorable coordinates, by
construction). -/
theorem einsumS_diag_vanish (pat : ContractPattern inputRanks outputRank)
    (T : ∀ k : Fin inputRanks.length,
      Tensor (fun a : Fin (inputRanks.get k) =>
        pat.indexExtent (pat.inputBinding k a)) S)
    (c : ∀ j : Fin outputRank, Fin (pat.indexExtent (pat.outputBinding j)))
    (j j' : Fin outputRank) (hb : pat.outputBinding j = pat.outputBinding j')
    (hc : (c j).val ≠ (c j').val) :
    pat.einsumS T c = 0 := by
  unfold einsumS
  refine Finset.sum_eq_zero fun ν _ => ?_
  rw [if_neg]
  intro hall
  apply hc
  have hj := congrArg Fin.val (hall j)
  have hj' := congrArg Fin.val (hall j')
  have hν : (ν (pat.outputBinding j)).val = (ν (pat.outputBinding j')).val :=
    congrArg (fun m => (ν m).val) hb
  omega

/-- Full recovery under an injective output binding: every pattern
output coordinate is a row-form coordinate, so the einsum tensor is
recovered whole from the contraction row (with T-A).  Injectivity is
exactly the einsum well-formedness that makes the output reindexing a
bijection. -/
theorem einsumS_eq_contract_of_injective
    (pat : ContractPattern inputRanks outputRank)
    (T : ∀ k : Fin inputRanks.length,
      Tensor (fun a : Fin (inputRanks.get k) =>
        pat.indexExtent (pat.inputBinding k a)) S)
    (hinj : Function.Injective pat.outputBinding)
    (c : ∀ j : Fin outputRank, Fin (pat.indexExtent (pat.outputBinding j))) :
    ∃ w : ∀ m : {x : Fin pat.nIndices // x ∈ pat.outSet}, Fin (pat.indexExtent m.val),
      (∀ j, w ⟨pat.outputBinding j, pat.outputBinding_mem_outSet j⟩ = c j) ∧
      pat.einsumS T c
        = contractRaw pat.inducedMap pat.outSet pat.indexExtent (fun _ => rfl)
            (tprod T) w := by
  classical
  have hchoice : ∀ m : {x : Fin pat.nIndices // x ∈ pat.outSet},
      ∃ j, pat.outputBinding j = m.val := fun m => by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp m.prop
    exact ⟨j, hj⟩
  choose sec hsec using hchoice
  have hw : ∀ j, (fun m : {x : Fin pat.nIndices // x ∈ pat.outSet} =>
        Fin.cast (congrArg pat.indexExtent (hsec m)) (c (sec m)))
      ⟨pat.outputBinding j, pat.outputBinding_mem_outSet j⟩ = c j := by
    intro j
    have hj : sec ⟨pat.outputBinding j, pat.outputBinding_mem_outSet j⟩ = j :=
      hinj (hsec ⟨pat.outputBinding j, pat.outputBinding_mem_outSet j⟩)
    apply Fin.ext
    simp only [Fin.val_cast]
    exact congrArg (fun x => (c x).val) hj
  refine ⟨fun m => Fin.cast (congrArg pat.indexExtent (hsec m)) (c (sec m)), hw, ?_⟩
  rw [contractRaw_tprod_eq_einsumS]
  congr 1
  exact (funext hw).symm

/-- **T-B, γ's value-relevance receipt**: a dead index — hit by no
input binding and no output binding — scales the pattern's value by its
extent (`|B(m)| • 1_S`, as an `ℕ`-scalar on the semiring): the
would-be third case of the row-form definition is a value-relevant free
choice, which is why γ makes it unrepresentable in rows rather than
discouraged. -/
theorem einsumS_dead_index (pat : ContractPattern inputRanks outputRank)
    (T : ∀ k : Fin inputRanks.length,
      Tensor (fun a : Fin (inputRanks.get k) =>
        pat.indexExtent (pat.inputBinding k a)) S)
    (i₀ : Fin pat.nIndices)
    (hβ : ∀ (k : Fin inputRanks.length) (a : Fin (inputRanks.get k)),
      pat.inputBinding k a ≠ i₀)
    (hβ₀ : ∀ j, pat.outputBinding j ≠ i₀)
    (c : ∀ j : Fin outputRank, Fin (pat.indexExtent (pat.outputBinding j))) :
    pat.einsumS T c
      = pat.indexExtent i₀ •
        ∑ ν ∈ Finset.univ.filter
            (fun ν : ∀ i, Fin (pat.indexExtent i) =>
              (∀ j, ν (pat.outputBinding j) = c j) ∧ (ν i₀).val = 0),
          ∏ k, T k fun a => ν (pat.inputBinding k a) := by
  classical
  rcases Nat.eq_zero_or_pos (pat.indexExtent i₀) with h0 | hpos
  · -- extent 0: the full index-assignment type is empty; both sides are 0
    haveI : IsEmpty (∀ i, Fin (pat.indexExtent i)) :=
      ⟨fun ν => (h0 ▸ ν i₀).elim0⟩
    unfold einsumS
    rw [Finset.univ_eq_empty, Finset.sum_empty, Finset.filter_empty,
      Finset.sum_empty, smul_zero]
  · -- split each compatible assignment into (dead coordinate, pinned rest):
    -- the summand never reads the dead coordinate, so it contributes a
    -- pure cardinality factor
    unfold einsumS
    rw [← Finset.sum_filter]
    have key : ∑ ν ∈ (Finset.univ.filter fun ν : ∀ i, Fin (pat.indexExtent i) =>
          ∀ j, ν (pat.outputBinding j) = c j),
            ∏ k, T k (fun a => ν (pat.inputBinding k a))
        = ∑ p ∈ (Finset.univ : Finset (Fin (pat.indexExtent i₀))) ×ˢ
            (Finset.univ.filter fun ν : ∀ i, Fin (pat.indexExtent i) =>
              (∀ j, ν (pat.outputBinding j) = c j) ∧ (ν i₀).val = 0),
            ∏ k, T k fun a => p.2 (pat.inputBinding k a) := by
      refine Finset.sum_bij'
        (i := fun ν _ => (ν i₀, Function.update ν i₀ ⟨0, hpos⟩))
        (j := fun p _ => Function.update p.2 i₀ p.1) ?_ ?_ ?_ ?_ ?_
      · intro ν hν
        have hout := (Finset.mem_filter.mp hν).2
        refine Finset.mem_product.mpr ⟨Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_, ?_⟩⟩
        · dsimp only
          rw [Function.update_of_ne (hβ₀ j)]; exact hout j
        · dsimp only
          rw [Function.update_self]
      · intro p hp
        have hout := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2.1
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩
        rw [Function.update_of_ne (hβ₀ j)]; exact hout j
      · -- left inverse
        intro ν _
        dsimp only
        rw [Function.update_idem]
        exact Function.update_eq_self i₀ ν
      · -- right inverse
        intro p hp
        have hzero := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2.2
        refine Prod.ext ?_ ?_
        · simp only [Function.update_self]
        · show Function.update (Function.update p.2 i₀ p.1) i₀ ⟨0, hpos⟩ = p.2
          rw [Function.update_idem]
          have : (⟨0, hpos⟩ : Fin (pat.indexExtent i₀)) = p.2 i₀ :=
            Fin.ext (by rw [hzero])
          rw [this]
          exact Function.update_eq_self i₀ p.2
      · intro ν _
        dsimp only
        refine Finset.prod_congr rfl fun k _ => ?_
        congr 1
        funext a
        rw [Function.update_of_ne (hβ k a)]
    rw [key, Finset.sum_product]
    dsimp only
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

end ContractPattern

/-! ## Positions and the dependent-assignment correspondence -/

namespace Shape

theorem mem_positions_iff : ∀ {s : Shape} {ν : List ℕ},
    ν ∈ Shape.positions s
      ↔ ν.length = s.length ∧ ∀ i, i < s.length → ν.getD i 0 < s.getD i 0 := by
  intro s
  induction s with
  | nil =>
    intro ν
    simp only [Shape.positions, List.mem_singleton, List.length_nil]
    constructor
    · rintro rfl; exact ⟨rfl, fun i h => absurd h (Nat.not_lt_zero i)⟩
    · rintro ⟨h, _⟩; exact List.eq_nil_of_length_eq_zero h
  | cons e rest ih =>
    intro ν
    simp only [Shape.positions, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨x, hx, ν', hν', rfl⟩
      obtain ⟨hlen, hbound⟩ := ih.mp hν'
      refine ⟨by simp [hlen], fun i hi => ?_⟩
      match i with
      | 0 => simpa using hx
      | Nat.succ n =>
        simp only [List.getD_cons_succ]
        exact hbound n (Nat.lt_of_succ_lt_succ hi)
    · rintro ⟨hlen, hbound⟩
      match ν with
      | [] => simp at hlen
      | x :: ν' =>
        refine ⟨x, by simpa using hbound 0 (Nat.succ_pos _), ν', ?_, rfl⟩
        refine ih.mpr ⟨by simpa using hlen, fun i hi => ?_⟩
        simpa using hbound (i + 1) (Nat.succ_lt_succ hi)

private theorem nodup_flatMap_of_disjoint {α β : Type*} (f : α → List β) :
    ∀ l : List α, (∀ x ∈ l, (f x).Nodup) →
      l.Pairwise (fun x y => ∀ b ∈ f x, b ∉ f y) → (l.flatMap f).Nodup
  | [], _, _ => by simp
  | a :: l, hall, hpw => by
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpw
    rw [List.flatMap_cons]
    refine (hall a List.mem_cons_self).append
      (nodup_flatMap_of_disjoint f l
        (fun x hx => hall x (List.mem_cons_of_mem _ hx)) htail) ?_
    intro b hb hb'
    obtain ⟨x, hx, hbx⟩ := List.mem_flatMap.mp hb'
    exact hhead x hx b hb hbx

theorem positions_nodup : ∀ s : Shape, (Shape.positions s).Nodup := by
  intro s
  induction s with
  | nil => simp [Shape.positions]
  | cons e rest ih =>
    unfold Shape.positions
    refine nodup_flatMap_of_disjoint _ _
      (fun x _ => ih.map fun a b hab => by injection hab) ?_
    refine List.pairwise_lt_range.imp ?_
    intro x y hxy b hb hb'
    obtain ⟨ν', _, rfl⟩ := List.mem_map.mp hb
    obtain ⟨ν'', _, h⟩ := List.mem_map.mp hb'
    injection h with h1 _
    exact absurd h1.symm (Nat.ne_of_lt hxy)

end Shape

namespace ContractPattern

open HouseTensor

variable {inputRanks : List Nat} {outputRank : Nat}

private theorem getD_ofFn {n : ℕ} (f : Fin n → ℕ) (i : ℕ) (h : i < n) :
    (List.ofFn f).getD i 0 = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [h]

/-- Encode a dependent index assignment as a coordinate list. -/
def encodeAssign {n : ℕ} {E : Fin n → ℕ} (ν : ∀ i, Fin (E i)) : List ℕ :=
  List.ofFn fun i => (ν i).val

theorem encodeAssign_getD {n : ℕ} {E : Fin n → ℕ} (ν : ∀ i, Fin (E i))
    (i : Fin n) : (encodeAssign ν).getD i.val 0 = (ν i).val := by
  rw [encodeAssign, getD_ofFn _ _ i.isLt]

theorem encodeAssign_mem_positions {n : ℕ} {E : Fin n → ℕ} (ν : ∀ i, Fin (E i)) :
    encodeAssign ν ∈ Shape.positions (List.ofFn E) := by
  refine Shape.mem_positions_iff.mpr ⟨by simp [encodeAssign], fun i hi => ?_⟩
  have hi' : i < n := by rwa [List.length_ofFn] at hi
  rw [show ((List.ofFn E).getD i 0) = E ⟨i, hi'⟩ from getD_ofFn E i hi',
    show ((encodeAssign ν).getD i 0) = (ν ⟨i, hi'⟩).val from
      encodeAssign_getD ν ⟨i, hi'⟩]
  exact (ν ⟨i, hi'⟩).isLt

/-- Bounds extracted from positions membership. -/
theorem bounds_of_mem_positions {n : ℕ} {E : Fin n → ℕ} {ν : List ℕ}
    (h : ν ∈ Shape.positions (List.ofFn E)) :
    ∀ i : Fin n, ν.getD i.val 0 < E i := by
  intro i
  obtain ⟨_, hbound⟩ := Shape.mem_positions_iff.mp h
  have := hbound i.val (by simp)
  rwa [getD_ofFn E i.val i.isLt] at this

/-- Decode a bounded coordinate list into a dependent assignment. -/
def decodeAssign {n : ℕ} (E : Fin n → ℕ) (ν : List ℕ)
    (h : ∀ i : Fin n, ν.getD i.val 0 < E i) : ∀ i, Fin (E i) :=
  fun i => ⟨ν.getD i.val 0, h i⟩

theorem decode_encode {n : ℕ} {E : Fin n → ℕ} (ν : ∀ i, Fin (E i))
    (h : ∀ i : Fin n, (encodeAssign ν).getD i.val 0 < E i) :
    decodeAssign E (encodeAssign ν) h = ν := by
  funext i
  exact Fin.ext (encodeAssign_getD ν i)

theorem encode_decode {n : ℕ} {E : Fin n → ℕ} {ν : List ℕ}
    (hmem : ν ∈ Shape.positions (List.ofFn E))
    (h : ∀ i : Fin n, ν.getD i.val 0 < E i) :
    encodeAssign (decodeAssign E ν h) = ν := by
  obtain ⟨hlen, _⟩ := Shape.mem_positions_iff.mp hmem
  have hlen' : ν.length = n := by simpa using hlen
  refine List.ext_getElem (by simp [encodeAssign, hlen']) fun i h1 h2 => ?_
  have hi : i < n := by simpa [encodeAssign] using h1
  have h3 : (encodeAssign (decodeAssign E ν h))[i] = ν.getD i 0 := by
    have h4 := encodeAssign_getD (decodeAssign E ν h) ⟨i, hi⟩
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      Option.getD_some] at h4
  rw [h3, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
    Option.getD_some]

/-! ## Monadic evaluation lemmas (`Option`, all-finite) -/

private theorem mapM_eq_map_of_forall {α β : Type*} (f : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => by simp
  | a :: l, h => by
    rw [List.mapM_cons, h a List.mem_cons_self,
      mapM_eq_map_of_forall f g l fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

private theorem foldlM_mul?_fin : ∀ (l : List ℚ) (q : ℚ),
    (l.map ERat.fin).foldlM ERat.mul? (ERat.fin q) = some (ERat.fin (q * l.prod))
  | [], q => by simp
  | a :: l, q => by
    rw [List.map_cons, List.foldlM_cons]
    show (List.map ERat.fin l).foldlM ERat.mul? (ERat.fin (q * a))
      = some (ERat.fin (q * (a :: l).prod))
    rw [foldlM_mul?_fin l (q * a), List.prod_cons, mul_assoc]

private theorem prod?_map_fin (l : List ℚ) :
    ERat.prod? (l.map ERat.fin) = some (ERat.fin l.prod) := by
  rw [ERat.prod?, foldlM_mul?_fin l 1, one_mul]

private theorem foldlM_add?_fin : ∀ (l : List ℚ) (q : ℚ),
    (l.map ERat.fin).foldlM ERat.add? (ERat.fin q) = some (ERat.fin (q + l.sum))
  | [], q => by simp
  | a :: l, q => by
    rw [List.map_cons, List.foldlM_cons]
    show (List.map ERat.fin l).foldlM ERat.add? (ERat.fin (q + a))
      = some (ERat.fin (q + (a :: l).sum))
    rw [foldlM_add?_fin l (q + a), List.sum_cons, add_assoc]

private theorem sum?_map_fin (l : List ℚ) :
    ERat.sum? (l.map ERat.fin) = some (ERat.fin l.sum) := by
  rw [ERat.sum?, foldlM_add?_fin l 0, zero_add]

/-! ## T-E: the executable tie at the ℚ locus -/

/-- **T-E, the executable tie**: wherever the input reads are finite
rationals forming tensors `T` (the premise `hin` — the exact-`ℚ`
locus), the catalogue's `contractExact` evaluator computes the
pattern's semiring semantics.  Composing with T-A: the box evaluator
computes the row contraction of the lazy tensor product. -/
theorem contractExact_eq_einsumS {H : Hypernet} (σ : H.Valuation)
    (inputs : List Wire) (pat : ContractPattern inputRanks outputRank)
    (T : ∀ k : Fin inputRanks.length,
      Tensor (fun a : Fin (inputRanks.get k) =>
        pat.indexExtent (pat.inputBinding k a)) ℚ)
    (hin : ∀ (k : Fin inputRanks.length)
        (v : ∀ a : Fin (inputRanks.get k), Fin (pat.indexExtent (pat.inputBinding k a))),
      σ.entryAt (inputs.getD k.val 0) (List.ofFn fun a => (v a).val)
        = some (ERat.fin (T k v)))
    (c : ∀ j : Fin outputRank, Fin (pat.indexExtent (pat.outputBinding j))) :
    contractExact σ inputs pat (List.ofFn fun j => (c j).val)
      = some (ERat.fin (pat.einsumS T c)) := by
  classical
  -- the total per-assignment value function (guarded decode)
  set F : List ℕ → ℚ := fun ν =>
    if h : ∀ i : Fin pat.nIndices, ν.getD i.val 0 < pat.indexExtent i then
      ∏ k, T k fun a => decodeAssign pat.indexExtent ν h (pat.inputBinding k a)
    else 0 with hF
  set target : List ℕ := List.ofFn fun j => (c j).val with htarget
  set assigns : List (List ℕ) :=
    (Shape.positions pat.idxShape).filter
      (fun ν => decide (pat.outCoords ν = target)) with hassigns
  have hmem_assigns : ∀ ν ∈ assigns,
      ν ∈ Shape.positions (List.ofFn pat.indexExtent) ∧ pat.outCoords ν = target := by
    intro ν hν
    have := List.mem_filter.mp hν
    exact ⟨this.1, of_decide_eq_true this.2⟩
  -- Step 1: the inner evaluation is finite and computes F, on assigns
  have hinner : ∀ ν ∈ assigns,
      ((List.finRange inputRanks.length).mapM
        (fun k => σ.entryAt (inputs.getD k.val 0) (pat.inCoords ν k))
        >>= ERat.prod?) = some (ERat.fin (F ν)) := by
    intro ν hν
    obtain ⟨hpos, _⟩ := hmem_assigns ν hν
    have hbound := bounds_of_mem_positions hpos
    have hread : ∀ k ∈ List.finRange inputRanks.length,
        σ.entryAt (inputs.getD k.val 0) (pat.inCoords ν k)
          = some (ERat.fin (T k fun a =>
              decodeAssign pat.indexExtent ν hbound (pat.inputBinding k a))) := by
      intro k _
      have hco : pat.inCoords ν k = List.ofFn fun a =>
          ((decodeAssign pat.indexExtent ν hbound (pat.inputBinding k a)).val) := by
        unfold ContractPattern.inCoords
        rw [List.ofFn_eq_map]
        rfl
      rw [hco]
      exact hin k _
    have hFν : F ν = ((List.finRange inputRanks.length).map
        (fun k => T k fun a =>
          decodeAssign pat.indexExtent ν hbound (pat.inputBinding k a))).prod := by
      rw [hF]
      dsimp only
      rw [dif_pos hbound, ← List.ofFn_eq_map, List.prod_ofFn]
    rw [mapM_eq_map_of_forall _
      (fun k => ERat.fin (T k fun a =>
        decodeAssign pat.indexExtent ν hbound (pat.inputBinding k a)))
      _ hread]
    show ERat.prod? ((List.finRange inputRanks.length).map
        (fun k => ERat.fin (T k fun a =>
          decodeAssign pat.indexExtent ν hbound (pat.inputBinding k a))))
      = some (ERat.fin (F ν))
    rw [show (List.finRange inputRanks.length).map
          (fun k => ERat.fin (T k fun a =>
            decodeAssign pat.indexExtent ν hbound (pat.inputBinding k a)))
        = ((List.finRange inputRanks.length).map
            (fun k => T k fun a =>
              decodeAssign pat.indexExtent ν hbound (pat.inputBinding k a))).map
            ERat.fin from List.map_map.symm,
      prod?_map_fin, hFν]
  -- Step 2: contractExact computes the list sum of F over assigns
  have hCE : contractExact σ inputs pat target
      = some (ERat.fin ((assigns.map F).sum)) := by
    show (assigns.mapM (fun ν => (List.finRange inputRanks.length).mapM
        (fun k => σ.entryAt (inputs.getD k.val 0) (pat.inCoords ν k))
        >>= ERat.prod?) >>= ERat.sum?)
      = some (ERat.fin ((assigns.map F).sum))
    rw [mapM_eq_map_of_forall _ (fun ν => ERat.fin (F ν)) _ hinner]
    show ERat.sum? (assigns.map fun ν => ERat.fin (F ν))
      = some (ERat.fin ((assigns.map F).sum))
    rw [show assigns.map (fun ν => ERat.fin (F ν)) = (assigns.map F).map ERat.fin from
        List.map_map.symm,
      sum?_map_fin]
  -- Step 3: the list sum is the Finset einsum sum
  have hnodup : assigns.Nodup :=
    (Shape.positions_nodup pat.idxShape).filter _
  have hsum : (assigns.map F).sum = pat.einsumS T c := by
    rw [← List.sum_toFinset _ hnodup]
    unfold einsumS
    rw [← Finset.sum_filter]
    refine Finset.sum_bij'
      (i := fun ν hν => decodeAssign pat.indexExtent ν
        (bounds_of_mem_positions (hmem_assigns ν (List.mem_toFinset.mp hν)).1))
      (j := fun ν' _ => encodeAssign ν') ?_ ?_ ?_ ?_ ?_
    · intro ν hν
      obtain ⟨hpos, hout⟩ := hmem_assigns ν (List.mem_toFinset.mp hν)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩
      apply Fin.ext
      show ν.getD (pat.outputBinding j).val 0 = (c j).val
      have h1 : pat.outCoords ν = target := hout
      rw [htarget] at h1
      unfold ContractPattern.outCoords at h1
      rw [← List.ofFn_eq_map] at h1
      exact congrFun (List.ofFn_inj.mp h1) j
    · intro ν' hν'
      have hout : ∀ j, ν' (pat.outputBinding j) = c j :=
        (Finset.mem_filter.mp hν').2
      refine List.mem_toFinset.mpr (List.mem_filter.mpr
        ⟨encodeAssign_mem_positions ν', decide_eq_true ?_⟩)
      show pat.outCoords (encodeAssign ν') = target
      rw [htarget]
      unfold ContractPattern.outCoords
      rw [← List.ofFn_eq_map]
      exact congrArg List.ofFn (funext fun j => by
        rw [encodeAssign_getD ν' (pat.outputBinding j), hout j])
    · intro ν hν
      exact encode_decode (hmem_assigns ν (List.mem_toFinset.mp hν)).1 _
    · intro ν' _
      exact decode_encode ν' _
    · intro ν hν
      obtain ⟨hpos, _⟩ := hmem_assigns ν (List.mem_toFinset.mp hν)
      exact dif_pos (bounds_of_mem_positions hpos)
  rw [hCE, hsum]

/-! ## T-G / T-H: the admissibility interface at the `SemOk` stratum

The semantic universe consumes hypernets through θ's possibilistic wall
over the admissible-valuation region (`SuFunctor.HypernetInclusion`,
`mem_admRegion_iff`); `Hypernet.Valuation.Admissible` is the ∀-clause
over `PrimApp.SemOk`.  The contract arm of that clause is characterized
here against the row-form semantics — SU wall → `Admissible` → `SemOk` →
`einsumS` (T-E) → `contractRaw ∘ tprod` (T-A). -/

/-- **T-G, the admissibility interface**: under the exact-`ℚ` input premise, the
`SemOk` clause of a `contract` application holds iff every output read,
at every index assignment, is a `δ`-rounding of the pattern's row-form
semantics at that coordinate. -/
theorem SemOk_contract_iff {H : Hypernet} (σ : H.Valuation)
    (δ : Dtype) (r : RoundMode) (inputs : List Wire) (output : Wire)
    (pat : ContractPattern inputRanks outputRank)
    (T : ∀ k : Fin inputRanks.length,
      Tensor (fun a : Fin (inputRanks.get k) =>
        pat.indexExtent (pat.inputBinding k a)) ℚ)
    (hin : ∀ (k : Fin inputRanks.length)
        (v : ∀ a : Fin (inputRanks.get k), Fin (pat.indexExtent (pat.inputBinding k a))),
      σ.entryAt (inputs.getD k.val 0) (List.ofFn fun a => (v a).val)
        = some (ERat.fin (T k v))) :
    PrimApp.SemOk σ (.contract δ r inputs output inputRanks outputRank pat)
      ↔ ∀ ν' : ∀ i, Fin (pat.indexExtent i), ∃ eOut,
          σ.entryAt output (List.ofFn fun j => ((ν' (pat.outputBinding j)).val))
            = some eOut ∧
          δ.RoundOkE r
            (ERat.fin (pat.einsumS T fun j => ν' (pat.outputBinding j))) eOut := by
  classical
  have houtCoords : ∀ ν' : ∀ i, Fin (pat.indexExtent i),
      pat.outCoords (encodeAssign ν')
        = List.ofFn fun j => ((ν' (pat.outputBinding j)).val) := by
    intro ν'
    unfold ContractPattern.outCoords
    rw [← List.ofFn_eq_map]
    exact congrArg List.ofFn (funext fun j =>
      encodeAssign_getD ν' (pat.outputBinding j))
  constructor
  · intro hsem ν'
    have hν₀ : encodeAssign ν' ∈ Shape.positions pat.idxShape :=
      encodeAssign_mem_positions ν'
    obtain ⟨eOut, eExact, hout, hexact, hround⟩ := hsem (encodeAssign ν') hν₀
    refine ⟨eOut, ?_, ?_⟩
    · rw [← houtCoords ν']; exact hout
    · have := contractExact_eq_einsumS σ inputs pat T hin
        (fun j => ν' (pat.outputBinding j))
      rw [← houtCoords ν'] at this
      rw [hexact] at this
      obtain rfl : eExact = ERat.fin (pat.einsumS T fun j => ν' (pat.outputBinding j)) :=
        Option.some.inj this
      exact hround
  · intro hchar ν₀ hν₀
    have hbound := bounds_of_mem_positions (E := pat.indexExtent) hν₀
    set ν' := decodeAssign pat.indexExtent ν₀ hbound with hν'
    have henc : encodeAssign ν' = ν₀ := encode_decode hν₀ hbound
    obtain ⟨eOut, hout, hround⟩ := hchar ν'
    refine ⟨eOut, ERat.fin (pat.einsumS T fun j => ν' (pat.outputBinding j)), ?_, ?_, hround⟩
    · rw [← houtCoords ν', henc] at hout
      exact hout
    · have := contractExact_eq_einsumS σ inputs pat T hin
        (fun j => ν' (pat.outputBinding j))
      rw [← houtCoords ν', henc] at this
      exact this

end ContractPattern

/-- **T-H, the `Admissible` stitch**: an admissible valuation of a
hypernet containing a `contract` application satisfies the T-G
characterization at that application — the form in which the einsum
adequacy is consumed by θ's wall into the semantic universe. -/
theorem Hypernet.Valuation.Admissible.contract_char {H : Hypernet}
    {σ : H.Valuation} (hσ : σ.Admissible)
    {δ : Dtype} {r : RoundMode} {inputs : List Wire} {output : Wire}
    {inputRanks : List Nat} {outputRank : Nat}
    {pat : ContractPattern inputRanks outputRank}
    (happ : PrimApp.contract δ r inputs output inputRanks outputRank pat
      ∈ H.applications)
    (T : ∀ k : Fin inputRanks.length,
      HouseTensor.Tensor (fun a : Fin (inputRanks.get k) =>
        pat.indexExtent (pat.inputBinding k a)) ℚ)
    (hin : ∀ (k : Fin inputRanks.length)
        (v : ∀ a : Fin (inputRanks.get k), Fin (pat.indexExtent (pat.inputBinding k a))),
      σ.entryAt (inputs.getD k.val 0) (List.ofFn fun a => (v a).val)
        = some (ERat.fin (T k v))) :
    ∀ ν' : ∀ i, Fin (pat.indexExtent i), ∃ eOut,
      σ.entryAt output (List.ofFn fun j => ((ν' (pat.outputBinding j)).val))
        = some eOut ∧
      δ.RoundOkE r
        (ERat.fin (pat.einsumS T fun j => ν' (pat.outputBinding j))) eOut :=
  (ContractPattern.SemOk_contract_iff σ δ r inputs output pat T hin).mp
    (hσ _ happ)

end PPLC

/-! ## Axiom receipts -/

#print axioms PPLC.ContractPattern.contractRaw_tprod_eq_einsumS
#print axioms PPLC.ContractPattern.NoDeadIndex.inducedRow_gamma
#print axioms PPLC.ContractPattern.einsumS_dead_index
#print axioms PPLC.HouseTensor.contractRaw_broadcast_const
#print axioms PPLC.HouseTensor.Row.extent_determined
#print axioms PPLC.ContractPattern.einsumS_diag_vanish
#print axioms PPLC.ContractPattern.einsumS_eq_contract_of_injective
#print axioms PPLC.ContractPattern.contractExact_eq_einsumS
#print axioms PPLC.ContractPattern.SemOk_contract_iff
#print axioms PPLC.Hypernet.Valuation.Admissible.contract_char
