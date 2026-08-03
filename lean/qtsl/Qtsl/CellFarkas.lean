import Qtsl.CellFlavors
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Farkas exclusion certificates for simplicial cell schemas

`SimpC.CellIntDisjoint` — the cell box's semantic well-formedness
conjunct — quantifies over real barycentric weights, so it is not
checkable from the schema data by any finite scan. But `MaskRegion` and
`MaskRegionStrict` are *linear* feasibility conditions in those weights:
for an ordered cell pair `(i, k)`, "strictly in `i` and weakly in `k`"
is a linear system over the two weight vectors (the ambient point is
eliminated by matching the coordinate rows), and its infeasibility has
a finite exact-rational certificate in the Motzkin–Farkas style. This
module defines that certificate (`PairCert`), its decidable validity
check (`checkPair` — exact rational arithmetic; it verifies, it never
solves), and the soundness results:

* `checkPair_sound` — a valid certificate refutes joint membership;
* `checkTable_sound` — valid certificates for every ordered pair
  discharge `SimpC.CellIntDisjoint` outright, so the cell typing rule's
  disjointness side condition becomes finite certificate data;
* `checkTables_ts_sound` — per-cluster tables discharge the
  tensor-simplicial exclusion through
  `CellSchemaTS.product_exclusion`: certificates are checked in the
  small cluster dimensions, never against the exponential product
  roster.

## The certificate, geometrically

A valid certificate is a separating affine functional in multiplier
clothing: `fun y => alpha + gamma ⬝ y` is nonpositive on the strict
cell's core vertices and nonnegative on its extension vertices — hence
nonpositive across the cell's whole region, and strictly negative on
its relative interior as soon as some multiplier `p v` is nonzero —
while `fun y => beta - gamma ⬝ y` does the same for the weak cell. The
gap condition (`0 < alpha + beta`, or `alpha + beta = 0` with a nonzero
strict-side multiplier) makes the two sides collide.

Soundness needs no linear-programming theory: multiply each masked
vertex's (vanishing) certificate row by that vertex's real barycentric
weight, sum, and read off a sign contradiction. Rational multipliers
refute *real*-weighted membership because the derivation is valid over
any ordered field extending ℚ.

Completeness — a certificate exists whenever the pair system really is
infeasible (Motzkin transposition) — is deliberately not stated here:
finding multipliers is untrusted producer machinery elsewhere; this
module is the checker and its warrant.
-/

namespace PPLC

/-- ℚ-valued twin of `finSum`. -/
def finSumQ (n : ℕ) (f : Fin n → ℚ) : ℚ := ((List.finRange n).map f).sum

theorem finSum_eq_sum (n : ℕ) (f : Fin n → ℝ) :
    finSum n f = ∑ v, f v := (Fin.sum_univ_def f).symm

theorem finSumQ_eq_sum (n : ℕ) (f : Fin n → ℚ) :
    finSumQ n f = ∑ v, f v := (Fin.sum_univ_def f).symm

theorem finSumQ_cast (n : ℕ) (f : Fin n → ℚ) :
    ((finSumQ n f : ℚ) : ℝ) = ∑ v, ((f v : ℚ) : ℝ) := by
  rw [finSumQ_eq_sum]
  push_cast
  rfl

namespace CellFarkas

/-- A Farkas-style exclusion certificate for one ordered cell pair of a
`SimpC` — cell `i` read strictly, cell `k` weakly. `alpha` and `beta`
multiply the two sum-to-one rows, `gamma` the coordinate-matching rows,
`p` and `q` the sign rows of the two cells (meaningful on the
respective masks; the checker reads them nowhere else). This field list
is the row-payload contract for the schema-row conformance family. -/
structure PairCert (C : SimpC) where
  alpha : ℚ
  beta : ℚ
  gamma : Fin C.ambDim → ℚ
  p : Fin C.nVertices → ℚ
  q : Fin C.nVertices → ℚ

variable {C : SimpC}

/-- The strict-side affine functional at vertex `v`:
`alpha + gamma ⬝ coord v`. -/
def PairCert.affA (cert : PairCert C) (v : Fin C.nVertices) : ℚ :=
  cert.alpha + finSumQ C.ambDim (fun j => cert.gamma j * C.coord v j)

/-- The weak-side affine functional at vertex `v`:
`beta - gamma ⬝ coord v`. -/
def PairCert.affB (cert : PairCert C) (v : Fin C.nVertices) : ℚ :=
  cert.beta - finSumQ C.ambDim (fun j => cert.gamma j * C.coord v j)

/-- Validity of a certificate for the ordered pair `(i, k)`: multiplier
signs, the per-vertex row identities on each cell's mask, and the gap
condition. Exact rational arithmetic over the schema data — nothing is
solved, nothing is approximated. -/
def checkPair (C : SimpC) (i k : Fin C.cells.length)
    (cert : PairCert C) : Bool :=
  ((List.finRange C.nVertices).all fun v => decide (0 ≤ cert.p v)) &&
  ((List.finRange C.nVertices).all fun v => decide (0 ≤ cert.q v)) &&
  ((List.finRange C.nVertices).all fun v =>
    !((C.cells.get i).1 v) ||
      decide (cert.affA v
        + (bif (C.cells.get i).2 v then -(cert.p v) else cert.p v) = 0)) &&
  ((List.finRange C.nVertices).all fun v =>
    !((C.cells.get k).1 v) ||
      decide (cert.affB v
        + (bif (C.cells.get k).2 v then -(cert.q v) else cert.q v) = 0)) &&
  (decide (0 < cert.alpha + cert.beta) ||
   (decide (cert.alpha + cert.beta = 0) &&
    ((List.finRange C.nVertices).any fun v =>
      (C.cells.get i).1 v && decide (cert.p v ≠ 0))))

/-! ## Soundness -/

/-- The one-side evaluation identity: multiplying each masked vertex's
(vanishing) certificate row by that vertex's barycentric weight and
summing, the sum-to-one and coordinate rows collapse the affine part to
its value at the represented point, leaving the multiplier tail. Stated
for any weight vector with the `MaskRegion` support/sum/coordinate
structure — the weak and strict memberships both provide it. -/
private theorem key_eq {mask ext : Fin C.nVertices → Bool}
    {x : Fin C.ambDim → ℚ} {lam : Fin C.nVertices → ℝ}
    (hsupp : ∀ v, mask v = false → lam v = 0)
    (hsum : finSum C.nVertices lam = 1)
    (hcoord : ∀ j : Fin C.ambDim,
      finSum C.nVertices (fun v => lam v * (C.coord v j : ℝ)) = (x j : ℝ))
    (a : ℚ) (g : Fin C.ambDim → ℚ) (r : Fin C.nVertices → ℚ)
    (hvan : ∀ v, mask v = true →
      a + finSumQ C.ambDim (fun j => g j * C.coord v j)
        + (bif ext v then -(r v) else r v) = 0) :
    (a : ℝ) + (∑ j, (g j : ℝ) * (x j : ℝ))
      + (∑ v, lam v * (((bif ext v then -(r v) else r v) : ℚ) : ℝ)) = 0 := by
  have hsum' : ∑ v, lam v = 1 := by rw [← finSum_eq_sum]; exact hsum
  have hcoord' : ∀ j : Fin C.ambDim,
      ∑ v, lam v * ((C.coord v j : ℚ) : ℝ) = (x j : ℝ) := fun j => by
    rw [← finSum_eq_sum]; exact hcoord j
  -- the ℝ-cast whole-row coefficient at each vertex
  set F : Fin C.nVertices → ℝ := fun v =>
    ((a + finSumQ C.ambDim (fun j => g j * C.coord v j)
      + (bif ext v then -(r v) else r v) : ℚ) : ℝ) with hF
  -- weighted rows sum to zero: masked rows vanish, unmasked weights vanish
  have hzero : ∑ v, lam v * F v = 0 := by
    refine Finset.sum_eq_zero fun v _ => ?_
    cases hmv : mask v with
    | true =>
        have h0 : F v = 0 := by
          simp only [hF]
          rw [hvan v hmv]
          exact Rat.cast_zero
        rw [h0, mul_zero]
    | false => rw [hsupp v hmv, zero_mul]
  -- decompose each row coefficient into its three ℝ pieces
  have hFsplit : ∀ v, F v
      = (a : ℝ) + (∑ j, (g j : ℝ) * ((C.coord v j : ℚ) : ℝ))
        + (((bif ext v then -(r v) else r v) : ℚ) : ℝ) := by
    intro v
    simp only [hF]
    rw [Rat.cast_add, Rat.cast_add, finSumQ_cast]
    congr 2
    exact Finset.sum_congr rfl fun j _ => Rat.cast_mul _ _
  -- exchange the double sum in the middle piece
  have hmid : ∑ v, lam v * (∑ j, (g j : ℝ) * ((C.coord v j : ℚ) : ℝ))
      = ∑ j, (g j : ℝ) * (∑ v, lam v * ((C.coord v j : ℚ) : ℝ)) := by
    calc ∑ v, lam v * (∑ j, (g j : ℝ) * ((C.coord v j : ℚ) : ℝ))
        = ∑ v, ∑ j, lam v * ((g j : ℝ) * ((C.coord v j : ℚ) : ℝ)) :=
          Finset.sum_congr rfl fun v _ => by rw [Finset.mul_sum]
      _ = ∑ j, ∑ v, lam v * ((g j : ℝ) * ((C.coord v j : ℚ) : ℝ)) :=
          Finset.sum_comm
      _ = ∑ j, (g j : ℝ) * (∑ v, lam v * ((C.coord v j : ℚ) : ℝ)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
  -- expand the weighted sum along the decomposition
  have hexpand : ∑ v, lam v * F v
      = (a : ℝ) * (∑ v, lam v)
        + (∑ j, (g j : ℝ) * (∑ v, lam v * ((C.coord v j : ℚ) : ℝ)))
        + (∑ v, lam v * (((bif ext v then -(r v) else r v) : ℚ) : ℝ)) := by
    calc ∑ v, lam v * F v
        = ∑ v, ((a : ℝ) * lam v
            + lam v * (∑ j, (g j : ℝ) * ((C.coord v j : ℚ) : ℝ))
            + lam v * (((bif ext v then -(r v) else r v) : ℚ) : ℝ)) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [hFsplit v]; ring
      _ = (∑ v, (a : ℝ) * lam v)
            + (∑ v, lam v * (∑ j, (g j : ℝ) * ((C.coord v j : ℚ) : ℝ)))
            + (∑ v, lam v * (((bif ext v then -(r v) else r v) : ℚ) : ℝ)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (a : ℝ) * (∑ v, lam v)
            + (∑ j, (g j : ℝ) * (∑ v, lam v * ((C.coord v j : ℚ) : ℝ)))
            + (∑ v, lam v * (((bif ext v then -(r v) else r v) : ℚ) : ℝ)) := by
          rw [← Finset.mul_sum, hmid]
  rw [hexpand, hsum', mul_one] at hzero
  calc (a : ℝ) + (∑ j, (g j : ℝ) * (x j : ℝ))
        + (∑ v, lam v * (((bif ext v then -(r v) else r v) : ℚ) : ℝ))
      = (a : ℝ) + (∑ j, (g j : ℝ) * (∑ v, lam v * ((C.coord v j : ℚ) : ℝ)))
        + (∑ v, lam v * (((bif ext v then -(r v) else r v) : ℚ) : ℝ)) := by
        congr 2
        exact Finset.sum_congr rfl fun j _ => by rw [hcoord' j]
    _ = 0 := hzero

/-- The multiplier tail is nonnegative against weak membership signs. -/
private theorem tail_nonneg {mask ext : Fin C.nVertices → Bool}
    {lam : Fin C.nVertices → ℝ}
    (hsupp : ∀ v, mask v = false → lam v = 0)
    (hext : ∀ v, ext v = true → lam v ≤ 0)
    (hcore : ∀ v, mask v = true → ext v = false → 0 ≤ lam v)
    (r : Fin C.nVertices → ℚ) (hr : ∀ v, 0 ≤ r v) :
    0 ≤ ∑ v, lam v * (((bif ext v then -(r v) else r v) : ℚ) : ℝ) := by
  refine Finset.sum_nonneg fun v _ => ?_
  have hrv : (0 : ℝ) ≤ (r v : ℝ) := by exact_mod_cast hr v
  cases hev : ext v with
  | true =>
      rw [Bool.cond_true, Rat.cast_neg]
      have h1 : lam v ≤ 0 := hext v hev
      nlinarith
  | false =>
      rw [Bool.cond_false]
      cases hmv : mask v with
      | true => exact mul_nonneg (hcore v hmv hev) hrv
      | false => rw [hsupp v hmv, zero_mul]

/-- The multiplier tail is strictly positive against strict membership
signs as soon as some masked multiplier is positive. -/
private theorem tail_pos {mask ext : Fin C.nVertices → Bool}
    {lam : Fin C.nVertices → ℝ}
    (hsupp : ∀ v, mask v = false → lam v = 0)
    (hext : ∀ v, ext v = true → lam v < 0)
    (hcore : ∀ v, mask v = true → ext v = false → 0 < lam v)
    (r : Fin C.nVertices → ℚ) (hr : ∀ v, 0 ≤ r v)
    (hwit : ∃ v, mask v = true ∧ 0 < r v) :
    0 < ∑ v, lam v * (((bif ext v then -(r v) else r v) : ℚ) : ℝ) := by
  obtain ⟨v0, hm0, hr0⟩ := hwit
  refine Finset.sum_pos' (fun v _ => ?_) ⟨v0, Finset.mem_univ v0, ?_⟩
  · -- termwise nonnegativity, with the strict signs weakened
    have hrv : (0 : ℝ) ≤ (r v : ℝ) := by exact_mod_cast hr v
    cases hev : ext v with
    | true =>
        rw [Bool.cond_true, Rat.cast_neg]
        have h1 : lam v ≤ 0 := le_of_lt (hext v hev)
        nlinarith
    | false =>
        rw [Bool.cond_false]
        cases hmv : mask v with
        | true => exact mul_nonneg (le_of_lt (hcore v hmv hev)) hrv
        | false => rw [hsupp v hmv, zero_mul]
  · -- the witness vertex's term is strictly positive
    have hr0' : (0 : ℝ) < (r v0 : ℝ) := by exact_mod_cast hr0
    cases hev : ext v0 with
    | true =>
        rw [Bool.cond_true, Rat.cast_neg]
        have h1 : lam v0 < 0 := hext v0 hev
        nlinarith
    | false =>
        rw [Bool.cond_false]
        exact mul_pos (hcore v0 hm0 hev) hr0'

/-- **Certificate soundness.** A certificate passing `checkPair` for the
ordered pair `(i, k)` refutes joint membership: no point is strictly in
cell `i` and weakly in cell `k`. (No `i ≠ k` hypothesis is needed: a
valid certificate refutes the joint system whatever the indices.) -/
theorem checkPair_sound {i k : Fin C.cells.length} {cert : PairCert C}
    (hc : checkPair C i k cert = true) :
    ∀ x : Fin C.ambDim → ℚ,
      MaskRegionStrict C (C.cells.get i).1 (C.cells.get i).2 x →
      ¬ MaskRegion C (C.cells.get k).1 (C.cells.get k).2 x := by
  intro x hs hw
  unfold checkPair at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hp, hq⟩, hvi⟩, hvk⟩, hgap⟩ := hc
  rw [List.all_eq_true] at hp hq hvi hvk
  have hp' : ∀ v, 0 ≤ cert.p v := fun v =>
    of_decide_eq_true (hp v (List.mem_finRange v))
  have hq' : ∀ v, 0 ≤ cert.q v := fun v =>
    of_decide_eq_true (hq v (List.mem_finRange v))
  -- the strict-side row identities, unfolded
  have hvi' : ∀ v, (C.cells.get i).1 v = true →
      cert.alpha + finSumQ C.ambDim (fun j => cert.gamma j * C.coord v j)
        + (bif (C.cells.get i).2 v then -(cert.p v) else cert.p v) = 0 := by
    intro v hv
    have h := hvi v (List.mem_finRange v)
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [hv] at h
      exact absurd h (by decide)
    · have h' := of_decide_eq_true h
      unfold PairCert.affA at h'
      exact h'
  -- the weak-side row identities, reshaped for the negated functional
  have hvk' : ∀ v, (C.cells.get k).1 v = true →
      cert.beta + finSumQ C.ambDim (fun j => (-(cert.gamma j)) * C.coord v j)
        + (bif (C.cells.get k).2 v then -(cert.q v) else cert.q v) = 0 := by
    intro v hv
    have h := hvk v (List.mem_finRange v)
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [hv] at h
      exact absurd h (by decide)
    · have h' := of_decide_eq_true h
      unfold PairCert.affB at h'
      have hneg : finSumQ C.ambDim (fun j => (-(cert.gamma j)) * C.coord v j)
          = -(finSumQ C.ambDim (fun j => cert.gamma j * C.coord v j)) := by
        rw [finSumQ_eq_sum, finSumQ_eq_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hneg]
      linarith [h']
  -- destructure both memberships
  obtain ⟨lam, hsuppS, hsumS, hcoordS, hextS, hcoreS⟩ := hs
  obtain ⟨mu, hsuppW, hsumW, hcoordW, hextW, hcoreW⟩ := hw
  -- the two side identities
  have EQi := key_eq (C := C) hsuppS hsumS hcoordS
    cert.alpha cert.gamma cert.p hvi'
  have EQk := key_eq (C := C) hsuppW hsumW hcoordW
    cert.beta (fun j => -(cert.gamma j)) cert.q hvk'
  -- the negated-γ sum collapses against the positive one
  have hnegsum : ∑ j, ((-(cert.gamma j) : ℚ) : ℝ) * (x j : ℝ)
      = -(∑ j, ((cert.gamma j : ℚ) : ℝ) * (x j : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [hnegsum] at EQk
  -- tail signs
  have hTi := tail_nonneg hsuppS (fun v hv => le_of_lt (hextS v hv))
    (fun v hm he => le_of_lt (hcoreS v hm he)) cert.p hp'
  have hTk := tail_nonneg hsuppW hextW hcoreW cert.q hq'
  -- the gap condition delivers the contradiction
  rw [Bool.or_eq_true] at hgap
  rcases hgap with hpos | hzero
  · have hδ : (0 : ℚ) < cert.alpha + cert.beta := of_decide_eq_true hpos
    have hδ' : (0 : ℝ) < (cert.alpha : ℝ) + (cert.beta : ℝ) := by
      exact_mod_cast hδ
    linarith [EQi, EQk, hTi, hTk]
  · rw [Bool.and_eq_true] at hzero
    obtain ⟨hz, hany⟩ := hzero
    have hδ : cert.alpha + cert.beta = 0 := of_decide_eq_true hz
    have hδ' : (cert.alpha : ℝ) + (cert.beta : ℝ) = 0 := by exact_mod_cast hδ
    rw [List.any_eq_true] at hany
    obtain ⟨v0, _, hv0⟩ := hany
    rw [Bool.and_eq_true] at hv0
    obtain ⟨hm0, hp0⟩ := hv0
    have hp0' : cert.p v0 ≠ 0 := of_decide_eq_true hp0
    have hTi' := tail_pos hsuppS hextS hcoreS cert.p hp'
      ⟨v0, hm0, lt_of_le_of_ne (hp' v0) (Ne.symm hp0')⟩
    linarith [EQi, EQk, hTi', hTk]

/-- A table of certificates, one per ordered cell pair (total as a
function; diagonal entries are never consulted). -/
def CertTable (C : SimpC) : Type :=
  Fin C.cells.length → Fin C.cells.length → PairCert C

/-- Validity of a whole table: every off-diagonal ordered pair's
certificate passes `checkPair`. -/
def checkTable (C : SimpC) (tbl : CertTable C) : Bool :=
  (List.finRange C.cells.length).all fun i =>
    (List.finRange C.cells.length).all fun k =>
      (i == k) || checkPair C i k (tbl i k)

/-- **The side condition, discharged.** A valid certificate table makes
`SimpC.CellIntDisjoint` — a statement quantifying over real weight
vectors — a consequence of finitely many exact rational identities. -/
theorem checkTable_sound {tbl : CertTable C}
    (h : checkTable C tbl = true) : C.CellIntDisjoint := by
  intro i k hik x hs hw
  unfold checkTable at h
  rw [List.all_eq_true] at h
  have h1 := h i (List.mem_finRange i)
  rw [List.all_eq_true] at h1
  have h2 := h1 k (List.mem_finRange k)
  rw [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · exact absurd (eq_of_beq h2) hik
  · exact checkPair_sound h2 x hs hw

/-- Per-cluster certificate tables for a tensor-simplicial schema. -/
def CertTables (T : CellSchemaTS) : Type :=
  (c : Fin T.m) → CertTable (T.complexes c)

/-- **Additive certificate cost, end to end.** Valid per-cluster tables
discharge the tensor-simplicial exclusion through
`CellSchemaTS.product_exclusion` — certificates are checked in the
small cluster dimensions, never against the exponential product
roster. -/
theorem checkTables_ts_sound {T : CellSchemaTS} {tbls : CertTables T}
    (h : ∀ c, checkTable (T.complexes c) (tbls c) = true) :
    T.CellIntDisjoint :=
  T.product_exclusion fun c => checkTable_sound (h c)

#print axioms checkPair_sound
#print axioms checkTable_sound

end CellFarkas
end PPLC
