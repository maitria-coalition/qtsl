import Qtsl.Catalogue

/-!
# Rename transport of `SemOk`

A *rename* is a wire map `f : Wire → Wire` applied to every wire field
of a primitive application, payloads untouched. This module proves the
semantic transport theorem: against a **type-exact** rename — one with
`H'.wireType (f w) = H.wireType w` for every wire, full equality of
`Option`s — an application's semantic clause holds at the renamed
hypernet iff it holds at the original under the pulled-back valuation.

Contents:

* `PrimApp.rename` and its `inputWires`/`outputWires` laws;
* `Hypernet.Valuation.pull` — precomposition of a valuation with a
  type-exact rename — and the transport of the three read interfaces
  (`entryFlat_pull`, `entryAt_pull`, `wireQ_pull`); the none-branches
  consume the `←` direction of type-exactness, which is why the
  hypothesis is an equality of `Option`s and not mere
  `some`-preservation;
* `contractExact_pull` — the one read whose transport needs a typing
  hypothesis: `contractExact` addresses its inputs by `List.getD`, so
  the in-range/out-of-range boundary must agree on both sides, which is
  exactly the arity clause of `TypeConsistent`'s contract case;
* `PrimApp.SemOk_rename` — the fourteen-case transport theorem;
* `admissible_map_rename` — the list-level corollary (the
  restriction-congruence engine for open-hypernet composition).

No injectivity and no retraction appear anywhere: a type-exact rename
transports `SemOk` outright. This module discharges the rename-transport
successor named in `Qtsl.HypernetCospan`'s header.
-/

namespace PPLC

/-! ## Renaming applications -/

/-- Rename every wire of a primitive application along `f`; payload
fields (types, values, shapes, patterns, tables) are untouched. -/
def PrimApp.rename (f : Wire → Wire) : PrimApp → PrimApp
  | .const ty c out => .const ty c (f out)
  | .contract δ r inputs output inputRanks outputRank pat =>
      .contract δ r (inputs.map f) (f output) inputRanks outputRank pat
  | .cast δfrom δto r shape input output =>
      .cast δfrom δto r shape (f input) (f output)
  | .cell schema input outputs => .cell schema (f input) (outputs.map f)
  | .reshape newShape input output => .reshape newShape (f input) (f output)
  | .broadcast toShape input output => .broadcast toShape (f input) (f output)
  | .copy k input outputs => .copy k (f input) (outputs.map f)
  | .delete input => .delete (f input)
  | .swap in1 in2 out1 out2 => .swap (f in1) (f in2) (f out1) (f out2)
  | .stack k shape inputs output => .stack k shape (inputs.map f) (f output)
  | .relu shape input output => .relu shape (f input) (f output)
  | .ppoly nvars coeffs inputs output =>
      .ppoly nvars coeffs (inputs.map f) (f output)
  | .pderiv shape axis input output => .pderiv shape axis (f input) (f output)
  | .facet shape axis hi input output =>
      .facet shape axis hi (f input) (f output)

theorem PrimApp.rename_inputWires (f : Wire → Wire) (a : PrimApp) :
    (a.rename f).inputWires = a.inputWires.map f := by
  cases a <;> simp [rename, inputWires]

theorem PrimApp.rename_outputWires (f : Wire → Wire) (a : PrimApp) :
    (a.rename f).outputWires = a.outputWires.map f := by
  cases a <;> simp [rename, outputWires]

/-! ## Pulling valuations back along a type-exact rename -/

namespace Hypernet.Valuation

/-- Pull a valuation on `H'` back to `H` along a type-exact rename:
read the renamed wire. -/
def pull {H H' : Hypernet} (f : Wire → Wire)
    (hty : ∀ w, H'.wireType (f w) = H.wireType w)
    (σ' : H'.Valuation) : H.Valuation :=
  fun w τ hw => σ' (f w) τ ((hty w).trans hw)

/-! ### Case equations for the read interfaces

`entryFlat`, `entryAt`, and `wireQ` are dependent matches on
`h : H.wireType w`; these equations are the non-dependent interface the
transport lemmas rewrite with (re-unfolding the matches downstream
would re-open the dependent-motive fight each time). -/

theorem entryFlat_none {H : Hypernet} (σ : H.Valuation) {w : Wire}
    (hw : H.wireType w = none) (i : ℕ) : σ.entryFlat w i = none := by
  unfold entryFlat
  split
  · rfl
  · next τ h => simp [hw] at h

theorem entryFlat_some {H : Hypernet} (σ : H.Valuation) {w : Wire}
    {τ : TensorType} (hw : H.wireType w = some τ) (i : ℕ) :
    σ.entryFlat w i = (σ w τ hw).entryE i := by
  unfold entryFlat
  split
  · next h => simp [hw] at h
  · next τ' h =>
      obtain rfl : τ' = τ := Option.some.inj (h.symm.trans hw)
      rfl

theorem entryAt_none {H : Hypernet} (σ : H.Valuation) {w : Wire}
    (hw : H.wireType w = none) (c : List ℕ) : σ.entryAt w c = none := by
  unfold entryAt
  split
  · rfl
  · next τ h => simp [hw] at h

theorem entryAt_some {H : Hypernet} (σ : H.Valuation) {w : Wire}
    {τ : TensorType} (hw : H.wireType w = some τ) (c : List ℕ) :
    σ.entryAt w c
      = (Shape.flatten τ.shape c).bind fun i => (σ w τ hw).entryE i := by
  unfold entryAt
  split
  · next h => simp [hw] at h
  · next τ' h =>
      obtain rfl : τ' = τ := Option.some.inj (h.symm.trans hw)
      rfl

theorem wireQ_none {H : Hypernet} (σ : H.Valuation) {w : Wire}
    (hw : H.wireType w = none) : σ.wireQ w = none := by
  unfold wireQ
  split
  · rfl
  · next τ h => simp [hw] at h

theorem wireQ_some {H : Hypernet} (σ : H.Valuation) {w : Wire}
    {τ : TensorType} (hw : H.wireType w = some τ) :
    σ.wireQ w
      = match hf : ERat.allFinQ ((σ w τ hw).val.map Subtype.val) with
        | none => none
        | some l => some ⟨τ.shape, l, by
            have h1 := ERat.allFinQ_length _ _ hf
            rw [List.length_map] at h1
            exact h1.trans (σ w τ hw).property⟩ := by
  unfold wireQ
  split
  · next h => simp [hw] at h
  · next τ' h =>
      obtain rfl : τ' = τ := Option.some.inj (h.symm.trans hw)
      rfl

/-! ### The transport lemmas

The `none` branches consume the `←` direction of type-exactness: from
`H.wireType w = none` they need `H'.wireType (f w) = none`, which mere
`some`-preservation cannot supply. -/

theorem entryFlat_pull {H H' : Hypernet} (f : Wire → Wire)
    (hty : ∀ w, H'.wireType (f w) = H.wireType w) (σ' : H'.Valuation)
    (w : Wire) (i : ℕ) :
    (σ'.pull f hty).entryFlat w i = σ'.entryFlat (f w) i := by
  cases hw : H.wireType w with
  | none => rw [entryFlat_none _ hw, entryFlat_none _ ((hty w).trans hw)]
  | some τ =>
      rw [entryFlat_some _ hw, entryFlat_some _ ((hty w).trans hw)]
      rfl

theorem entryAt_pull {H H' : Hypernet} (f : Wire → Wire)
    (hty : ∀ w, H'.wireType (f w) = H.wireType w) (σ' : H'.Valuation)
    (w : Wire) (c : List ℕ) :
    (σ'.pull f hty).entryAt w c = σ'.entryAt (f w) c := by
  cases hw : H.wireType w with
  | none => rw [entryAt_none _ hw, entryAt_none _ ((hty w).trans hw)]
  | some τ =>
      rw [entryAt_some _ hw, entryAt_some _ ((hty w).trans hw)]
      rfl

theorem wireQ_pull {H H' : Hypernet} (f : Wire → Wire)
    (hty : ∀ w, H'.wireType (f w) = H.wireType w) (σ' : H'.Valuation)
    (w : Wire) :
    (σ'.pull f hty).wireQ w = σ'.wireQ (f w) := by
  cases hw : H.wireType w with
  | none => rw [wireQ_none _ hw, wireQ_none _ ((hty w).trans hw)]
  | some τ =>
      rw [wireQ_some _ hw, wireQ_some _ ((hty w).trans hw)]
      rfl

end Hypernet.Valuation

/-- Transport of the exact contraction read. This is the one read whose
transport needs a typing fact: `contractExact` addresses its inputs by
`List.getD k.val 0`, and the index range is `Fin inputRanks.length` —
so the arity clause `inputs.length = inputRanks.length` is exactly what
keeps every read in range on both sides (out of range, the two sides
would read wire `0` and wire `f 0` respectively). -/
theorem contractExact_pull {H H' : Hypernet} (f : Wire → Wire)
    (hty : ∀ w, H'.wireType (f w) = H.wireType w) (σ' : H'.Valuation)
    (inputs : List Wire) {inputRanks : List Nat} {outputRank : Nat}
    (pat : ContractPattern inputRanks outputRank)
    (hlen : inputs.length = inputRanks.length) (t : List ℕ) :
    contractExact (σ'.pull f hty) inputs pat t
      = contractExact σ' (inputs.map f) pat t := by
  have hpt : ∀ (ν : List ℕ) (k : Fin inputRanks.length),
      (σ'.pull f hty).entryAt (inputs.getD k.val 0) (pat.inCoords ν k)
        = σ'.entryAt ((inputs.map f).getD k.val 0) (pat.inCoords ν k) := by
    intro ν k
    have hk : k.val < inputs.length := lt_of_lt_of_eq k.isLt hlen.symm
    have hwire : (inputs.map f).getD k.val 0 = f (inputs.getD k.val 0) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_getElem hk]
    rw [Hypernet.Valuation.entryAt_pull, hwire]
  unfold contractExact
  simp only [hpt]

/-- **Rename transport of `SemOk`.** Against a type-exact rename, the
semantic clause of the renamed application at `σ'` is equivalent to the
clause of the original at the pulled-back valuation. Exactly one of the
fourteen cases consumes the typing hypothesis: `contract`, through its
arity clause (see `contractExact_pull`); `broadcast` additionally
transports its `wireType` read by type-exactness alone. -/
theorem PrimApp.SemOk_rename {H H' : Hypernet} (f : Wire → Wire)
    (hty : ∀ w, H'.wireType (f w) = H.wireType w) (σ' : H'.Valuation)
    (a : PrimApp) (hTC : a.TypeConsistent H.wireType) :
    (a.rename f).SemOk σ' ↔ a.SemOk (σ'.pull f hty) := by
  cases a with
  | const ty c out =>
      simp only [rename, SemOk, Hypernet.Valuation.entryFlat_pull]
  | contract δ r inputs output inputRanks outputRank pat =>
      simp only [rename, SemOk, Hypernet.Valuation.entryAt_pull,
        contractExact_pull f hty σ' inputs pat hTC.1]
  | cast δfrom δto r shape input output =>
      simp only [rename, SemOk, Hypernet.Valuation.entryFlat_pull]
  | cell schema input outputs =>
      simp only [rename, SemOk, Hypernet.Valuation.entryFlat_pull,
        Hypernet.Valuation.entryAt_pull, List.get_eq_getElem,
        List.getElem_map]
      -- residue: the output-indicator quantifier's `Fin` domain
      -- (`(outputs.map f).length` vs `outputs.length`) — simp does not
      -- rewrite binder domains; transport the index by `Fin.cast`.
      refine and_congr_right fun _ => exists_congr fun x =>
        and_congr_right fun _ => exists_congr fun k =>
        and_congr_right fun _ =>
        ⟨fun hsem j => hsem (Fin.cast (by simp) j),
         fun hsem j => hsem (Fin.cast (by simp) j)⟩
  | reshape newShape input output =>
      simp only [rename, SemOk, Hypernet.Valuation.entryFlat_pull]
  | broadcast toShape input output =>
      simp only [rename, SemOk, Hypernet.Valuation.entryAt_pull, hty]
  | copy k input outputs =>
      simp only [rename, SemOk, Hypernet.Valuation.entryFlat_pull,
        List.forall_mem_map]
  | delete input =>
      simp only [rename, SemOk]
  | swap in1 in2 out1 out2 =>
      simp only [rename, SemOk, Hypernet.Valuation.entryFlat_pull]
  | stack k shape inputs output =>
      simp only [rename, SemOk, Hypernet.Valuation.entryFlat_pull,
        Fin.getElem_fin, List.getElem_map]
      exact ⟨fun hsem i j => hsem (Fin.cast (by simp) i) j,
             fun hsem i j => hsem (Fin.cast (by simp) i) j⟩
  | relu shape input output =>
      simp only [rename, SemOk, Hypernet.Valuation.entryFlat_pull]
  | ppoly nvars coeffs inputs output =>
      simp only [rename, SemOk, Hypernet.Valuation.entryFlat_pull,
        List.length_map, List.getElem_map]
  | pderiv shape axis input output =>
      simp only [rename, SemOk, Hypernet.Valuation.wireQ_pull]
  | facet shape axis hi input output =>
      simp only [rename, SemOk, Hypernet.Valuation.wireQ_pull]

/-- List-level corollary: a renamed application list is pointwise
`SemOk` at `σ'` iff the original list is pointwise `SemOk` at the
pulled-back valuation — the restriction-congruence engine. -/
theorem admissible_map_rename {H H' : Hypernet} (f : Wire → Wire)
    (hty : ∀ w, H'.wireType (f w) = H.wireType w) (σ' : H'.Valuation)
    (T : List PrimApp) (hTC : ∀ a ∈ T, a.TypeConsistent H.wireType) :
    (∀ a ∈ T.map (·.rename f), a.SemOk σ')
      ↔ (∀ a ∈ T, a.SemOk (σ'.pull f hty)) := by
  simp only [List.forall_mem_map]
  exact forall₂_congr fun a ha => PrimApp.SemOk_rename f hty σ' a (hTC a ha)

/-! ## Axiom receipts (in-package convention: `#print axioms`) -/

#print axioms PrimApp.rename_inputWires
#print axioms PrimApp.rename_outputWires
#print axioms Hypernet.Valuation.entryFlat_pull
#print axioms Hypernet.Valuation.entryAt_pull
#print axioms Hypernet.Valuation.wireQ_pull
#print axioms contractExact_pull
#print axioms PrimApp.SemOk_rename
#print axioms admissible_map_rename

end PPLC
