import Qtsl.PrimitiveBasisSoundWF

/-!
# Soundness of the primitive basis: the conclusion repair

`PrimitiveBasisSoundWF` repaired the falsified landed statement by
adding hypotheses (`OutputsConnected`, `SaturatingContracts`).  This
module carries the deeper repair — the ruled direction: the gaps were
never defects of the *hypernets*, they were defects of the *conclusion*
and of one clause of the landed semantics, so the repairs move there:

* **G1 (disconnected output wires)** SHOULD be unconstrained: the
  completion statement's target class closes under free cylinders —
  unread wires denote freedom.  `IsPiecewisePolyRelCyl` is the closed
  class; the G1 falsification exhibit (`freeOutH`) flips from
  counterexample to positive instance (`freeOutH_soundX`).
* **G2 (non-injective `outputBinding`)** has implicit-`copy` semantics:
  repeated output coordinates contribute DIAGONAL equations.  The
  re-voiced contract clause (`PrimApp.SemOkX`) quantifies over *all*
  output positions through `contractExact`, whose empty fibers pin the
  off-diagonal entries to `0` (`diag_semOkX_offDiag`).
* **G3 (zero-extent summed indices)**: the empty sum denotes the ZERO
  polynomial.  Under `SemOkX` this is a theorem about `0`
  (`zero_semOkX_pins`), where the landed clause was vacuous for every
  valuation (`zero_semOk_vacuous`).

G2 also has an **interface twin**, found at prereg time: repeated
*disconnected* output wires (`outs j = outs j'`) force the diagonal
equation `y j = y j'` with no polynomial pinning either coordinate, so
a per-coordinate Bool mask cannot express the denotation.  The class
therefore carries **shared free generators**: a mask
`fr : Fin m → Option (Fin k)`; masked coordinates read a generator
(shared exactly when the wire is shared), unmasked coordinates read the
piece polynomial.

The re-voicing of the landed `SemOk .contract` itself is
certificate-vocabulary change and stays bake-sequenced; everything here
proves against the LOCAL `SemOkX`, with the bridge kept honest in both
directions: `SemOkX → SemOk` holds *unconditionally* (the re-voicing
only pins more), and the converse holds exactly on the saturated
fragment — so `DenotRelX ⊆ DenotRel` always, with equality under
`SaturatingContracts`, and the interim `PrimitiveBasisSoundWF` becomes
a corollary (`primitiveBasisSoundWF_of_conclusionRepair`).

The headline, hypothesis-set identical to the landed (falsified)
statement: `primitiveBasisSoundX` — every exact-⟨B,Q⟩ ten-box hypernet
with a closed scalar-rational interface has `DenotRelX` a finite union
of polynomial cylinder-graphs over basic closed pieces.  The σ-free
symbolic machinery (`symStep`, `symFold`, `pieceOf`, `hypernetPieces`,
`step_lens`, `step_memK`, `fold_wf`) is consumed unchanged; only the
σ-facing contract seams and the interface resolution fork.
-/

namespace PPLC

open MvPolynomial

variable {d : ℕ}

/-! ## The re-voiced semantics, local to this module -/

/-- The landed `SemOk` with one clause re-voiced: `contract` pins the
output at EVERY position of its output shape through `contractExact`.
Off the image of `outCoords` the assignment fiber is empty and
`contractExact` returns the empty sum `0` — G2's off-diagonal zeros and
G3's zero-extent output are both instances of the same pinning.  Every
other box keeps the landed semantics verbatim (definitionally). -/
def PrimApp.SemOkX {H : Hypernet} (σ : H.Valuation) : PrimApp → Prop
  | .contract δ r inputs output _ir _orank pat =>
      ∀ t ∈ Shape.positions pat.outShape,
        ∃ eOut eExact,
          σ.entryAt output t = some eOut ∧
          contractExact σ inputs pat t = some eExact ∧
          δ.RoundOkE r eExact eOut
  | app => app.SemOk σ

/-- The re-voicing only adds pinning: `SemOkX → SemOk`, with NO
saturation hypothesis (image positions are positions,
`outCoords_mem_positions`). -/
theorem PrimApp.semOk_of_semOkX {H : Hypernet} {σ : H.Valuation} :
    ∀ {app : PrimApp}, app.SemOkX σ → app.SemOk σ
  | .const .., h => h
  | .contract _δ _r _inputs _output _ir _orank pat, h => fun _ν₀ hν₀ =>
      h _ (outCoords_mem_positions pat hν₀)
  | .cast .., h => h
  | .cell .., h => h
  | .reshape .., h => h
  | .broadcast .., h => h
  | .copy .., h => h
  | .delete .., h => h
  | .swap .., h => h
  | .stack .., h => h
  | .relu .., h => h
  | .ppoly .., h => h
  | .pderiv .., h => h
  | .facet .., h => h

/-- On the saturated fragment the re-voicing is conservative:
`SemOk → SemOkX` under `saturating`. -/
theorem PrimApp.semOkX_of_semOk {H : Hypernet} {σ : H.Valuation} :
    ∀ {app : PrimApp}, app.SemOk σ → app.saturating → app.SemOkX σ
  | .const .., h, _ => h
  | .contract _δ _r _inputs _output _ir _orank _pat, h, hsat => by
      intro t ht
      obtain ⟨ν₀, hν₀, hout⟩ := hsat t ht
      obtain ⟨eOut, eExact, h1, h2, h3⟩ := h ν₀ hν₀
      rw [hout] at h1 h2
      exact ⟨eOut, eExact, h1, h2, h3⟩
  | .cast .., h, _ => h
  | .cell .., h, _ => h
  | .reshape .., h, _ => h
  | .broadcast .., h, _ => h
  | .copy .., h, _ => h
  | .delete .., h, _ => h
  | .swap .., h, _ => h
  | .stack .., h, _ => h
  | .relu .., h, _ => h
  | .ppoly .., h, _ => h
  | .pderiv .., h, _ => h
  | .facet .., h, _ => h

/-- Admissibility under the re-voiced semantics. -/
def Hypernet.Valuation.AdmissibleX {H : Hypernet} (σ : H.Valuation) : Prop :=
  ∀ app ∈ H.applications, app.SemOkX σ

theorem Hypernet.Valuation.admissible_of_admissibleX {H : Hypernet}
    {σ : H.Valuation} (h : σ.AdmissibleX) : σ.Admissible :=
  fun app happ => PrimApp.semOk_of_semOkX (h app happ)

theorem Hypernet.Valuation.admissibleX_of_admissible {H : Hypernet}
    {σ : H.Valuation} (h : σ.Admissible) (hsat : H.SaturatingContracts) :
    σ.AdmissibleX :=
  fun app happ => PrimApp.semOkX_of_semOk (h app happ) (hsat app happ)

/-- The interface denotation under the re-voiced semantics. -/
def Hypernet.DenotRelX (H : Hypernet) (d m : ℕ)
    (ins : Fin d → Wire) (outs : Fin m → Wire) :
    Set ((Fin d → ℚ) × (Fin m → ℚ)) :=
  { xy | ∃ σ : H.Valuation, σ.AdmissibleX ∧
      (∀ i, σ.entryFlat (ins i) 0 = some (.fin (xy.1 i))) ∧
      (∀ j, σ.entryFlat (outs j) 0 = some (.fin (xy.2 j))) }

/-- The re-voicing only shrinks denotations. -/
theorem Hypernet.denotRelX_subset (H : Hypernet) {d m : ℕ}
    (ins : Fin d → Wire) (outs : Fin m → Wire) :
    H.DenotRelX d m ins outs ⊆ H.DenotRel d m ins outs := by
  rintro xy ⟨σ, hadm, hin, hout⟩
  exact ⟨σ, Hypernet.Valuation.admissible_of_admissibleX hadm, hin, hout⟩

/-- On the saturated fragment the re-voicing changes nothing: the
bridge that keeps the chain honest. -/
theorem Hypernet.denotRelX_eq_of_saturating (H : Hypernet) {d m : ℕ}
    (hsat : H.SaturatingContracts)
    (ins : Fin d → Wire) (outs : Fin m → Wire) :
    H.DenotRelX d m ins outs = H.DenotRel d m ins outs := by
  refine Set.Subset.antisymm (H.denotRelX_subset ins outs) ?_
  rintro xy ⟨σ, hadm, hin, hout⟩
  exact ⟨σ, Hypernet.Valuation.admissibleX_of_admissible hadm hsat,
    hin, hout⟩

/-! ## The `contract` σ-lemmas, saturation-free -/

/-- `contract_semOk_reads` with the saturation step deleted: the
re-voiced clause applies at each target directly. -/
theorem contract_semOkX_reads {H : Hypernet} {σ : H.Valuation}
    {x : Fin d → ℚ} {δ : Dtype} {inputs : List Wire} {output : Wire}
    {inputRanks : List ℕ} {outputRank : ℕ}
    {pat : ContractPattern inputRanks outputRank}
    (hsem : (PrimApp.contract δ .exact inputs output
      inputRanks outputRank pat).SemOkX σ)
    (hto : H.wireType output = some ⟨pat.outShape, δ⟩)
    {shapes : List Shape} {tabs : List (PTab d)}
    (hlen₁ : inputs.length = inputRanks.length)
    (hlen₂ : shapes.length = inputs.length)
    (hlen₃ : tabs.length = inputs.length)
    (hty : ∀ (kk : ℕ) (hk : kk < inputs.length), ∃ δk,
      H.wireType (inputs[kk]'hk) = some ⟨shapes[kk]'(by omega), δk⟩)
    (htablen : ∀ (kk : ℕ) (hk : kk < tabs.length),
      (tabs[kk]'hk).length = (shapes[kk]'(by omega)).totalSize)
    (hreads : ∀ (kk : ℕ) (hk : kk < inputs.length),
      readsTab σ x (inputs[kk]'hk) (tabs[kk]'(by omega)))
    (hrank : ∀ k : Fin inputRanks.length,
      (shapes.getD k.val []).length = inputRanks.get k)
    (hextent : ∀ (k : Fin inputRanks.length) (a : Fin (inputRanks.get k)),
      (shapes.getD k.val []).getD a.val 0
        = pat.indexExtent (pat.inputBinding k a)) :
    readsTab σ x output (contractTab pat shapes tabs)
    ∧ (δ = Dtype.B → ∀ p ∈ contractTab pat shapes tabs,
        MvPolynomial.eval x p = 0 ∨ MvPolynomial.eval x p = 1) := by
  have hex := contractExact_eval σ x pat hlen₁ hlen₂ hlen₃ hty htablen
    hreads hrank hextent
  have hsem' : ∀ t ∈ Shape.positions pat.outShape,
      ∃ eOut eExact,
        σ.entryAt output t = some eOut ∧
        contractExact σ inputs pat t = some eExact ∧
        δ.RoundOkE .exact eExact eOut := hsem
  have hpt : ∀ (n : ℕ) (hn : n < (contractTab pat shapes tabs).length),
      σ.entryFlat output n = some (.fin (MvPolynomial.eval x
        ((contractTab pat shapes tabs)[n]'hn)))
      ∧ δ.ValueSet (.fin (MvPolynomial.eval x
        ((contractTab pat shapes tabs)[n]'hn))) := by
    intro n hn
    have hn' : n < pat.outShape.totalSize := by
      rw [← contractTab_length (pat := pat) (shapes := shapes)
        (tabs := tabs)]
      exact hn
    have hnp : n < (Shape.positions pat.outShape).length := by
      rw [Shape.length_positions]
      exact hn'
    have htmem : (Shape.positions pat.outShape)[n]'hnp
        ∈ Shape.positions pat.outShape := List.getElem_mem hnp
    obtain ⟨eOut, eExact, hread_out, hex', hro⟩ := hsem' _ htmem
    rw [hex _] at hex'
    obtain rfl := Option.some.inj hex'
    obtain ⟨rfl, hvs⟩ := hro
    have hflat := Shape.flatten_positions_getElem pat.outShape n hn'
    rw [entryAt_eq_bind' σ hto rfl, hflat] at hread_out
    replace hread_out : σ.entryFlat output n
        = some (.fin (MvPolynomial.eval x (contractPolyAt pat shapes tabs
            ((Shape.positions pat.outShape)[n]'hnp)))) := hread_out
    have hgot : (contractTab pat shapes tabs)[n]'hn
        = contractPolyAt pat shapes tabs
            ((Shape.positions pat.outShape)[n]'hnp) := by
      show ((Shape.positions pat.outShape).map
        (contractPolyAt pat shapes tabs))[n]'(by
          rw [List.length_map]; exact hnp) = _
      rw [List.getElem_map]
    rw [hgot]
    exact ⟨hread_out, hvs⟩
  refine ⟨readsTab_of_reads hto (by
    rw [contractTab_length]) (fun n hn => (hpt n hn).1), ?_⟩
  rintro rfl p hp
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hp
  exact valueSet_B_iff.mp (hpt n hn).2

/-- `contract_semOk_build` strengthened to the re-voiced clause: the
symbolic table pins every position, so the constructed valuation
satisfies `SemOkX` — the target is arbitrary, no saturation needed. -/
theorem contract_semOkX_build {H : Hypernet} {σ : H.Valuation}
    {x : Fin d → ℚ} {δ : Dtype} {inputs : List Wire} {output : Wire}
    {inputRanks : List ℕ} {outputRank : ℕ}
    {pat : ContractPattern inputRanks outputRank}
    (hbq : δ.isBQ = true)
    (hto : H.wireType output = some ⟨pat.outShape, δ⟩)
    {shapes : List Shape} {tabs : List (PTab d)}
    (hlen₁ : inputs.length = inputRanks.length)
    (hlen₂ : shapes.length = inputs.length)
    (hlen₃ : tabs.length = inputs.length)
    (hty : ∀ (kk : ℕ) (hk : kk < inputs.length), ∃ δk,
      H.wireType (inputs[kk]'hk) = some ⟨shapes[kk]'(by omega), δk⟩)
    (htablen : ∀ (kk : ℕ) (hk : kk < tabs.length),
      (tabs[kk]'hk).length = (shapes[kk]'(by omega)).totalSize)
    (hreads : ∀ (kk : ℕ) (hk : kk < inputs.length),
      readsTab σ x (inputs[kk]'hk) (tabs[kk]'(by omega)))
    (hrank : ∀ k : Fin inputRanks.length,
      (shapes.getD k.val []).length = inputRanks.get k)
    (hextent : ∀ (k : Fin inputRanks.length) (a : Fin (inputRanks.get k)),
      (shapes.getD k.val []).getD a.val 0
        = pat.indexExtent (pat.inputBinding k a))
    (hread_out : readsTab σ x output (contractTab pat shapes tabs))
    (hbool : δ = Dtype.B → ∀ p ∈ contractTab pat shapes tabs,
      MvPolynomial.eval x p = 0 ∨ MvPolynomial.eval x p = 1) :
    (PrimApp.contract δ .exact inputs output
      inputRanks outputRank pat).SemOkX σ := by
  intro t ht
  have hex := contractExact_eval σ x pat hlen₁ hlen₂ hlen₃ hty htablen
    hreads hrank hextent
  have hsome := Shape.flatten_isSome_iff.mpr (Shape.mem_positions.mp ht)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hn' : n < pat.outShape.totalSize := Shape.flatten_lt hn
  obtain ⟨hnp, htget⟩ := Shape.eq_getElem_positions_of_flatten hn
  have hnc : n < (contractTab pat shapes tabs).length := by
    rw [contractTab_length]
    exact hn'
  have hval : (contractTab pat shapes tabs)[n]'hnc
      = contractPolyAt pat shapes tabs t := by
    show ((Shape.positions pat.outShape).map
      (contractPolyAt pat shapes tabs))[n]'(by
        rw [List.length_map]; exact hnp) = _
    rw [List.getElem_map, ← htget]
  refine ⟨.fin (MvPolynomial.eval x (contractPolyAt pat shapes tabs t)),
    .fin (MvPolynomial.eval x (contractPolyAt pat shapes tabs t)),
    ?_, hex _, ?_⟩
  · rw [entryAt_eq_bind' σ hto rfl, hn]
    show σ.entryFlat output n = _
    rw [hread_out.read hnc, hval]
  · exact roundOkExactBQ (Dtype.isBQ_cases hbq)
      (fun hB => by
        rw [← hval]
        exact hbool hB _ (List.getElem_mem hnc))

/-! ## Forward and backward plumbing under `SemOkX`

Only the `contract` case forks; every other case delegates to the
landed lemma (`SemOkX` is definitionally `SemOk` off-`contract`, and
`saturating` is definitionally `True` there). -/

/-- `step_mp` under the re-voiced semantics, saturation-free. -/
theorem step_mpX {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {app : PrimApp} (hsem : app.SemOkX σ)
    (htc : app.TypeConsistent H.wireType)
    (htb : app.isTenBox = true) (hbqa : app.exactBQ = true)
    (st : SymSt d)
    (hreads : ∀ w tab, st.val w = some tab → readsTab σ x w tab)
    (hlens : ∀ w tab, st.val w = some tab →
      ∃ τ, H.wireType w = some τ ∧ tab.length = τ.shape.totalSize)
    (hcons : ∀ w ∈ app.inputWires, (st.val w).isSome) :
    ∃ c ∈ appChoices app,
      (∀ w tab, (symStep H.wireType st app c).val w = some tab →
        readsTab σ x w tab) ∧
      (∀ w tab, (symStep H.wireType st app c).val w = some tab →
        ∃ τ, H.wireType w = some τ ∧ tab.length = τ.shape.totalSize) ∧
      (CondsHold x st.conds →
        CondsHold x (symStep H.wireType st app c).conds) := by
  cases app with
  | contract δ r inputs output ir orank pat =>
      have hres : ∀ w ∈ (PrimApp.contract δ r inputs output ir orank
          pat).inputWires, ∃ tab, st.val w = some tab ∧
          readsTab σ x w tab ∧ ∃ τ, H.wireType w = some τ ∧
          tab.length = τ.shape.totalSize := by
        intro w hw
        obtain ⟨tab, htab⟩ := Option.isSome_iff_exists.mp (hcons w hw)
        exact ⟨tab, htab, hreads w tab htab, hlens w tab htab⟩
      have hbqa' : δ.isBQ = true ∧ r.isExact = true := by
        simpa [PrimApp.exactBQ] using hbqa
      obtain ⟨hbq, hexact⟩ := hbqa'
      obtain rfl := RoundMode.isExact_eq hexact
      have hto := contract_output_ty htc
      have hlen₁ : inputs.length = ir.length := htc.1
      have hlen₂ : (inputs.map (wireShapeOf H.wireType)).length
          = inputs.length := List.length_map ..
      have hlen₃ : (inputs.map fun w => (st.val w).getD []).length
          = inputs.length := List.length_map ..
      have hty : ∀ (kk : ℕ) (hk : kk < inputs.length), ∃ δk,
          H.wireType (inputs[kk]'hk) = some
            ⟨(inputs.map (wireShapeOf H.wireType))[kk]'(by omega), δk⟩ := by
        intro kk hk
        refine ⟨δ, ?_⟩
        rw [show (inputs.map (wireShapeOf H.wireType))[kk]'(by omega)
          = wireShapeOf H.wireType (inputs[kk]'hk) from List.getElem_map ..]
        exact contract_input_ty htc hk
      have htabres : ∀ (kk : ℕ) (hk : kk < inputs.length),
          st.val (inputs[kk]'hk)
            = some ((inputs.map fun w => (st.val w).getD [])[kk]'(by omega))
          ∧ ((inputs.map fun w => (st.val w).getD [])[kk]'(by omega)).length
            = ((inputs.map (wireShapeOf H.wireType))[kk]'(by omega)).totalSize := by
        intro kk hk
        obtain ⟨tab, htab, -, τ, hτ, htlen⟩ :=
          hres _ (List.getElem_mem hk)
        have hget : (inputs.map fun w => (st.val w).getD [])[kk]'(by omega)
            = tab := by
          rw [show (inputs.map fun w => (st.val w).getD [])[kk]'(by omega)
            = (st.val (inputs[kk]'hk)).getD [] from List.getElem_map ..,
            htab]
          rfl
        have hshape : (inputs.map (wireShapeOf H.wireType))[kk]'(by omega)
            = τ.shape := by
          rw [show (inputs.map (wireShapeOf H.wireType))[kk]'(by omega)
            = wireShapeOf H.wireType (inputs[kk]'hk) from
              List.getElem_map .., wireShapeOf_some hτ]
        rw [hget, hshape]
        exact ⟨htab, htlen⟩
      have htablen : ∀ (kk : ℕ)
          (hk : kk < (inputs.map fun w => (st.val w).getD []).length),
          ((inputs.map fun w => (st.val w).getD [])[kk]'hk).length
            = ((inputs.map (wireShapeOf H.wireType))[kk]'(by omega)).totalSize :=
        fun kk hk => (htabres kk (by omega)).2
      have hreads' : ∀ (kk : ℕ) (hk : kk < inputs.length),
          readsTab σ x (inputs[kk]'hk)
            ((inputs.map fun w => (st.val w).getD [])[kk]'(by omega)) :=
        fun kk hk => hreads _ _ (htabres kk hk).1
      have hcr := contract_semOkX_reads hsem hto hlen₁ hlen₂ hlen₃
        hty htablen hreads' (contract_input_rank htc)
        (contract_input_extent htc)
      refine ⟨0, List.mem_cons_self .., ?_, ?_, ?_⟩
      · intro w tab htab
        rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
        · have hj0 : j = 0 := by simpa using hj
          subst hj0
          have hwout : w = output := by simpa using hwj
          subst hwout
          exact hcr.1
        · exact hreads w tab hbase
      · intro w tab htab
        rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
        · have hj0 : j = 0 := by simpa using hj
          subst hj0
          have hwout : w = output := by simpa using hwj
          subst hwout
          exact ⟨⟨pat.outShape, δ⟩, hto, contractTab_length⟩
        · exact hlens w tab hbase
      · intro hch
        refine CondsHold.append.mpr ⟨hch, ?_⟩
        split
        · next hB =>
            subst hB
            exact condsHold_boolConds_iff.mpr (hcr.2 rfl)
        · intro q hq
          exact absurd hq List.not_mem_nil
  | const ty cv out =>
      exact step_mp (PrimApp.semOk_of_semOkX hsem) htc htb hbqa trivial
        st hreads hlens hcons
  | cast δfrom δto r shape input output =>
      exact step_mp (PrimApp.semOk_of_semOkX hsem) htc htb hbqa trivial
        st hreads hlens hcons
  | cell schema input outputs =>
      exact step_mp (PrimApp.semOk_of_semOkX hsem) htc htb hbqa trivial
        st hreads hlens hcons
  | reshape newShape input output =>
      exact step_mp (PrimApp.semOk_of_semOkX hsem) htc htb hbqa trivial
        st hreads hlens hcons
  | broadcast toShape input output =>
      exact step_mp (PrimApp.semOk_of_semOkX hsem) htc htb hbqa trivial
        st hreads hlens hcons
  | copy kk input outputs =>
      exact step_mp (PrimApp.semOk_of_semOkX hsem) htc htb hbqa trivial
        st hreads hlens hcons
  | delete input =>
      exact step_mp (PrimApp.semOk_of_semOkX hsem) htc htb hbqa trivial
        st hreads hlens hcons
  | swap in1 in2 out1 out2 =>
      exact step_mp (PrimApp.semOk_of_semOkX hsem) htc htb hbqa trivial
        st hreads hlens hcons
  | stack kk shape inputs output =>
      exact step_mp (PrimApp.semOk_of_semOkX hsem) htc htb hbqa trivial
        st hreads hlens hcons
  | relu shape input output => exact absurd htb (by simp [PrimApp.isTenBox])
  | ppoly nv co inputs output =>
      exact absurd htb (by simp [PrimApp.isTenBox])
  | pderiv shape ax input output =>
      exact absurd htb (by simp [PrimApp.isTenBox])
  | facet shape ax hi input output =>
      exact absurd htb (by simp [PrimApp.isTenBox])

/-- The forward fold under the re-voiced semantics: an
`AdmissibleX` valuation selects a choice vector whose symbolic fold it
reads throughout.  `fold_mp` minus `SaturatingContracts`. -/
theorem fold_mpX {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {ins : Fin d → Wire}
    (hadm : σ.AdmissibleX) (hten : H.TenBoxOnly) (hbq : H.ExactBQ)
    (hic : H.InterfaceClosed ins) :
    ∀ (rest pre : List PrimApp), H.applications = pre ++ rest →
    ∀ st : SymSt d,
      (∀ w, (st.val w).isSome ↔
        ((∃ i, ins i = w) ∨ w ∈ pre.flatMap PrimApp.outputWires)) →
      (∀ w tab, st.val w = some tab → readsTab σ x w tab) →
      (∀ w tab, st.val w = some tab →
        ∃ τ, H.wireType w = some τ ∧ tab.length = τ.shape.totalSize) →
      CondsHold x st.conds →
      ∃ χ ∈ choiceLists (rest.map appChoices),
        CondsHold x (symFold H.wireType st rest χ).conds ∧
        (∀ w tab, (symFold H.wireType st rest χ).val w = some tab →
          readsTab σ x w tab) ∧
        (∀ w tab, (symFold H.wireType st rest χ).val w = some tab →
          ∃ τ, H.wireType w = some τ ∧
            tab.length = τ.shape.totalSize) := by
  intro rest
  induction rest with
  | nil =>
      intro pre hsplit st hdom hreads hlens hconds
      exact ⟨[], List.mem_singleton.mpr rfl, hconds, hreads, hlens⟩
  | cons app rest' ih =>
      intro pre hsplit st hdom hreads hlens hconds
      have happ_mem : app ∈ H.applications := by
        rw [hsplit]
        exact List.mem_append_right _ (List.mem_cons_self ..)
      have htb := hten app happ_mem
      have hcons : ∀ w ∈ app.inputWires, (st.val w).isSome := by
        intro w hw
        by_cases hprod : w ∈ H.producedWires
        · exact (hdom w).mpr (Or.inr
            (acyclic_consumed_in_prefix hsplit hw hprod))
        · have hcw : w ∈ H.consumedWires :=
            List.mem_flatMap.mpr ⟨app, happ_mem, hw⟩
          exact (hdom w).mpr (Or.inl (hic.2.2 w hcw hprod))
      obtain ⟨c, hc, hreads', hlens', hconds'⟩ := step_mpX
        (hadm app happ_mem) (H.typeConsistent app happ_mem) htb
        (hbq app happ_mem) st hreads hlens hcons
      have hsplit' : H.applications = (pre ++ [app]) ++ rest' := by
        rw [hsplit, List.append_assoc]
        rfl
      have hdom' : ∀ w, ((symStep H.wireType st app c).val w).isSome ↔
          ((∃ i, ins i = w) ∨ w ∈ (pre ++ [app]).flatMap
            PrimApp.outputWires) := by
        intro w
        rw [symStep_dom htb, hdom w, List.flatMap_append]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.mem_append]
        tauto
      obtain ⟨χ', hχ'mem, hχconds, hχreads, hχlens⟩ := ih (pre ++ [app])
        hsplit' (symStep H.wireType st app c) hdom' hreads' hlens'
        (hconds' hconds)
      refine ⟨c :: χ', ?_, hχconds, hχreads, hχlens⟩
      rw [List.map_cons]
      exact mem_choiceLists.mpr
        (List.Forall₂.cons hc (mem_choiceLists.mp hχ'mem))

/-- `step_build` strengthened to conclude `SemOkX`. -/
theorem step_buildX {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {app : PrimApp}
    (htc : app.TypeConsistent H.wireType) (htb : app.isTenBox = true)
    (hbqa : app.exactBQ = true) (hdisja : app.cellDisjoint)
    (hnd : app.outputWires.Nodup)
    (hio : ∀ w ∈ app.inputWires, w ∉ app.outputWires)
    (st : SymSt d) {c : ℕ} (hcv : c ∈ appChoices app)
    (hcons : ∀ w ∈ app.inputWires, (st.val w).isSome)
    (hlens : ∀ w tab, st.val w = some tab →
      ∃ τ, H.wireType w = some τ ∧ tab.length = τ.shape.totalSize)
    (hfr : ∀ w tab, (symStep H.wireType st app c).val w = some tab →
      readsTab σ x w tab)
    (hcond : CondsHold x (symStep H.wireType st app c).conds) :
    app.SemOkX σ := by
  cases app with
  | contract δ r inputs output ir orank pat =>
      have hkeep : ∀ w ∈ (PrimApp.contract δ r inputs output ir orank
          pat).inputWires,
          (symStep H.wireType st (.contract δ r inputs output ir orank
            pat) c).val w = st.val w :=
        fun w hw => symStep_val_of_not_output (hio w hw)
      have hresB : ∀ w ∈ (PrimApp.contract δ r inputs output ir orank
          pat).inputWires, ∃ tab, st.val w = some tab ∧
          readsTab σ x w tab ∧ ∃ τ, H.wireType w = some τ ∧
          tab.length = τ.shape.totalSize := by
        intro w hw
        obtain ⟨tab, htab⟩ := Option.isSome_iff_exists.mp (hcons w hw)
        exact ⟨tab, htab, hfr w tab (by rw [hkeep w hw]; exact htab),
          hlens w tab htab⟩
      have hbqa' : δ.isBQ = true ∧ r.isExact = true := by
        simpa [PrimApp.exactBQ] using hbqa
      obtain ⟨hbq, hexact⟩ := hbqa'
      obtain rfl := RoundMode.isExact_eq hexact
      have hto := contract_output_ty htc
      have hlen₁ : inputs.length = ir.length := htc.1
      have hlen₂ : (inputs.map (wireShapeOf H.wireType)).length
          = inputs.length := List.length_map ..
      have hlen₃ : (inputs.map fun w => (st.val w).getD []).length
          = inputs.length := List.length_map ..
      have hty : ∀ (kk : ℕ) (hk : kk < inputs.length), ∃ δk,
          H.wireType (inputs[kk]'hk) = some
            ⟨(inputs.map (wireShapeOf H.wireType))[kk]'(by omega), δk⟩ := by
        intro kk hk
        refine ⟨δ, ?_⟩
        rw [show (inputs.map (wireShapeOf H.wireType))[kk]'(by omega)
          = wireShapeOf H.wireType (inputs[kk]'hk) from List.getElem_map ..]
        exact contract_input_ty htc hk
      have htabres : ∀ (kk : ℕ) (hk : kk < inputs.length),
          st.val (inputs[kk]'hk)
            = some ((inputs.map fun w => (st.val w).getD [])[kk]'(by omega))
          ∧ ((inputs.map fun w => (st.val w).getD [])[kk]'(by omega)).length
            = ((inputs.map (wireShapeOf H.wireType))[kk]'(by omega)).totalSize := by
        intro kk hk
        obtain ⟨tab, htab, -, τ, hτ, htlen⟩ :=
          hresB _ (List.getElem_mem hk)
        have hget : (inputs.map fun w => (st.val w).getD [])[kk]'(by omega)
            = tab := by
          rw [show (inputs.map fun w => (st.val w).getD [])[kk]'(by omega)
            = (st.val (inputs[kk]'hk)).getD [] from List.getElem_map ..,
            htab]
          rfl
        have hshape : (inputs.map (wireShapeOf H.wireType))[kk]'(by omega)
            = τ.shape := by
          rw [show (inputs.map (wireShapeOf H.wireType))[kk]'(by omega)
            = wireShapeOf H.wireType (inputs[kk]'hk) from
              List.getElem_map .., wireShapeOf_some hτ]
        rw [hget, hshape]
        exact ⟨htab, htlen⟩
      have htablen : ∀ (kk : ℕ)
          (hk : kk < (inputs.map fun w => (st.val w).getD []).length),
          ((inputs.map fun w => (st.val w).getD [])[kk]'hk).length
            = ((inputs.map (wireShapeOf H.wireType))[kk]'(by omega)).totalSize :=
        fun kk hk => (htabres kk (by omega)).2
      have hreads' : ∀ (kk : ℕ) (hk : kk < inputs.length),
          readsTab σ x (inputs[kk]'hk)
            ((inputs.map fun w => (st.val w).getD [])[kk]'(by omega)) := by
        intro kk hk
        refine hfr _ _ ?_
        rw [hkeep _ (List.getElem_mem hk)]
        exact (htabres kk hk).1
      have hself : (symStep H.wireType st
          (.contract δ .exact inputs output ir orank pat) c).val output
          = some (contractTab pat (inputs.map (wireShapeOf H.wireType))
              (inputs.map fun w => (st.val w).getD [])) := by
        simp only [symStep]
        exact assignIdx_single _ _ _
      have hbool : δ = Dtype.B → ∀ p ∈ contractTab pat
          (inputs.map (wireShapeOf H.wireType))
          (inputs.map fun w => (st.val w).getD []),
          MvPolynomial.eval x p = 0 ∨ MvPolynomial.eval x p = 1 := by
        intro hB
        have hc2 := (CondsHold.append.mp hcond).2
        rw [hB, if_pos rfl] at hc2
        exact condsHold_boolConds_iff.mp hc2
      exact contract_semOkX_build hbq hto hlen₁ hlen₂ hlen₃ hty htablen
        hreads' (contract_input_rank htc) (contract_input_extent htc)
        (hfr _ _ hself) hbool
  | const ty cv out =>
      exact step_build htc htb hbqa hdisja hnd hio st hcv hcons hlens
        hfr hcond
  | cast δfrom δto r shape input output =>
      exact step_build htc htb hbqa hdisja hnd hio st hcv hcons hlens
        hfr hcond
  | cell schema input outputs =>
      exact step_build htc htb hbqa hdisja hnd hio st hcv hcons hlens
        hfr hcond
  | reshape newShape input output =>
      exact step_build htc htb hbqa hdisja hnd hio st hcv hcons hlens
        hfr hcond
  | broadcast toShape input output =>
      exact step_build htc htb hbqa hdisja hnd hio st hcv hcons hlens
        hfr hcond
  | copy kk input outputs =>
      exact step_build htc htb hbqa hdisja hnd hio st hcv hcons hlens
        hfr hcond
  | delete input =>
      exact step_build htc htb hbqa hdisja hnd hio st hcv hcons hlens
        hfr hcond
  | swap in1 in2 out1 out2 =>
      exact step_build htc htb hbqa hdisja hnd hio st hcv hcons hlens
        hfr hcond
  | stack kk shape inputs output =>
      exact step_build htc htb hbqa hdisja hnd hio st hcv hcons hlens
        hfr hcond
  | relu shape input output => exact absurd htb (by simp [PrimApp.isTenBox])
  | ppoly nv co inputs output =>
      exact absurd htb (by simp [PrimApp.isTenBox])
  | pderiv shape ax input output =>
      exact absurd htb (by simp [PrimApp.isTenBox])
  | facet shape ax hi input output =>
      exact absurd htb (by simp [PrimApp.isTenBox])

/-- `fold_admissible` strengthened to conclude `AdmissibleX`-shape
membership: every application satisfies the re-voiced semantics. -/
theorem fold_admissibleX {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {ins : Fin d → Wire}
    (hten : H.TenBoxOnly) (hbq : H.ExactBQ) (hic : H.InterfaceClosed ins)
    (hdisj : ∀ app ∈ H.applications, app.cellDisjoint) :
    ∀ (rest pre : List PrimApp), H.applications = pre ++ rest →
    ∀ (st : SymSt d) (χ : List ℕ),
      χ ∈ choiceLists (rest.map appChoices) →
      (∀ w, (st.val w).isSome ↔
        ((∃ i, ins i = w) ∨ w ∈ pre.flatMap PrimApp.outputWires)) →
      (∀ w tab, st.val w = some tab →
        ∃ τ, H.wireType w = some τ ∧ tab.length = τ.shape.totalSize) →
      (∀ w tab, (symFold H.wireType st rest χ).val w = some tab →
        readsTab σ x w tab) →
      CondsHold x (symFold H.wireType st rest χ).conds →
      ∀ app ∈ rest, app.SemOkX σ := by
  intro rest
  induction rest with
  | nil =>
      intro pre hsplit st χ hχ hdom hlens hreadF hcondF app happ
      exact absurd happ List.not_mem_nil
  | cons app rest' ih =>
      intro pre hsplit st χ hχ hdom hlens hreadF hcondF app' happ'
      have hχ' := mem_choiceLists.mp hχ
      rw [List.map_cons] at hχ'
      obtain ⟨c, χ', rfl, hc, hrest⟩ : ∃ c χ', χ = c :: χ' ∧
          c ∈ appChoices app ∧
          List.Forall₂ (· ∈ ·) χ' (rest'.map appChoices) := by
        cases hχ' with
        | cons hc hrest => exact ⟨_, _, rfl, hc, hrest⟩
      · have happ_mem : app ∈ H.applications := by
          rw [hsplit]
          exact List.mem_append_right _ (List.mem_cons_self ..)
        have htb := hten app happ_mem
        have hcons : ∀ w ∈ app.inputWires, (st.val w).isSome := by
          intro w hw
          by_cases hprod : w ∈ H.producedWires
          · exact (hdom w).mpr (Or.inr
              (acyclic_consumed_in_prefix hsplit hw hprod))
          · have hcw : w ∈ H.consumedWires :=
              List.mem_flatMap.mpr ⟨app, happ_mem, hw⟩
            exact (hdom w).mpr (Or.inl (hic.2.2 w hcw hprod))
        have hsplit' : H.applications = (pre ++ [app]) ++ rest' := by
          rw [hsplit, List.append_assoc]
          rfl
        have hdom' : ∀ w, ((symStep H.wireType st app c).val w).isSome ↔
            ((∃ i, ins i = w) ∨ w ∈ (pre ++ [app]).flatMap
              PrimApp.outputWires) := by
          intro w
          rw [symStep_dom htb, hdom w, List.flatMap_append]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
            List.mem_append]
          tauto
        have hreadF' : ∀ w tab,
            (symFold H.wireType (symStep H.wireType st app c) rest'
              χ').val w = some tab → readsTab σ x w tab := hreadF
        have hcondF' : CondsHold x (symFold H.wireType
            (symStep H.wireType st app c) rest' χ').conds := hcondF
        have hfrStep : ∀ w tab,
            (symStep H.wireType st app c).val w = some tab →
            readsTab σ x w tab := by
          intro w tab htab
          refine hreadF' w tab ?_
          rw [symFold_val_frozen rest' χ' _ w
            (dom_not_in_post hic hsplit ((hdom' w).mp
              (by rw [htab]; rfl)))]
          exact htab
        have hcondStep : CondsHold x
            (symStep H.wireType st app c).conds := by
          intro q hq
          exact hcondF' q (symFold_conds_mono rest' χ' _ q hq)
        rcases List.mem_cons.mp happ' with rfl | happ'2
        · exact step_buildX (H.typeConsistent app' happ_mem) htb
            (hbq app' happ_mem) (hdisj app' happ_mem)
            (nodup_of_flatMap_nodup H.linearity.2 app' happ_mem)
            (acyclic_input_not_output hsplit) st hc hcons hlens
            hfrStep hcondStep
        · exact ih (pre ++ [app]) hsplit' (symStep H.wireType st app c)
            χ' (mem_choiceLists.mpr hrest) hdom'
            (step_lens (H.typeConsistent app happ_mem) htb st _
              hlens hcons)
            hreadF' hcondF' app' happ'2

/-! ## The freedom mask and the cylinder class -/

/-- The freedom mask of an interface: `none` at connected output ports
(input ports or produced wires); at a disconnected port, the first
port naming the same wire — the shared free generator (repeated
disconnected output wires are an implicit `copy` of the interface, and
copies contribute diagonal equations, so generators are shared
per-wire, not per-coordinate). -/
def outMask (H : Hypernet) {d m : ℕ} (ins : Fin d → Wire)
    (outs : Fin m → Wire) (j : Fin m) : Option (Fin m) :=
  if (∃ i, ins i = outs j) ∨ outs j ∈ H.producedWires then none
  else (List.finRange m).find? fun j' => outs j' == outs j

theorem outMask_eq_none_iff {H : Hypernet} {d m : ℕ}
    {ins : Fin d → Wire} {outs : Fin m → Wire} {j : Fin m} :
    outMask H ins outs j = none
      ↔ ((∃ i, ins i = outs j) ∨ outs j ∈ H.producedWires) := by
  by_cases hc : (∃ i, ins i = outs j) ∨ outs j ∈ H.producedWires
  · simp only [outMask, if_pos hc]
    exact iff_of_true trivial hc
  · simp only [outMask, if_neg hc]
    constructor
    · intro h
      have hs : ((List.finRange m).find? fun j' =>
          outs j' == outs j).isSome :=
        List.find?_isSome.mpr ⟨j, List.mem_finRange j, by simp⟩
      rw [h] at hs
      exact absurd hs (by simp)
    · intro h
      exact absurd h hc

theorem outMask_some_wire {H : Hypernet} {d m : ℕ}
    {ins : Fin d → Wire} {outs : Fin m → Wire} {j j₀ : Fin m}
    (h : outMask H ins outs j = some j₀) : outs j₀ = outs j := by
  by_cases hc : (∃ i, ins i = outs j) ∨ outs j ∈ H.producedWires
  · simp only [outMask, if_pos hc] at h
    simp at h
  · simp only [outMask, if_neg hc] at h
    simpa using List.find?_some h

theorem outMask_some_not_connected {H : Hypernet} {d m : ℕ}
    {ins : Fin d → Wire} {outs : Fin m → Wire} {j j₀ : Fin m}
    (h : outMask H ins outs j = some j₀) :
    ¬ ((∃ i, ins i = outs j) ∨ outs j ∈ H.producedWires) := by
  intro hc
  simp only [outMask, if_pos hc] at h
  simp at h

/-- The canonical port of a shared free wire is its own canonical
port: generator indices are idempotent, which is what makes the
sharing well-defined. -/
theorem outMask_idem {H : Hypernet} {d m : ℕ}
    {ins : Fin d → Wire} {outs : Fin m → Wire} {j j₀ : Fin m}
    (h : outMask H ins outs j = some j₀) :
    outMask H ins outs j₀ = some j₀ := by
  have hw := outMask_some_wire h
  have hnc := outMask_some_not_connected h
  have hnc₀ : ¬ ((∃ i, ins i = outs j₀) ∨ outs j₀ ∈ H.producedWires) := by
    rw [hw]
    exact hnc
  have hpred : (fun j' => outs j' == outs j₀)
      = (fun j' => outs j' == outs j) := by
    funext j'
    rw [hw]
  simp only [outMask, if_neg hnc₀, hpred]
  simpa only [outMask, if_neg hnc] using h

/-- A piece read through a freedom mask: coordinates masked `some i`
read the `i`-th shared free generator; unmasked coordinates read the
piece polynomial. -/
def PieceData.cylGraph {d m : ℕ} (P : PieceData d m) {k : ℕ}
    (fr : Fin m → Option (Fin k)) : Set ((Fin d → ℚ) × (Fin m → ℚ)) :=
  { xy | (∀ q ∈ P.conds, 0 ≤ eval xy.1 q) ∧
         ∃ z : Fin k → ℚ, ∀ j,
           xy.2 j = ((fr j).map z).getD (eval xy.1 (P.val j)) }

/-- The conclusion-repaired target class: finite unions of
ℚ-polynomial graphs over basic closed pieces, closed under free
cylinders with shared generators. -/
def IsPiecewisePolyRelCyl {d m : ℕ}
    (R : Set ((Fin d → ℚ) × (Fin m → ℚ))) : Prop :=
  ∃ (k : ℕ) (fr : Fin m → Option (Fin k)) (Ps : List (PieceData d m)),
    R = ⋃ P ∈ Ps, P.cylGraph fr

/-- An all-`none` mask reads no generator: the cylinder graph is the
plain graph. -/
theorem PieceData.cylGraph_of_forall_none {d m k : ℕ}
    (P : PieceData d m) {fr : Fin m → Option (Fin k)}
    (hfr : ∀ j, fr j = none) : P.cylGraph fr = P.graph := by
  ext xy
  constructor
  · rintro ⟨hc, z, hz⟩
    refine ⟨hc, fun j => ?_⟩
    have h := hz j
    rw [hfr j] at h
    exact h
  · rintro ⟨hc, hv⟩
    refine ⟨hc, fun _ => 0, fun j => ?_⟩
    rw [hfr j]
    exact hv j

/-- The landed class embeds: `k = 0`, no coordinate masked. -/
theorem IsPiecewisePolyRelCyl.of_isPiecewisePolyRel {d m : ℕ}
    {R : Set ((Fin d → ℚ) × (Fin m → ℚ))}
    (h : IsPiecewisePolyRel R) : IsPiecewisePolyRelCyl R := by
  obtain ⟨Ps, rfl⟩ := h
  refine ⟨0, fun _ => none, Ps,
    (Set.iUnion₂_congr fun P _ =>
      P.cylGraph_of_forall_none fun _ => rfl).symm⟩

theorem IsPiecewisePolyRelCyl.empty (d m : ℕ) :
    IsPiecewisePolyRelCyl (∅ : Set ((Fin d → ℚ) × (Fin m → ℚ))) := by
  refine ⟨0, fun _ => none, [], ?_⟩
  ext z
  simp

/-! ## The ground table with freedom -/

/-- `groundOf` with output-port freedom: an unassigned typed wire named
by an output port takes the canonical port's value from `y` (the
`find?` canonicalization agrees with `outMask`'s by construction);
other unassigned typed wires zero-fill. -/
noncomputable def groundOfX (H : Hypernet) {d m : ℕ}
    (outs : Fin m → Wire) (y : Fin m → ℚ)
    (stv : Wire → Option (PTab d)) (x : Fin d → ℚ) : Wire → List ℚ :=
  fun w => match H.wireType w, stv w with
  | none, _ => []
  | some _τ, some tab => tab.map (MvPolynomial.eval x)
  | some τ, none =>
      match (List.finRange m).find? (fun j' => outs j' == w) with
      | some j₀ => List.replicate τ.shape.totalSize (y j₀)
      | none => List.replicate τ.shape.totalSize 0

theorem groundOfX_some {H : Hypernet} {d m : ℕ} {outs : Fin m → Wire}
    {y : Fin m → ℚ} {stv : Wire → Option (PTab d)} {x : Fin d → ℚ}
    {w : Wire} {τ : TensorType} {tab : PTab d}
    (hτ : H.wireType w = some τ) (hv : stv w = some tab) :
    groundOfX H outs y stv x w = tab.map (MvPolynomial.eval x) := by
  simp only [groundOfX, hτ, hv]

theorem groundOfX_free {H : Hypernet} {d m : ℕ} {outs : Fin m → Wire}
    {y : Fin m → ℚ} {stv : Wire → Option (PTab d)} {x : Fin d → ℚ}
    {w : Wire} {τ : TensorType} {j₀ : Fin m}
    (hτ : H.wireType w = some τ) (hv : stv w = none)
    (hf : (List.finRange m).find? (fun j' => outs j' == w) = some j₀) :
    groundOfX H outs y stv x w
      = List.replicate τ.shape.totalSize (y j₀) := by
  simp only [groundOfX, hτ, hv, hf]

theorem groundOfX_zero {H : Hypernet} {d m : ℕ} {outs : Fin m → Wire}
    {y : Fin m → ℚ} {stv : Wire → Option (PTab d)} {x : Fin d → ℚ}
    {w : Wire} {τ : TensorType}
    (hτ : H.wireType w = some τ) (hv : stv w = none)
    (hf : (List.finRange m).find? (fun j' => outs j' == w) = none) :
    groundOfX H outs y stv x w = List.replicate τ.shape.totalSize 0 := by
  simp only [groundOfX, hτ, hv, hf]

/-! ## The master equality, conclusion-repaired -/

/-- **The master equality**: with the re-voiced contract semantics, the
interface denotation of ANY exact-⟨B,Q⟩ ten-box hypernet with closed
scalar-rational interface — no output connection, no saturation — is
the union of the choice-indexed piece cylinder-graphs through the
interface's freedom mask.  The pieces are `pieceOf`, unchanged from the
hypothesis-repaired development; only the mask is new. -/
theorem denotRelX_eq_cylPieces {H : Hypernet} {d' m : ℕ}
    {ins : Fin d' → Wire} {outs : Fin m → Wire}
    (hten : H.TenBoxOnly) (hbq : H.ExactBQ) (hic : H.InterfaceClosed ins)
    (hins : ∀ i, H.ScalarQPort (ins i))
    (houts : ∀ j, H.ScalarQPort (outs j))
    (hdisj : ∀ app ∈ H.applications, app.cellDisjoint) :
    H.DenotRelX d' m ins outs
      = ⋃ P ∈ hypernetPieces H ins outs,
          P.cylGraph (outMask H ins outs) := by
  have hdom0 : ∀ w, ((initSt d' ins).val w).isSome ↔
      ((∃ i, ins i = w) ∨ w ∈ ([] : List PrimApp).flatMap
        PrimApp.outputWires) := by
    intro w
    rw [initSt_val_isSome]
    simp
  have hlens0 : ∀ w tab, (initSt d' ins).val w = some tab →
      ∃ τ, H.wireType w = some τ ∧ tab.length = τ.shape.totalSize := by
    intro w tab htab
    obtain ⟨i, rfl, rfl⟩ := initSt_val_cases htab
    obtain ⟨τ, hτ, -, hsz⟩ := hins i
    refine ⟨τ, hτ, ?_⟩
    rw [hsz]
    rfl
  ext ⟨x, y⟩
  constructor
  · rintro ⟨σ, hadm, hinr, houtr⟩
    have hreads0 : ∀ w tab, (initSt d' ins).val w = some tab →
        readsTab σ x w tab := by
      intro w tab htab
      obtain ⟨i, rfl, rfl⟩ := initSt_val_cases htab
      obtain ⟨τ, hτ, -, hsz⟩ := hins i
      refine readsTab_of_reads hτ (by rw [hsz]; rfl) ?_
      intro idx hidx
      have hidx0 : idx = 0 := Nat.lt_one_iff.mp (by simpa using hidx)
      subst hidx0
      show σ.entryFlat (ins i) 0
        = some (.fin (MvPolynomial.eval x (MvPolynomial.X i)))
      rw [eval_X]
      exact hinr i
    obtain ⟨χ, hχ, hcondF, hreadF, hlensF⟩ := fold_mpX hadm hten hbq
      hic H.applications [] rfl (initSt d' ins) hdom0 hreads0 hlens0
      (fun q hq => absurd hq List.not_mem_nil)
    refine Set.mem_iUnion₂.mpr ⟨pieceOf H ins outs χ,
      List.mem_map.mpr ⟨χ, hχ, rfl⟩, hcondF, fun j₀ => y j₀,
      fun j => ?_⟩
    cases hmask : outMask H ins outs j with
    | some j₀ =>
        show y j = y j₀
        have hw := outMask_some_wire hmask
        have h1 := houtr j
        have h2 := houtr j₀
        rw [hw] at h2
        exact ERat.fin.inj (Option.some.inj (h1.symm.trans h2))
    | none =>
        show y j = MvPolynomial.eval x ((pieceOf H ins outs χ).val j)
        have hconn := outMask_eq_none_iff.mp hmask
        have hsome : ((symFold H.wireType (initSt d' ins)
            H.applications χ).val (outs j)).isSome := by
          rcases hconn with ⟨i, hi⟩ | hprod
          · exact (symFold_dom H.applications χ _ hten (outs j)).mpr
              (Or.inr (initSt_val_isSome.mpr ⟨i, hi⟩))
          · exact (symFold_dom H.applications χ _ hten (outs j)).mpr
              (Or.inl hprod)
        obtain ⟨tab, htab⟩ := Option.isSome_iff_exists.mp hsome
        obtain ⟨τ, hτ, hlen⟩ := hlensF _ _ htab
        obtain ⟨τ', hτ', -, hsz⟩ := houts j
        have hττ : τ' = τ := Option.some.inj (hτ'.symm.trans hτ)
        rw [hττ] at hsz
        have hlen1 : tab.length = 1 := by
          rw [hlen]
          exact hsz
        have h0 : 0 < tab.length := by omega
        have hpv : (pieceOf H ins outs χ).val j = tab[0]'h0 := by
          show (((symFold H.wireType (initSt d' ins) H.applications
            χ).val (outs j)).getD []).getD 0 0 = _
          rw [htab]
          show tab.getD 0 0 = _
          exact Shape.getD_eq_getElem' tab 0 h0
        have hrd := (hreadF _ _ htab).read h0
        have hout := houtr j
        have hyv : y j = MvPolynomial.eval x (tab[0]'h0) :=
          ERat.fin.inj (Option.some.inj (hout.symm.trans hrd))
        rw [hpv]
        exact hyv
  · intro hmem
    obtain ⟨P, hP, hgraph⟩ := Set.mem_iUnion₂.mp hmem
    obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hP
    have hgraph' : (∀ p ∈ (pieceOf H ins outs χ).conds,
        0 ≤ MvPolynomial.eval x p) ∧
        ∃ z : Fin m → ℚ, ∀ j,
          y j = ((outMask H ins outs j).map z).getD
            (MvPolynomial.eval x ((pieceOf H ins outs χ).val j)) :=
      hgraph
    obtain ⟨hconds', z, hz⟩ := hgraph'
    have hcondF : CondsHold x (symFold H.wireType (initSt d' ins)
        H.applications χ).conds := hconds'
    have hmemk0 : ∀ w tab, (initSt d' ins).val w = some tab →
        ∀ τ, H.wireType w = some τ →
        ∀ p ∈ tab, τ.dtype.kind.MemK (MvPolynomial.eval x p) ∧
          (τ.dtype.sign = .nn → 0 ≤ MvPolynomial.eval x p) := by
      intro w tab htab τ hτ p hp
      obtain ⟨i, rfl, rfl⟩ := initSt_val_cases htab
      obtain ⟨τ', hτ', hdt, -⟩ := hins i
      have hττ : τ = τ' := Option.some.inj (hτ.symm.trans hτ')
      obtain rfl := List.mem_singleton.mp hp
      rw [hττ, hdt]
      exact ⟨trivial, fun h => nomatch h⟩
    obtain ⟨hlensF, hmemkF⟩ := fold_wf H.applications [] rfl hten hbq
      hic (initSt d' ins) χ hdom0 hlens0 hmemk0 hcondF
    have hwfX : ∀ w τ, H.wireType w = some τ →
        (groundOfX H outs y (symFold H.wireType (initSt d' ins)
          H.applications χ).val x w).length = τ.shape.totalSize ∧
        ∀ q ∈ groundOfX H outs y (symFold H.wireType (initSt d' ins)
          H.applications χ).val x w,
          τ.dtype.kind.MemK q ∧ (τ.dtype.sign = .nn → 0 ≤ q) := by
      intro w τ hτ
      cases hval : (symFold H.wireType (initSt d' ins)
          H.applications χ).val w with
      | some tab =>
          rw [groundOfX_some hτ hval]
          obtain ⟨τ'', hτ'', hlen⟩ := hlensF w tab hval
          have hττ : τ'' = τ := Option.some.inj (hτ''.symm.trans hτ)
          rw [hττ] at hlen
          refine ⟨by rw [List.length_map]; exact hlen, ?_⟩
          intro q hq
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
          exact hmemkF w tab hval τ hτ p hp
      | none =>
          cases hfind : (List.finRange m).find?
              (fun j' => outs j' == w) with
          | none =>
              rw [groundOfX_zero hτ hval hfind]
              refine ⟨List.length_replicate .., ?_⟩
              intro q hq
              obtain rfl := List.eq_of_mem_replicate hq
              exact ⟨memK_zero _, fun _ => le_refl 0⟩
          | some j₀ =>
              rw [groundOfX_free hτ hval hfind]
              refine ⟨List.length_replicate .., ?_⟩
              intro q hq
              obtain rfl := List.eq_of_mem_replicate hq
              have hwj : outs j₀ = w := by
                simpa using List.find?_some hfind
              obtain ⟨τ', hτ', hdt, -⟩ := houts j₀
              rw [hwj] at hτ'
              have hττ : τ = τ' := Option.some.inj (hτ.symm.trans hτ')
              rw [hττ, hdt]
              exact ⟨trivial, fun h => nomatch h⟩
    have hreadF : ∀ w tab, (symFold H.wireType (initSt d' ins)
        H.applications χ).val w = some tab →
        readsTab (BasisGen.mkVal H (groundOfX H outs y (symFold
          H.wireType (initSt d' ins) H.applications χ).val x) hwfX)
          x w tab := by
      intro w tab htab
      obtain ⟨τ, hτ, -⟩ := hlensF w tab htab
      intro i
      rw [BasisGen.mkVal_reads H _ hwfX hτ i, groundOfX_some hτ htab,
        List.getElem?_map, Option.map_map]
      rfl
    have hadmX : (BasisGen.mkVal H (groundOfX H outs y (symFold
        H.wireType (initSt d' ins) H.applications χ).val x)
          hwfX).AdmissibleX :=
      fun app happ => fold_admissibleX hten hbq hic hdisj
        H.applications [] rfl (initSt d' ins) χ hχ hdom0 hlens0
        hreadF hcondF app happ
    refine ⟨BasisGen.mkVal H (groundOfX H outs y (symFold H.wireType
      (initSt d' ins) H.applications χ).val x) hwfX, hadmX, ?_, ?_⟩
    · intro i
      have hini : (initSt d' ins).val (ins i)
          = some [MvPolynomial.X i] := initSt_val_ins hic.1 i
      have hfin : (symFold H.wireType (initSt d' ins)
          H.applications χ).val (ins i) = some [MvPolynomial.X i] := by
        rw [symFold_val_frozen H.applications χ _ _ ?_]
        · exact hini
        · intro app happ hw
          exact hic.2.1 i (List.mem_flatMap.mpr ⟨app, happ, hw⟩)
      have hrd := (hreadF _ _ hfin).read (i := 0) (by simp)
      rw [show ([MvPolynomial.X i] : PTab d')[0]'(by simp)
        = MvPolynomial.X i from rfl, eval_X] at hrd
      exact hrd
    · intro j
      cases hmask : outMask H ins outs j with
      | none =>
          have hconn := outMask_eq_none_iff.mp hmask
          have hsome : ((symFold H.wireType (initSt d' ins)
              H.applications χ).val (outs j)).isSome := by
            rcases hconn with ⟨i, hi⟩ | hprod
            · exact (symFold_dom H.applications χ _ hten (outs j)).mpr
                (Or.inr (initSt_val_isSome.mpr ⟨i, hi⟩))
            · exact (symFold_dom H.applications χ _ hten (outs j)).mpr
                (Or.inl hprod)
          obtain ⟨tab, htab⟩ := Option.isSome_iff_exists.mp hsome
          obtain ⟨τ, hτ, hlen⟩ := hlensF _ _ htab
          obtain ⟨τ', hτ', -, hsz⟩ := houts j
          have hττ : τ' = τ := Option.some.inj (hτ'.symm.trans hτ)
          rw [hττ] at hsz
          have hlen1 : tab.length = 1 := by
            rw [hlen]
            exact hsz
          have h0 : 0 < tab.length := by omega
          have hrd := (hreadF _ _ htab).read h0
          have hyv := hz j
          rw [hmask] at hyv
          have hyv' : y j = MvPolynomial.eval x
              ((pieceOf H ins outs χ).val j) := hyv
          have hpv : (pieceOf H ins outs χ).val j = tab[0]'h0 := by
            show (((symFold H.wireType (initSt d' ins) H.applications
              χ).val (outs j)).getD []).getD 0 0 = _
            rw [htab]
            show tab.getD 0 0 = _
            exact Shape.getD_eq_getElem' tab 0 h0
          rw [hpv] at hyv'
          rw [hrd, ← hyv']
      | some j₀ =>
          have hnc := outMask_some_not_connected hmask
          have hnone : (symFold H.wireType (initSt d' ins)
              H.applications χ).val (outs j) = none := by
            cases hval : (symFold H.wireType (initSt d' ins)
                H.applications χ).val (outs j) with
            | none => rfl
            | some tab =>
                have hs : ((symFold H.wireType (initSt d' ins)
                    H.applications χ).val (outs j)).isSome := by
                  rw [hval]
                  rfl
                rcases (symFold_dom H.applications χ _ hten
                    (outs j)).mp hs with hprod | hini
                · exact absurd (Or.inr hprod) hnc
                · exact absurd (Or.inl (initSt_val_isSome.mp hini)) hnc
          have hfind : (List.finRange m).find?
              (fun j' => outs j' == outs j) = some j₀ := by
            simpa only [outMask, if_neg hnc] using hmask
          obtain ⟨τ', hτ', -, hsz⟩ := houts j
          have hyj : y j = y j₀ := by
            have h1 : y j = z j₀ := by
              have h := hz j
              rw [hmask] at h
              exact h
            have h2 : y j₀ = z j₀ := by
              have h := hz j₀
              rw [outMask_idem hmask] at h
              exact h
            rw [h1, h2]
          rw [BasisGen.mkVal_reads H _ hwfX hτ' 0,
            groundOfX_free hτ' hnone hfind, hsz]
          show Option.map ERat.fin ((List.replicate 1 (y j₀))[0]?)
            = some (ERat.fin (y j))
          rw [hyj]
          rfl

/-! ## The headline -/

/-- **The conclusion-repaired soundness statement**: the landed
statement's exact hypothesis set, with the conclusion moved to the
cylinder-closed class and the semantics re-voiced through
`contractExact`. -/
def PrimitiveBasisSoundX : Prop :=
  ∀ (H : Hypernet) (d m : ℕ) (ins : Fin d → Wire) (outs : Fin m → Wire),
    H.TenBoxOnly → H.ExactBQ → H.InterfaceClosed ins →
    (∀ i, H.ScalarQPort (ins i)) → (∀ j, H.ScalarQPort (outs j)) →
    IsPiecewisePolyRelCyl (H.DenotRelX d m ins outs)

theorem primitiveBasisSoundX : PrimitiveBasisSoundX := by
  intro H d' m ins outs hten hbq hic hins houts
  by_cases hdisj : ∀ app ∈ H.applications, app.cellDisjoint
  · exact ⟨m, outMask H ins outs, hypernetPieces H ins outs,
      denotRelX_eq_cylPieces hten hbq hic hins houts hdisj⟩
  · push Not at hdisj
    obtain ⟨app, happ, hnd⟩ := hdisj
    have hempty : H.DenotRelX d' m ins outs = ∅ := by
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨σ, hadm, -, -⟩
      have hsem := hadm app happ
      cases app <;> first | exact hnd hsem.1 | exact hnd trivial
    rw [hempty]
    exact IsPiecewisePolyRelCyl.empty _ _

/-! ## Subsumption: the interim exhibit is a corollary -/

/-- The hypothesis-repaired statement follows from the conclusion
repair: under `SaturatingContracts` the re-voicing is invisible
(`denotRelX_eq_of_saturating`), and under `OutputsConnected` the mask
is all-`none`, collapsing cylinder graphs to plain graphs.  Proven
without invoking the landed `primitiveBasisSoundWF`. -/
theorem primitiveBasisSoundWF_of_conclusionRepair :
    PrimitiveBasisSoundWF := by
  intro H d' m ins outs hten hbq hic hoc hsat hins houts
  by_cases hdisj : ∀ app ∈ H.applications, app.cellDisjoint
  · have hmask : ∀ j, outMask H ins outs j = none :=
      fun j => outMask_eq_none_iff.mpr (hoc j)
    have hmain := denotRelX_eq_cylPieces hten hbq hic hins houts hdisj
    rw [H.denotRelX_eq_of_saturating hsat ins outs] at hmain
    refine ⟨hypernetPieces H ins outs, ?_⟩
    rw [hmain]
    exact Set.iUnion₂_congr fun P _ =>
      P.cylGraph_of_forall_none hmask
  · push Not at hdisj
    obtain ⟨app, happ, hnd⟩ := hdisj
    have hempty : H.DenotRel d' m ins outs = ∅ := by
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨σ, hadm, -, -⟩
      have hsem := hadm app happ
      cases app <;> first | exact hnd hsem.1 | exact hnd trivial
    rw [hempty]
    exact IsPiecewisePolyRel.empty _ _

/-! ## The G1 flip: the falsification exhibit turns positive -/

/-- The empty net has no contracts, so the re-voicing changes nothing:
its repaired denotation is the same full line that refuted the landed
statement. -/
theorem freeOutH_denotRelX :
    freeOutH.DenotRelX 0 1 (fun i => i.elim0) ![0] = Set.univ := by
  rw [freeOutH.denotRelX_eq_of_saturating
    (fun app happ => absurd happ List.not_mem_nil)]
  exact freeOutH_denotRel

/-- **The flip**: the exact configuration of `not_primitiveBasisSound`
goes THROUGH the conclusion-repaired theorem — the full line is the
free cylinder on the disconnected wire. -/
theorem freeOutH_soundX :
    IsPiecewisePolyRelCyl
      (freeOutH.DenotRelX 0 1 (fun i => i.elim0) ![0]) := by
  refine primitiveBasisSoundX freeOutH 0 1 (fun i => i.elim0) ![0]
    (fun app happ => absurd happ List.not_mem_nil)
    (fun app happ => absurd happ List.not_mem_nil)
    ⟨fun a => a.elim0, fun i => i.elim0,
      fun w hw => absurd hw List.not_mem_nil⟩
    (fun i => i.elim0) ?_
  intro j
  have hj : j = 0 := Fin.ext (Nat.lt_one_iff.mp j.isLt)
  subst hj
  exact ⟨⟨[], Dtype.Q⟩, freeOutH_wireType0, rfl, rfl⟩

/-- The full line is in the repaired class — which, with the landed
`not_isPiecewisePolyRel_univ`, certifies the class properly grew. -/
theorem univ_isPiecewisePolyRelCyl :
    IsPiecewisePolyRelCyl
      (Set.univ : Set ((Fin 0 → ℚ) × (Fin 1 → ℚ))) :=
  freeOutH_denotRelX ▸ freeOutH_soundX

theorem cylClass_properly_extends :
    IsPiecewisePolyRelCyl
      (Set.univ : Set ((Fin 0 → ℚ) × (Fin 1 → ℚ))) ∧
    ¬ IsPiecewisePolyRel
      (Set.univ : Set ((Fin 0 → ℚ) × (Fin 1 → ℚ))) :=
  ⟨univ_isPiecewisePolyRelCyl, not_isPiecewisePolyRel_univ⟩

/-! ## The G2 witness: repeated output binding is an implicit `copy` -/

/-- The diagonal pattern: no inputs, one summed index of extent 2,
both output axes bound to it — `einsum` `"→ii"`. -/
def diagPat : ContractPattern [] 2 where
  nIndices := 1
  indexExtent := fun _ => 2
  inputBinding := fun i => i.elim0
  outputBinding := fun _ => ⟨0, Nat.one_pos⟩

/-- A single rank-2 rational wire to host the diagonal output. -/
def diagH : Hypernet where
  wireType := fun w => if w = 0 then some ⟨[2, 2], Dtype.Q⟩ else none
  applications := []
  linearity := ⟨List.nodup_nil, List.nodup_nil⟩
  acyclic := fun i => i.elim0
  typeConsistent := fun _ h => nomatch h

theorem diagPat_exact_offDiag (σ : diagH.Valuation) :
    contractExact σ [] diagPat [0, 1] = some (.fin 0) := rfl

theorem diagPat_exact_diag (σ : diagH.Valuation) :
    contractExact σ [] diagPat [0, 0] = some (.fin 1) := by
  show ERat.sum? [ERat.fin 1] = some (.fin 1)
  simpa using ERat.sum?_fin [(1 : ℚ)]

/-- **G2, machine-checked**: under the re-voiced semantics the
repeated output binding acts as an implicit `copy` — the off-diagonal
entry is pinned to `0` (the empty fiber's sum) and the diagonal to `1`
(the empty product), the identity matrix.  Under the landed `SemOk`
the off-diagonal position is not in the image of `outCoords` and is
unconstrained. -/
theorem diag_semOkX_offDiag {σ : diagH.Valuation}
    (hsem : (PrimApp.contract Dtype.Q .exact [] 0 [] 2
      diagPat).SemOkX σ) :
    σ.entryAt 0 [0, 1] = some (.fin 0) := by
  obtain ⟨eOut, eExact, h1, h2, h3⟩ := hsem [0, 1] (by decide)
  rw [diagPat_exact_offDiag σ] at h2
  obtain rfl := Option.some.inj h2
  obtain ⟨rfl, -⟩ := h3
  exact h1

theorem diag_semOkX_diag {σ : diagH.Valuation}
    (hsem : (PrimApp.contract Dtype.Q .exact [] 0 [] 2
      diagPat).SemOkX σ) :
    σ.entryAt 0 [0, 0] = some (.fin 1) := by
  obtain ⟨eOut, eExact, h1, h2, h3⟩ := hsem [0, 0] (by decide)
  rw [diagPat_exact_diag σ] at h2
  obtain rfl := Option.some.inj h2
  obtain ⟨rfl, -⟩ := h3
  exact h1

/-! ## The G3 witness: the empty sum is a theorem about `0` -/

/-- The zero-sum pattern: one summed index of extent 0, scalar
output — `einsum` over an empty range. -/
def zeroPat : ContractPattern [] 0 where
  nIndices := 1
  indexExtent := fun _ => 0
  inputBinding := fun i => i.elim0
  outputBinding := fun a => a.elim0

theorem zeroPat_exact (σ : freeOutH.Valuation) :
    contractExact σ [] zeroPat [] = some (.fin 0) := rfl

/-- G3's landed half: the zero-extent contraction's landed `SemOk` is
VACUOUS — every valuation satisfies it, pinning nothing. -/
theorem zero_semOk_vacuous (σ : freeOutH.Valuation) :
    (PrimApp.contract Dtype.Q .exact [] 0 [] 0 zeroPat).SemOk σ :=
  fun _ν₀ hν₀ => absurd hν₀ List.not_mem_nil

/-- **G3 as a theorem about `0`**: the re-voiced semantics pins the
empty sum — the scalar output is exactly the zero polynomial's
value. -/
theorem zero_semOkX_pins {σ : freeOutH.Valuation}
    (hsem : (PrimApp.contract Dtype.Q .exact [] 0 [] 0
      zeroPat).SemOkX σ) :
    σ.entryAt 0 [] = some (.fin 0) := by
  obtain ⟨eOut, eExact, h1, h2, h3⟩ := hsem [] (by decide)
  rw [zeroPat_exact σ] at h2
  obtain rfl := Option.some.inj h2
  obtain ⟨rfl, -⟩ := h3
  exact h1

#print axioms primitiveBasisSoundX
#print axioms denotRelX_eq_cylPieces
#print axioms primitiveBasisSoundWF_of_conclusionRepair
#print axioms PrimApp.semOk_of_semOkX
#print axioms Hypernet.denotRelX_eq_of_saturating
#print axioms freeOutH_soundX
#print axioms univ_isPiecewisePolyRelCyl
#print axioms diag_semOkX_offDiag
#print axioms zero_semOkX_pins
#print axioms zero_semOk_vacuous

end PPLC
