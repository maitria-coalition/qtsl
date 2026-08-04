import Qtsl.TensorNF
import Qtsl.DenotationComplete

/-!
# Soundness of the primitive basis: falsification and repair

The landed `PrimitiveBasisSound` statement is FALSE, for three
independent reasons, each a degree of freedom that reaches the
interface unpinned:

* **G1 (free output wires).**  `outs j` is only required to be a
  `ScalarQPort`; an output wire neither produced by any application nor
  equal to any input is unconstrained by every `SemOk`, so the
  denotation contains a full line in that coordinate — and a finite
  union of piece graphs has finite sections.  `not_primitiveBasisSound`
  machine-checks this on the empty hypernet.
* **G2 (non-injective `outputBinding`).**  `SemOk .contract` pins the
  output only at coordinates in the image of `outCoords`; a pattern
  binding two output axes to one index pins only the diagonal, and the
  free off-diagonal entries flow into downstream sums.
* **G3 (zero-extent summed indices).**  A zero extent empties
  `positions pat.idxShape`, making `SemOk .contract` vacuous — the
  whole output goes free (correct semantics would pin empty sums
  to `0`).

The repair carries two hypotheses: `Hypernet.OutputsConnected` (every
output port is an input port or a produced wire) and
`Hypernet.SaturatingContracts` (every contraction pattern hits every
output position — `ContractPattern.Saturating`, which G2/G3 violate).
`PrimitiveBasisSoundWF` is the repaired statement; the soundness proof
proceeds by symbolic forward evaluation along the SSA order
(`Hypernet.acyclic` orders `applications`; `linearity` gives
produce-once and consume-once), with pieces indexed by cell choices.

A deeper repair — re-voicing `SemOk .contract` to quantify over all
output positions with `contractExact` directly, which pins empty sums
to zero and makes `Saturating` unnecessary — is a certificate-
vocabulary change that belongs to the theory-pair bake, not to this
module; the hypotheses here are chosen to leave every landed
definition untouched.
-/

namespace PPLC

open MvPolynomial

variable {d : ℕ}

/-! ## The repair vocabulary -/

/-- Every output port is an input port or a produced wire.  The
output-side twin of `InterfaceClosed`: without it, σ is free on a
disconnected output wire and the denotation contains a full line. -/
def Hypernet.OutputsConnected (H : Hypernet) {d m : ℕ}
    (ins : Fin d → Wire) (outs : Fin m → Wire) : Prop :=
  ∀ j, (∃ i, ins i = outs j) ∨ outs j ∈ H.producedWires

/-- Per-application saturation: `contract` patterns hit every output
position; every other box is unconstrained. -/
def PrimApp.saturating : PrimApp → Prop
  | .contract _ _ _ _ _ _ pat => pat.Saturating
  | _ => True

/-- All contraction patterns in the net are saturating. -/
def Hypernet.SaturatingContracts (H : Hypernet) : Prop :=
  ∀ app ∈ H.applications, app.saturating

/-- **The repaired soundness statement**: `PrimitiveBasisSound` with
output connection and contraction saturation. -/
def PrimitiveBasisSoundWF : Prop :=
  ∀ (H : Hypernet) (d m : ℕ) (ins : Fin d → Wire) (outs : Fin m → Wire),
    H.TenBoxOnly → H.ExactBQ → H.InterfaceClosed ins →
    H.OutputsConnected ins outs → H.SaturatingContracts →
    (∀ i, H.ScalarQPort (ins i)) → (∀ j, H.ScalarQPort (outs j)) →
    IsPiecewisePolyRel (H.DenotRel d m ins outs)

/-! ## The falsification: G1 on the empty hypernet -/

/-- The empty hypernet with one typed scalar-rational wire. -/
def freeOutH : Hypernet where
  wireType := fun w => if w = 0 then some ⟨[], Dtype.Q⟩ else none
  applications := []
  linearity := ⟨List.nodup_nil, List.nodup_nil⟩
  acyclic := fun i => i.elim0
  typeConsistent := fun _ h => nomatch h

theorem freeOutH_wireType0 : freeOutH.wireType 0 = some ⟨[], Dtype.Q⟩ := rfl

/-- The empty net's denotation on a disconnected output is the full
line. -/
theorem freeOutH_denotRel :
    freeOutH.DenotRel 0 1 (fun i => i.elim0) ![0] = Set.univ := by
  ext ⟨xf, y⟩
  simp only [Set.mem_univ, iff_true]
  show ∃ σ : freeOutH.Valuation, σ.Admissible ∧ _ ∧ _
  have hg : ∀ w τ, freeOutH.wireType w = some τ →
      ((fun w' => if w' = 0 then [y 0] else []) w).length
        = τ.shape.totalSize ∧
      ∀ q ∈ (fun w' => if w' = 0 then [y 0] else []) w,
        τ.dtype.kind.MemK q ∧ (τ.dtype.sign = .nn → 0 ≤ q) := by
    intro w τ hτ
    by_cases hw : w = 0
    · subst hw
      have hτ' : τ = ⟨[], Dtype.Q⟩ :=
        (Option.some.inj (freeOutH_wireType0.symm.trans hτ)).symm
      subst hτ'
      refine ⟨rfl, ?_⟩
      intro q _
      exact ⟨trivial, fun h => nomatch h⟩
    · have : freeOutH.wireType w = none := by
        show (if w = 0 then some (⟨[], Dtype.Q⟩ : TensorType) else none)
          = none
        rw [if_neg hw]
      rw [this] at hτ
      exact absurd hτ (by simp)
  refine ⟨BasisGen.mkVal freeOutH _ hg, ?_, ?_, ?_⟩
  · intro app happ
    exact absurd happ List.not_mem_nil
  · intro i
    exact i.elim0
  · intro j
    have hj : j = 0 := Fin.ext (Nat.lt_one_iff.mp j.isLt)
    subst hj
    show (BasisGen.mkVal freeOutH _ hg).entryFlat 0 0
      = some (ERat.fin (y 0))
    rw [BasisGen.mkVal_reads freeOutH _ hg freeOutH_wireType0 0]
    rfl

/-- Some rational avoids any finite list. -/
theorem exists_notMem_ratList (L : List ℚ) : ∃ q : ℚ, ∀ p ∈ L, q ≠ p := by
  refine ⟨1 + L.foldr max 0, ?_⟩
  have hle : ∀ p ∈ L, p ≤ L.foldr max 0 := by
    induction L with
    | nil =>
        intro p hp
        exact absurd hp List.not_mem_nil
    | cons a L ih =>
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact le_max_left ..
        · exact le_trans (ih p hp) (le_max_right ..)
  intro p hp heq
  have h1 := hle p hp
  rw [← heq] at h1
  linarith

/-- The full line is not a finite union of piece graphs: each piece
contributes at most one output value per input point. -/
theorem not_isPiecewisePolyRel_univ :
    ¬ IsPiecewisePolyRel (Set.univ : Set ((Fin 0 → ℚ) × (Fin 1 → ℚ))) := by
  rintro ⟨Ps, hPs⟩
  obtain ⟨q, hq⟩ := exists_notMem_ratList
    (Ps.map fun P => MvPolynomial.eval (fun i => (i : Fin 0).elim0) (P.val 0))
  have hmem : ((fun i => (i : Fin 0).elim0), fun _ => q) ∈
      (Set.univ : Set ((Fin 0 → ℚ) × (Fin 1 → ℚ))) := Set.mem_univ _
  rw [hPs] at hmem
  obtain ⟨P, hP, hgraph⟩ := Set.mem_iUnion₂.mp hmem
  have hgraph' : (∀ p ∈ P.conds, 0 ≤ MvPolynomial.eval
      (fun i => (i : Fin 0).elim0) p) ∧
      ∀ j, (fun _ => q) j = MvPolynomial.eval
        (fun i => (i : Fin 0).elim0) (P.val j) := hgraph
  exact hq _ (List.mem_map.mpr ⟨P, hP, rfl⟩) (hgraph'.2 0)

/-- **The landed soundness statement is false**: a scalar-rational
output wire disconnected from the (empty) net is unconstrained, its
denotation is the full line, and full lines are not finite unions of
piece graphs.  (`InterfaceClosed` covers only the input side; the
`OutputsConnected` hypothesis of `PrimitiveBasisSoundWF` is exactly
what this counterexample shows to be missing.) -/
theorem not_primitiveBasisSound : ¬ PrimitiveBasisSound := by
  intro h
  have hten : freeOutH.TenBoxOnly := fun app happ =>
    absurd happ List.not_mem_nil
  have hbq : freeOutH.ExactBQ := fun app happ =>
    absurd happ List.not_mem_nil
  have hic : freeOutH.InterfaceClosed (fun i => (i : Fin 0).elim0) :=
    ⟨fun a => a.elim0, fun i => i.elim0,
     fun w hw => absurd hw List.not_mem_nil⟩
  have hport : ∀ j : Fin 1, freeOutH.ScalarQPort ((![0] : Fin 1 → Wire) j) := by
    intro j
    have hj : j = 0 := Fin.ext (Nat.lt_one_iff.mp j.isLt)
    subst hj
    exact ⟨⟨[], Dtype.Q⟩, freeOutH_wireType0, rfl, rfl⟩
  have hres := h freeOutH 0 1 (fun i => i.elim0) ![0] hten hbq hic
    (fun i => i.elim0) hport
  rw [freeOutH_denotRel] at hres
  exact not_isPiecewisePolyRel_univ hres

/-! ## Symbolic state -/

/-- The symbolic evaluation state: per-wire optional entry tables and
accumulated carving conditions. -/
structure SymSt (d : ℕ) where
  val : Wire → Option (PTab d)
  conds : PTab d

/-- Assign consecutive tables to a list of wires (later wires shadow
earlier ones; the callers only use it on `Nodup` lists). -/
def assignIdx (f : ℕ → PTab d) : List Wire → (Wire → Option (PTab d)) →
    Wire → Option (PTab d)
  | [], base => base
  | w :: ws, base => fun w' =>
      if w' = w then some (f 0)
      else assignIdx (fun j => f (j + 1)) ws base w'

theorem assignIdx_of_not_mem (f : ℕ → PTab d) :
    ∀ {ws : List Wire} (base : Wire → Option (PTab d)) {w' : Wire},
      w' ∉ ws → assignIdx f ws base w' = base w' := by
  intro ws
  induction ws generalizing f with
  | nil => intro base w' _; rfl
  | cons w ws ih =>
      intro base w' h
      show (if w' = w then some (f 0)
        else assignIdx (fun j => f (j + 1)) ws base w') = base w'
      rw [if_neg (fun hh => h (by rw [hh]; exact List.mem_cons_self ..)),
        ih _ _ (fun hh => h (List.mem_cons_of_mem _ hh))]

theorem assignIdx_getElem (f : ℕ → PTab d) :
    ∀ {ws : List Wire}, ws.Nodup → ∀ (base : Wire → Option (PTab d))
      {j : ℕ} (hj : j < ws.length),
      assignIdx f ws base (ws[j]'hj) = some (f j) := by
  intro ws
  induction ws generalizing f with
  | nil =>
      intro _ base j hj
      exact absurd hj (by simp)
  | cons w ws ih =>
      intro hnd base j hj
      obtain ⟨hw, hnd2⟩ := List.nodup_cons.mp hnd
      match j with
      | 0 =>
          show (if w = w then some (f 0) else _) = some (f 0)
          rw [if_pos rfl]
      | j + 1 =>
          have hjl : j < ws.length := by simpa using hj
          show (if ws[j]'hjl = w then some (f 0)
            else assignIdx (fun j => f (j + 1)) ws base (ws[j]'hjl))
            = some (f (j + 1))
          rw [if_neg (fun hh => hw (by rw [← hh]; exact List.getElem_mem hjl)),
            ih _ hnd2 base hjl]

theorem assignIdx_isSome (f : ℕ → PTab d) :
    ∀ (ws : List Wire) (base : Wire → Option (PTab d)) (w' : Wire),
      (assignIdx f ws base w').isSome ↔ w' ∈ ws ∨ (base w').isSome := by
  intro ws
  induction ws generalizing f with
  | nil =>
      intro base w'
      simp [assignIdx]
  | cons w ws ih =>
      intro base w'
      show (if w' = w then some (f 0)
        else assignIdx (fun j => f (j + 1)) ws base w').isSome ↔ _
      by_cases h : w' = w
      · subst h
        simp
      · rw [if_neg h, ih]
        simp [List.mem_cons, h]

/-- Elements produced by `assignIdx` are tables of the assignment (at
an identified wire) or of the base. -/
theorem assignIdx_cases (f : ℕ → PTab d) :
    ∀ (ws : List Wire) (base : Wire → Option (PTab d)) (w' : Wire)
      {tab : PTab d}, assignIdx f ws base w' = some tab →
      (∃ j, ∃ hj : j < ws.length, w' = ws[j]'hj ∧ tab = f j)
      ∨ base w' = some tab := by
  intro ws
  induction ws generalizing f with
  | nil =>
      intro base w' tab h
      exact Or.inr h
  | cons w ws ih =>
      intro base w' tab h
      replace h : (if w' = w then some (f 0)
        else assignIdx (fun j => f (j + 1)) ws base w') = some tab := h
      by_cases hw : w' = w
      · rw [if_pos hw] at h
        exact Or.inl ⟨0, Nat.succ_pos _, hw, (Option.some.inj h).symm⟩
      · rw [if_neg hw] at h
        rcases ih _ _ _ h with ⟨j, hj, hwj, htab⟩ | hbase
        · exact Or.inl ⟨j + 1, Nat.succ_lt_succ hj, hwj, htab⟩
        · exact Or.inr hbase

/-- The shape a wire-typing assigns, defaulting to scalar. -/
def wireShapeOf (wt : Wire → Option TensorType) (w : Wire) : Shape :=
  ((wt w).map TensorType.shape).getD []

theorem wireShapeOf_some {wt : Wire → Option TensorType} {w : Wire}
    {τ : TensorType} (h : wt w = some τ) : wireShapeOf wt w = τ.shape := by
  rw [wireShapeOf, h]
  rfl

/-! ## The symbolic step and fold -/

/-- One step of symbolic forward evaluation.  Total with junk defaults;
the correctness invariants live in the fold lemmas, never in the
definition. -/
noncomputable def symStep (wt : Wire → Option TensorType) (st : SymSt d)
    (app : PrimApp) (choice : ℕ) : SymSt d :=
  match app with
  | .const _ty c out =>
      ⟨assignIdx (fun _ => c.entriesQ.map MvPolynomial.C) [out] st.val,
       st.conds⟩
  | .contract δ _r inputs output _ir _or pat =>
      let tab := contractTab pat (inputs.map (wireShapeOf wt))
        (inputs.map fun w => (st.val w).getD [])
      ⟨assignIdx (fun _ => tab) [output] st.val,
       st.conds ++ (if δ = Dtype.B then boolConds tab else [])⟩
  | .cast _δfrom δto _r _shape input output =>
      let tab := (st.val input).getD []
      ⟨assignIdx (fun _ => tab) [output] st.val,
       st.conds ++ (if δto = Dtype.B then boolConds tab else [])⟩
  | .cell schema input outputs =>
      let tab := (st.val input).getD []
      ⟨assignIdx (fun j => oneHotTab j choice) outputs st.val,
       st.conds ++ (if hc : choice < schema.cells.length then
         maskCondsAt schema (schema.cells.get ⟨choice, hc⟩).1
           (schema.cells.get ⟨choice, hc⟩).2 (fun j => tab.getD j.val 0)
         else [])⟩
  | .reshape _new input output =>
      ⟨assignIdx (fun _ => (st.val input).getD []) [output] st.val,
       st.conds⟩
  | .broadcast toShape input output =>
      ⟨assignIdx (fun _ => broadcastTab (wireShapeOf wt input) toShape
        ((st.val input).getD [])) [output] st.val, st.conds⟩
  | .copy _k input outputs =>
      ⟨assignIdx (fun _ => (st.val input).getD []) outputs st.val,
       st.conds⟩
  | .delete _ => st
  | .swap in1 in2 out1 out2 =>
      ⟨assignIdx (fun j => if j = 0 then (st.val in2).getD []
        else (st.val in1).getD []) [out1, out2] st.val, st.conds⟩
  | .stack _k _shape inputs output =>
      ⟨assignIdx (fun _ => stackTab (inputs.map fun w => (st.val w).getD []))
        [output] st.val, st.conds⟩
  | .relu .. | .ppoly .. | .pderiv .. | .facet .. => st

/-- Symbolic forward evaluation along an application list, consuming
one choice per application. -/
noncomputable def symFold (wt : Wire → Option TensorType) :
    SymSt d → List PrimApp → List ℕ → SymSt d
  | st, [], _ => st
  | st, app :: apps, χ => symFold wt (symStep wt st app (χ.headD 0)) apps χ.tail

/-! ## Choice enumeration -/

/-- The choice alternatives one application contributes: which cell
fires, for `cell`; a single dummy choice for everything else. -/
def appChoices : PrimApp → List ℕ
  | .cell schema _ _ => List.range schema.cells.length
  | _ => [0]

/-- All pointwise selections from a list of option lists. -/
def choiceLists : List (List ℕ) → List (List ℕ)
  | [] => [[]]
  | opts :: rest => opts.flatMap fun c => (choiceLists rest).map (c :: ·)

theorem mem_choiceLists : ∀ {L : List (List ℕ)} {χ : List ℕ},
    χ ∈ choiceLists L ↔ List.Forall₂ (· ∈ ·) χ L := by
  intro L
  induction L with
  | nil =>
      intro χ
      show χ ∈ [[]] ↔ _
      rw [List.mem_singleton]
      constructor
      · rintro rfl
        exact List.Forall₂.nil
      · intro h
        cases h
        rfl
  | cons opts rest ih =>
      intro χ
      show χ ∈ opts.flatMap (fun c => (choiceLists rest).map (c :: ·)) ↔ _
      rw [List.mem_flatMap]
      constructor
      · rintro ⟨c, hc, hχ⟩
        obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hχ
        exact List.Forall₂.cons hc (ih.mp hcs)
      · intro h
        cases h with
        | cons hc hrest =>
            exact ⟨_, hc, List.mem_map.mpr ⟨_, ih.mpr hrest, rfl⟩⟩

/-- The choice vectors of an application list. -/
def cellChoices (apps : List PrimApp) : List (List ℕ) :=
  choiceLists (apps.map appChoices)

/-! ## The initial state and the pieces -/

/-- The initial symbolic state: input ports carry the coordinate
polynomials, everything else is unassigned. -/
noncomputable def initSt (d' : ℕ) (ins : Fin d' → Wire) : SymSt d' :=
  ⟨fun w => ((List.finRange d').find? fun i => ins i == w).map
    fun i => [MvPolynomial.X i], []⟩

theorem find?_of_unique {α : Type*} {p : α → Bool} :
    ∀ {l : List α} {a : α}, a ∈ l → p a = true →
      (∀ b ∈ l, p b = true → b = a) → l.find? p = some a := by
  intro l
  induction l with
  | nil =>
      intro a ha
      exact absurd ha List.not_mem_nil
  | cons b l ih =>
      intro a ha hpa huniq
      by_cases hpb : p b = true
      · rw [List.find?_cons_of_pos hpb, huniq b (List.mem_cons_self ..) hpb]
      · rw [List.find?_cons_of_neg (by simpa using hpb)]
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact absurd hpa hpb
        · exact ih ha' hpa
            (fun c hc hpc => huniq c (List.mem_cons_of_mem _ hc) hpc)

theorem initSt_val_ins {d' : ℕ} {ins : Fin d' → Wire}
    (hinj : Function.Injective ins) (i : Fin d') :
    (initSt d' ins).val (ins i) = some [MvPolynomial.X i] := by
  show (((List.finRange d').find? fun i' => ins i' == ins i).map
    fun i' => ([MvPolynomial.X i'] : PTab d')) = _
  rw [find?_of_unique (List.mem_finRange i) (by simp)
    (fun b _ hb => hinj (by simpa using hb))]
  rfl

theorem initSt_val_isSome {d' : ℕ} {ins : Fin d' → Wire} {w : Wire} :
    ((initSt d' ins).val w).isSome ↔ ∃ i, ins i = w := by
  show ((((List.finRange d').find? fun i => ins i == w).map
    fun i => ([MvPolynomial.X i] : PTab d'))).isSome ↔ _
  rw [Option.isSome_map, List.find?_isSome]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, by simpa using hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, List.mem_finRange i, by simp⟩

theorem initSt_val_cases {d' : ℕ} {ins : Fin d' → Wire} {w : Wire}
    {tab : PTab d'} (h : (initSt d' ins).val w = some tab) :
    ∃ i, ins i = w ∧ tab = [MvPolynomial.X i] := by
  replace h : (((List.finRange d').find? fun i => ins i == w).map
    fun i => ([MvPolynomial.X i] : PTab d')) = some tab := h
  obtain ⟨i, hfind, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨i, by simpa using List.find?_some hfind, rfl⟩

/-- The piece one choice vector carves. -/
noncomputable def pieceOf (H : Hypernet) {d' m : ℕ} (ins : Fin d' → Wire)
    (outs : Fin m → Wire) (χ : List ℕ) : PieceData d' m :=
  ⟨(symFold H.wireType (initSt d' ins) H.applications χ).conds,
   fun j => (((symFold H.wireType (initSt d' ins) H.applications χ).val
     (outs j)).getD []).getD 0 0⟩

/-- The finite piece list of a hypernet's interface. -/
noncomputable def hypernetPieces (H : Hypernet) {d' m : ℕ}
    (ins : Fin d' → Wire) (outs : Fin m → Wire) : List (PieceData d' m) :=
  (cellChoices H.applications).map (pieceOf H ins outs)

/-! ## σ-free structural facts of the fold -/

theorem symStep_conds_mono {wt : Wire → Option TensorType} {st : SymSt d}
    {app : PrimApp} {c : ℕ} :
    ∀ q ∈ st.conds, q ∈ (symStep wt st app c).conds := by
  intro q hq
  cases app <;>
    first
      | exact hq
      | exact List.mem_append_left _ hq

theorem symFold_conds_mono {wt : Wire → Option TensorType} :
    ∀ (apps : List PrimApp) (χ : List ℕ) (st : SymSt d),
      ∀ q ∈ st.conds, q ∈ (symFold wt st apps χ).conds
  | [], _, _, _, hq => hq
  | _ :: apps, χ, st, q, hq =>
      symFold_conds_mono apps χ.tail _ q (symStep_conds_mono q hq)

theorem symStep_val_of_not_output {wt : Wire → Option TensorType}
    {st : SymSt d} {app : PrimApp} {c : ℕ} {w : Wire}
    (hw : w ∉ app.outputWires) :
    (symStep wt st app c).val w = st.val w := by
  cases app <;>
    first
      | rfl
      | exact assignIdx_of_not_mem _ _ hw

theorem symFold_val_frozen {wt : Wire → Option TensorType} :
    ∀ (apps : List PrimApp) (χ : List ℕ) (st : SymSt d) (w : Wire),
      (∀ app ∈ apps, w ∉ app.outputWires) →
      (symFold wt st apps χ).val w = st.val w
  | [], _, _, _, _ => rfl
  | app :: apps, χ, st, w, h => by
      rw [show symFold wt st (app :: apps) χ
        = symFold wt (symStep wt st app (χ.headD 0)) apps χ.tail from rfl,
        symFold_val_frozen apps χ.tail _ w
          (fun a ha => h a (List.mem_cons_of_mem _ ha)),
        symStep_val_of_not_output (h app (List.mem_cons_self ..))]

theorem symStep_dom {wt : Wire → Option TensorType} {st : SymSt d}
    {app : PrimApp} (hten : app.isTenBox = true) {c : ℕ} (w : Wire) :
    ((symStep wt st app c).val w).isSome
      ↔ w ∈ app.outputWires ∨ (st.val w).isSome := by
  cases app <;>
    first
      | exact (assignIdx_isSome _ _ _ w)
      | (show (st.val w).isSome ↔ w ∈ ([] : List Wire) ∨ (st.val w).isSome
         simp)
      | exact absurd hten (by simp [PrimApp.isTenBox])

theorem symFold_dom {wt : Wire → Option TensorType} :
    ∀ (apps : List PrimApp) (χ : List ℕ) (st : SymSt d),
      (∀ app ∈ apps, app.isTenBox = true) → ∀ w : Wire,
      ((symFold wt st apps χ).val w).isSome
        ↔ w ∈ apps.flatMap PrimApp.outputWires ∨ (st.val w).isSome
  | [], _, _, _, w => by simp [symFold]
  | app :: apps, χ, st, hten, w => by
      rw [show symFold wt st (app :: apps) χ
        = symFold wt (symStep wt st app (χ.headD 0)) apps χ.tail from rfl,
        symFold_dom apps χ.tail _
          (fun a ha => hten a (List.mem_cons_of_mem _ ha)) w,
        symStep_dom (hten app (List.mem_cons_self ..)) w,
        List.flatMap_cons, List.mem_append]
      tauto

/-- Consumed wires of an application are produced strictly earlier. -/
theorem acyclic_consumed_in_prefix {H : Hypernet}
    {pre rest : List PrimApp} {app : PrimApp}
    (hsplit : H.applications = pre ++ app :: rest) {w : Wire}
    (hw : w ∈ app.inputWires) (hprod : w ∈ H.producedWires) :
    w ∈ pre.flatMap PrimApp.outputWires := by
  obtain ⟨app', happ', hw'⟩ := List.mem_flatMap.mp hprod
  obtain ⟨j, hj, happj⟩ := List.mem_iff_getElem.mp happ'
  have hilen : pre.length < H.applications.length := by
    rw [hsplit, List.length_append]
    simp
  have hi_get : H.applications[(⟨pre.length, hilen⟩
      : Fin H.applications.length)] = app := by
    show H.applications[pre.length]'hilen = app
    rw [List.getElem_of_eq hsplit hilen,
      List.getElem_append_right (Nat.le_refl pre.length)]
    simp
  have happj' : H.applications[(⟨j, hj⟩ : Fin H.applications.length)]
      = app' := happj
  have hji := H.acyclic ⟨pre.length, hilen⟩ w (by rw [hi_get]; exact hw)
    ⟨j, hj⟩ (by rw [happj']; exact hw')
  have hjpre : j < pre.length := hji
  have hj_get : H.applications[(⟨j, hj⟩ : Fin H.applications.length)]
      = pre[j]'hjpre := by
    show H.applications[j]'hj = pre[j]'hjpre
    rw [List.getElem_of_eq hsplit hj]
    exact List.getElem_append_left ..
  refine List.mem_flatMap.mpr ⟨pre[j]'hjpre, List.getElem_mem hjpre, ?_⟩
  rw [← hj_get, happj']
  exact hw'

/-- A `Nodup` flat-map has `Nodup` blocks. -/
theorem nodup_of_flatMap_nodup {α β : Type*} {f : α → List β} :
    ∀ {l : List α}, (l.flatMap f).Nodup → ∀ a ∈ l, (f a).Nodup := by
  intro l
  induction l with
  | nil =>
      intro _ a ha
      exact absurd ha List.not_mem_nil
  | cons b l ih =>
      intro h a ha
      rw [List.flatMap_cons] at h
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact (List.nodup_append.mp h).1
      · exact ih (List.nodup_append.mp h).2.1 a ha'

/-- Zero is in every kind's member set. -/
theorem memK_zero (k : Kind) : k.MemK 0 := by
  cases k
  case bool => exact Or.inl rfl
  case int => exact Rat.den_ofNat
  case rat => trivial
  case f16 => exact FloatFmt.rep_zero _
  case bf16 => exact FloatFmt.rep_zero _
  case f32 => exact FloatFmt.rep_zero _
  case f64 => exact FloatFmt.rep_zero _

/-! ## Type-consistency bridges for `contract` -/

theorem contract_output_ty {wt : Wire → Option TensorType} {δ : Dtype}
    {r : RoundMode} {inputs : List Wire} {output : Wire}
    {inputRanks : List ℕ} {outputRank : ℕ}
    {pat : ContractPattern inputRanks outputRank}
    (htc : (PrimApp.contract δ r inputs output inputRanks outputRank
      pat).TypeConsistent wt) :
    wt output = some ⟨pat.outShape, δ⟩ := by
  obtain ⟨-, -, ⟨τ, hτ, hdt, hrk⟩, -, hout⟩ := htc
  have hsh : τ.shape = pat.outShape := by
    refine List.ext_getElem ?_ ?_
    · rw [show pat.outShape.length = outputRank from by
        rw [ContractPattern.outShape, List.length_ofFn]]
      exact hrk
    · intro i h₁ h₂
      have hi : i < outputRank := by
        rw [← hrk]
        exact h₁
      obtain ⟨τ', hτ', hgd⟩ := hout ⟨i, hi⟩
      have hττ : τ' = τ := Option.some.inj (hτ'.symm.trans hτ)
      rw [hττ] at hgd
      have hos : (ContractPattern.outShape pat)[i]'h₂
          = pat.indexExtent (pat.outputBinding ⟨i, hi⟩) := by
        show (List.ofFn (fun a =>
          pat.indexExtent (pat.outputBinding a)))[i]'(by
            rw [List.length_ofFn]; exact hi) = _
        rw [List.getElem_ofFn]
      rw [← Shape.getD_eq_getElem' τ.shape 0 h₁, hgd, hos]
  have hτeq : τ = ⟨pat.outShape, δ⟩ := by
    obtain ⟨tsh, tdt⟩ := τ
    simp only [TensorType.mk.injEq]
    exact ⟨hsh, hdt⟩
  rw [← hτeq]
  exact hτ

theorem tensorType_eq_of {τ : TensorType} {sh : Shape} {dt : Dtype}
    (hs : τ.shape = sh) (hd : τ.dtype = dt) : τ = ⟨sh, dt⟩ := by
  obtain ⟨a, b⟩ := τ
  simp only [TensorType.mk.injEq]
  exact ⟨hs, hd⟩

theorem RoundMode.isExact_eq {r : RoundMode} (h : r.isExact = true) :
    r = .exact := by
  cases r <;> first | rfl | exact absurd h (by simp [RoundMode.isExact])

theorem contract_input_ty {wt : Wire → Option TensorType} {δ : Dtype}
    {r : RoundMode} {inputs : List Wire} {output : Wire}
    {inputRanks : List ℕ} {outputRank : ℕ}
    {pat : ContractPattern inputRanks outputRank}
    (htc : (PrimApp.contract δ r inputs output inputRanks outputRank
      pat).TypeConsistent wt)
    {kk : ℕ} (hk : kk < inputs.length) :
    wt (inputs[kk]'hk)
      = some ⟨wireShapeOf wt (inputs[kk]'hk), δ⟩ := by
  obtain ⟨hlen, hin, -, -, -⟩ := htc
  have hkr : kk < inputRanks.length := by rw [← hlen]; exact hk
  have hpair : (inputs[kk]'hk, inputRanks[kk]'hkr) ∈ inputs.zip inputRanks := by
    have hkz : kk < (inputs.zip inputRanks).length := by
      rw [List.length_zip, hlen, Nat.min_self]
      exact hkr
    have := List.getElem_mem hkz
    rwa [List.getElem_zip] at this
  obtain ⟨τ, hτ, hdt, -⟩ := hin _ hpair
  rw [hτ, wireShapeOf_some hτ]
  exact congrArg some (tensorType_eq_of rfl hdt)

theorem contract_input_rank {wt : Wire → Option TensorType} {δ : Dtype}
    {r : RoundMode} {inputs : List Wire} {output : Wire}
    {inputRanks : List ℕ} {outputRank : ℕ}
    {pat : ContractPattern inputRanks outputRank}
    (htc : (PrimApp.contract δ r inputs output inputRanks outputRank
      pat).TypeConsistent wt)
    (k : Fin inputRanks.length) :
    ((inputs.map (wireShapeOf wt)).getD k.val []).length
      = inputRanks.get k := by
  obtain ⟨hlen, hin, -, -, -⟩ := htc
  have hk : k.val < inputs.length := by rw [hlen]; exact k.isLt
  have hkm : k.val < (inputs.map (wireShapeOf wt)).length := by
    rw [List.length_map]
    exact hk
  rw [Shape.getD_eq_getElem' _ _ hkm, List.getElem_map]
  have hpair : (inputs[k.val]'hk, inputRanks[k.val]'k.isLt)
      ∈ inputs.zip inputRanks := by
    have hkz : k.val < (inputs.zip inputRanks).length := by
      rw [List.length_zip, hlen, Nat.min_self]
      exact k.isLt
    have := List.getElem_mem hkz
    rwa [List.getElem_zip] at this
  obtain ⟨τ, hτ, -, hrk⟩ := hin _ hpair
  rw [wireShapeOf_some hτ]
  exact hrk

theorem contract_input_extent {wt : Wire → Option TensorType} {δ : Dtype}
    {r : RoundMode} {inputs : List Wire} {output : Wire}
    {inputRanks : List ℕ} {outputRank : ℕ}
    {pat : ContractPattern inputRanks outputRank}
    (htc : (PrimApp.contract δ r inputs output inputRanks outputRank
      pat).TypeConsistent wt)
    (k : Fin inputRanks.length) (a : Fin (inputRanks.get k)) :
    ((inputs.map (wireShapeOf wt)).getD k.val []).getD a.val 0
      = pat.indexExtent (pat.inputBinding k a) := by
  obtain ⟨hlen, -, -, hbind, -⟩ := htc
  have hk : k.val < inputs.length := by rw [hlen]; exact k.isLt
  have hkm : k.val < (inputs.map (wireShapeOf wt)).length := by
    rw [List.length_map]
    exact hk
  obtain ⟨τ, hτ, hgd⟩ := hbind k a
  have hgd0 : inputs.getD k.val 0 = inputs[k.val]'hk :=
    Shape.getD_eq_getElem' _ _ hk
  rw [hgd0] at hτ
  rw [Shape.getD_eq_getElem' _ _ hkm, List.getElem_map,
    wireShapeOf_some hτ]
  exact hgd

/-- The single-step forward lemma: an admissible valuation of one
ten-box application determines a choice under which the symbolic step
tracks it — reads, lengths, and emitted conditions. -/
theorem step_mp {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {app : PrimApp} (hsem : app.SemOk σ)
    (htc : app.TypeConsistent H.wireType)
    (htb : app.isTenBox = true) (hbqa : app.exactBQ = true)
    (hsata : app.saturating) (st : SymSt d)
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
  have hres : ∀ w ∈ app.inputWires, ∃ tab, st.val w = some tab ∧
      readsTab σ x w tab ∧ ∃ τ, H.wireType w = some τ ∧
      tab.length = τ.shape.totalSize := by
    intro w hw
    obtain ⟨tab, htab⟩ := Option.isSome_iff_exists.mp (hcons w hw)
    exact ⟨tab, htab, hreads w tab htab, hlens w tab htab⟩
  cases app with
  | const ty cv out =>
      refine ⟨0, List.mem_cons_self .., ?_, ?_, fun h => h⟩
      · intro w tab htab
        rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
        · have hj0 : j = 0 := by simpa using hj
          subst hj0
          have hwout : w = out := by simpa using hwj
          subst hwout
          exact const_semOk_reads hsem hbqa
        · exact hreads w tab hbase
      · intro w tab htab
        rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
        · have hj0 : j = 0 := by simpa using hj
          subst hj0
          have hwout : w = out := by simpa using hwj
          subst hwout
          refine ⟨ty, htc, ?_⟩
          rw [List.length_map, TensorValue.length_entriesQ]
        · exact hlens w tab hbase
  | contract δ r inputs output ir orank pat =>
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
      have hcr := contract_semOk_reads hsem hsata hto hlen₁ hlen₂ hlen₃
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
  | cast δfrom δto r shape input output =>
      have hbqa' : δfrom.isBQ = true ∧ δto.isBQ = true ∧ r.isExact = true := by
        simpa [PrimApp.exactBQ, Bool.and_assoc] using hbqa
      obtain ⟨hbqf, hbqt, hexact⟩ := hbqa'
      obtain rfl := RoundMode.isExact_eq hexact
      obtain ⟨hti, hto⟩ := htc
      obtain ⟨tab, htab, hrd, τ, hτ, htlen⟩ :=
        hres input (List.mem_cons_self ..)
      have hτeq : τ = ⟨shape, δfrom⟩ := Option.some.inj (hτ.symm.trans hti)
      have hlen : tab.length = shape.totalSize := by
        rw [htlen, hτeq]
      have hcc := cast_semOk_reads hsem hto hbqt hlen hrd
      refine ⟨0, List.mem_cons_self .., ?_, ?_, ?_⟩
      · intro w tab' htab'
        rcases assignIdx_cases _ _ _ _ htab' with ⟨j, hj, hwj, rfl⟩ | hbase
        · have hj0 : j = 0 := by simpa using hj
          subst hj0
          have hwout : w = output := by simpa using hwj
          subst hwout
          rw [show (st.val input).getD [] = tab from by rw [htab]; rfl]
          exact hcc.1
        · exact hreads w tab' hbase
      · intro w tab' htab'
        rcases assignIdx_cases _ _ _ _ htab' with ⟨j, hj, hwj, rfl⟩ | hbase
        · have hj0 : j = 0 := by simpa using hj
          subst hj0
          have hwout : w = output := by simpa using hwj
          subst hwout
          refine ⟨⟨shape, δto⟩, hto, ?_⟩
          rw [show (st.val input).getD [] = tab from by rw [htab]; rfl]
          exact hlen
        · exact hlens w tab' hbase
      · intro hch
        refine CondsHold.append.mpr ⟨hch, ?_⟩
        split
        · next hB =>
            subst hB
            refine condsHold_boolConds_iff.mpr ?_
            rw [show (st.val input).getD [] = tab from by rw [htab]; rfl]
            exact hcc.2 rfl
        · intro q hq
          exact absurd hq List.not_mem_nil
  | cell schema input outputs =>
      obtain ⟨⟨δin, hti⟩, hcount, houts⟩ := htc
      obtain ⟨tab, htab, hrd, τ, hτ, htlen⟩ :=
        hres input (List.mem_cons_self ..)
      have hτeq : τ = ⟨[schema.ambDim], δin⟩ :=
        Option.some.inj (hτ.symm.trans hti)
      have hlen : tab.length = schema.ambDim := by
        rw [htlen, hτeq]
        show Shape.totalSize [schema.ambDim] = schema.ambDim
        rw [Shape.totalSize_cons, Shape.totalSize_nil, Nat.mul_one]
      have hcc := cell_semOk_reads hsem hti houts hlen hrd
      obtain ⟨hdisj, k, hcondk, honehot⟩ := hcc
      refine ⟨k.val, ?_, ?_, ?_, ?_⟩
      · show k.val ∈ appChoices (.cell schema input outputs)
        exact List.mem_range.mpr k.isLt
      · intro w tab' htab'
        rcases assignIdx_cases _ _ _ _ htab' with ⟨j, hj, hwj, rfl⟩ | hbase
        · subst hwj
          exact honehot j hj
        · exact hreads w tab' hbase
      · intro w tab' htab'
        rcases assignIdx_cases _ _ _ _ htab' with ⟨j, hj, hwj, rfl⟩ | hbase
        · subst hwj
          refine ⟨⟨[], Dtype.B⟩, houts _ (List.getElem_mem hj), ?_⟩
          rw [oneHotTab_length]
          rfl
        · exact hlens w tab' hbase
      · intro hch
        refine CondsHold.append.mpr ⟨hch, ?_⟩
        rw [dif_pos k.isLt]
        rw [show (st.val input).getD [] = tab from by rw [htab]; rfl]
        rw [show (⟨k.val, k.isLt⟩ : Fin schema.cells.length) = k from
          Fin.ext rfl]
        exact hcondk
  | reshape newShape input output =>
      obtain ⟨τ, hτi, hsz, hτo⟩ := htc
      obtain ⟨tab, htab, hrd, τ', hτ', htlen⟩ :=
        hres input (List.mem_cons_self ..)
      have hττ : τ' = τ := Option.some.inj (hτ'.symm.trans hτi)
      refine ⟨0, List.mem_cons_self .., ?_, ?_, fun h => h⟩
      · intro w tab' htab'
        rcases assignIdx_cases _ _ _ _ htab' with ⟨j, hj, hwj, rfl⟩ | hbase
        · have hj0 : j = 0 := by simpa using hj
          subst hj0
          have hwout : w = output := by simpa using hwj
          subst hwout
          rw [show (st.val input).getD [] = tab from by rw [htab]; rfl]
          exact reshape_semOk_reads hsem hrd
        · exact hreads w tab' hbase
      · intro w tab' htab'
        rcases assignIdx_cases _ _ _ _ htab' with ⟨j, hj, hwj, rfl⟩ | hbase
        · have hj0 : j = 0 := by simpa using hj
          subst hj0
          have hwout : w = output := by simpa using hwj
          subst hwout
          refine ⟨⟨newShape, τ.dtype⟩, hτo, ?_⟩
          rw [show (st.val input).getD [] = tab from by rw [htab]; rfl,
            htlen, hττ]
          exact hsz
        · exact hlens w tab' hbase
  | broadcast toShape input output =>
      obtain ⟨τ, hτi, hbc, hτo⟩ := htc
      obtain ⟨tab, htab, hrd, τ', hτ', htlen⟩ :=
        hres input (List.mem_cons_self ..)
      have hττ : τ' = τ := Option.some.inj (hτ'.symm.trans hτi)
      rw [hττ] at htlen
      refine ⟨0, List.mem_cons_self .., ?_, ?_, fun h => h⟩
      · intro w tab' htab'
        rcases assignIdx_cases _ _ _ _ htab' with ⟨j, hj, hwj, rfl⟩ | hbase
        · have hj0 : j = 0 := by simpa using hj
          subst hj0
          have hwout : w = output := by simpa using hwj
          subst hwout
          rw [show (st.val input).getD [] = tab from by rw [htab]; rfl,
            wireShapeOf_some hτi]
          exact broadcast_semOk_reads hsem hτi hτo hbc htlen hrd
        · exact hreads w tab' hbase
      · intro w tab' htab'
        rcases assignIdx_cases _ _ _ _ htab' with ⟨j, hj, hwj, rfl⟩ | hbase
        · have hj0 : j = 0 := by simpa using hj
          subst hj0
          have hwout : w = output := by simpa using hwj
          subst hwout
          exact ⟨⟨toShape, τ.dtype⟩, hτo, broadcastTab_length⟩
        · exact hlens w tab' hbase
  | copy kk input outputs =>
      obtain ⟨hcount, τ, hτi, houts⟩ := htc
      obtain ⟨tab, htab, hrd, τ', hτ', htlen⟩ :=
        hres input (List.mem_cons_self ..)
      have hττ : τ' = τ := Option.some.inj (hτ'.symm.trans hτi)
      rw [hττ] at htlen
      have hcp := copy_semOk_reads hsem hrd
      refine ⟨0, List.mem_cons_self .., ?_, ?_, fun h => h⟩
      · intro w tab' htab'
        rcases assignIdx_cases _ _ _ _ htab' with ⟨j, hj, hwj, rfl⟩ | hbase
        · subst hwj
          rw [show (st.val input).getD [] = tab from by rw [htab]; rfl]
          exact hcp _ (List.getElem_mem hj)
        · exact hreads w tab' hbase
      · intro w tab' htab'
        rcases assignIdx_cases _ _ _ _ htab' with ⟨j, hj, hwj, rfl⟩ | hbase
        · subst hwj
          refine ⟨τ, houts _ (List.getElem_mem hj), ?_⟩
          rw [show (st.val input).getD [] = tab from by rw [htab]; rfl]
          exact htlen
        · exact hlens w tab' hbase
  | delete input =>
      exact ⟨0, List.mem_cons_self .., hreads, hlens, fun h => h⟩
  | swap in1 in2 out1 out2 =>
      obtain ⟨hs1, hs2, ho1, ho2⟩ := htc
      obtain ⟨tab1, htab1, hrd1, τ1, hτ1, htlen1⟩ :=
        hres in1 (List.mem_cons_self ..)
      obtain ⟨tab2, htab2, hrd2, τ2, hτ2, htlen2⟩ :=
        hres in2 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hsw := swap_semOk_reads hsem hrd1 hrd2
      refine ⟨0, List.mem_cons_self .., ?_, ?_, fun h => h⟩
      · intro w tab' htab'
        rcases assignIdx_cases _ _ _ _ htab' with ⟨j, hj, hwj, rfl⟩ | hbase
        · match j, hj with
          | 0, _ =>
              have hwout : w = out1 := by simpa using hwj
              subst hwout
              show readsTab σ x _
                (if (0 : ℕ) = 0 then (st.val in2).getD []
                  else (st.val in1).getD [])
              rw [if_pos rfl,
                show (st.val in2).getD [] = tab2 from by rw [htab2]; rfl]
              exact hsw.1
          | 1, _ =>
              have hwout : w = out2 := by simpa using hwj
              subst hwout
              show readsTab σ x _
                (if (1 : ℕ) = 0 then (st.val in2).getD []
                  else (st.val in1).getD [])
              rw [if_neg (by omega),
                show (st.val in1).getD [] = tab1 from by rw [htab1]; rfl]
              exact hsw.2
        · exact hreads w tab' hbase
      · intro w tab' htab'
        rcases assignIdx_cases _ _ _ _ htab' with ⟨j, hj, hwj, rfl⟩ | hbase
        · match j, hj with
          | 0, _ =>
              have hwout : w = out1 := by simpa using hwj
              subst hwout
              refine ⟨τ2, by rw [ho1]; exact hτ2, ?_⟩
              show (if (0 : ℕ) = 0 then (st.val in2).getD []
                else (st.val in1).getD []).length = _
              rw [if_pos rfl,
                show (st.val in2).getD [] = tab2 from by rw [htab2]; rfl]
              exact htlen2
          | 1, _ =>
              have hwout : w = out2 := by simpa using hwj
              subst hwout
              refine ⟨τ1, by rw [ho2]; exact hτ1, ?_⟩
              show (if (1 : ℕ) = 0 then (st.val in2).getD []
                else (st.val in1).getD []).length = _
              rw [if_neg (by omega),
                show (st.val in1).getD [] = tab1 from by rw [htab1]; rfl]
              exact htlen1
        · exact hlens w tab' hbase
  | stack kk shape inputs output =>
      obtain ⟨hcount, τ, hτo, hsh, hins⟩ := htc
      have htabres : ∀ (j : ℕ) (hj : j < inputs.length),
          st.val (inputs[j]'hj)
            = some ((inputs.map fun w => (st.val w).getD [])[j]'(by
                rw [List.length_map]; exact hj))
          ∧ ((inputs.map fun w => (st.val w).getD [])[j]'(by
                rw [List.length_map]; exact hj)).length
            = shape.totalSize := by
        intro j hj
        obtain ⟨tab, htab, -, τ', hτ', htlen⟩ :=
          hres _ (List.getElem_mem hj)
        have hτeq : τ' = ⟨shape, τ.dtype⟩ := Option.some.inj
          (hτ'.symm.trans (hins _ (List.getElem_mem hj)))
        have hget : (inputs.map fun w => (st.val w).getD [])[j]'(by
            rw [List.length_map]; exact hj) = tab := by
          rw [show (inputs.map fun w => (st.val w).getD [])[j]'(by
            rw [List.length_map]; exact hj)
            = (st.val (inputs[j]'hj)).getD [] from List.getElem_map ..,
            htab]
          rfl
        rw [hget]
        refine ⟨htab, ?_⟩
        rw [htlen, hτeq]
      have hst := stack_semOk_reads hsem
        (show H.wireType output = some ⟨kk :: shape, τ.dtype⟩ from by
          rw [hτo]
          exact congrArg some (tensorType_eq_of hsh rfl)) hcount
        (List.length_map ..)
        (fun j hj => (htabres j (by rw [List.length_map] at hj; exact hj)).2)
        (fun j hj => hreads _ _ (htabres j hj).1)
      refine ⟨0, List.mem_cons_self .., ?_, ?_, fun h => h⟩
      · intro w tab' htab'
        rcases assignIdx_cases _ _ _ _ htab' with ⟨j, hj, hwj, rfl⟩ | hbase
        · have hj0 : j = 0 := by simpa using hj
          subst hj0
          have hwout : w = output := by simpa using hwj
          subst hwout
          exact hst
        · exact hreads w tab' hbase
      · intro w tab' htab'
        rcases assignIdx_cases _ _ _ _ htab' with ⟨j, hj, hwj, rfl⟩ | hbase
        · have hj0 : j = 0 := by simpa using hj
          subst hj0
          have hwout : w = output := by simpa using hwj
          subst hwout
          refine ⟨τ, hτo, ?_⟩
          rw [stackTab_length (P := shape.totalSize)
            (fun t ht => by
              obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
              exact (htabres j (by rw [List.length_map] at hj; exact hj)).2),
            List.length_map, hcount, hsh, Shape.totalSize_cons]
        · exact hlens w tab' hbase
  | relu shape input output => exact absurd htb (by simp [PrimApp.isTenBox])
  | ppoly nv co inputs output =>
      exact absurd htb (by simp [PrimApp.isTenBox])
  | pderiv shape ax input output =>
      exact absurd htb (by simp [PrimApp.isTenBox])
  | facet shape ax hi input output =>
      exact absurd htb (by simp [PrimApp.isTenBox])

/-- The forward fold: an admissible valuation selects a choice vector
whose symbolic fold it reads throughout. -/
theorem fold_mp {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {ins : Fin d → Wire}
    (hadm : σ.Admissible) (hten : H.TenBoxOnly) (hbq : H.ExactBQ)
    (hsat : H.SaturatingContracts) (hic : H.InterfaceClosed ins) :
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
      obtain ⟨c, hc, hreads', hlens', hconds'⟩ := step_mp
        (hadm app happ_mem) (H.typeConsistent app happ_mem) htb
        (hbq app happ_mem) (hsat app happ_mem) st hreads hlens hcons
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


/-! ## The backward direction: freezing, well-formedness, admissibility -/

/-- Cell schemas are interior-disjoint, per application. -/
def PrimApp.cellDisjoint : PrimApp → Prop
  | .cell schema _ _ => schema.CellIntDisjoint
  | _ => True

/-- No application consumes its own output. -/
theorem acyclic_input_not_output {H : Hypernet}
    {pre rest : List PrimApp} {app : PrimApp}
    (hsplit : H.applications = pre ++ app :: rest) :
    ∀ w ∈ app.inputWires, w ∉ app.outputWires := by
  intro w hw hw'
  have hilen : pre.length < H.applications.length := by
    rw [hsplit, List.length_append]
    simp
  have hi_get : H.applications[(⟨pre.length, hilen⟩
      : Fin H.applications.length)] = app := by
    show H.applications[pre.length]'hilen = app
    rw [List.getElem_of_eq hsplit hilen,
      List.getElem_append_right (Nat.le_refl pre.length)]
    simp
  have := H.acyclic ⟨pre.length, hilen⟩ w (by rw [hi_get]; exact hw)
    ⟨pre.length, hilen⟩ (by rw [hi_get]; exact hw')
  exact absurd this (lt_irrefl _)

/-- Wires produced by the prefix (or the head) are not produced again
by the suffix. -/
theorem produced_prefix_not_in_post {H : Hypernet}
    {pre post : List PrimApp} {app : PrimApp}
    (hsplit : H.applications = pre ++ app :: post) {w : Wire}
    (hw : w ∈ (pre ++ [app]).flatMap PrimApp.outputWires) :
    ∀ app' ∈ post, w ∉ app'.outputWires := by
  intro app' happ' hw'
  have hnd := H.linearity.2
  have hsplit2 : H.applications = (pre ++ [app]) ++ post := by
    rw [hsplit, List.append_assoc]
    rfl
  rw [hsplit2, List.flatMap_append] at hnd
  exact (List.nodup_append.mp hnd).2.2 w hw w
    (List.mem_flatMap.mpr ⟨app', happ', hw'⟩) rfl

/-- Wires in the (inputs ∪ prefix)-domain are untouched by the suffix. -/
theorem dom_not_in_post {H : Hypernet} {ins : Fin d → Wire}
    (hic : H.InterfaceClosed ins) {pre post : List PrimApp} {app : PrimApp}
    (hsplit : H.applications = pre ++ app :: post) {w : Wire}
    (hw : (∃ i, ins i = w) ∨ w ∈ (pre ++ [app]).flatMap PrimApp.outputWires) :
    ∀ app' ∈ post, w ∉ app'.outputWires := by
  intro app' happ' hw'
  rcases hw with ⟨i, rfl⟩ | hpre
  · refine hic.2.1 i (List.mem_flatMap.mpr ⟨app', ?_, hw'⟩)
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ happ')
  · exact produced_prefix_not_in_post hsplit hpre app' happ' hw'

theorem getD_mem_or_eq {α : Type*} (l : List α) (n : ℕ) (dflt : α) :
    l.getD n dflt ∈ l ∨ l.getD n dflt = dflt := by
  rcases Nat.lt_or_ge n l.length with h | h
  · rw [Shape.getD_eq_getElem' l dflt h]
    exact Or.inl (List.getElem_mem h)
  · right
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
    rfl

/-- The step preserves table lengths (σ-free). -/
theorem step_lens {H : Hypernet} {app : PrimApp}
    (htc : app.TypeConsistent H.wireType) (htb : app.isTenBox = true)
    (st : SymSt d) (c : ℕ)
    (hlens : ∀ w tab, st.val w = some tab →
      ∃ τ, H.wireType w = some τ ∧ tab.length = τ.shape.totalSize)
    (hcons : ∀ w ∈ app.inputWires, (st.val w).isSome) :
    ∀ w tab, (symStep H.wireType st app c).val w = some tab →
      ∃ τ, H.wireType w = some τ ∧ tab.length = τ.shape.totalSize := by
  have hresL : ∀ w ∈ app.inputWires, ∃ tab, st.val w = some tab ∧
      ∃ τ, H.wireType w = some τ ∧ tab.length = τ.shape.totalSize := by
    intro w hw
    obtain ⟨tab, htab⟩ := Option.isSome_iff_exists.mp (hcons w hw)
    exact ⟨tab, htab, hlens w tab htab⟩
  cases app with
  | const ty cv out =>
      intro w tab htab
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · have hj0 : j = 0 := by simpa using hj
        subst hj0
        have hwout : w = out := by simpa using hwj
        subst hwout
        refine ⟨ty, htc, ?_⟩
        rw [List.length_map, TensorValue.length_entriesQ]
      · exact hlens w tab hbase
  | contract δ r inputs output ir orank pat =>
      intro w tab htab
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · have hj0 : j = 0 := by simpa using hj
        subst hj0
        have hwout : w = output := by simpa using hwj
        subst hwout
        exact ⟨⟨pat.outShape, δ⟩, contract_output_ty htc, contractTab_length⟩
      · exact hlens w tab hbase
  | cast δfrom δto r shape input output =>
      obtain ⟨hti, hto⟩ := htc
      obtain ⟨tabi, htabi, τ', hτ', htlen⟩ :=
        hresL input (List.mem_cons_self ..)
      have hτeq : τ' = ⟨shape, δfrom⟩ := Option.some.inj (hτ'.symm.trans hti)
      intro w tab htab
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · have hj0 : j = 0 := by simpa using hj
        subst hj0
        have hwout : w = output := by simpa using hwj
        subst hwout
        refine ⟨⟨shape, δto⟩, hto, ?_⟩
        rw [show (st.val input).getD [] = tabi from by rw [htabi]; rfl,
          htlen, hτeq]
      · exact hlens w tab hbase
  | cell schema input outputs =>
      obtain ⟨⟨δin, hti⟩, hcount, houts⟩ := htc
      intro w tab htab
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · subst hwj
        refine ⟨⟨[], Dtype.B⟩, houts _ (List.getElem_mem hj), ?_⟩
        rw [oneHotTab_length]
        rfl
      · exact hlens w tab hbase
  | reshape newShape input output =>
      obtain ⟨τ, hτi, hsz, hτo⟩ := htc
      obtain ⟨tabi, htabi, τ', hτ', htlen⟩ :=
        hresL input (List.mem_cons_self ..)
      have hττ : τ' = τ := Option.some.inj (hτ'.symm.trans hτi)
      intro w tab htab
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · have hj0 : j = 0 := by simpa using hj
        subst hj0
        have hwout : w = output := by simpa using hwj
        subst hwout
        refine ⟨⟨newShape, τ.dtype⟩, hτo, ?_⟩
        rw [show (st.val input).getD [] = tabi from by rw [htabi]; rfl,
          htlen, hττ]
        exact hsz
      · exact hlens w tab hbase
  | broadcast toShape input output =>
      obtain ⟨τ, hτi, hbc, hτo⟩ := htc
      intro w tab htab
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · have hj0 : j = 0 := by simpa using hj
        subst hj0
        have hwout : w = output := by simpa using hwj
        subst hwout
        exact ⟨⟨toShape, τ.dtype⟩, hτo, broadcastTab_length⟩
      · exact hlens w tab hbase
  | copy kk input outputs =>
      obtain ⟨hcount, τ, hτi, houts⟩ := htc
      obtain ⟨tabi, htabi, τ', hτ', htlen⟩ :=
        hresL input (List.mem_cons_self ..)
      have hττ : τ' = τ := Option.some.inj (hτ'.symm.trans hτi)
      intro w tab htab
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · subst hwj
        refine ⟨τ, houts _ (List.getElem_mem hj), ?_⟩
        rw [show (st.val input).getD [] = tabi from by rw [htabi]; rfl,
          htlen, hττ]
      · exact hlens w tab hbase
  | delete input =>
      exact hlens
  | swap in1 in2 out1 out2 =>
      obtain ⟨hs1, hs2, ho1, ho2⟩ := htc
      obtain ⟨tab1, htab1, τ1, hτ1, htlen1⟩ :=
        hresL in1 (List.mem_cons_self ..)
      obtain ⟨tab2, htab2, τ2, hτ2, htlen2⟩ :=
        hresL in2 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      intro w tab htab
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · match j, hj with
        | 0, _ =>
            subst hwj
            refine ⟨τ2, by rw [ho1]; exact hτ2, ?_⟩
            show (if (0 : ℕ) = 0 then (st.val in2).getD []
              else (st.val in1).getD []).length = _
            rw [if_pos rfl,
              show (st.val in2).getD [] = tab2 from by rw [htab2]; rfl]
            exact htlen2
        | 1, _ =>
            subst hwj
            refine ⟨τ1, by rw [ho2]; exact hτ1, ?_⟩
            show (if (1 : ℕ) = 0 then (st.val in2).getD []
              else (st.val in1).getD []).length = _
            rw [if_neg (by omega),
              show (st.val in1).getD [] = tab1 from by rw [htab1]; rfl]
            exact htlen1
      · exact hlens w tab hbase
  | stack kk shape inputs output =>
      obtain ⟨hcount, τ, hτo, hsh, hins⟩ := htc
      have htabres : ∀ (j : ℕ) (hj : j < inputs.length),
          ((inputs.map fun w => (st.val w).getD [])[j]'(by
            rw [List.length_map]; exact hj)).length = shape.totalSize := by
        intro j hj
        obtain ⟨tab, htab, τ', hτ', htlen⟩ := hresL _ (List.getElem_mem hj)
        have hτeq : τ' = ⟨shape, τ.dtype⟩ := Option.some.inj
          (hτ'.symm.trans (hins _ (List.getElem_mem hj)))
        rw [show (inputs.map fun w => (st.val w).getD [])[j]'(by
          rw [List.length_map]; exact hj)
          = (st.val (inputs[j]'hj)).getD [] from List.getElem_map ..,
          htab]
        show tab.length = _
        rw [htlen, hτeq]
      intro w tab htab
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · have hj0 : j = 0 := by simpa using hj
        subst hj0
        have hwout : w = output := by simpa using hwj
        subst hwout
        refine ⟨τ, hτo, ?_⟩
        rw [stackTab_length (P := shape.totalSize)
          (fun t ht => by
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
            exact htabres j (by rw [List.length_map] at hj; exact hj)),
          List.length_map, hcount, hsh, Shape.totalSize_cons]
      · exact hlens w tab hbase
  | relu shape input output => exact absurd htb (by simp [PrimApp.isTenBox])
  | ppoly nv co inputs output =>
      exact absurd htb (by simp [PrimApp.isTenBox])
  | pderiv shape ax input output =>
      exact absurd htb (by simp [PrimApp.isTenBox])
  | facet shape ax hi input output =>
      exact absurd htb (by simp [PrimApp.isTenBox])

/-- The step preserves carrier validity at the evaluation point,
given the step's conditions hold there (σ-free). -/
theorem step_memK {H : Hypernet} {x : Fin d → ℚ} {app : PrimApp}
    (htc : app.TypeConsistent H.wireType) (htb : app.isTenBox = true)
    (hbqa : app.exactBQ = true) (st : SymSt d) (c : ℕ)
    (hmemk : ∀ w tab, st.val w = some tab → ∀ τ, H.wireType w = some τ →
      ∀ p ∈ tab, τ.dtype.kind.MemK (MvPolynomial.eval x p) ∧
        (τ.dtype.sign = .nn → 0 ≤ MvPolynomial.eval x p))
    (hcons : ∀ w ∈ app.inputWires, (st.val w).isSome)
    (hcond : CondsHold x (symStep H.wireType st app c).conds) :
    ∀ w tab, (symStep H.wireType st app c).val w = some tab →
      ∀ τ, H.wireType w = some τ →
      ∀ p ∈ tab, τ.dtype.kind.MemK (MvPolynomial.eval x p) ∧
        (τ.dtype.sign = .nn → 0 ≤ MvPolynomial.eval x p) := by
  have hresM : ∀ w ∈ app.inputWires, ∃ tab, st.val w = some tab ∧
      ∀ τ, H.wireType w = some τ →
      ∀ p ∈ tab, τ.dtype.kind.MemK (MvPolynomial.eval x p) ∧
        (τ.dtype.sign = .nn → 0 ≤ MvPolynomial.eval x p) := by
    intro w hw
    obtain ⟨tab, htab⟩ := Option.isSome_iff_exists.mp (hcons w hw)
    exact ⟨tab, htab, hmemk w tab htab⟩
  cases app with
  | const ty cv out =>
      intro w tab htab τ hτ p hp
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · have hj0 : j = 0 := by simpa using hj
        subst hj0
        have hwout : w = out := by simpa using hwj
        subst hwout
        have hτeq : τ = ty := Option.some.inj (hτ.symm.trans htc)
        subst hτeq
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        rw [eval_C]
        exact TensorValue.entriesQ_memK (Dtype.isBQ_ext hbqa) cv q hq
      · exact hmemk w tab hbase τ hτ p hp
  | contract δ r inputs output ir orank pat =>
      have hbqa' : δ.isBQ = true ∧ r.isExact = true := by
        simpa [PrimApp.exactBQ] using hbqa
      intro w tab htab τ hτ p hp
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · have hj0 : j = 0 := by simpa using hj
        subst hj0
        have hwout : w = output := by simpa using hwj
        subst hwout
        have hτeq : τ = ⟨pat.outShape, δ⟩ :=
          Option.some.inj (hτ.symm.trans (contract_output_ty htc))
        subst hτeq
        refine valueSetBQ (Dtype.isBQ_cases hbqa'.1) ?_
        intro hB
        have hc2 := (CondsHold.append.mp hcond).2
        rw [hB, if_pos rfl] at hc2
        exact condsHold_boolConds_iff.mp hc2 p hp
      · exact hmemk w tab hbase τ hτ p hp
  | cast δfrom δto r shape input output =>
      have hbqa' : δfrom.isBQ = true ∧ δto.isBQ = true ∧ r.isExact = true := by
        simpa [PrimApp.exactBQ, Bool.and_assoc] using hbqa
      obtain ⟨hti, hto⟩ := htc
      intro w tab htab τ hτ p hp
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · have hj0 : j = 0 := by simpa using hj
        subst hj0
        have hwout : w = output := by simpa using hwj
        subst hwout
        have hτeq : τ = ⟨shape, δto⟩ := Option.some.inj (hτ.symm.trans hto)
        subst hτeq
        refine valueSetBQ (Dtype.isBQ_cases hbqa'.2.1) ?_
        intro hB
        have hc2 := (CondsHold.append.mp hcond).2
        rw [hB, if_pos rfl] at hc2
        exact condsHold_boolConds_iff.mp hc2 p hp
      · exact hmemk w tab hbase τ hτ p hp
  | cell schema input outputs =>
      obtain ⟨⟨δin, hti⟩, hcount, houts⟩ := htc
      intro w tab htab τ hτ p hp
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · subst hwj
        have hτeq : τ = ⟨[], Dtype.B⟩ := Option.some.inj
          (hτ.symm.trans (houts _ (List.getElem_mem hj)))
        subst hτeq
        replace hp : p ∈ [if j = c then (1 : MvPolynomial (Fin d) ℚ)
          else 0] := hp
        obtain rfl := List.mem_singleton.mp hp
        refine valueSetBQ (Or.inl rfl) ?_
        intro _
        by_cases hjc : j = c
        · rw [if_pos hjc, map_one]
          exact Or.inr rfl
        · rw [if_neg hjc, map_zero]
          exact Or.inl rfl
      · exact hmemk w tab hbase τ hτ p hp
  | reshape newShape input output =>
      obtain ⟨τ0, hτi, hsz, hτo⟩ := htc
      obtain ⟨tabi, htabi, hmi⟩ := hresM input (List.mem_cons_self ..)
      intro w tab htab τ hτ p hp
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · have hj0 : j = 0 := by simpa using hj
        subst hj0
        have hwout : w = output := by simpa using hwj
        subst hwout
        have hτeq : τ = ⟨newShape, τ0.dtype⟩ :=
          Option.some.inj (hτ.symm.trans hτo)
        subst hτeq
        rw [show (st.val input).getD [] = tabi from by
          rw [htabi]; rfl] at hp
        exact hmi τ0 hτi p hp
      · exact hmemk w tab hbase τ hτ p hp
  | broadcast toShape input output =>
      obtain ⟨τ0, hτi, hbc, hτo⟩ := htc
      obtain ⟨tabi, htabi, hmi⟩ := hresM input (List.mem_cons_self ..)
      intro w tab htab τ hτ p hp
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · have hj0 : j = 0 := by simpa using hj
        subst hj0
        have hwout : w = output := by simpa using hwj
        subst hwout
        have hτeq : τ = ⟨toShape, τ0.dtype⟩ :=
          Option.some.inj (hτ.symm.trans hτo)
        subst hτeq
        rw [show (st.val input).getD [] = tabi from by
          rw [htabi]; rfl] at hp
        obtain ⟨cpos, -, rfl⟩ := List.mem_map.mp hp
        rcases getD_mem_or_eq tabi _ 0 with hmem | h0
        · exact hmi τ0 hτi _ hmem
        · rw [h0, map_zero]
          exact ⟨memK_zero _, fun _ => le_refl 0⟩
      · exact hmemk w tab hbase τ hτ p hp
  | copy kk input outputs =>
      obtain ⟨hcount, τ0, hτi, houts⟩ := htc
      obtain ⟨tabi, htabi, hmi⟩ := hresM input (List.mem_cons_self ..)
      intro w tab htab τ hτ p hp
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · subst hwj
        have hτeq : τ = τ0 := Option.some.inj
          (hτ.symm.trans (houts _ (List.getElem_mem hj)))
        subst hτeq
        rw [show (st.val input).getD [] = tabi from by
          rw [htabi]; rfl] at hp
        exact hmi τ hτi p hp
      · exact hmemk w tab hbase τ hτ p hp
  | delete input =>
      exact hmemk
  | swap in1 in2 out1 out2 =>
      obtain ⟨hs1, hs2, ho1, ho2⟩ := htc
      obtain ⟨tab1, htab1, hm1⟩ := hresM in1 (List.mem_cons_self ..)
      obtain ⟨tab2, htab2, hm2⟩ :=
        hresM in2 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      obtain ⟨τ2, hτ2⟩ := Option.isSome_iff_exists.mp hs2
      obtain ⟨τ1, hτ1⟩ := Option.isSome_iff_exists.mp hs1
      intro w tab htab τ hτ p hp
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · match j, hj with
        | 0, _ =>
            subst hwj
            have hτeq : τ = τ2 := Option.some.inj
              (hτ.symm.trans (by rw [ho1]; exact hτ2))
            subst hτeq
            replace hp : p ∈ (st.val in2).getD [] := by
              simpa using hp
            rw [show (st.val in2).getD [] = tab2 from by
              rw [htab2]; rfl] at hp
            exact hm2 τ hτ2 p hp
        | 1, _ =>
            subst hwj
            have hτeq : τ = τ1 := Option.some.inj
              (hτ.symm.trans (by rw [ho2]; exact hτ1))
            subst hτeq
            replace hp : p ∈ (st.val in1).getD [] := by
              simpa using hp
            rw [show (st.val in1).getD [] = tab1 from by
              rw [htab1]; rfl] at hp
            exact hm1 τ hτ1 p hp
      · exact hmemk w tab hbase τ hτ p hp
  | stack kk shape inputs output =>
      obtain ⟨hcount, τ0, hτo, hsh, hins⟩ := htc
      intro w tab htab τ hτ p hp
      rcases assignIdx_cases _ _ _ _ htab with ⟨j, hj, hwj, rfl⟩ | hbase
      · have hj0 : j = 0 := by simpa using hj
        subst hj0
        have hwout : w = output := by simpa using hwj
        subst hwout
        have hτeq : τ = τ0 := Option.some.inj (hτ.symm.trans hτo)
        subst hτeq
        obtain ⟨t, ht, hpt⟩ := List.mem_flatMap.mp hp
        obtain ⟨w', hw', rfl⟩ := List.mem_map.mp ht
        obtain ⟨tabw, htabw, hmw⟩ := hresM w' hw'
        rw [show (st.val w').getD [] = tabw from by
          rw [htabw]; rfl] at hpt
        have := hmw _ (hins w' hw') p hpt
        exact this
      · exact hmemk w tab hbase τ hτ p hp
  | relu shape input output => exact absurd htb (by simp [PrimApp.isTenBox])
  | ppoly nv co inputs output =>
      exact absurd htb (by simp [PrimApp.isTenBox])
  | pderiv shape ax input output =>
      exact absurd htb (by simp [PrimApp.isTenBox])
  | facet shape ax hi input output =>
      exact absurd htb (by simp [PrimApp.isTenBox])

/-- The σ-free fold facts: lengths and carrier validity of every
assigned table, given the final conditions hold. -/
theorem fold_wf {H : Hypernet} {x : Fin d → ℚ} {ins : Fin d → Wire} :
    ∀ (rest pre : List PrimApp), H.applications = pre ++ rest →
    H.TenBoxOnly → H.ExactBQ → H.InterfaceClosed ins →
    ∀ (st : SymSt d) (χ : List ℕ),
      (∀ w, (st.val w).isSome ↔
        ((∃ i, ins i = w) ∨ w ∈ pre.flatMap PrimApp.outputWires)) →
      (∀ w tab, st.val w = some tab →
        ∃ τ, H.wireType w = some τ ∧ tab.length = τ.shape.totalSize) →
      (∀ w tab, st.val w = some tab → ∀ τ, H.wireType w = some τ →
        ∀ p ∈ tab, τ.dtype.kind.MemK (MvPolynomial.eval x p) ∧
          (τ.dtype.sign = .nn → 0 ≤ MvPolynomial.eval x p)) →
      CondsHold x (symFold H.wireType st rest χ).conds →
      (∀ w tab, (symFold H.wireType st rest χ).val w = some tab →
        ∃ τ, H.wireType w = some τ ∧ tab.length = τ.shape.totalSize) ∧
      (∀ w tab, (symFold H.wireType st rest χ).val w = some tab →
        ∀ τ, H.wireType w = some τ →
        ∀ p ∈ tab, τ.dtype.kind.MemK (MvPolynomial.eval x p) ∧
          (τ.dtype.sign = .nn → 0 ≤ MvPolynomial.eval x p)) := by
  intro rest
  induction rest with
  | nil =>
      intro pre hsplit hten hbq hic st χ hdom hlens hmemk hconds
      exact ⟨hlens, hmemk⟩
  | cons app rest' ih =>
      intro pre hsplit hten hbq hic st χ hdom hlens hmemk hconds
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
      have hcondStep : CondsHold x
          (symStep H.wireType st app (χ.headD 0)).conds := by
        intro q hq
        exact hconds q (symFold_conds_mono rest' χ.tail _ q hq)
      have hsplit' : H.applications = (pre ++ [app]) ++ rest' := by
        rw [hsplit, List.append_assoc]
        rfl
      have hdom' : ∀ w,
          ((symStep H.wireType st app (χ.headD 0)).val w).isSome ↔
          ((∃ i, ins i = w) ∨ w ∈ (pre ++ [app]).flatMap
            PrimApp.outputWires) := by
        intro w
        rw [symStep_dom htb, hdom w, List.flatMap_append]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.mem_append]
        tauto
      exact ih (pre ++ [app]) hsplit' hten hbq hic
        (symStep H.wireType st app (χ.headD 0)) χ.tail hdom'
        (step_lens (H.typeConsistent app happ_mem) htb st _ hlens hcons)
        (step_memK (H.typeConsistent app happ_mem) htb
          (hbq app happ_mem) st _ hmemk hcons hcondStep)
        hconds


theorem assignIdx_single (f : ℕ → PTab d) (w : Wire)
    (base : Wire → Option (PTab d)) :
    assignIdx f [w] base w = some (f 0) := by
  show (if w = w then some (f 0) else _) = _
  rw [if_pos rfl]

theorem assignIdx_pair₁ (f : ℕ → PTab d) (w₁ w₂ : Wire)
    (base : Wire → Option (PTab d)) :
    assignIdx f [w₁, w₂] base w₁ = some (f 0) := by
  show (if w₁ = w₁ then some (f 0) else _) = _
  rw [if_pos rfl]

theorem assignIdx_pair₂ (f : ℕ → PTab d) {w₁ w₂ : Wire} (hne : w₂ ≠ w₁)
    (base : Wire → Option (PTab d)) :
    assignIdx f [w₁, w₂] base w₂ = some (f 1) := by
  show (if w₂ = w₁ then some (f 0)
    else if w₂ = w₂ then some (f 1) else base w₂) = _
  rw [if_neg hne, if_pos rfl]

/-- The single-step admissibility verification: σ reading the
post-step tables, with the step's conditions holding and the schema
disjoint, satisfies the application's semantics. -/
theorem step_build {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
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
    app.SemOk σ := by
  have hkeep : ∀ w ∈ app.inputWires,
      (symStep H.wireType st app c).val w = st.val w :=
    fun w hw => symStep_val_of_not_output (hio w hw)
  have hresB : ∀ w ∈ app.inputWires, ∃ tab, st.val w = some tab ∧
      readsTab σ x w tab ∧ ∃ τ, H.wireType w = some τ ∧
      tab.length = τ.shape.totalSize := by
    intro w hw
    obtain ⟨tab, htab⟩ := Option.isSome_iff_exists.mp (hcons w hw)
    exact ⟨tab, htab, hfr w tab (by rw [hkeep w hw]; exact htab),
      hlens w tab htab⟩
  cases app with
  | const ty cv out =>
      have hself : (symStep H.wireType st (.const ty cv out) c).val out
          = some (cv.entriesQ.map MvPolynomial.C) := by
        show assignIdx (fun _ => cv.entriesQ.map MvPolynomial.C)
          [out] st.val out = _
        exact assignIdx_getElem _ (List.nodup_singleton _) _ Nat.one_pos
      exact const_semOk_build hbqa (hfr _ _ hself)
  | contract δ r inputs output ir orank pat =>
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
      exact contract_semOk_build hbq hto hlen₁ hlen₂ hlen₃ hty htablen
        hreads' (contract_input_rank htc) (contract_input_extent htc)
        (hfr _ _ hself) hbool
  | cast δfrom δto r shape input output =>
      have hbqa' : δfrom.isBQ = true ∧ δto.isBQ = true ∧ r.isExact = true := by
        simpa [PrimApp.exactBQ, Bool.and_assoc] using hbqa
      obtain ⟨hbqf, hbqt, hexact⟩ := hbqa'
      obtain rfl := RoundMode.isExact_eq hexact
      obtain ⟨hti, hto⟩ := htc
      obtain ⟨tabi, htabi, hrd, τ', hτ', htlen⟩ :=
        hresB input (List.mem_cons_self ..)
      have hτeq : τ' = ⟨shape, δfrom⟩ := Option.some.inj (hτ'.symm.trans hti)
      have hlen : tabi.length = shape.totalSize := by
        rw [htlen, hτeq]
      have hself : (symStep H.wireType st
          (.cast δfrom δto .exact shape input output) c).val output
          = some tabi := by
        simp only [symStep]
        rw [assignIdx_single]
        show some ((st.val input).getD []) = some tabi
        rw [htabi]
        rfl
      have hbool : δto = Dtype.B → ∀ p ∈ tabi,
          MvPolynomial.eval x p = 0 ∨ MvPolynomial.eval x p = 1 := by
        intro hB
        have hc2 := (CondsHold.append.mp hcond).2
        rw [hB, if_pos rfl] at hc2
        have := condsHold_boolConds_iff.mp hc2
        rwa [show (st.val input).getD [] = tabi from by
          rw [htabi]; rfl] at this
      exact cast_semOk_build hbqt hlen hrd (hfr _ _ hself) hbool
  | cell schema input outputs =>
      obtain ⟨⟨δin, hti⟩, hcount, houts⟩ := htc
      obtain ⟨tabi, htabi, hrd, τ', hτ', htlen⟩ :=
        hresB input (List.mem_cons_self ..)
      have hτeq : τ' = ⟨[schema.ambDim], δin⟩ :=
        Option.some.inj (hτ'.symm.trans hti)
      have hlen : tabi.length = schema.ambDim := by
        rw [htlen, hτeq]
        show Shape.totalSize [schema.ambDim] = schema.ambDim
        rw [Shape.totalSize_cons, Shape.totalSize_nil, Nat.mul_one]
      have hc : c < schema.cells.length := List.mem_range.mp hcv
      have hconds : CondsHold x (maskCondsAt schema
          (schema.cells.get ⟨c, hc⟩).1 (schema.cells.get ⟨c, hc⟩).2
          (fun j => tabi.getD j.val 0)) := by
        have hc2 := (CondsHold.append.mp hcond).2
        rw [dif_pos hc] at hc2
        rwa [show (st.val input).getD [] = tabi from by
          rw [htabi]; rfl] at hc2
      have houtreads : ∀ (j : ℕ) (hj : j < outputs.length),
          readsTab σ x (outputs[j]'hj) (oneHotTab j c) := by
        intro j hj
        refine hfr _ _ ?_
        simp only [symStep]
        have hnd' : outputs.Nodup := hnd
        exact assignIdx_getElem _ hnd' _ hj
      exact cell_semOk_build hdisja hti hlen hrd ⟨c, hc⟩ hconds houtreads
  | reshape newShape input output =>
      obtain ⟨tabi, htabi, hrd, -⟩ := hresB input (List.mem_cons_self ..)
      have hself : (symStep H.wireType st
          (.reshape newShape input output) c).val output = some tabi := by
        simp only [symStep]
        rw [assignIdx_single]
        show some ((st.val input).getD []) = some tabi
        rw [htabi]
        rfl
      exact reshape_semOk_build hrd (hfr _ _ hself)
  | broadcast toShape input output =>
      obtain ⟨τ0, hτi, hbc, hτo⟩ := htc
      obtain ⟨tabi, htabi, hrd, τ', hτ', htlen⟩ :=
        hresB input (List.mem_cons_self ..)
      have hττ : τ' = τ0 := Option.some.inj (hτ'.symm.trans hτi)
      rw [hττ] at htlen
      have hself : (symStep H.wireType st
          (.broadcast toShape input output) c).val output
          = some (broadcastTab τ0.shape toShape tabi) := by
        simp only [symStep]
        rw [assignIdx_single]
        show some (broadcastTab (wireShapeOf H.wireType input) toShape
          ((st.val input).getD [])) = _
        rw [wireShapeOf_some hτi,
          show (st.val input).getD [] = tabi from by rw [htabi]; rfl]
      exact broadcast_semOk_build hτi hτo hbc htlen hrd (hfr _ _ hself)
  | copy kk input outputs =>
      obtain ⟨tabi, htabi, hrd, -⟩ := hresB input (List.mem_cons_self ..)
      refine copy_semOk_build hrd ?_
      intro o ho
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ho
      refine hfr _ _ ?_
      simp only [symStep]
      have hnd' : outputs.Nodup := hnd
      rw [assignIdx_getElem _ hnd' _ hj]
      show some ((st.val input).getD []) = some tabi
      rw [htabi]
      rfl
  | delete input =>
      trivial
  | swap in1 in2 out1 out2 =>
      obtain ⟨tab1, htab1, hrd1, -⟩ := hresB in1 (List.mem_cons_self ..)
      obtain ⟨tab2, htab2, hrd2, -⟩ :=
        hresB in2 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hnd' : ([out1, out2] : List Wire).Nodup := hnd
      have hne : out2 ≠ out1 := fun he =>
        (List.nodup_cons.mp hnd').1 (List.mem_singleton.mpr he.symm)
      have hself1 : (symStep H.wireType st
          (.swap in1 in2 out1 out2) c).val out1 = some tab2 := by
        simp only [symStep]
        rw [assignIdx_pair₁]
        show some (if (0 : ℕ) = 0 then (st.val in2).getD []
          else (st.val in1).getD []) = some tab2
        rw [if_pos rfl,
          show (st.val in2).getD [] = tab2 from by rw [htab2]; rfl]
      have hself2 : (symStep H.wireType st
          (.swap in1 in2 out1 out2) c).val out2 = some tab1 := by
        simp only [symStep]
        rw [assignIdx_pair₂ _ hne]
        show some (if (1 : ℕ) = 0 then (st.val in2).getD []
          else (st.val in1).getD []) = some tab1
        rw [if_neg (by omega),
          show (st.val in1).getD [] = tab1 from by rw [htab1]; rfl]
      exact swap_semOk_build hrd1 hrd2 (hfr _ _ hself1) (hfr _ _ hself2)
  | stack kk shape inputs output =>
      obtain ⟨hcount, τ0, hτo, hsh, hins⟩ := htc
      have htabres : ∀ (j : ℕ) (hj : j < inputs.length),
          st.val (inputs[j]'hj)
            = some ((inputs.map fun w => (st.val w).getD [])[j]'(by
                rw [List.length_map]; exact hj))
          ∧ ((inputs.map fun w => (st.val w).getD [])[j]'(by
                rw [List.length_map]; exact hj)).length
            = shape.totalSize := by
        intro j hj
        obtain ⟨tab, htab, -, τ', hτ', htlen⟩ :=
          hresB _ (List.getElem_mem hj)
        have hτeq : τ' = ⟨shape, τ0.dtype⟩ := Option.some.inj
          (hτ'.symm.trans (hins _ (List.getElem_mem hj)))
        have hget : (inputs.map fun w => (st.val w).getD [])[j]'(by
            rw [List.length_map]; exact hj) = tab := by
          rw [show (inputs.map fun w => (st.val w).getD [])[j]'(by
            rw [List.length_map]; exact hj)
            = (st.val (inputs[j]'hj)).getD [] from List.getElem_map ..,
            htab]
          rfl
        rw [hget]
        refine ⟨htab, ?_⟩
        rw [htlen, hτeq]
      have hself : (symStep H.wireType st
          (.stack kk shape inputs output) c).val output
          = some (stackTab (inputs.map fun w => (st.val w).getD [])) := by
        simp only [symStep]
        exact assignIdx_single _ _ _
      exact stack_semOk_build hcount (List.length_map ..)
        (fun j hj => (htabres j (by rw [List.length_map] at hj; exact hj)).2)
        (fun j hj => hfr _ _ (by
          rw [hkeep _ (List.getElem_mem hj)]
          exact (htabres j hj).1))
        (hfr _ _ hself)
  | relu shape input output => exact absurd htb (by simp [PrimApp.isTenBox])
  | ppoly nv co inputs output =>
      exact absurd htb (by simp [PrimApp.isTenBox])
  | pderiv shape ax input output =>
      exact absurd htb (by simp [PrimApp.isTenBox])
  | facet shape ax hi input output =>
      exact absurd htb (by simp [PrimApp.isTenBox])

/-- Admissibility of a valuation that reads the final fold: every
application's semantics holds. -/
theorem fold_admissible {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
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
      ∀ app ∈ rest, app.SemOk σ := by
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
        · exact step_build (H.typeConsistent app' happ_mem) htb
            (hbq app' happ_mem) (hdisj app' happ_mem)
            (nodup_of_flatMap_nodup H.linearity.2 app' happ_mem)
            (acyclic_input_not_output hsplit) st hc hcons hlens
            hfrStep hcondStep
        · exact ih (pre ++ [app]) hsplit' (symStep H.wireType st app c)
            χ' (mem_choiceLists.mpr hrest) hdom'
            (step_lens (H.typeConsistent app happ_mem) htb st _
              hlens hcons)
            hreadF' hcondF' app' happ'2


/-! ## The ground table and the master equality -/

/-- The rational ground table a symbolic state induces at a point:
assigned tables evaluate; typed unassigned wires zero-fill; untyped
wires are empty. -/
noncomputable def groundOf (H : Hypernet) {d' : ℕ}
    (stv : Wire → Option (PTab d')) (x : Fin d' → ℚ) : Wire → List ℚ :=
  fun w => match H.wireType w, stv w with
  | none, _ => []
  | some τ, none => List.replicate τ.shape.totalSize 0
  | some τ, some tab => tab.map (MvPolynomial.eval x)

theorem groundOf_some {H : Hypernet} {d' : ℕ}
    {stv : Wire → Option (PTab d')} {x : Fin d' → ℚ} {w : Wire}
    {τ : TensorType} {tab : PTab d'}
    (hτ : H.wireType w = some τ) (hv : stv w = some tab) :
    groundOf H stv x w = tab.map (MvPolynomial.eval x) := by
  simp only [groundOf, hτ, hv]

theorem groundOf_none {H : Hypernet} {d' : ℕ}
    {stv : Wire → Option (PTab d')} {x : Fin d' → ℚ} {w : Wire}
    {τ : TensorType} (hτ : H.wireType w = some τ) (hv : stv w = none) :
    groundOf H stv x w = List.replicate τ.shape.totalSize 0 := by
  simp only [groundOf, hτ, hv]

/-- **The master equality**: the interface denotation is the union of
the choice-indexed piece graphs. -/
theorem denotRel_eq_pieces {H : Hypernet} {d' m : ℕ}
    {ins : Fin d' → Wire} {outs : Fin m → Wire}
    (hten : H.TenBoxOnly) (hbq : H.ExactBQ) (hic : H.InterfaceClosed ins)
    (hoc : H.OutputsConnected ins outs) (hsat : H.SaturatingContracts)
    (hins : ∀ i, H.ScalarQPort (ins i))
    (houts : ∀ j, H.ScalarQPort (outs j))
    (hdisj : ∀ app ∈ H.applications, app.cellDisjoint) :
    H.DenotRel d' m ins outs
      = ⋃ P ∈ hypernetPieces H ins outs, P.graph := by
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
    obtain ⟨χ, hχ, hcondF, hreadF, hlensF⟩ := fold_mp hadm hten hbq hsat
      hic H.applications [] rfl (initSt d' ins) hdom0 hreads0 hlens0
      (fun q hq => absurd hq List.not_mem_nil)
    refine Set.mem_iUnion₂.mpr ⟨pieceOf H ins outs χ,
      List.mem_map.mpr ⟨χ, hχ, rfl⟩, hcondF, ?_⟩
    intro j
    have hsome : ((symFold H.wireType (initSt d' ins)
        H.applications χ).val (outs j)).isSome := by
      rcases hoc j with ⟨i, hi⟩ | hprod
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
      show (((symFold H.wireType (initSt d' ins) H.applications χ).val
        (outs j)).getD []).getD 0 0 = _
      rw [htab]
      show tab.getD 0 0 = _
      exact Shape.getD_eq_getElem' tab 0 h0
    have hrd := (hreadF _ _ htab).read h0
    have hout := houtr j
    have hyv : y j = MvPolynomial.eval x (tab[0]'h0) :=
      ERat.fin.inj (Option.some.inj (hout.symm.trans hrd))
    show y j = MvPolynomial.eval x ((pieceOf H ins outs χ).val j)
    rw [hpv]
    exact hyv
  · intro hmem
    obtain ⟨P, hP, hgraph⟩ := Set.mem_iUnion₂.mp hmem
    obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hP
    have hgraph' : (∀ p ∈ (pieceOf H ins outs χ).conds,
        0 ≤ MvPolynomial.eval x p) ∧
        ∀ j, y j = MvPolynomial.eval x ((pieceOf H ins outs χ).val j) :=
      hgraph
    have hcondF : CondsHold x (symFold H.wireType (initSt d' ins)
        H.applications χ).conds := hgraph'.1
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
    obtain ⟨hlensF, hmemkF⟩ := fold_wf H.applications [] rfl hten hbq hic
      (initSt d' ins) χ hdom0 hlens0 hmemk0 hcondF
    have hwf : ∀ w τ, H.wireType w = some τ →
        (groundOf H (symFold H.wireType (initSt d' ins)
          H.applications χ).val x w).length = τ.shape.totalSize ∧
        ∀ q ∈ groundOf H (symFold H.wireType (initSt d' ins)
          H.applications χ).val x w,
          τ.dtype.kind.MemK q ∧ (τ.dtype.sign = .nn → 0 ≤ q) := by
      intro w τ hτ
      cases hval : (symFold H.wireType (initSt d' ins)
          H.applications χ).val w with
      | none =>
          rw [groundOf_none hτ hval]
          refine ⟨List.length_replicate .., ?_⟩
          intro q hq
          obtain rfl := List.eq_of_mem_replicate hq
          exact ⟨memK_zero _, fun _ => le_refl 0⟩
      | some tab =>
          rw [groundOf_some hτ hval]
          obtain ⟨τ'', hτ'', hlen⟩ := hlensF w tab hval
          have hττ : τ'' = τ := Option.some.inj (hτ''.symm.trans hτ)
          rw [hττ] at hlen
          refine ⟨by rw [List.length_map]; exact hlen, ?_⟩
          intro q hq
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
          exact hmemkF w tab hval τ hτ p hp
    have hreadF : ∀ w tab, (symFold H.wireType (initSt d' ins)
        H.applications χ).val w = some tab →
        readsTab (BasisGen.mkVal H (groundOf H (symFold H.wireType
          (initSt d' ins) H.applications χ).val x) hwf) x w tab := by
      intro w tab htab
      obtain ⟨τ, hτ, -⟩ := hlensF w tab htab
      intro i
      rw [BasisGen.mkVal_reads H _ hwf hτ i, groundOf_some hτ htab,
        List.getElem?_map, Option.map_map]
      rfl
    have hadm : (BasisGen.mkVal H (groundOf H (symFold H.wireType
        (initSt d' ins) H.applications χ).val x) hwf).Admissible :=
      fun app happ => fold_admissible hten hbq hic hdisj
        H.applications [] rfl (initSt d' ins) χ hχ hdom0 hlens0
        hreadF hcondF app happ
    refine ⟨BasisGen.mkVal H (groundOf H (symFold H.wireType
      (initSt d' ins) H.applications χ).val x) hwf, hadm, ?_, ?_⟩
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
      have hsome : ((symFold H.wireType (initSt d' ins)
          H.applications χ).val (outs j)).isSome := by
        rcases hoc j with ⟨i, hi⟩ | hprod
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
      have hyv := hgraph'.2 j
      have hpv : (pieceOf H ins outs χ).val j = tab[0]'h0 := by
        show (((symFold H.wireType (initSt d' ins) H.applications χ).val
          (outs j)).getD []).getD 0 0 = _
        rw [htab]
        show tab.getD 0 0 = _
        exact Shape.getD_eq_getElem' tab 0 h0
      rw [hpv] at hyv
      rw [hrd, ← hyv]

theorem primitiveBasisSoundWF : PrimitiveBasisSoundWF := by
  intro H d' m ins outs hten hbq hic hoc hsat hins houts
  by_cases hdisj : ∀ app ∈ H.applications, app.cellDisjoint
  · exact ⟨hypernetPieces H ins outs,
      denotRel_eq_pieces hten hbq hic hoc hsat hins houts hdisj⟩
  · push_neg at hdisj
    obtain ⟨app, happ, hnd⟩ := hdisj
    have hempty : H.DenotRel d' m ins outs = ∅ := by
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨σ, hadm, -, -⟩
      have hsem := hadm app happ
      cases app <;> first | exact hnd hsem.1 | exact hnd trivial
    rw [hempty]
    exact IsPiecewisePolyRel.empty _ _

#print axioms not_primitiveBasisSound
#print axioms fold_mp
#print axioms fold_admissible
#print axioms primitiveBasisSoundWF

end PPLC
