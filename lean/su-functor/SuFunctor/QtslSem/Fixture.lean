import SuFunctor.QtslSem.BLComponents
import SuFunctor.Plain.CheckerFace

/-!
# The semantics off the presentation, exercised: cut through the free
# promotion, to a semantic-universe statement

The assembly applied (`qtslSemBL` — the free-promotion transpose of the
structural fragment's interpretation), and the acceptance fixture: one
settled rule (cut), entered as a generator cell of the presented virtual
double category, covered into a cell of the free promotion, mapped
through the promoted functor, and read at the checker face — the upper
probability of the conclusion's complement over the credal compile of
the premise-and-admissibility cylinder vanishes
(`SuFunctor.Plain.semanticallyValid_iff_face`).

The point of the fixture is the route, not the endpoint: the endpoint
proposition follows from `sound_cut` directly, but here its proof term
routes through `LaxDoubleFunctor.mapCell` of the promoted semantics on
the cut generator's covering — the composite the design owes is
exercised end to end, kernel-checked.  Deleting the cut component from
the interpretation, corrupting a side condition in its gate, or citing
a different generator in the covering each breaks this file — the
assembly admits no partial-functor fallback.
-/

namespace SuFunctor

namespace QtslSem

open PPLC CategoryTheory VdcPresentation
open VirtualDoubleCategoryData

/-- **The semantics of the wired fragment off its presentation**:
the free-promotion transpose of the interpretation — a lax (indeed
pseudo) double functor from the free promotion of the presented virtual
double category into the implication double category, determined by the
per-rule soundness components alone. -/
noncomputable def qtslSemBL (H : Hypernet) :
    LaxDoubleFunctor (FreePromotion (Presented (blPresentation H)))
      (ImplDouble BLCtx) :=
  (blInterpretation H).sem fun m n f g => ImplDouble.cell_subsingleton m n f g

/-- The cut instance on formulas `φ`, `χ`, `ψ`: premises `φ ⊢ χ` and
`φ ∧ χ ⊢ ψ`, conclusion `φ ⊢ ψ`. -/
def cutRule (φ χ ψ : Formula) : BLRule :=
  .cut ⟨φ, ψ⟩ ⟨φ, χ⟩ ⟨.and φ χ, ψ⟩ χ

/-- The cut instance's side conditions all hold definitionally. -/
theorem cutRule_gate (H : Hypernet) (φ χ ψ : Formula) :
    (blPresentation H).gate (cutRule φ χ ψ) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The premise string of the cut instance, over the presented
carrier. -/
def cutTops (H : Hypernet) (φ χ ψ : Formula) :
    LoosePath (VirtualDoubleCategoryData.Loose
      (C := Presented (blPresentation H)))
      (.of .pt) (.of .pt) :=
  .cons (b := .of .pt) (⟨φ, χ⟩ : Sequent)
    (.single (⟨.and φ χ, ψ⟩ : Sequent))

/-- The cut generator as a multicell of the presented virtual double
category. -/
def cutCell (H : Hypernet) (φ χ ψ : Formula) :
    VirtualDoubleCategoryData.Cell (C := Presented (blPresentation H))
      (cutTops H φ χ ψ) ((⟨φ, ψ⟩ : Sequent) :
        VirtualDoubleCategoryData.Loose (.of .pt) (.of .pt))
      (𝟙 (Presented.of BLCtx.pt)) (𝟙 (Presented.of BLCtx.pt)) := by
  exact ⟨⟨DerivT.gen (P := blPresentation H) (cutRule φ χ ψ)
    (cutRule_gate H φ χ ψ)⟩⟩

/-- The cut generator's covering, as a cell of the free promotion: the
singleton covering of the conclusion by the cut multicell. -/
def cutCovering (H : Hypernet) (φ χ ψ : Formula) :
    PseudoDoubleCategoryStruct.Cell
      (C := FreePromotion (Presented (blPresentation H)))
      (a := .of (.of .pt)) (b := .of (.of .pt))
      (c := .of (.of .pt)) (d := .of (.of .pt))
      (cutTops H φ χ ψ)
      (LoosePath.single ((⟨φ, ψ⟩ : Sequent) :
        VirtualDoubleCategoryData.Loose (Presented.of BLCtx.pt)
          (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt))) := by
  exact ⟨⟨(VirtualDoubleCategoryStruct.CellSeq.singleton
    (cutCell H φ χ ψ)).castDom (LoosePath.comp_nil _)⟩⟩

/-- **The fixture: cut, composed through the universal property, lands
at the checker face.**  From the semantic validity of the two premises,
the vanishing of the upper probability of the conclusion's complement
over the credal compile of the premise-and-admissibility cylinder — with
the proof term routed through the promoted functor's action on the cut
generator's covering cell. -/
theorem cut_face_through_promotion (H : Hypernet) (φ χ ψ : Formula)
    (h₁ : Sequent.semanticallyValid H ⟨φ, χ⟩)
    (h₂ : Sequent.semanticallyValid H ⟨.and φ χ, ψ⟩) :
    Plain.upperProb (Plain.admCyl H ⟨φ, ψ⟩) (Plain.postEvt H ⟨φ, ψ⟩)ᶜ = 0 := by
  have himp := ((qtslSemBL H).mapCell (cutCovering H φ χ ψ)).down
  exact (Plain.semanticallyValid_iff_face H ⟨φ, ψ⟩).mp
    (himp ⟨h₁, h₂, trivial⟩).1

/-!
## The tranche fixture: a composite derivation through two wired families

One derivation, two generators, spliced by simultaneous substitution:
`eqElim` rewrites the body formula `(2 + 4) ≤ 10` to `6 ≤ 10` along the
equality `(2 + 4) = 6`, whose premise is discharged *inside the
derivation* by a `pConstExact` generator (closed evaluation, kernel
computation) — so the composite consumes only the body premise.  One
level deeper than the cut fixture: the covering exercises
`DerivT.subst` with a mixed sequence (a zero-premise generator leg and
an identity leg), and the gate of `eqElim` is discharged for an
*arbitrary* hypernet, because constants' shapes are
declaration-independent. -/

/-- The unnormalized constant term `2 + 4`. -/
private abbrev sumTerm : Term := .add (.const 2) (.const 4)

/-- The equality premise `φ ⊢ (2 + 4) = 6`. -/
def eqConstPremise (φ : Formula) : Sequent :=
  ⟨φ, .atom .eq sumTerm (.const 6)⟩

/-- The body premise `φ ⊢ (2 + 4) ≤ 10`. -/
def bodyConstPremise (φ : Formula) : Sequent :=
  ⟨φ, .atom .le sumTerm (.const 10)⟩

/-- The conclusion `φ ⊢ 6 ≤ 10`. -/
def constConcl (φ : Formula) : Sequent :=
  ⟨φ, .atom .le (.const 6) (.const 10)⟩

/-- The `eqElim` instance rewriting the body formula `(· ≤ 10)` at wire
`0` from `2 + 4` to `6`. -/
def eqElimConstRule (φ : Formula) : BLRule :=
  .eqElim (constConcl φ) (eqConstPremise φ) (bodyConstPremise φ) 0
    sumTerm (.const 6) (.atom .le (.var 0) (.const 10))

/-- The `eqElim` instance's gate holds over an arbitrary hypernet:
constants' shapes are declaration-independent, and both substitution
side conditions are definitional. -/
theorem eqElimConstRule_gate (H : Hypernet) (φ : Formula) :
    (blPresentation H).gate (eqElimConstRule φ) :=
  ⟨rfl, rfl, rfl, ⟨[], rfl, rfl⟩, rfl, rfl⟩

/-- The `pConstExact` instance discharging the equality premise by
closed evaluation. -/
def pConstEqRule (φ : Formula) : BLRule :=
  .pConstExact (eqConstPremise φ) sumTerm (.const 6) .eq

/-- The evaluation gate: `(2 + 4) = 6` computes.  (`norm_num` rather
than `decide`: rational addition does not kernel-reduce under the
`Decidable` instances alone.) -/
theorem pConstEqRule_gate (H : Hypernet) (φ : Formula) :
    (blPresentation H).gate (pConstEqRule φ) := by
  refine ⟨?_, rfl⟩
  norm_num [Formula.evalClosed, Term.evalQ?, BowTie.evalQ]

/-- The `pConstExact` generator as a standalone zero-premise
derivation.  (Every generator leg is a named, ground-typed definition:
nested anonymous constructors postpone as whole-argument metavariables,
and the presentation's `tops`/`bot` cannot reduce on a metavariable
rule — so the outer unification dies before the arguments elaborate.) -/
def pConstEqDeriv (H : Hypernet) (φ : Formula) :
    DerivT (blPresentation H) .nil (eqConstPremise φ)
      (𝟙 BLCtx.pt) (𝟙 BLCtx.pt) :=
  DerivT.gen (P := blPresentation H) (pConstEqRule φ)
    (pConstEqRule_gate H φ)

/-- The identity derivation on the body premise, as the covering's
second leg. -/
def bodyIdDeriv (H : Hypernet) (φ : Formula) :
    DerivT (blPresentation H) (.single (bodyConstPremise φ))
      (bodyConstPremise φ) (𝟙 BLCtx.pt) (𝟙 BLCtx.pt) :=
  DerivT.id (P := blPresentation H) (bodyConstPremise φ)

/-- The covering sequence of the composite fixture: the equality
premise covered by the `pConstExact` generator (a zero-premise leg),
the body premise covered by the identity derivation. -/
def eqElimConstDerivSeq (H : Hypernet) (φ : Formula) :
    DerivSeqT (blPresentation H)
      (.cons (b := .pt) (eqConstPremise φ) (.single (bodyConstPremise φ)))
      (.single (bodyConstPremise φ)) (𝟙 BLCtx.pt) (𝟙 BLCtx.pt) :=
  DerivSeqT.cons (pConstEqDeriv H φ)
    (DerivSeqT.cons (bodyIdDeriv H φ) (DerivSeqT.nil (𝟙 BLCtx.pt)))

/-- **The composite derivation**: the `eqElim` generator with its
equality premise covered by the `pConstExact` generator and its body
premise covered by the identity — a multicell from the body premise
alone to the rewritten conclusion. -/
def eqElimConstDeriv (H : Hypernet) (φ : Formula) :
    DerivT (blPresentation H) (.single (bodyConstPremise φ))
      (constConcl φ) (𝟙 BLCtx.pt) (𝟙 BLCtx.pt) :=
  DerivT.subst
    (DerivT.gen (P := blPresentation H) (eqElimConstRule φ)
      (eqElimConstRule_gate H φ))
    (eqElimConstDerivSeq H φ)

/-- The composite fixture's premise string over the presented
carrier. -/
def constTops (H : Hypernet) (φ : Formula) :
    LoosePath (VirtualDoubleCategoryData.Loose
      (C := Presented (blPresentation H)))
      (.of .pt) (.of .pt) :=
  .single (bodyConstPremise φ : Sequent)

/-- The composite derivation as a multicell of the presented virtual
double category. -/
def eqElimConstCell (H : Hypernet) (φ : Formula) :
    VirtualDoubleCategoryData.Cell (C := Presented (blPresentation H))
      (constTops H φ) ((constConcl φ) :
        VirtualDoubleCategoryData.Loose (.of .pt) (.of .pt))
      (𝟙 (Presented.of BLCtx.pt)) (𝟙 (Presented.of BLCtx.pt)) := by
  exact ⟨⟨eqElimConstDeriv H φ⟩⟩

/-- The composite derivation's covering, as a cell of the free
promotion. -/
def eqElimConstCovering (H : Hypernet) (φ : Formula) :
    PseudoDoubleCategoryStruct.Cell
      (C := FreePromotion (Presented (blPresentation H)))
      (a := .of (.of .pt)) (b := .of (.of .pt))
      (c := .of (.of .pt)) (d := .of (.of .pt))
      (constTops H φ)
      (LoosePath.single ((constConcl φ) :
        VirtualDoubleCategoryData.Loose (Presented.of BLCtx.pt)
          (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt))) := by
  exact ⟨⟨(VirtualDoubleCategoryStruct.CellSeq.singleton
    (eqElimConstCell H φ)).castDom (LoosePath.comp_nil _)⟩⟩

/-- **The tranche fixture: two new generators, one composite derivation,
composed through the universal property, landing at the checker face.**
From the semantic validity of the body premise alone — the equality
premise is discharged inside the derivation by closed evaluation — the
vanishing of the upper probability of the rewritten conclusion's
complement over the credal compile of the premise-and-admissibility
cylinder, with the proof term routed through the promoted functor's
action on the composite covering cell. -/
theorem eqElim_const_face_through_promotion (H : Hypernet) (φ : Formula)
    (h : Sequent.semanticallyValid H
      ⟨φ, .atom .le (.add (.const 2) (.const 4)) (.const 10)⟩) :
    Plain.upperProb (Plain.admCyl H ⟨φ, .atom .le (.const 6) (.const 10)⟩)
      (Plain.postEvt H ⟨φ, .atom .le (.const 6) (.const 10)⟩)ᶜ = 0 := by
  have himp := ((qtslSemBL H).mapCell (eqElimConstCovering H φ)).down
  exact (Plain.semanticallyValid_iff_face H (constConcl φ)).mp
    (himp ⟨h, trivial⟩).1

/-!
## The relu-chain fixture: a composite with an empty premise string

Two activation-split generators, spliced by simultaneous substitution:
`reluPos` on the link `v → w` collapses the second relu to the identity
(`w = v`) from the nonnegativity of its preactivation — and that
premise `v ≥ 0` is discharged *inside the derivation* by `reluNN` on
the link `u → v` (relu outputs are nonnegative, zero-premise).  One
shape past the `eqElim` fixture: the covering's only leg is itself
zero-premise and there is no identity leg, so the composite's premise
string is EMPTY — the endpoint carries no validity hypotheses at all, a
checker-face fact obtained purely from the hypernet's application rows
(the two `reluLinked` gates).

(The PSD-certificate pairing the tranche brief suggested is blocked by
the proof theory: `syzygyConclusionForm`'s `.neg`-disjunct would let a
PSD conclusion take the `.ge … (.const 0)` shape, but `reluPos`'s
premise demands the bare-variable atom `.ge (.var preact) (.const 0)`,
and a PSD quadratic form equal to a nonconstant linear polynomial does
not exist.  Bridging would take an `eqElim`/`arithAtom` bridge — more
generators, no new coverage.) -/

/-- The nonnegativity sequent `φ ⊢ v ≥ 0` for a wire `v`. -/
def reluNNSeq (φ : Formula) (v : Wire) : Sequent :=
  ⟨φ, .atom .ge (.var v) (.const 0)⟩

/-- The positive-branch conclusion `φ ⊢ w = v`. -/
def reluChainConcl (φ : Formula) (v w : Wire) : Sequent :=
  ⟨φ, .atom .eq (.var w) (.var v)⟩

/-- The `reluNN` instance on the link `u → v`, concluding `φ ⊢ v ≥ 0`. -/
def reluNNRule (φ : Formula) (u v : Wire) : BLRule :=
  .reluNN (reluNNSeq φ v) u v

/-- The `reluNN` instance's gate: the link, and a definitional
conclusion form. -/
theorem reluNNRule_gate (H : Hypernet) (φ : Formula) {u v : Wire}
    (h : reluLinked H u v) :
    (blPresentation H).gate (reluNNRule φ u v) :=
  ⟨h, rfl⟩

/-- The `reluPos` instance on the link `v → w`, from `φ ⊢ v ≥ 0` to
`φ ⊢ w = v`. -/
def reluPosRule (φ : Formula) (v w : Wire) : BLRule :=
  .reluPos (reluChainConcl φ v w) (reluNNSeq φ v) v w

/-- The `reluPos` instance's gate: the link, and three definitional
forms. -/
theorem reluPosRule_gate (H : Hypernet) (φ : Formula) {v w : Wire}
    (h : reluLinked H v w) :
    (blPresentation H).gate (reluPosRule φ v w) :=
  ⟨h, rfl, rfl, rfl⟩

/-- The `reluNN` generator as a standalone zero-premise derivation
(named, ground-typed leg). -/
def reluNNDeriv (H : Hypernet) (φ : Formula) (u v : Wire)
    (h : reluLinked H u v) :
    DerivT (blPresentation H) .nil (reluNNSeq φ v)
      (𝟙 BLCtx.pt) (𝟙 BLCtx.pt) :=
  DerivT.gen (P := blPresentation H) (reluNNRule φ u v)
    (reluNNRule_gate H φ h)

/-- The covering sequence of the relu chain: the single nonnegativity
premise covered by the `reluNN` generator — a zero-premise leg and
nothing else, so the composite's premise string is empty. -/
def reluChainDerivSeq (H : Hypernet) (φ : Formula) (u v : Wire)
    (h : reluLinked H u v) :
    DerivSeqT (blPresentation H) (.single (reluNNSeq φ v))
      .nil (𝟙 BLCtx.pt) (𝟙 BLCtx.pt) :=
  DerivSeqT.cons (reluNNDeriv H φ u v h) (DerivSeqT.nil (𝟙 BLCtx.pt))

/-- **The composite derivation**: the `reluPos` generator with its
nonnegativity premise covered by the `reluNN` generator — a premise-free
multicell concluding `φ ⊢ w = v`. -/
def reluChainDeriv (H : Hypernet) (φ : Formula) (u v w : Wire)
    (h₁ : reluLinked H u v) (h₂ : reluLinked H v w) :
    DerivT (blPresentation H) .nil (reluChainConcl φ v w)
      (𝟙 BLCtx.pt) (𝟙 BLCtx.pt) :=
  DerivT.subst
    (DerivT.gen (P := blPresentation H) (reluPosRule φ v w)
      (reluPosRule_gate H φ h₂))
    (reluChainDerivSeq H φ u v h₁)

/-- The relu chain's (empty) premise string over the presented
carrier. -/
def reluChainTops (H : Hypernet) :
    LoosePath (VirtualDoubleCategoryData.Loose
      (C := Presented (blPresentation H)))
      (.of .pt) (.of .pt) :=
  .nil

/-- The composite derivation as a multicell of the presented virtual
double category. -/
def reluChainCell (H : Hypernet) (φ : Formula) (u v w : Wire)
    (h₁ : reluLinked H u v) (h₂ : reluLinked H v w) :
    VirtualDoubleCategoryData.Cell (C := Presented (blPresentation H))
      (reluChainTops H) ((reluChainConcl φ v w) :
        VirtualDoubleCategoryData.Loose (.of .pt) (.of .pt))
      (𝟙 (Presented.of BLCtx.pt)) (𝟙 (Presented.of BLCtx.pt)) := by
  exact ⟨⟨reluChainDeriv H φ u v w h₁ h₂⟩⟩

/-- The composite derivation's covering, as a cell of the free
promotion. -/
def reluChainCovering (H : Hypernet) (φ : Formula) (u v w : Wire)
    (h₁ : reluLinked H u v) (h₂ : reluLinked H v w) :
    PseudoDoubleCategoryStruct.Cell
      (C := FreePromotion (Presented (blPresentation H)))
      (a := .of (.of .pt)) (b := .of (.of .pt))
      (c := .of (.of .pt)) (d := .of (.of .pt))
      (reluChainTops H)
      (LoosePath.single ((reluChainConcl φ v w) :
        VirtualDoubleCategoryData.Loose (Presented.of BLCtx.pt)
          (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt))) := by
  exact ⟨⟨(VirtualDoubleCategoryStruct.CellSeq.singleton
    (reluChainCell H φ u v w h₁ h₂)).castDom (LoosePath.comp_nil _)⟩⟩

/-- **The relu-chain fixture: two activation-split generators, one
premise-free composite, landing at the checker face with no validity
hypotheses.**  From the hypernet's application rows alone — the two
relu links — the vanishing of the upper probability of the
positive-branch conclusion's complement, with the proof term routed
through the promoted functor's action on the composite covering cell. -/
theorem reluChain_face_through_promotion (H : Hypernet) (φ : Formula)
    (u v w : Wire) (h₁ : reluLinked H u v) (h₂ : reluLinked H v w) :
    Plain.upperProb (Plain.admCyl H ⟨φ, .atom .eq (.var w) (.var v)⟩)
      (Plain.postEvt H ⟨φ, .atom .eq (.var w) (.var v)⟩)ᶜ = 0 := by
  have himp := ((qtslSemBL H).mapCell
    (reluChainCovering H φ u v w h₁ h₂)).down
  exact (Plain.semanticallyValid_iff_face H (reluChainConcl φ v w)).mp
    (himp trivial).1

/-!
## The subdivide-fan fixture: an n-ary premise string through the builder

The `subdivide` generator at a literal arity — two branches — with its
region premise discharged *inside the derivation* by a `convIntro`
generator (region membership from its barycentric halfspace form).  One
shape past the relu chain: the covering's generator leg has a NONEMPTY
premise string of its own (`convIntro` is one-premise), so the splice
re-associates a mixed three-leg covering — a one-premise generator leg
and two identity legs — onto the fan's `Fin`-built premise string, which
reduces definitionally at the literal arity (the builder recurses on the
arity, deliberately not via `List.ofFn`).

The geometric side conditions (the shape row, the halfspace form, the
cover checker's verdict) enter as hypotheses — the `reluLinked`
precedent: the fixture demonstrates the route (builder, splice,
promotion, checker face) with the cover certificate abstract;
discharging a concrete cover check is decision-procedure territory, not
route territory. -/

/-- The halfspace premise `φ ⊢ hpF`. -/
def fanHalfspaceP (φ hpF : Formula) : Sequent := ⟨φ, hpF⟩

/-- The region premise `φ ⊢ x ∈ (simplex, S)`. -/
def fanRegionP (φ : Formula) (termX : Term) (simplex : Simplex)
    (S : ExtensionSet) : Sequent :=
  ⟨φ, .inRegion termX simplex S⟩

/-- The `k`-th branch premise: the region hypothesis strengthened to
the `k`-th cover element, same conclusion as the fan. -/
def fanBranchP (φ ψ : Formula) (termX : Term)
    (branchSimplex : Fin 2 → Simplex) (branchS : Fin 2 → ExtensionSet)
    (k : Fin 2) : Sequent :=
  ⟨.and φ (.inRegion termX (branchSimplex k) (branchS k)), ψ⟩

/-- The subdivide instance at the two-branch fan. -/
def subdivideFanRule (φ ψ : Formula) (termX : Term) (simplex : Simplex)
    (S : ExtensionSet) (branchSimplex : Fin 2 → Simplex)
    (branchS : Fin 2 → ExtensionSet) (cert : Term) : BLRule :=
  .subdivide ⟨φ, ψ⟩ (fanRegionP φ termX simplex S) 2
    (fanBranchP φ ψ termX branchSimplex branchS)
    termX simplex S branchSimplex branchS cert

/-- The fan's side conditions: four definitional forms and the cover
checker's verdict. -/
theorem subdivideFanRule_gate (H : Hypernet) (φ ψ : Formula)
    (termX : Term) (simplex : Simplex) (S : ExtensionSet)
    (branchSimplex : Fin 2 → Simplex) (branchS : Fin 2 → ExtensionSet)
    (cert : Term)
    (hcover : coverInfeasibilityValid termX simplex S 2
      branchSimplex branchS cert) :
    (blPresentation H).gate
      (subdivideFanRule φ ψ termX simplex S branchSimplex branchS cert) :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl, hcover⟩

/-- The `convIntro` instance concluding the fan's region premise. -/
def fanRegionIntroRule (φ hpF : Formula) (termX : Term)
    (simplex : Simplex) (S : ExtensionSet) : BLRule :=
  .convIntro (fanRegionP φ termX simplex S) (fanHalfspaceP φ hpF)
    termX simplex S

/-- The `convIntro` instance's gate: the shape row and the halfspace
form as hypotheses, the two sequent forms definitional. -/
theorem fanRegionIntroRule_gate (H : Hypernet) (φ hpF : Formula)
    (termX : Term) (simplex : Simplex) (S : ExtensionSet)
    (hbshape : termX.bshape H = some [simplex.complex.ambDim])
    (hform : barycentricHalfspaceForm termX simplex S hpF) :
    (blPresentation H).gate (fanRegionIntroRule φ hpF termX simplex S) :=
  ⟨rfl, hbshape, hform, rfl⟩

/-- The `convIntro` generator as a standalone one-premise derivation
(named, ground-typed leg). -/
def fanRegionIntroDeriv (H : Hypernet) (φ hpF : Formula) (termX : Term)
    (simplex : Simplex) (S : ExtensionSet)
    (hbshape : termX.bshape H = some [simplex.complex.ambDim])
    (hform : barycentricHalfspaceForm termX simplex S hpF) :
    DerivT (blPresentation H) (.single (fanHalfspaceP φ hpF))
      (fanRegionP φ termX simplex S) (𝟙 BLCtx.pt) (𝟙 BLCtx.pt) :=
  DerivT.gen (P := blPresentation H)
    (fanRegionIntroRule φ hpF termX simplex S)
    (fanRegionIntroRule_gate H φ hpF termX simplex S hbshape hform)

/-- The identity derivation on the `k`-th branch premise (named,
ground-typed leg). -/
def fanBranchIdDeriv (H : Hypernet) (φ ψ : Formula) (termX : Term)
    (branchSimplex : Fin 2 → Simplex) (branchS : Fin 2 → ExtensionSet)
    (k : Fin 2) :
    DerivT (blPresentation H)
      (.single (fanBranchP φ ψ termX branchSimplex branchS k))
      (fanBranchP φ ψ termX branchSimplex branchS k)
      (𝟙 BLCtx.pt) (𝟙 BLCtx.pt) :=
  DerivT.id (P := blPresentation H)
    (fanBranchP φ ψ termX branchSimplex branchS k)

/-- The fan's covered premise string — the rule's `Fin`-built tops —
as a named, ground-typed path: in a declared type, nested path literals
over a constant loose family leave endpoint metavariables that the
claim context's `PUnit`-valued tight arrows can never pin (the
named-leg discipline, extended from generator legs to the path
expressions themselves). -/
def subdivideFanCovered (φ ψ : Formula) (termX : Term)
    (simplex : Simplex) (S : ExtensionSet)
    (branchSimplex : Fin 2 → Simplex) (branchS : Fin 2 → ExtensionSet) :
    LoosePath (fun _ _ : BLCtx => Sequent) BLCtx.pt BLCtx.pt :=
  .cons (b := .pt) (fanRegionP φ termX simplex S)
    (.ofFin (fanBranchP φ ψ termX branchSimplex branchS))

/-- The fan covering's premise string — halfspace premise, then the two
branch premises — as a named, ground-typed path. -/
def subdivideFanPs (φ ψ hpF : Formula) (termX : Term)
    (branchSimplex : Fin 2 → Simplex) (branchS : Fin 2 → ExtensionSet) :
    LoosePath (fun _ _ : BLCtx => Sequent) BLCtx.pt BLCtx.pt :=
  .cons (b := .pt) (fanHalfspaceP φ hpF)
    (.cons (b := .pt) (fanBranchP φ ψ termX branchSimplex branchS 0)
      (.single (fanBranchP φ ψ termX branchSimplex branchS 1)))

/-- The covering sequence of the fan: the region premise covered by the
`convIntro` generator (a one-premise leg), the two branch premises
covered by identities.  The covered string is the fan's `Fin`-built
premise string, reduced at the literal arity. -/
def subdivideFanDerivSeq (H : Hypernet) (φ ψ hpF : Formula)
    (termX : Term) (simplex : Simplex) (S : ExtensionSet)
    (branchSimplex : Fin 2 → Simplex) (branchS : Fin 2 → ExtensionSet)
    (hbshape : termX.bshape H = some [simplex.complex.ambDim])
    (hform : barycentricHalfspaceForm termX simplex S hpF) :
    DerivSeqT (blPresentation H)
      (subdivideFanCovered φ ψ termX simplex S branchSimplex branchS)
      (subdivideFanPs φ ψ hpF termX branchSimplex branchS)
      (𝟙 BLCtx.pt) (𝟙 BLCtx.pt) :=
  DerivSeqT.cons
    (fanRegionIntroDeriv H φ hpF termX simplex S hbshape hform)
    (DerivSeqT.cons
      (fanBranchIdDeriv H φ ψ termX branchSimplex branchS 0)
      (DerivSeqT.cons
        (fanBranchIdDeriv H φ ψ termX branchSimplex branchS 1)
        (DerivSeqT.nil (𝟙 BLCtx.pt))))

/-- **The composite derivation**: the fan generator with its region
premise covered by `convIntro` and its branch premises covered by
identities — a multicell from the halfspace premise and the two branch
premises to the fan's conclusion. -/
def subdivideFanDeriv (H : Hypernet) (φ ψ hpF : Formula)
    (termX : Term) (simplex : Simplex) (S : ExtensionSet)
    (branchSimplex : Fin 2 → Simplex) (branchS : Fin 2 → ExtensionSet)
    (cert : Term)
    (hbshape : termX.bshape H = some [simplex.complex.ambDim])
    (hform : barycentricHalfspaceForm termX simplex S hpF)
    (hcover : coverInfeasibilityValid termX simplex S 2
      branchSimplex branchS cert) :
    DerivT (blPresentation H)
      (subdivideFanPs φ ψ hpF termX branchSimplex branchS)
      ((⟨φ, ψ⟩ : Sequent)) (𝟙 BLCtx.pt) (𝟙 BLCtx.pt) :=
  DerivT.subst
    (DerivT.gen (P := blPresentation H)
      (subdivideFanRule φ ψ termX simplex S branchSimplex branchS cert)
      (subdivideFanRule_gate H φ ψ termX simplex S branchSimplex branchS
        cert hcover))
    (subdivideFanDerivSeq H φ ψ hpF termX simplex S branchSimplex
      branchS hbshape hform)

/-- The fan fixture's premise string over the presented carrier. -/
def subdivideFanTops (H : Hypernet) (φ ψ hpF : Formula) (termX : Term)
    (branchSimplex : Fin 2 → Simplex) (branchS : Fin 2 → ExtensionSet) :
    LoosePath (VirtualDoubleCategoryData.Loose
      (C := Presented (blPresentation H)))
      (.of .pt) (.of .pt) :=
  .cons (b := .of .pt) (fanHalfspaceP φ hpF : Sequent)
    (.cons (b := .of .pt)
      (fanBranchP φ ψ termX branchSimplex branchS 0 : Sequent)
      (.single (fanBranchP φ ψ termX branchSimplex branchS 1 : Sequent)))

/-- The composite derivation as a multicell of the presented virtual
double category. -/
def subdivideFanCell (H : Hypernet) (φ ψ hpF : Formula) (termX : Term)
    (simplex : Simplex) (S : ExtensionSet)
    (branchSimplex : Fin 2 → Simplex) (branchS : Fin 2 → ExtensionSet)
    (cert : Term)
    (hbshape : termX.bshape H = some [simplex.complex.ambDim])
    (hform : barycentricHalfspaceForm termX simplex S hpF)
    (hcover : coverInfeasibilityValid termX simplex S 2
      branchSimplex branchS cert) :
    VirtualDoubleCategoryData.Cell (C := Presented (blPresentation H))
      (subdivideFanTops H φ ψ hpF termX branchSimplex branchS)
      ((⟨φ, ψ⟩ : Sequent) :
        VirtualDoubleCategoryData.Loose (.of .pt) (.of .pt))
      (𝟙 (Presented.of BLCtx.pt)) (𝟙 (Presented.of BLCtx.pt)) := by
  exact ⟨⟨subdivideFanDeriv H φ ψ hpF termX simplex S branchSimplex
    branchS cert hbshape hform hcover⟩⟩

/-- The composite derivation's covering, as a cell of the free
promotion. -/
def subdivideFanCovering (H : Hypernet) (φ ψ hpF : Formula)
    (termX : Term) (simplex : Simplex) (S : ExtensionSet)
    (branchSimplex : Fin 2 → Simplex) (branchS : Fin 2 → ExtensionSet)
    (cert : Term)
    (hbshape : termX.bshape H = some [simplex.complex.ambDim])
    (hform : barycentricHalfspaceForm termX simplex S hpF)
    (hcover : coverInfeasibilityValid termX simplex S 2
      branchSimplex branchS cert) :
    PseudoDoubleCategoryStruct.Cell
      (C := FreePromotion (Presented (blPresentation H)))
      (a := .of (.of .pt)) (b := .of (.of .pt))
      (c := .of (.of .pt)) (d := .of (.of .pt))
      (subdivideFanTops H φ ψ hpF termX branchSimplex branchS)
      (LoosePath.single ((⟨φ, ψ⟩ : Sequent) :
        VirtualDoubleCategoryData.Loose (Presented.of BLCtx.pt)
          (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt))) := by
  exact ⟨⟨(VirtualDoubleCategoryStruct.CellSeq.singleton
    (subdivideFanCell H φ ψ hpF termX simplex S branchSimplex branchS
      cert hbshape hform hcover)).castDom (LoosePath.comp_nil _)⟩⟩

/-- **The fan fixture: a `Fin`-built premise string, a mixed three-leg
covering with a one-premise generator leg, composed through the
universal property, landing at the checker face.**  From the validity
of the halfspace premise and the two branch premises — the region
premise is discharged inside the derivation by `convIntro` — the
vanishing of the upper probability of the fan conclusion's complement,
with the proof term routed through the promoted functor's action on the
composite covering cell. -/
theorem subdivideFan_face_through_promotion (H : Hypernet)
    (φ ψ hpF : Formula) (termX : Term) (simplex : Simplex)
    (S : ExtensionSet) (branchSimplex : Fin 2 → Simplex)
    (branchS : Fin 2 → ExtensionSet) (cert : Term)
    (hbshape : termX.bshape H = some [simplex.complex.ambDim])
    (hform : barycentricHalfspaceForm termX simplex S hpF)
    (hcover : coverInfeasibilityValid termX simplex S 2
      branchSimplex branchS cert)
    (h₁ : Sequent.semanticallyValid H ⟨φ, hpF⟩)
    (h₂ : Sequent.semanticallyValid H
      ⟨.and φ (.inRegion termX (branchSimplex 0) (branchS 0)), ψ⟩)
    (h₃ : Sequent.semanticallyValid H
      ⟨.and φ (.inRegion termX (branchSimplex 1) (branchS 1)), ψ⟩) :
    Plain.upperProb (Plain.admCyl H ⟨φ, ψ⟩) (Plain.postEvt H ⟨φ, ψ⟩)ᶜ = 0 := by
  have himp := ((qtslSemBL H).mapCell
    (subdivideFanCovering H φ ψ hpF termX simplex S branchSimplex
      branchS cert hbshape hform hcover)).down
  exact (Plain.semanticallyValid_iff_face H ⟨φ, ψ⟩).mp
    (himp ⟨h₁, h₂, h₃, trivial⟩).1

/-!
## The syzygy-pair fixture: a list-built premise string, bare generator

The `syzygy` generator on the ground two-component list, entered bare
(the cut pattern), its seven side conditions as hypotheses: the
H-parametrized payload (`SyzygyStep H`) is reassembled from the
constructor's data and the gate inside the component, so the fixture
exercises the list builder in the presented artifact and the payload
reassembly end to end.  (No cheap in-derivation discharge exists for
syzygy component premises: they are constrained only through the
combination checker, whose concrete witnesses are rational-arithmetic
decision-procedure territory — the CertRows posture.) -/

/-- The syzygy instance on the two-component list. -/
def syzygyPairRule (seq c₁ c₂ : Sequent) (combination conclusion : Term) :
    BLRule :=
  .syzygy seq [c₁, c₂] combination conclusion

/-- The pair's side conditions, hypotheses through and through — the
seven proof fields of the `SyzygyStep` payload. -/
theorem syzygyPairRule_gate (H : Hypernet) (seq c₁ c₂ : Sequent)
    (combination conclusion : Term)
    (hpreC : ∀ c ∈ [c₁, c₂], premiseContains seq.pre c.pre)
    (hshape : ∃ s, conclusion.bshape H = some s)
    (hfin : conclusion.finWires H)
    (hwpos : ∀ w ∈ seq.pre.freeWires ++ conclusion.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
    (hcompPos : ∀ c ∈ [c₁, c₂], ∀ w ∈ c.post.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
    (hvalid : syzygyCombinationValid combination [c₁, c₂] seq.pre
      conclusion)
    (hform : syzygyConclusionForm conclusion seq.post) :
    (blPresentation H).gate (syzygyPairRule seq c₁ c₂ combination
      conclusion) :=
  ⟨hpreC, hshape, hfin, hwpos, hcompPos, hvalid, hform⟩

/-- The pair fixture's premise string over the presented carrier. -/
def syzygyPairTops (H : Hypernet) (c₁ c₂ : Sequent) :
    LoosePath (VirtualDoubleCategoryData.Loose
      (C := Presented (blPresentation H)))
      (.of .pt) (.of .pt) :=
  .cons (b := .of .pt) (c₁ : Sequent) (.single (c₂ : Sequent))

/-- The syzygy generator as a multicell of the presented virtual double
category: the list-built premise string reduces to the pair. -/
def syzygyPairCell (H : Hypernet) (seq c₁ c₂ : Sequent)
    (combination conclusion : Term)
    (hpreC : ∀ c ∈ [c₁, c₂], premiseContains seq.pre c.pre)
    (hshape : ∃ s, conclusion.bshape H = some s)
    (hfin : conclusion.finWires H)
    (hwpos : ∀ w ∈ seq.pre.freeWires ++ conclusion.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
    (hcompPos : ∀ c ∈ [c₁, c₂], ∀ w ∈ c.post.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
    (hvalid : syzygyCombinationValid combination [c₁, c₂] seq.pre
      conclusion)
    (hform : syzygyConclusionForm conclusion seq.post) :
    VirtualDoubleCategoryData.Cell (C := Presented (blPresentation H))
      (syzygyPairTops H c₁ c₂)
      ((seq : Sequent) :
        VirtualDoubleCategoryData.Loose (.of .pt) (.of .pt))
      (𝟙 (Presented.of BLCtx.pt)) (𝟙 (Presented.of BLCtx.pt)) := by
  exact ⟨⟨DerivT.gen (P := blPresentation H)
    (syzygyPairRule seq c₁ c₂ combination conclusion)
    (syzygyPairRule_gate H seq c₁ c₂ combination conclusion
      hpreC hshape hfin hwpos hcompPos hvalid hform)⟩⟩

/-- The pair generator's covering, as a cell of the free promotion. -/
def syzygyPairCovering (H : Hypernet) (seq c₁ c₂ : Sequent)
    (combination conclusion : Term)
    (hpreC : ∀ c ∈ [c₁, c₂], premiseContains seq.pre c.pre)
    (hshape : ∃ s, conclusion.bshape H = some s)
    (hfin : conclusion.finWires H)
    (hwpos : ∀ w ∈ seq.pre.freeWires ++ conclusion.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
    (hcompPos : ∀ c ∈ [c₁, c₂], ∀ w ∈ c.post.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
    (hvalid : syzygyCombinationValid combination [c₁, c₂] seq.pre
      conclusion)
    (hform : syzygyConclusionForm conclusion seq.post) :
    PseudoDoubleCategoryStruct.Cell
      (C := FreePromotion (Presented (blPresentation H)))
      (a := .of (.of .pt)) (b := .of (.of .pt))
      (c := .of (.of .pt)) (d := .of (.of .pt))
      (syzygyPairTops H c₁ c₂)
      (LoosePath.single ((seq : Sequent) :
        VirtualDoubleCategoryData.Loose (Presented.of BLCtx.pt)
          (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt))) := by
  exact ⟨⟨(VirtualDoubleCategoryStruct.CellSeq.singleton
    (syzygyPairCell H seq c₁ c₂ combination conclusion hpreC hshape hfin
      hwpos hcompPos hvalid hform)).castDom (LoosePath.comp_nil _)⟩⟩

/-- **The pair fixture: a list-built premise string, the payload
reassembled behind the promotion, landing at the checker face.**  From
the validity of the two components and the payload's seven side
conditions, the vanishing of the upper probability of the syzygy
conclusion's complement, with the proof term routed through the
promoted functor's action on the pair covering cell. -/
theorem syzygyPair_face_through_promotion (H : Hypernet)
    (seq c₁ c₂ : Sequent) (combination conclusion : Term)
    (hpreC : ∀ c ∈ [c₁, c₂], premiseContains seq.pre c.pre)
    (hshape : ∃ s, conclusion.bshape H = some s)
    (hfin : conclusion.finWires H)
    (hwpos : ∀ w ∈ seq.pre.freeWires ++ conclusion.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
    (hcompPos : ∀ c ∈ [c₁, c₂], ∀ w ∈ c.post.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
    (hvalid : syzygyCombinationValid combination [c₁, c₂] seq.pre
      conclusion)
    (hform : syzygyConclusionForm conclusion seq.post)
    (hv₁ : c₁.semanticallyValid H) (hv₂ : c₂.semanticallyValid H) :
    Plain.upperProb (Plain.admCyl H seq) (Plain.postEvt H seq)ᶜ = 0 := by
  have himp := ((qtslSemBL H).mapCell
    (syzygyPairCovering H seq c₁ c₂ combination conclusion hpreC hshape
      hfin hwpos hcompPos hvalid hform)).down
  exact (Plain.semanticallyValid_iff_face H seq).mp
    (himp ⟨hv₁, hv₂, trivial⟩).1

/-!
## The antisym fixture: a two-premise generator, both legs discharged

The `antisym` generator at the constant pair `(2 + 4)`/`6`, with BOTH
premises — `φ ⊢ (2 + 4) ≤ 6` and `φ ⊢ (2 + 4) ≥ 6` — discharged
*inside the derivation* by `pConstExact` legs (closed evaluation).  One
shape past the relu chain: a TWO-premise generator covered entirely by
zero-premise legs, so the splice flattens a two-leg covering to the
empty premise string (the relu chain's covering had one leg) — the
endpoint carries no validity hypotheses at all. -/

/-- The `≤` premise `φ ⊢ (2 + 4) ≤ 6`. -/
def antisymLePremise (φ : Formula) : Sequent :=
  ⟨φ, .atom .le sumTerm (.const 6)⟩

/-- The `≥` premise `φ ⊢ (2 + 4) ≥ 6`. -/
def antisymGePremise (φ : Formula) : Sequent :=
  ⟨φ, .atom .ge sumTerm (.const 6)⟩

/-- The conclusion `φ ⊢ (2 + 4) = 6`. -/
def antisymConcl (φ : Formula) : Sequent :=
  ⟨φ, .atom .eq sumTerm (.const 6)⟩

/-- The `antisym` instance at the constant pair. -/
def antisymConstRule (φ : Formula) : BLRule :=
  .antisym (antisymConcl φ) (antisymLePremise φ) (antisymGePremise φ)
    sumTerm (.const 6)

/-- The antisym instance's gate holds definitionally: all five side
conditions are shape equations between literal formulas. -/
theorem antisymConstRule_gate (H : Hypernet) (φ : Formula) :
    (blPresentation H).gate (antisymConstRule φ) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The `pConstExact` instance discharging the `≤` premise by closed
evaluation. -/
def pConstLeRule (φ : Formula) : BLRule :=
  .pConstExact (antisymLePremise φ) sumTerm (.const 6) .le

/-- The evaluation gate: `(2 + 4) ≤ 6` computes. -/
theorem pConstLeRule_gate (H : Hypernet) (φ : Formula) :
    (blPresentation H).gate (pConstLeRule φ) := by
  refine ⟨?_, rfl⟩
  norm_num [Formula.evalClosed, Term.evalQ?, BowTie.evalQ]

/-- The `pConstExact` instance discharging the `≥` premise by closed
evaluation. -/
def pConstGeRule (φ : Formula) : BLRule :=
  .pConstExact (antisymGePremise φ) sumTerm (.const 6) .ge

/-- The evaluation gate: `(2 + 4) ≥ 6` computes. -/
theorem pConstGeRule_gate (H : Hypernet) (φ : Formula) :
    (blPresentation H).gate (pConstGeRule φ) := by
  refine ⟨?_, rfl⟩
  norm_num [Formula.evalClosed, Term.evalQ?, BowTie.evalQ]

/-- The `≤` leg as a standalone zero-premise derivation. -/
def pConstLeDeriv (H : Hypernet) (φ : Formula) :
    DerivT (blPresentation H) .nil (antisymLePremise φ)
      (𝟙 BLCtx.pt) (𝟙 BLCtx.pt) :=
  DerivT.gen (P := blPresentation H) (pConstLeRule φ)
    (pConstLeRule_gate H φ)

/-- The `≥` leg as a standalone zero-premise derivation. -/
def pConstGeDeriv (H : Hypernet) (φ : Formula) :
    DerivT (blPresentation H) .nil (antisymGePremise φ)
      (𝟙 BLCtx.pt) (𝟙 BLCtx.pt) :=
  DerivT.gen (P := blPresentation H) (pConstGeRule φ)
    (pConstGeRule_gate H φ)

/-- The covering sequence: both premises covered by zero-premise
`pConstExact` legs — the flattened domain is empty. -/
def antisymConstDerivSeq (H : Hypernet) (φ : Formula) :
    DerivSeqT (blPresentation H)
      (.cons (b := .pt) (antisymLePremise φ)
        (.single (antisymGePremise φ)))
      .nil (𝟙 BLCtx.pt) (𝟙 BLCtx.pt) :=
  DerivSeqT.cons (pConstLeDeriv H φ)
    (DerivSeqT.cons (pConstGeDeriv H φ) (DerivSeqT.nil (𝟙 BLCtx.pt)))

/-- **The composite derivation**: the `antisym` generator with both
inequality premises covered by `pConstExact` generators — a premise-free
multicell concluding `φ ⊢ (2 + 4) = 6`. -/
def antisymConstDeriv (H : Hypernet) (φ : Formula) :
    DerivT (blPresentation H) .nil (antisymConcl φ)
      (𝟙 BLCtx.pt) (𝟙 BLCtx.pt) :=
  DerivT.subst
    (DerivT.gen (P := blPresentation H) (antisymConstRule φ)
      (antisymConstRule_gate H φ))
    (antisymConstDerivSeq H φ)

/-- The antisym composite's (empty) premise string over the presented
carrier. -/
def antisymConstTops (H : Hypernet) :
    LoosePath (VirtualDoubleCategoryData.Loose
      (C := Presented (blPresentation H)))
      (.of .pt) (.of .pt) :=
  .nil

/-- The composite derivation as a multicell of the presented virtual
double category. -/
def antisymConstCell (H : Hypernet) (φ : Formula) :
    VirtualDoubleCategoryData.Cell (C := Presented (blPresentation H))
      (antisymConstTops H) ((antisymConcl φ) :
        VirtualDoubleCategoryData.Loose (.of .pt) (.of .pt))
      (𝟙 (Presented.of BLCtx.pt)) (𝟙 (Presented.of BLCtx.pt)) := by
  exact ⟨⟨antisymConstDeriv H φ⟩⟩

/-- The composite derivation's covering, as a cell of the free
promotion. -/
def antisymConstCovering (H : Hypernet) (φ : Formula) :
    PseudoDoubleCategoryStruct.Cell
      (C := FreePromotion (Presented (blPresentation H)))
      (a := .of (.of .pt)) (b := .of (.of .pt))
      (c := .of (.of .pt)) (d := .of (.of .pt))
      (antisymConstTops H)
      (LoosePath.single ((antisymConcl φ) :
        VirtualDoubleCategoryData.Loose (Presented.of BLCtx.pt)
          (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt))) := by
  exact ⟨⟨(VirtualDoubleCategoryStruct.CellSeq.singleton
    (antisymConstCell H φ)).castDom (LoosePath.comp_nil _)⟩⟩

/-- **The antisym fixture: a two-premise generator covered entirely by
closed evaluation, landing at the checker face with no validity
hypotheses.**  Both inequality premises are discharged inside the
derivation, so the vanishing of the upper probability of the equality
conclusion's complement is obtained from kernel computation alone, with
the proof term routed through the promoted functor's action on the
composite covering cell. -/
theorem antisymConst_face_through_promotion (H : Hypernet) (φ : Formula) :
    Plain.upperProb
      (Plain.admCyl H ⟨φ, .atom .eq (.add (.const 2) (.const 4)) (.const 6)⟩)
      (Plain.postEvt H
        ⟨φ, .atom .eq (.add (.const 2) (.const 4)) (.const 6)⟩)ᶜ = 0 := by
  have himp := ((qtslSemBL H).mapCell (antisymConstCovering H φ)).down
  exact (Plain.semanticallyValid_iff_face H (antisymConcl φ)).mp
    (himp trivial).1

end QtslSem

end SuFunctor
