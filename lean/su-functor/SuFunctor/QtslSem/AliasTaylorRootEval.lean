import SuFunctor.QtslSem.BLFactoring
import Qtsl.Elaborators

/-!
# TaylorBound and RootEval: the FULL alias-derivation fixtures

The two class-stratum aliases whose elaboration target is the **wired**
`pConstExact` generator — per the catalogue's Group A rows, tier
**alias** → `pConstExact` — and therefore the only two of the family
that run the FULL `AliasSmallGain` recipe today: derivation-calculus
cells over the presented carrier, coverings into the free promotion,
face theorems through BOTH promoted functors, checker-face endpoints.
(The wave-1 structural/path-sugar fixtures transposed the recipe to
lemma level because their targets are unwired QTSL rules; here the
warrant stratum — `Qtsl.Elaborators`, ported for this fixture — meets
a live generator, and nothing is transposed.)

## The recipe, at the zero-premise target

`pConstExact` takes NO premises and its presentation gate is two
conjuncts (the closed evaluation and the post identity), so the
hypothesis-count collapse at this pair is **total**: the alias
structures carry both gate conjuncts as proof fields, the premise
string is `.nil`, and the generic face theorems take *zero*
hypotheses — kernel computation alone reaches the checker face
(contrast `AliasSmallGain`, whose faces keep the four premise
validities).  Each alias also carries a distinguishing **semantic
face** from the structure alone, on the far side of the kernel:

* `TaylorBoundStep.le_exp` — `(q : ℝ) ≤ e^{θT}` through the
  nonneg-remainder enclosure: the transcendental conclusion the
  checker never sees.
* `RootEvalStep.member` — `V(x₀) ≤ thr` exactly: the `QSat/eval`
  leaf's semantic witness (the record's `eval` field is this leaf,
  per the QSatFromRegion dissolution).

Neither structure mentions a hypernet: the `pConstExact` gate consults
no declaration tables, so the alias data is H-free and the fixtures
are generic in BOTH the ambient hypernet and the pre-formula — H
enters only at the semantic endpoint.
-/

namespace SuFunctor

namespace QtslSem

open PPLC CategoryTheory VdcPresentation
open VirtualDoubleCategoryData

/-!
## TaylorBound: structure, elaboration, gate
-/

/-- A TaylorBound step: the deadline battery's rational surrogate
`q ≤ Σ_{k ≤ n} (θT)^k / k!`.  Data fields carry the instance; the two
proof fields are exactly the `pConstExact` gate's two conjuncts (the
checked closed comparison and the post identity); `thetaNonneg` is the
alias's own side condition, load-bearing only for the semantic face
(`le_exp` — the negative-argument counterexample lives in the proof
section). -/
structure TaylorBoundStep where
  seq : Sequent
  q : Rat
  theta : Rat
  T : Nat
  n : Nat
  thetaNonneg : 0 ≤ theta
  leafEval : (taylorFormula q theta T n).evalClosed = some true
  postEq : seq.post = taylorFormula q theta T n

/-- The elaboration of a TaylorBound step: the `pConstExact` generator
with computed arguments — left side the literal `q`, right side the
producer-expanded partial sum.  TaylorBound has no constructor of its
own — this computation is its entire derivation-calculus presence. -/
def taylorRule (st : TaylorBoundStep) : BLRule :=
  .pConstExact st.seq (.const st.q)
    (.const (taylorPartialSum st.theta st.T st.n)) .le

/-- **The generic gate lemma**: the elaborated node's gate is
discharged entirely from the alias structure's fields — the
`pConstExact` gate's two conjuncts are `leafEval` and `postEq`,
verbatim.  No hypotheses beyond the structure. -/
theorem taylorRule_gate (H : Hypernet) (st : TaylorBoundStep) :
    (blPresentation H).gate (taylorRule st) :=
  ⟨st.leafEval, st.postEq⟩

/-- **The semantic face from the structure alone**: the checked wire
comparison bounds `q` by `e^{θT}` — the transcendental conclusion
appears in no field and in no gate; it lives here, on the far side of
the kernel replay. -/
theorem TaylorBoundStep.le_exp (st : TaylorBoundStep) :
    (st.q : ℝ) ≤ Real.exp (st.theta * st.T) :=
  taylorElab_le_exp st.thetaNonneg st.leafEval

/-!
## RootEval: structure, elaboration, gate
-/

/-- A RootEval step: membership of the init point in the root atom by
exact rational evaluation, sublevel branch — `V(x₀) ≤ thr` with the
left side the closed substituted term.  The two proof fields are the
`pConstExact` gate's two conjuncts. -/
structure RootEvalStep where
  seq : Sequent
  x0 : Nat → Rat
  V : QArith.Poly
  thr : Rat
  leafEval : (rootEvalFormula x0 V thr).evalClosed = some true
  postEq : seq.post = rootEvalFormula x0 V thr

/-- The elaboration of a RootEval step: the `pConstExact` generator
with computed arguments — left side the closed polynomial term at the
point, right side the threshold literal. -/
def rootEvalRule (st : RootEvalStep) : BLRule :=
  .pConstExact st.seq (polyClosedTerm st.x0 st.V) (.const st.thr) .le

/-- **The generic gate lemma**: the two conjuncts are the structure's
two proof fields, verbatim. -/
theorem rootEvalRule_gate (H : Hypernet) (st : RootEvalStep) :
    (blPresentation H).gate (rootEvalRule st) :=
  ⟨st.leafEval, st.postEq⟩

/-- **The semantic face from the structure alone**: the checker's
`true` verdict IS the exact membership inequality — the `QSat/eval`
leaf's semantic witness, through the wire-level exactness identity. -/
theorem RootEvalStep.member (st : RootEvalStep) :
    QArith.Poly.eval st.x0 st.V ≤ st.thr :=
  (rootEvalFormula_true_iff st.x0 st.V st.thr).mp st.leafEval

/-!
## Cells and coverings (shared plumbing, zero-premise form)

The premise string is `.nil` — the `antisymConst` plumbing, with the
generator entered bare rather than under a `subst`.
-/

/-- The empty premise string over the presented carrier (the named,
ground-typed path def — the fixture-path discipline; the promotion
cell's tops slot does not resolve a dotted `.nil` through its
unfolding). -/
def nilTops (H : Hypernet) :
    LoosePath (VirtualDoubleCategoryData.Loose
      (C := Presented (blPresentation H)))
      (.of .pt) (.of .pt) :=
  .nil

/-- The elaborated TaylorBound step as a multicell of the presented
virtual double category: one `pConstExact` generator, entered bare,
with the empty premise string. -/
def taylorCell (H : Hypernet) (st : TaylorBoundStep) :
    VirtualDoubleCategoryData.Cell (C := Presented (blPresentation H))
      (nilTops H)
      ((st.seq : Sequent) :
        VirtualDoubleCategoryData.Loose (.of .pt) (.of .pt))
      (𝟙 (Presented.of BLCtx.pt)) (𝟙 (Presented.of BLCtx.pt)) := by
  exact ⟨⟨DerivT.gen (P := blPresentation H) (taylorRule st)
    (taylorRule_gate H st)⟩⟩

/-- The elaborated TaylorBound step's covering, as a cell of the free
promotion: the singleton covering of the conclusion by the
zero-premise multicell. -/
def taylorCovering (H : Hypernet) (st : TaylorBoundStep) :
    PseudoDoubleCategoryStruct.Cell
      (C := FreePromotion (Presented (blPresentation H)))
      (a := .of (.of .pt)) (b := .of (.of .pt))
      (c := .of (.of .pt)) (d := .of (.of .pt))
      (nilTops H)
      (LoosePath.single ((st.seq : Sequent) :
        VirtualDoubleCategoryData.Loose (Presented.of BLCtx.pt)
          (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt))) := by
  exact ⟨⟨(VirtualDoubleCategoryStruct.CellSeq.singleton
    (taylorCell H st)).castDom (LoosePath.comp_nil _)⟩⟩

/-- The elaborated RootEval step as a multicell of the presented
virtual double category. -/
def rootEvalCell (H : Hypernet) (st : RootEvalStep) :
    VirtualDoubleCategoryData.Cell (C := Presented (blPresentation H))
      (nilTops H)
      ((st.seq : Sequent) :
        VirtualDoubleCategoryData.Loose (.of .pt) (.of .pt))
      (𝟙 (Presented.of BLCtx.pt)) (𝟙 (Presented.of BLCtx.pt)) := by
  exact ⟨⟨DerivT.gen (P := blPresentation H) (rootEvalRule st)
    (rootEvalRule_gate H st)⟩⟩

/-- The elaborated RootEval step's covering. -/
def rootEvalCovering (H : Hypernet) (st : RootEvalStep) :
    PseudoDoubleCategoryStruct.Cell
      (C := FreePromotion (Presented (blPresentation H)))
      (a := .of (.of .pt)) (b := .of (.of .pt))
      (c := .of (.of .pt)) (d := .of (.of .pt))
      (nilTops H)
      (LoosePath.single ((st.seq : Sequent) :
        VirtualDoubleCategoryData.Loose (Presented.of BLCtx.pt)
          (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt))) := by
  exact ⟨⟨(VirtualDoubleCategoryStruct.CellSeq.singleton
    (rootEvalCell H st)).castDom (LoosePath.comp_nil _)⟩⟩

/-!
## The face theorems, both carriers, ZERO hypotheses

Contrast `smallGain_face_through_promotion`'s four premise validities:
here every gate conjunct rides the structure and the generator takes
no premises, so kernel computation alone reaches the checker face.
-/

/-- **The TaylorBound fixture: a TaylorBound step, elaborated to its
`pConstExact` node and composed through the universal property, lands
at the checker face with no hypotheses at all.** -/
theorem taylor_face_through_promotion (H : Hypernet)
    (st : TaylorBoundStep) :
    Plain.upperProb (Plain.admCyl H st.seq)
      (Plain.postEvt H st.seq)ᶜ = 0 := by
  have himp := ((qtslSemBL H).mapCell (taylorCovering H st)).down
  exact (Plain.semanticallyValid_iff_face H st.seq).mp (himp trivial).1

/-- The TaylorBound fixture's judgment-layer twin: same endpoint, the
route through the thin carrier. -/
theorem taylor_face_through_promotionJ (H : Hypernet)
    (st : TaylorBoundStep) :
    Plain.upperProb (Plain.admCyl H st.seq)
      (Plain.postEvt H st.seq)ᶜ = 0 := by
  obtain ⟨_, himp⟩ :=
    ((qtslSemBLJ H).mapCell (taylorCovering H st)).down
  exact (Plain.semanticallyValid_iff_face H st.seq).mp (himp trivial).1

/-- **The RootEval fixture: the membership leaf, elaborated and
composed through the universal property to the checker face — no
hypotheses.** -/
theorem rootEval_face_through_promotion (H : Hypernet)
    (st : RootEvalStep) :
    Plain.upperProb (Plain.admCyl H st.seq)
      (Plain.postEvt H st.seq)ᶜ = 0 := by
  have himp := ((qtslSemBL H).mapCell (rootEvalCovering H st)).down
  exact (Plain.semanticallyValid_iff_face H st.seq).mp (himp trivial).1

/-- The RootEval fixture's judgment-layer twin. -/
theorem rootEval_face_through_promotionJ (H : Hypernet)
    (st : RootEvalStep) :
    Plain.upperProb (Plain.admCyl H st.seq)
      (Plain.postEvt H st.seq)ᶜ = 0 := by
  obtain ⟨_, himp⟩ :=
    ((qtslSemBLJ H).mapCell (rootEvalCovering H st)).down
  exact (Plain.semanticallyValid_iff_face H st.seq).mp (himp trivial).1

/-!
## The concrete TaylorBound instance: q = 8/3, θ = 1/2, T = 2, n = 3

The order-3 partial sum of `e^{θT} = e¹` is exactly
`1 + 1 + 1/2 + 1/6 = 8/3`, so the leaf holds **tight at equality** —
any truncation of the sum drops the right side strictly below `q`,
which is what makes the constants mutant-sensitive (a partial-sum
corruption cannot be absorbed by slack).  The semantic face reads
`8/3 ≤ e` — true with margin ≈ 0.052, the enclosure's honesty visible
in the constants.  Generic in the ambient hypernet AND the
pre-formula: the gate consults neither.
-/

namespace TaylorDemo

/-- The concrete step, generic in the pre-formula. -/
def step (φ : Formula) : TaylorBoundStep where
  seq := ⟨φ, taylorFormula (8/3) (1/2) 2 3⟩
  q := 8/3
  theta := 1/2
  T := 2
  n := 3
  thetaNonneg := by norm_num
  leafEval := by
    first
      | decide +kernel
      | norm_num [taylorFormula, taylorPartialSum, Finset.sum_range_succ,
          Nat.factorial, Formula.evalClosed, Term.evalQ?, BowTie.evalQ]
  postEq := rfl

/-- **The concrete fixture at the checker face**, both quantifiers
outermost: over any hypernet and any pre-formula, the upper
probability of the Taylor leaf's complement vanishes — kernel
computation alone. -/
theorem face (H : Hypernet) (φ : Formula) :
    Plain.upperProb
      (Plain.admCyl H ⟨φ, taylorFormula (8/3) (1/2) 2 3⟩)
      (Plain.postEvt H ⟨φ, taylorFormula (8/3) (1/2) 2 3⟩)ᶜ = 0 :=
  taylor_face_through_promotion H (step φ)

/-- The judgment-layer twin. -/
theorem faceJ (H : Hypernet) (φ : Formula) :
    Plain.upperProb
      (Plain.admCyl H ⟨φ, taylorFormula (8/3) (1/2) 2 3⟩)
      (Plain.postEvt H ⟨φ, taylorFormula (8/3) (1/2) 2 3⟩)ᶜ = 0 :=
  taylor_face_through_promotionJ H (step φ)

/-- The concrete semantic face: `8/3 ≤ e` (as `e^{(1/2)·2}`), from the
structure alone — the transcendental endpoint the checker never
computed. -/
theorem le_exp (φ : Formula) :
    ((8/3 : Rat) : ℝ) ≤ Real.exp ((1/2 : Rat) * (2 : Nat)) :=
  (step φ).le_exp

end TaylorDemo

/-!
## The concrete RootEval instance: V = (1/4)x₀² + 3x₀x₁ + 2 at (2, −1/3)

`V(x₀) = 1 − 2 + 2 = 1 = thr`: **tight at equality**.  The `1/4`
coefficient is load-bearing for mutant sensitivity: a coefficient-drop
corruption of the closed-term builder REPLACES each coefficient by 1,
raising the evaluation to `4 − 2/3 + 1 = 13/3 > 1` — the leaf refuses.
(First-draft constants `x² + 3xy + 2` at `(3/2, −1/3)` made that
corruption invisible — the mutated and true evaluations coincided at
`11/4`; these constants were chosen against that, the `λ = 2` lesson
of the SmallGain exemplar in its contrapositive form.)
-/

namespace RootDemo

/-- The evaluation point: `(2, −1/3, 0, 0, …)`. -/
def x0 : Nat → Rat :=
  fun i => if i = 0 then 2 else if i = 1 then -(1/3) else 0

/-- The sparse polynomial `(1/4)·x₀² + 3·x₀x₁ + 2`. -/
def V : QArith.Poly :=
  [([(0, 2)], 1/4), ([(0, 1), (1, 1)], 3), ([], 2)]

/-- The concrete step, generic in the pre-formula. -/
def step (φ : Formula) : RootEvalStep where
  seq := ⟨φ, rootEvalFormula x0 V 1⟩
  x0 := x0
  V := V
  thr := 1
  leafEval := by
    first
      | decide +kernel
      | norm_num [rootEvalFormula, polyClosedTerm, monoClosedTerm,
          constPowTerm, x0, V, Formula.evalClosed, Term.evalQ?,
          BowTie.evalQ]
  postEq := rfl

/-- **The concrete fixture at the checker face**: over any hypernet
and any pre-formula, the membership leaf's complement has vanishing
upper probability — kernel computation alone. -/
theorem face (H : Hypernet) (φ : Formula) :
    Plain.upperProb (Plain.admCyl H ⟨φ, rootEvalFormula x0 V 1⟩)
      (Plain.postEvt H ⟨φ, rootEvalFormula x0 V 1⟩)ᶜ = 0 :=
  rootEval_face_through_promotion H (step φ)

/-- The judgment-layer twin. -/
theorem faceJ (H : Hypernet) (φ : Formula) :
    Plain.upperProb (Plain.admCyl H ⟨φ, rootEvalFormula x0 V 1⟩)
      (Plain.postEvt H ⟨φ, rootEvalFormula x0 V 1⟩)ᶜ = 0 :=
  rootEval_face_through_promotionJ H (step φ)

/-- The concrete semantic witness: `V(x₀) = 1 ≤ 1`, exactly — the
`QSat/eval` leaf's membership, recovered from the checker's verdict
rather than recomputed. -/
theorem member (φ : Formula) : QArith.Poly.eval x0 V ≤ 1 :=
  (step φ).member

end RootDemo

end QtslSem

end SuFunctor
