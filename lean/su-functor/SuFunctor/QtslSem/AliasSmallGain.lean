import SuFunctor.QtslSem.BLFactoring
import Qtsl.Composition

/-!
# The alias-derivation fixture: SmallGain elaborated to its Syzygy node

SmallGain is a **tier-3 alias** (design ruling, 2026-07-18; the
BL-rules catalogue row, composition rules): it has no `RuleTag`, no wire node, and no
`BLRule` constructor — its conclusion is *identically* the
$(1,\lambda,1,1)$-weighted Syzygy combination of its four premises, so
a SmallGain step enters the derivation calculus as **one `syzygy`
generator with computed arguments**, and the semantic functor correctly
has no smallGain component.  This file is the exemplar of the
alias-derivation pattern the class-stratum aliases copy.

## The recipe (what varies per alias, what is shared)

1. **Alias structure** (varies; already producer-side): a structure
   whose data fields carry the instance and whose proof fields carry
   both the alias's side conditions and the elaboration identity — here
   `SmallGainStep H` (`Qtsl.Composition`), whose `foldEq` field is the
   $(1,\lambda,1,1)$ cancellation and whose `combTerm` *is* the fold.
2. **Elaboration function** (varies; one line): alias structure to the
   target core generator with computed arguments — here
   `smallGainRule st = .syzygy st.seq st.components st.combTerm
   st.concl`.  No new generator enters the presentation.
3. **Generic gate lemma** (shared shape): the target generator's gate
   discharged *entirely from the structure's fields* — here via the
   kernel-checked collapse `SmallGainStep.toSyzygy`, whose seven proof
   fields are the syzygy gate's seven conjuncts verbatim.  Zero
   hypotheses beyond the structure.
4. **Cell and covering** (shared): the elaborated generator entered
   bare (`DerivT.gen`), singleton covering into the free promotion —
   the settled fixture plumbing, unchanged.
5. **Generic face theorems, both carriers** (shared shape): from the
   validity of the alias's premises alone — the side conditions ride
   the structure, so *no side-condition hypotheses survive* (contrast
   the raw `syzygyPair` fixture, which takes the payload's seven side
   conditions as hypotheses: the hypothesis-count collapse is the
   measurable signature of the alias pattern).
6. **Concrete instance** (varies): concrete rationals over a small
   concrete hypernet, the elaboration identity checked as an exact
   canonical polynomial identity by kernel computation, and the
   checker-face endpoint stated with the alias's conclusion explicit.

The n-ary form (`SmallGainN`, entering the catalogue in parallel) is
shape-identical under this recipe: the components list goes
`Fin`-indexed (`LoosePath.ofFin` instead of the ground cons-chain), and
everything else is unchanged.  Its fixture is deliberately not built
here.
-/

namespace SuFunctor

namespace QtslSem

open PPLC CategoryTheory VdcPresentation
open VirtualDoubleCategoryData

/-!
## The elaboration: a SmallGain step is one syzygy generator

`SmallGainStep.combTerm` is the $(1,\lambda,1,1)$-weighted fold of the
four premise polynomials — the alias's whole content.  The elaboration
hands the syzygy generator that fold as its combination; the checker
replays a two-line polynomial identity and never sees a fixpoint.
-/

/-- The elaboration of a SmallGain step: the `syzygy` generator on the
step's four components, with the $(1,\lambda,1,1)$ fold as the
combination.  SmallGain has no constructor of its own — this
computation is its entire derivation-calculus presence. -/
def smallGainRule {H : Hypernet} (st : SmallGainStep H) : BLRule :=
  .syzygy st.seq st.components st.combTerm st.concl

/-- **The generic gate lemma**: the elaborated node's gate is
discharged entirely from the alias structure's fields — the seven
conjuncts of the syzygy gate are the seven proof fields of the
kernel-checked collapse `SmallGainStep.toSyzygy`, verbatim.  No
hypotheses beyond the structure. -/
theorem smallGainRule_gate (H : Hypernet) (st : SmallGainStep H) :
    (blPresentation H).gate (smallGainRule st) :=
  ⟨st.toSyzygy.preContains, st.toSyzygy.conclShape, st.toSyzygy.conclFin,
    st.toSyzygy.wiresPos, st.toSyzygy.compPostWiresPos, st.toSyzygy.valid,
    st.toSyzygy.postForm⟩

/-- The elaborated step's premise string over the presented carrier:
the two dissipation sequents, then the two membership sequents (the
named ground-typed path def — the fixture-path discipline). -/
def smallGainTops (H : Hypernet) (st : SmallGainStep H) :
    LoosePath (VirtualDoubleCategoryData.Loose
      (C := Presented (blPresentation H)))
      (.of .pt) (.of .pt) :=
  .cons (b := .of .pt) (st.diss1 : Sequent)
    (.cons (b := .of .pt) (st.diss2 : Sequent)
      (.cons (b := .of .pt) (st.mem1 : Sequent)
        (.single (st.mem2 : Sequent))))

/-- The elaborated SmallGain step as a multicell of the presented
virtual double category: one syzygy generator, entered bare. -/
def smallGainCell (H : Hypernet) (st : SmallGainStep H) :
    VirtualDoubleCategoryData.Cell (C := Presented (blPresentation H))
      (smallGainTops H st) ((st.seq : Sequent) :
        VirtualDoubleCategoryData.Loose (.of .pt) (.of .pt))
      (𝟙 (Presented.of BLCtx.pt)) (𝟙 (Presented.of BLCtx.pt)) := by
  exact ⟨⟨DerivT.gen (P := blPresentation H) (smallGainRule st)
    (smallGainRule_gate H st)⟩⟩

/-- The elaborated step's covering, as a cell of the free promotion:
the singleton covering of the conclusion by the syzygy multicell. -/
def smallGainCovering (H : Hypernet) (st : SmallGainStep H) :
    PseudoDoubleCategoryStruct.Cell
      (C := FreePromotion (Presented (blPresentation H)))
      (a := .of (.of .pt)) (b := .of (.of .pt))
      (c := .of (.of .pt)) (d := .of (.of .pt))
      (smallGainTops H st)
      (LoosePath.single ((st.seq : Sequent) :
        VirtualDoubleCategoryData.Loose (Presented.of BLCtx.pt)
          (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt))) := by
  exact ⟨⟨(VirtualDoubleCategoryStruct.CellSeq.singleton
    (smallGainCell H st)).castDom (LoosePath.comp_nil _)⟩⟩

/-!
## The generic face theorems: premise validity in, checker face out

Contrast the hypothesis lists with `syzygyPair_face_through_promotion`:
the seven side-condition hypotheses are gone — the alias structure
carries them — and only the four premise validities remain.
-/

/-- **The alias fixture: a SmallGain step, elaborated to its syzygy
node and composed through the universal property, lands at the checker
face.**  From the validity of the two dissipation premises and the two
membership premises alone — every side condition rides the structure —
the vanishing of the upper probability of the small-gain conclusion's
complement, with the proof term routed through the promoted functor's
action on the elaborated covering cell. -/
theorem smallGain_face_through_promotion (H : Hypernet)
    (st : SmallGainStep H)
    (h₁ : st.diss1.semanticallyValid H)
    (h₂ : st.diss2.semanticallyValid H)
    (hm₁ : st.mem1.semanticallyValid H)
    (hm₂ : st.mem2.semanticallyValid H) :
    Plain.upperProb (Plain.admCyl H st.seq)
      (Plain.postEvt H st.seq)ᶜ = 0 := by
  have himp := ((qtslSemBL H).mapCell (smallGainCovering H st)).down
  exact (Plain.semanticallyValid_iff_face H st.seq).mp
    (himp ⟨h₁, h₂, hm₁, hm₂, trivial⟩).1

/-- **The alias fixture's twin: the elaborated SmallGain step, composed
through the universal property into the judgment layer, lands at the
same checker face.**  Hypotheses and endpoint are the alias fixture's,
verbatim; the proof term routes through the promoted functor into the
carrier, on the same covering cell. -/
theorem smallGain_face_through_promotionJ (H : Hypernet)
    (st : SmallGainStep H)
    (h₁ : st.diss1.semanticallyValid H)
    (h₂ : st.diss2.semanticallyValid H)
    (hm₁ : st.mem1.semanticallyValid H)
    (hm₂ : st.mem2.semanticallyValid H) :
    Plain.upperProb (Plain.admCyl H st.seq)
      (Plain.postEvt H st.seq)ᶜ = 0 := by
  obtain ⟨_, himp⟩ :=
    ((qtslSemBLJ H).mapCell (smallGainCovering H st)).down
  exact (Plain.semanticallyValid_iff_face H st.seq).mp
    (himp ⟨h₁, h₂, hm₁, hm₂, trivial⟩).1

/-!
## The concrete instance: $\lambda = 2$, $\theta = 1/3$

A SmallGain-shaped instance over the demo hypernet (one rational wire),
at genuinely non-unit $\lambda$: at $\lambda = 1$ the $(1,\lambda,1,1)$
weights degenerate to all-ones and a corrupted weighting would be
semantically invisible; at $\lambda = 2$ the weighting is load-bearing.
The membership slacks are strictly negative (the memberships hold with
margin, not at equality), and every polynomial obligation — the two
membership identities, the $(1,\lambda,1,1)$ cancellation `foldEq`, and
the conclusion identity — is checked as an exact canonical polynomial
identity by kernel computation.

Worked constants: $e_1 = e_2 = w - 2$; $\sigma_2 = 1/100$,
$\alpha_1 = 9/200$ give $m_1 = \lambda\sigma_2 - (1-\theta)\alpha_1 =
-1/100$; $\sigma_1 = 1/50$, $\alpha_2 = 3/100$ give
$m_2 = \sigma_1 - \lambda(1-\theta)\alpha_2 = -1/50$; the fold is
$e_1 + 2e_2 + m_1 + m_2 = 3w - 603/100$, and with
$\theta(\alpha_1 + \lambda\alpha_2) = 7/200$ the Lyapunov part is
$3w - 1213/200$ — so the small-gain conclusion
$\mathcal{L}(V_1 + \lambda V_2) + \theta(\alpha_1 + \lambda\alpha_2)
\le 0$ reads $3w - 603/100 \le 0$ over the operating box $w \le 2$.
-/

namespace SmallGainDemo

open EvalDemo SoundnessDemo CompositionDemo

/-- The first membership slack: $-1/100$, strictly negative. -/
def memTerm1 : Term := .const (-(1/100))

/-- The second membership slack: $-1/50$, strictly negative. -/
def memTerm2 : Term := .const (-(1/50))

/-- The first membership sequent's conclusion. -/
def memPost1 : Formula := .atom .le memTerm1 (.const 0)

/-- The second membership sequent's conclusion. -/
def memPost2 : Formula := .atom .le memTerm2 (.const 0)

/-- The first membership premise is valid: a strictly negative constant
is at most zero, over any valuation. -/
theorem mem1Valid :
    (Sequent.mk leAtom memPost1).semanticallyValid H0 := by
  intro σ _ _
  refine ⟨⟨[], [-(1/100)], rfl⟩, ⟨[], [0], rfl⟩, rfl, rfl, ?_⟩
  show QTensor.rel2 _ _ _
  simp only [QTensor.rel2, QTensor.scalar, BowTie.holdsQ]
  first
    | decide
    | norm_num

/-- The second membership premise is valid. -/
theorem mem2Valid :
    (Sequent.mk leAtom memPost2).semanticallyValid H0 := by
  intro σ _ _
  refine ⟨⟨[], [-(1/50)], rfl⟩, ⟨[], [0], rfl⟩, rfl, rfl, ?_⟩
  show QTensor.rel2 _ _ _
  simp only [QTensor.rel2, QTensor.scalar, BowTie.holdsQ]
  first
    | decide
    | norm_num

/-- The concrete SmallGain step at $\lambda = 2$, $\theta = 1/3$: two
dissipation premises $w \le 2 \vdash w - 2 \le 0$ and two
strictly-slack membership premises, over the one-wire demo hypernet.
The four polynomial proof fields are kernel-computed exact canonical
identities. -/
def step : SmallGainStep H0 where
  seq := ⟨leAtom,
    .atom .le (.sub (.mul (.const 3) w0) (.const (603/100))) (.const 0)⟩
  diss1 := ⟨leAtom, qAtom⟩
  diss2 := ⟨leAtom, qAtom⟩
  mem1 := ⟨leAtom, memPost1⟩
  mem2 := ⟨leAtom, memPost2⟩
  lambda := 2
  theta := 1/3
  alpha1 := .const (9/200)
  alpha2 := .const (3/100)
  sigma1 := .const (1/50)
  sigma2 := .const (1/100)
  lyapTerm := .sub (.mul (.const 3) w0) (.const (1213/200))
  e1 := .sub w0 (.const 2)
  e2 := .sub w0 (.const 2)
  m1 := memTerm1
  m2 := memTerm2
  concl := .sub (.mul (.const 3) w0) (.const (603/100))
  diss1Post := rfl
  diss2Post := rfl
  mem1Post := rfl
  mem2Post := rfl
  mem1Poly := by decide +kernel
  mem2Poly := by decide +kernel
  e1IdxFree := rfl
  e2IdxFree := rfl
  m1IdxFree := rfl
  m2IdxFree := rfl
  conclIdxFree := rfl
  lambdaPos := by norm_num
  thetaLo := by norm_num
  thetaHi := by norm_num
  foldEq := by decide +kernel
  conclPoly := by decide +kernel
  postEq := rfl
  pre1 := fun a ha => ha
  pre2 := fun a ha => ha
  preM1 := fun a ha => ha
  preM2 := fun a ha => ha
  conclShape := ⟨[1], rfl⟩
  conclFin := by
    intro w hw
    have hw0 : w = 0 := by
      simpa [Term.freeWires, w0] using hw
    subst hw0
    exact ⟨⟨[1], Dtype.Q⟩, rfl, rfl⟩
  wiresPos := by
    intro w hw
    have hw0 : w = 0 := by
      simpa [Sequent.pre, Formula.freeWires, Term.freeWires, leAtom,
        w0] using hw
    subst hw0
    exact ⟨⟨[1], Dtype.Q⟩, rfl, by decide⟩
  compPostWiresPos := by
    intro c hc w hw
    have hw0 : w = 0 := by
      fin_cases hc <;>
        first
          | simpa [Formula.freeWires, Term.freeWires, qAtom, w0] using hw
          | simp [Formula.freeWires, Term.freeWires, memPost1, memPost2,
              memTerm1, memTerm2] at hw
    subst hw0
    exact ⟨⟨[1], Dtype.Q⟩, rfl, by decide⟩

/-- The concrete small-gain conclusion, explicit: over the operating
box $w \le 2$, the combined Lyapunov decrease
$\mathcal{L}(V_1 + 2V_2) + \tfrac{1}{3}(\alpha_1 + 2\alpha_2) \le 0$ —
concretely, $3w - 603/100 \le 0$. -/
def demoSeq : Sequent :=
  ⟨leAtom,
   .atom .le (.sub (.mul (.const 3) w0) (.const (603/100))) (.const 0)⟩

/-- **The concrete alias fixture at the checker face**: the
$\lambda = 2$, $\theta = 1/3$ SmallGain step, elaborated in Lean to its
single syzygy node and composed through the promoted semantics — the
upper probability of the small-gain conclusion's complement vanishes.
The premise validities are the demo's dissipation lemma (twice) and the
two membership lemmas; everything else was computed. -/
theorem demo_face :
    Plain.upperProb (Plain.admCyl H0 demoSeq)
      (Plain.postEvt H0 demoSeq)ᶜ = 0 :=
  smallGain_face_through_promotion H0 step
    supplierValid supplierValid mem1Valid mem2Valid

/-- The concrete fixture's judgment-layer twin: same step, same
endpoint, the route through the thin carrier. -/
theorem demo_faceJ :
    Plain.upperProb (Plain.admCyl H0 demoSeq)
      (Plain.postEvt H0 demoSeq)ᶜ = 0 :=
  smallGain_face_through_promotionJ H0 step
    supplierValid supplierValid mem1Valid mem2Valid

end SmallGainDemo

end QtslSem

end SuFunctor
