import SuFunctor.QtslSem.Decode.Fixture
import SuFunctor.QtslSem.BLMulti

/-!
# The decoder→BLMulti seam: decoded rows into the many-object
# presentation

The S1 fixture drove the decoded evaluation-leaf sequent through the
single-context carriers — one promoted functor per hypernet.  This
module re-routes the same decoded cargo through the many-object
presentation (`blPresentationM`), in the two shapes its design memo
names for the seam:

- **`emb`**: the decoded sequent enters as an embedded `pConstExact`
  generator at any context `⟨H⟩` (its gate transports definitionally:
  the embedded rule keeps its own gate at its context), covers into
  the free promotion, and faces through the ONE functor for all
  contexts (`qtslSemBLM`, and `qtslSemBLMJ` at the judgment layer),
  with the decode equality as the load-bearing hypothesis — the S1
  posture, verbatim.
- **`extend`**: one derivation — the decoded generator spliced into
  the cite derivation by simultaneous substitution — an empty-tops
  composite whose boundary tights are the extension arrow: from row
  bytes, through the many-object calculus, to a checker face over a
  disjoint union the rows never mentioned.  The composition happens
  inside the calculus (one covering, one `mapCell` trip), not as a
  chain of two functor trips.

The seam's data face, `satLeafSequents`, enumerates each decoded
satisfaction claim's evaluation-leaf sequent — the cargo an
`emb`-shaped generator carries — fail-closed through `leafSequent`;
this is the function the class-stratum campaign's fixtures consume
between `decodeQtslPresentationOps` and the presentation.

Fragment boundary, honest: at the v1 fragment hypernets ride as
sort-checked element references, so the contexts and unions here are
Lean-staged (`ProductLatticeDemo`'s pair at the concrete corollaries);
decoding the contexts themselves — the pinned unions as rows — is the
campaign's per-row widening.
-/

namespace SuFunctor

namespace QtslSem

namespace Decode

open PPLC PPLC.Geolog CategoryTheory VdcPresentation
open VirtualDoubleCategoryData

/-! ## The seam enumerator -/

/-- Each decoded satisfaction claim with an evaluation route yields its
leaf's concluded sequent — the cargo an `emb`-shaped generator carries
into the many-object presentation.  Fail-closed: any leaf outside the
ground fragment refuses through `leafSequent`, never a silent skip of
a claimed route. -/
def satLeafSequents (tb : QRowTbls) (pres : QtslPresentation) :
    QRes (List (Nat × Sequent)) :=
  pres.sats.filterMapM fun sat =>
    match sat.evalLeaf with
    | some p => do pure (some (sat.elem, ← leafSequent tb p))
    | none => pure none

/-- The fixture enumeration: the one staged claim yields exactly its
decoded leaf sequent.  (`rfl`, not `decide`: `Sequent` carries no
`DecidableEq` instance — kernel reduction directly.) -/
theorem satLeafSequents_fixture :
    satLeafSequents fixtureTbls fixtureExpected =
      .ok [(5, leafSeqDemo)] := by
  rfl

/-- The decoded leaf sequent is wire-free (closed constants), hence
well-scoped over every hypernet — what lets it ride an `emb` generator
at ANY context and transport along ANY extension arrow. -/
theorem leafSeqDemo_wellScoped (H : Hypernet) :
    leafSeqDemo.wellScoped H := by
  intro w hw
  rcases hw with h | h
  · simp [leafSeqDemo, Formula.freeWires] at h
  · simp [leafSeqDemo, Formula.freeWires, Term.freeWires] at h

/-! ## The emb route: the decoded generator at any context of the
many-object presentation -/

/-- The empty premise string over the many-object presented carrier at
an embedded context (named ground-typed path — the fixture-path
discipline). -/
def embDecodedTops (H : Hypernet) :
    LoosePath (VirtualDoubleCategoryData.Loose
      (C := Presented blPresentationM))
      (.of (.of H)) (.of (.of H)) :=
  .nil

/-- The decoded generator, embedded: a zero-premise multicell of the
many-object presented carrier at context `⟨H⟩`, identity tights — the
gate is the single-context gate, transported definitionally (an
embedded rule keeps its own gate at its context). -/
def embDecodedCell (H : Hypernet) :
    VirtualDoubleCategoryData.Cell (C := Presented blPresentationM)
      (embDecodedTops H)
      ((leafSeqDemo : Sequent) :
        VirtualDoubleCategoryData.Loose (.of (.of H)) (.of (.of H)))
      (𝟙 (Presented.of (BLHCtx.of H)))
      (𝟙 (Presented.of (BLHCtx.of H))) := by
  exact ⟨⟨DerivT.gen (P := blPresentationM) (.emb H decodedLeafRule)
    (decodedLeafRule_gate H)⟩⟩

/-- Its covering in the free promotion of the many-object carrier. -/
def embDecodedCovering (H : Hypernet) :
    PseudoDoubleCategoryStruct.Cell
      (C := FreePromotion (Presented blPresentationM))
      (a := .of (.of (.of H))) (b := .of (.of (.of H)))
      (c := .of (.of (.of H))) (d := .of (.of (.of H)))
      (embDecodedTops H)
      (LoosePath.single ((leafSeqDemo : Sequent) :
        VirtualDoubleCategoryData.Loose (Presented.of (BLHCtx.of H))
          (Presented.of (BLHCtx.of H))))
      (𝟙 (FreePromotion.of (Presented.of (BLHCtx.of H))))
      (𝟙 (FreePromotion.of (Presented.of (BLHCtx.of H)))) := by
  exact ⟨⟨(VirtualDoubleCategoryStruct.CellSeq.singleton
    (embDecodedCell H)).castDom (LoosePath.comp_nil _)⟩⟩

/-- **The decoded row at the checker face, through the one functor for
all contexts**: hypotheses and endpoint exactly as the single-context
S1 fixture theorem — the route now enters `blPresentationM` via `emb`
and is read by `qtslSemBLM.mapCell`.  The decode equality is the
hypothesis, so the row→SU route stays load-bearing. -/
theorem decodedLeaf_face_through_promotionM (H : Hypernet) (s : Sequent)
    (hdec : leafSequent fixtureTbls 7 = .ok s) :
    Plain.upperProb (Plain.admCyl H s) (Plain.postEvt H s)ᶜ = 0 := by
  have h2 : (Except.ok leafSeqDemo : QRes Sequent) = .ok s := by
    rw [← fixture_leaf_seq]; exact hdec
  injection h2 with h3
  subst h3
  have himp := (qtslSemBLM.mapCell (embDecodedCovering H)).down
  exact (Plain.semanticallyValid_iff_face H leafSeqDemo).mp
    (himp trivial).1

/-- The decoded row at the checker face, judgment-layer route through
the many-object carrier. -/
theorem decodedLeaf_face_through_promotionMJ (H : Hypernet) (s : Sequent)
    (hdec : leafSequent fixtureTbls 7 = .ok s) :
    Plain.upperProb (Plain.admCyl H s) (Plain.postEvt H s)ᶜ = 0 := by
  have h2 : (Except.ok leafSeqDemo : QRes Sequent) = .ok s := by
    rw [← fixture_leaf_seq]; exact hdec
  injection h2 with h3
  subst h3
  obtain ⟨_, himp⟩ := (qtslSemBLMJ.mapCell (embDecodedCovering H)).down
  exact (Plain.semanticallyValid_iff_face H leafSeqDemo).mp
    (himp trivial).1

/-! ## The extend route: the decoded generator spliced into the cite
derivation -/

/-- **The decoded cite derivation**: extend-then-weaken consuming the
decoded zero-premise generator — the `emb`-embedded decoded rule
spliced into the cite derivation by simultaneous substitution.  An
empty-tops composite whose boundary tights are the extension arrow.
(The substitution's composite boundary `𝟙 a ≫ e` is definitionally
`e`: field-wise composition, function eta, structure eta.) -/
def decodedCiteDeriv {a b : BLHCtx} (e : a ⟶ b) (rider : Formula)
    (hws : leafSeqDemo.wellScoped a.ctx) :
    DerivT blPresentationM .nil (citeFacet leafSeqDemo rider) e e :=
  DerivT.subst (citeDeriv e leafSeqDemo rider hws)
    (DerivSeqT.cons
      (DerivT.gen (P := blPresentationM) (.emb a.ctx decodedLeafRule)
        (decodedLeafRule_gate a.ctx))
      (DerivSeqT.nil (𝟙 a)))

/-- The empty premise string at a context, over the many-object
presented carrier. -/
def decodedCiteTops (a : BLHCtx) :
    LoosePath (VirtualDoubleCategoryData.Loose
      (C := Presented blPresentationM)) (.of a) (.of a) :=
  .nil

/-- The decoded cite composite as a multicell of the presented virtual
double category, framed by the extension arrow on both tight sides. -/
def decodedCiteCell {a b : BLHCtx} (e : a ⟶ b) (rider : Formula)
    (hws : leafSeqDemo.wellScoped a.ctx) :
    VirtualDoubleCategoryData.Cell (C := Presented blPresentationM)
      (decodedCiteTops a)
      ((citeFacet leafSeqDemo rider : Sequent) :
        VirtualDoubleCategoryData.Loose (.of b) (.of b))
      (e : Presented.of a ⟶ Presented.of b) e := by
  exact ⟨⟨decodedCiteDeriv e rider hws⟩⟩

/-- Its covering in the free promotion — empty tops, extension-arrow
tights. -/
def decodedCiteCovering {x y : BLHCtx} (e : x ⟶ y) (rider : Formula)
    (hws : leafSeqDemo.wellScoped x.ctx) :
    PseudoDoubleCategoryStruct.Cell
      (C := FreePromotion (Presented blPresentationM))
      (a := .of (.of x)) (b := .of (.of x))
      (c := .of (.of y)) (d := .of (.of y))
      (decodedCiteTops x)
      (LoosePath.single ((citeFacet leafSeqDemo rider : Sequent) :
        VirtualDoubleCategoryData.Loose (Presented.of y)
          (Presented.of y)))
      (e : FreePromotion.of (Presented.of x) ⟶ .of (.of y)) e := by
  exact ⟨⟨(VirtualDoubleCategoryStruct.CellSeq.singleton
    (decodedCiteCell e rider hws)).castDom (LoosePath.comp_nil _)⟩⟩

/-- **The decoded facet's validity over the extended context**: decode
equality in, validity of the cited facet over the target context out —
one covering, one `mapCell` trip; the derivation composed the decoded
generator with the transport inside the calculus. -/
theorem decodedCiteFacet_valid_through_M {a b : BLHCtx} (e : a ⟶ b)
    (rider : Formula) (s : Sequent)
    (hdec : leafSequent fixtureTbls 7 = .ok s)
    (hws : s.wellScoped a.ctx) :
    (citeFacet s rider).semanticallyValid b.ctx := by
  have h2 : (Except.ok leafSeqDemo : QRes Sequent) = .ok s := by
    rw [← fixture_leaf_seq]; exact hdec
  injection h2 with h3
  subst h3
  have himp := (qtslSemBLM.mapCell (decodedCiteCovering e rider hws)).down
  exact (himp trivial).1

/-- The decoded facet's validity through the judgment-layer route. -/
theorem decodedCiteFacet_valid_through_MJ {a b : BLHCtx} (e : a ⟶ b)
    (rider : Formula) (s : Sequent)
    (hdec : leafSequent fixtureTbls 7 = .ok s)
    (hws : s.wellScoped a.ctx) :
    (citeFacet s rider).semanticallyValid b.ctx := by
  have h2 : (Except.ok leafSeqDemo : QRes Sequent) = .ok s := by
    rw [← fixture_leaf_seq]; exact hdec
  injection h2 with h3
  subst h3
  obtain ⟨_, himp⟩ :=
    (qtslSemBLMJ.mapCell (decodedCiteCovering e rider hws)).down
  exact (himp trivial).1

/-! ## The decoded facet over disjoint unions -/

/-- The decoded facet at the checker face over a disjoint union, left
factor in (via `extLeft`). -/
theorem decodedCiteLeft_face_through_promotionM {H1 H2 : Hypernet}
    (hd : H1.WireDisjoint H2) (rider : Formula) (s : Sequent)
    (hdec : leafSequent fixtureTbls 7 = .ok s)
    (hws : s.wellScoped H1) :
    Plain.upperProb
      (Plain.admCyl (H1.disjUnion H2 hd) (citeFacet s rider))
      (Plain.postEvt (H1.disjUnion H2 hd) (citeFacet s rider))ᶜ = 0 :=
  (Plain.semanticallyValid_iff_face (H1.disjUnion H2 hd)
    (citeFacet s rider)).mp
    (decodedCiteFacet_valid_through_M (extLeft hd) rider s hdec hws)

/-- The decoded facet at the checker face over a disjoint union, right
factor in (via `extRight`). -/
theorem decodedCiteRight_face_through_promotionM {H1 H2 : Hypernet}
    (hd : H1.WireDisjoint H2) (rider : Formula) (s : Sequent)
    (hdec : leafSequent fixtureTbls 7 = .ok s)
    (hws : s.wellScoped H2) :
    Plain.upperProb
      (Plain.admCyl (H1.disjUnion H2 hd) (citeFacet s rider))
      (Plain.postEvt (H1.disjUnion H2 hd) (citeFacet s rider))ᶜ = 0 :=
  (Plain.semanticallyValid_iff_face (H1.disjUnion H2 hd)
    (citeFacet s rider)).mp
    (decodedCiteFacet_valid_through_M (extRight hd) rider s hdec hws)

/-- The left inclusion, judgment-layer route. -/
theorem decodedCiteLeft_face_through_promotionMJ {H1 H2 : Hypernet}
    (hd : H1.WireDisjoint H2) (rider : Formula) (s : Sequent)
    (hdec : leafSequent fixtureTbls 7 = .ok s)
    (hws : s.wellScoped H1) :
    Plain.upperProb
      (Plain.admCyl (H1.disjUnion H2 hd) (citeFacet s rider))
      (Plain.postEvt (H1.disjUnion H2 hd) (citeFacet s rider))ᶜ = 0 :=
  (Plain.semanticallyValid_iff_face (H1.disjUnion H2 hd)
    (citeFacet s rider)).mp
    (decodedCiteFacet_valid_through_MJ (extLeft hd) rider s hdec hws)

/-- The right inclusion, judgment-layer route. -/
theorem decodedCiteRight_face_through_promotionMJ {H1 H2 : Hypernet}
    (hd : H1.WireDisjoint H2) (rider : Formula) (s : Sequent)
    (hdec : leafSequent fixtureTbls 7 = .ok s)
    (hws : s.wellScoped H2) :
    Plain.upperProb
      (Plain.admCyl (H1.disjUnion H2 hd) (citeFacet s rider))
      (Plain.postEvt (H1.disjUnion H2 hd) (citeFacet s rider))ᶜ = 0 :=
  (Plain.semanticallyValid_iff_face (H1.disjUnion H2 hd)
    (citeFacet s rider)).mp
    (decodedCiteFacet_valid_through_MJ (extRight hd) rider s hdec hws)

/-! ## Concrete corollaries: row bytes to a union face, no hypotheses

The staged claim's decoded leaf, cited into the demo pair's disjoint
union — `hdec` discharged by the decode theorem, well-scopedness by
wire-freeness.  The union never appears in the staged rows: it is
reached only by the extension arrows of the many-object presentation. -/

open ProductLatticeDemo in
/-- The decoded leaf cited into `Hx ⊔ Hy` from the left, at the checker
face, through the many-object implication carrier — no hypotheses. -/
theorem decodedLeafCiteX_face_through_promotionM :
    Plain.upperProb
      (Plain.admCyl (Hx.disjUnion Hy HxHy_disjoint)
        (citeFacet leafSeqDemo riderJx))
      (Plain.postEvt (Hx.disjUnion Hy HxHy_disjoint)
        (citeFacet leafSeqDemo riderJx))ᶜ = 0 :=
  decodedCiteLeft_face_through_promotionM HxHy_disjoint riderJx
    leafSeqDemo fixture_leaf_seq (leafSeqDemo_wellScoped Hx)

open ProductLatticeDemo in
/-- The decoded leaf cited into `Hx ⊔ Hy` from the right, at the
checker face, judgment-layer carrier — no hypotheses. -/
theorem decodedLeafCiteY_face_through_promotionMJ :
    Plain.upperProb
      (Plain.admCyl (Hx.disjUnion Hy HxHy_disjoint)
        (citeFacet leafSeqDemo riderJy))
      (Plain.postEvt (Hx.disjUnion Hy HxHy_disjoint)
        (citeFacet leafSeqDemo riderJy))ᶜ = 0 :=
  decodedCiteRight_face_through_promotionMJ HxHy_disjoint riderJy
    leafSeqDemo fixture_leaf_seq (leafSeqDemo_wellScoped Hy)

end Decode

end QtslSem

end SuFunctor
