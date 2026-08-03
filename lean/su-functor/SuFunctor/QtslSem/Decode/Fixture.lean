import SuFunctor.QtslSem.Decode.Present
import SuFunctor.QtslSem.BLFactoring

/-!
# The decoder fixture: staged rows in, carrier cells out

A hand-staged QTSL-stratum row set (the reflection route's own
pre-pins play, at op level: a `Geolog` value constructed directly, so
every theorem below is kernel-checked over the decoder's actual
run) — one satisfaction claim against the qc closure: a `QSat` with
its judgment, subject, and a specification carrying one
`SProbGE`-formed safety-face component (the event-4 component
record), one `QProof` concluding the judgment, and a `qsat_eval`
route — (eval, sat) on the wire — to a polynomial-calculus leaf whose
concluded sequent is `⊤ ⊢ (2 + 4) = 6`.

The end-to-end story, and the reason this file imports the carriers:
the decoded evaluation leaf's sequent — extracted by `leafSequent`
from the same tables the presentation decode ran on — enters the
presented virtual double category as a `pConstExact` generator (its
gate is the leaf's own closed evaluation), covers into the free
promotion, and lands at the checker face through BOTH wired carriers
(`qtslSemBL` into the implication double category, `qtslSemBLJ` into
the judgment layer).  The face theorems take the decode equality as
their hypothesis, so the route from row bytes to semantic-universe
statement is load-bearing, not decorative: corrupting the judgment
decode breaks them.

Refusal fixtures ride variant op lists (a dropped subject row, an
orphaned proof, an unpinned reference, an ill-sorted subject, a
cyclic proof-kit list) — each refusal is a GREEN theorem here, and
the prereg'd mutants disable the corresponding checks to prove the
refusals are load-bearing.
-/

namespace SuFunctor

namespace QtslSem

namespace Decode

open PPLC PPLC.Geolog CategoryTheory VdcPresentation
open VirtualDoubleCategoryData

/-! ## The staged rows

Element layout (declaration order): 0 `QJudgment`, 1 `System`,
2 `Spec`, 3 `ForallSpec` (the SProbGE-formed face), 4 `PathPred`,
5 `QSat`, 6 `QProof`, 7 `Proof`, 8 `Judgment`, 9–12 `Term` (2, 4,
2+4, 6), 13–14 `Formula` (⊤, (2+4) = 6), 15–16 `QProofList` (nil,
cons). -/

/-- The fixture's dependency table: the qc closure alone. -/
def fixtureDeps : List Bytes := [chidQcV1]

/-- The element declarations (qc sort counters). -/
def fixtureDecls : List GOp :=
  [.elta (.ext 0 141),   -- 0 : QJudgment
   .elta (.ext 0 111),   -- 1 : System
   .elta (.ext 0 103),    -- 2 : Spec
   .elta (.ext 0 64),    -- 3 : ForallSpec
   .elta (.ext 0 63),    -- 4 : PathPred
   .elta (.ext 0 151),   -- 5 : QSat
   .elta (.ext 0 142),   -- 6 : QProof
   .elta (.ext 0 17),    -- 7 : Proof
   .elta (.ext 0 16),    -- 8 : Judgment
   .elta (.ext 0 14),    -- 9 : Term
   .elta (.ext 0 14),    -- 10 : Term
   .elta (.ext 0 14),    -- 11 : Term
   .elta (.ext 0 14),    -- 12 : Term
   .elta (.ext 0 15),    -- 13 : Formula
   .elta (.ext 0 15),    -- 14 : Formula
   .elta (.ext 0 147),   -- 15 : QProofList
   .elta (.ext 0 147)]   -- 16 : QProofList

/-- The ground rows: the leaf's terms, formulas, judgment, and
`Proof/concludes` hop (qc fun counters; `Q` literals in the minimal
uvarint-length spelling). -/
def fixtureGround : List GOp :=
  [.funa (.ext 0 336) [.lit 0 [1, 2, 1]] (.ref (.loc 9)),    -- TConst 2
   .funa (.ext 0 336) [.lit 0 [1, 4, 1]] (.ref (.loc 10)),   -- TConst 4
   .funa (.ext 0 337) [.ref (.loc 9), .ref (.loc 10)]
     (.ref (.loc 11)),                                       -- TAdd
   .funa (.ext 0 336) [.lit 0 [1, 6, 1]] (.ref (.loc 12)),   -- TConst 6
   .funa (.ext 0 352) [] (.ref (.loc 13)),                   -- FTrue
   .funa (.ext 0 345) [.ref (.loc 11), .ref (.loc 12)]
     (.ref (.loc 14)),                                       -- FAtomEQ
   .funa (.ext 0 354) [.ref (.loc 8)] (.ref (.loc 13)),      -- Judgment/pre
   .funa (.ext 0 355) [.ref (.loc 8)] (.ref (.loc 14)),      -- Judgment/post
   .funa (.ext 0 358) [.ref (.loc 7)] (.ref (.loc 8))]       -- Proof/concludes

/-- The specification rows: an `SProbGE`-formed safety face
(threshold 9/10, path opaque) and the component row attaching it —
`spec_forall` (f, spec), field names sorted bytewise. -/
def fixtureSpecRows : List GOp :=
  [.funa (.ext 0 649) [.lit 0 [1, 9, 10], .ref (.loc 4)]
     (.ref (.loc 3)),                                        -- SProbGE
   .rela (.ext 0 742) [.ref (.loc 3), .ref (.loc 2)]]        -- spec_forall

/-- The claim's subject row (`QSat/sys`), named so the variant lists
can drop or corrupt exactly it. -/
def rowSys : GOp := .funa (.ext 0 918) [.ref (.loc 5)] (.ref (.loc 1))

/-- The proof roster's concludes row, named for the orphan variant. -/
def rowConcludes : GOp :=
  .funa (.ext 0 899) [.ref (.loc 6)] (.ref (.loc 0))

/-- The claim rows: the `QSat` record, its evaluation route, the
`QProof`, and a one-entry proof-kit list. -/
def fixtureClaimRows : List GOp :=
  [.funa (.ext 0 917) [.ref (.loc 5)] (.ref (.loc 0)),       -- QSat/judgment
   rowSys,
   .funa (.ext 0 919) [.ref (.loc 5)] (.ref (.loc 2)),       -- QSat/spec
   .rela (.ext 0 921) [.ref (.loc 7), .ref (.loc 5)],        -- qsat_eval (eval, sat)
   rowConcludes,
   .funa (.ext 0 909) [] (.ref (.loc 15)),                   -- qplNil
   .funa (.ext 0 910) [.ref (.loc 7), .ref (.loc 15)]
     (.ref (.loc 16))]                                       -- qplCons

/-- The staged op list. -/
def fixtureOps : List GOp :=
  fixtureDecls ++ fixtureGround ++ fixtureSpecRows ++ fixtureClaimRows

/-- The scanned tables (total by construction; the error branch is
unreachable and any defect in it fails the theorems below). -/
def fixtureTbls : QRowTbls :=
  match scanQtslOps fixtureDeps fixtureOps with
  | .ok t => t
  | .error _ => ⟨[], [], []⟩

/-- The expected decoded presentation, in full. -/
def fixtureExpected : QtslPresentation :=
  { judgments := [0]
    sats := [⟨5, 0, 1,
      ⟨2, [⟨3, "SProbGE", [.lit 0 [1, 9, 10], .ref (.loc 4)]⟩], []⟩,
      none, some 7⟩]
    satConfs := []
    specEquivs := []
    regionSats := []
    invScopes := []
    proofs := [⟨6, 0⟩] }

/-- **The decode theorem**: the staged rows decode to exactly the
expected presentation. -/
theorem decode_fixture_ok :
    decodeQtslPresentationOps fixtureDeps fixtureOps =
      .ok fixtureExpected := by
  decide

/-- The evaluation leaf's concluded sequent, as the carriers consume
it. -/
def leafSeqDemo : Sequent :=
  ⟨.tt, .atom .eq (.add (.const 2) (.const 4)) (.const 6)⟩

/-- **The seam theorem**: the decoded evaluation leaf's sequent is
`⊤ ⊢ (2 + 4) = 6`.  (`rfl`, not `decide`: `Sequent` carries no
`DecidableEq` instance — the equality of the closed run and the closed
literal is checked by kernel reduction directly.) -/
theorem fixture_leaf_seq :
    leafSequent fixtureTbls 7 = .ok leafSeqDemo := by
  rfl

/-- **The kit-walk theorem**: the staged one-entry proof-kit list
decodes positionally. -/
theorem walk_fixture :
    walkQProofList fixtureTbls fixtureTbls.kitFuel 16 = .ok [7] := by
  decide

/-! ## Refusal fixtures (each a green theorem; the prereg'd mutants
disable the corresponding check to prove the refusal load-bearing) -/

/-- A dropped subject row refuses. -/
def fixtureOpsMissingSys : List GOp :=
  fixtureDecls ++ fixtureGround ++ fixtureSpecRows ++
    [.funa (.ext 0 917) [.ref (.loc 5)] (.ref (.loc 0)),
     .funa (.ext 0 919) [.ref (.loc 5)] (.ref (.loc 2)),
     .rela (.ext 0 921) [.ref (.loc 7), .ref (.loc 5)],
     rowConcludes,
     .funa (.ext 0 909) [] (.ref (.loc 15)),
     .funa (.ext 0 910) [.ref (.loc 7), .ref (.loc 15)] (.ref (.loc 16))]

theorem refuse_missing_sys :
    decodeQtslPresentationOps fixtureDeps fixtureOpsMissingSys =
      .error (.unreadable, "qsat_missing_sys", 5) := by
  decide

/-- An unconcluded proof refuses as an orphan. -/
def fixtureOpsOrphan : List GOp :=
  fixtureDecls ++ fixtureGround ++ fixtureSpecRows ++
    [.funa (.ext 0 917) [.ref (.loc 5)] (.ref (.loc 0)),
     rowSys,
     .funa (.ext 0 919) [.ref (.loc 5)] (.ref (.loc 2)),
     .rela (.ext 0 921) [.ref (.loc 7), .ref (.loc 5)],
     .funa (.ext 0 909) [] (.ref (.loc 15)),
     .funa (.ext 0 910) [.ref (.loc 7), .ref (.loc 15)] (.ref (.loc 16))]

theorem refuse_orphan_proof :
    decodeQtslPresentationOps fixtureDeps fixtureOpsOrphan =
      .error (.unreadable, "qproof_orphan", 6) := by
  decide

/-- A reference outside the pin table refuses at scan time with its
op index. -/
theorem refuse_unpinned :
    decodeQtslPresentationOps fixtureDeps
      (fixtureOps ++ [.funa (.ext 0 9999) [] (.lit 2 [0])]) =
      .error (.unsupported, "schema_ref_unpinned", 35) := by
  decide

/-- An ill-sorted subject (the spec element in the `System` slot)
refuses. -/
def fixtureOpsWrongSort : List GOp :=
  fixtureDecls ++ fixtureGround ++ fixtureSpecRows ++
    [.funa (.ext 0 917) [.ref (.loc 5)] (.ref (.loc 0)),
     .funa (.ext 0 918) [.ref (.loc 5)] (.ref (.loc 2)),
     .funa (.ext 0 919) [.ref (.loc 5)] (.ref (.loc 2)),
     .rela (.ext 0 921) [.ref (.loc 7), .ref (.loc 5)],
     rowConcludes,
     .funa (.ext 0 909) [] (.ref (.loc 15)),
     .funa (.ext 0 910) [.ref (.loc 7), .ref (.loc 15)] (.ref (.loc 16))]

theorem refuse_sys_wrong_sort :
    decodeQtslPresentationOps fixtureDeps fixtureOpsWrongSort =
      .error (.unreadable, "qsat_sys_not_system", 2) := by
  decide

/-- A cyclic proof-kit list refuses on fuel (never a silent
truncation). -/
def fixtureOpsCycle : List GOp :=
  fixtureOps ++
    [.elta (.ext 0 147),                                     -- 17 : QProofList
     .funa (.ext 0 910) [.ref (.loc 7), .ref (.loc 17)] (.ref (.loc 17))]

def fixtureTblsCycle : QRowTbls :=
  match scanQtslOps fixtureDeps fixtureOpsCycle with
  | .ok t => t
  | .error _ => ⟨[], [], []⟩

theorem refuse_qpl_cycle :
    walkQProofList fixtureTblsCycle fixtureTblsCycle.kitFuel 17 =
      .error (.unreadable, "qpl_walk_fuel", 17) := by
  decide

/-! ## The decoded row through both carriers

The `pConstExact` generator on the decoded leaf sequent: its gate is
the leaf's own closed evaluation `(2 + 4) = 6` (`norm_num` — rational
addition does not kernel-reduce under the `Decidable` instances
alone), entered bare, covered into the free promotion, read at the
checker face through each carrier. -/

/-- The generator on the decoded sequent. -/
def decodedLeafRule : BLRule :=
  .pConstExact leafSeqDemo (.add (.const 2) (.const 4)) (.const 6) .eq

/-- Its gate: the decoded atom's closed evaluation. -/
theorem decodedLeafRule_gate (H : Hypernet) :
    (blPresentation H).gate decodedLeafRule := by
  refine ⟨?_, rfl⟩
  norm_num [Formula.evalClosed, Term.evalQ?, BowTie.evalQ]

/-- The empty premise string over the presented carrier (the named
ground-typed path def — the fixture-path discipline). -/
def decodedLeafTops (H : Hypernet) :
    LoosePath (VirtualDoubleCategoryData.Loose
      (C := Presented (blPresentation H)))
      (.of .pt) (.of .pt) :=
  .nil

/-- The generator as a zero-premise multicell of the presented
virtual double category. -/
def decodedLeafCell (H : Hypernet) :
    VirtualDoubleCategoryData.Cell (C := Presented (blPresentation H))
      (decodedLeafTops H)
      ((leafSeqDemo : Sequent) :
        VirtualDoubleCategoryData.Loose (.of .pt) (.of .pt))
      (𝟙 (Presented.of BLCtx.pt)) (𝟙 (Presented.of BLCtx.pt)) := by
  exact ⟨⟨DerivT.gen (P := blPresentation H) decodedLeafRule
    (decodedLeafRule_gate H)⟩⟩

/-- Its covering in the free promotion. -/
def decodedLeafCovering (H : Hypernet) :
    PseudoDoubleCategoryStruct.Cell
      (C := FreePromotion (Presented (blPresentation H)))
      (a := .of (.of .pt)) (b := .of (.of .pt))
      (c := .of (.of .pt)) (d := .of (.of .pt))
      (decodedLeafTops H)
      (LoosePath.single ((leafSeqDemo : Sequent) :
        VirtualDoubleCategoryData.Loose (Presented.of BLCtx.pt)
          (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt)))
      (𝟙 (FreePromotion.of (Presented.of BLCtx.pt))) := by
  exact ⟨⟨(VirtualDoubleCategoryStruct.CellSeq.singleton
    (decodedLeafCell H)).castDom (LoosePath.comp_nil _)⟩⟩

/-- **The decoded row at the checker face, implication carrier**: from
the decode equality alone — no validity hypotheses; the sequent's
content was evaluated by the gate — the vanishing upper probability of
the decoded conclusion's complement, the proof term routed through the
promoted functor on the decoded generator's covering. -/
theorem decodedLeaf_face_through_promotion (H : Hypernet) (s : Sequent)
    (hdec : leafSequent fixtureTbls 7 = .ok s) :
    Plain.upperProb (Plain.admCyl H s) (Plain.postEvt H s)ᶜ = 0 := by
  have h2 : (Except.ok leafSeqDemo : QRes Sequent) = .ok s := by
    rw [← fixture_leaf_seq]; exact hdec
  injection h2 with h3
  subst h3
  have himp := ((qtslSemBL H).mapCell (decodedLeafCovering H)).down
  exact (Plain.semanticallyValid_iff_face H leafSeqDemo).mp
    (himp trivial).1

/-- **The decoded row at the checker face, judgment-layer carrier**:
hypotheses and endpoint verbatim; the proof term routes through the
promoted functor into the thin carrier. -/
theorem decodedLeaf_face_through_promotionJ (H : Hypernet) (s : Sequent)
    (hdec : leafSequent fixtureTbls 7 = .ok s) :
    Plain.upperProb (Plain.admCyl H s) (Plain.postEvt H s)ᶜ = 0 := by
  have h2 : (Except.ok leafSeqDemo : QRes Sequent) = .ok s := by
    rw [← fixture_leaf_seq]; exact hdec
  injection h2 with h3
  subst h3
  obtain ⟨_, himp⟩ := ((qtslSemBLJ H).mapCell (decodedLeafCovering H)).down
  exact (Plain.semanticallyValid_iff_face H leafSeqDemo).mp
    (himp trivial).1

end Decode

end QtslSem

end SuFunctor
