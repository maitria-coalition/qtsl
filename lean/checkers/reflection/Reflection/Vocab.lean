import Reflection.Types

/-!
# Pinned theory vocabulary

A sealed certificate commit references its theory declarations through
(dependency, counter) element references into pinned theory revisions.
This module carries the vocabulary those references resolve to: the
`Vocab` classification of every declaration the certificate fragment
consumes, and the generated pin table mapping (content hash, counter)
pairs to vocabulary entries.

Entries outside the accepted fragment are still *named* (`sOther` /
`fOther`) so that a certificate using them refuses with the
declaration's name rather than an anonymous miss.
-/

namespace PPLC
namespace Geolog

/-- Vocabulary classification of pinned theory declarations: sorts
(`s…`), constructor/field/record functions (`f…`), and ordinary
relations (`r…`). -/
inductive Vocab where
  | sProof | sTerm | sFormula | sJudgment | sCert | sWire
  | sSimpC | sSimplex | sExtSet | sCtxPath | sDtype | sShape
  | sTensorType | sKind | sSign | sExt
  | sEncJudgment | sPEnclosure
  | sRule (r : Nat)
  | sOther (name : String)
  | fTVar | fTConst | fTAdd | fTMul | fTSub | fTNeg | fTIdx | fTHole
  | fFAtom (b : Nat)
  | fFInRegion | fFAnd | fFOr | fFTrue | fFFalse | fFSpH
  | fPathHere | fPathL | fPathR
  | fMkDtype | fShapeEmpty | fShapeCons | fMkTensorType
  | fKindC (k : Nat) | fSignC (s : Nat) | fExtC (e : Nat)
  | fJudgPre | fJudgPost | fProofConcludes
  | fCertRoot | fCertRootEnc | fCertTheta | fCertNWires | fCertNApps
  | fCertNComplexes
  | fEncFunc | fEncN | fEncR | fEncCap | fPEncConcludes
  | fWireIndex | fWireType
  | fSimpCIndex | fSimpCNVert | fSimpCAmbDim | fSimpCNSimp | fSimpCNCells
  | fSimplexComplex | fExtSetSimplex
  | fRuleProof (r : Nat)
  | fRF (r k : Nat)
  | fSimpCCoord | fCplxSimpAt
  | rSimplexContains | rExtSetContains
  | rCellSimpHasV | rCellExtHasV
  | rPromIface | rSyzComp
  | fOther (name : String)
  deriving Repr, DecidableEq

/-- Sort declarations (legal at `elta` sort position). -/
def Vocab.isSort : Vocab → Bool
  | .sProof | .sTerm | .sFormula | .sJudgment | .sCert | .sWire
  | .sSimpC | .sSimplex | .sExtSet | .sCtxPath | .sDtype | .sShape
  | .sTensorType | .sKind | .sSign | .sExt
  | .sEncJudgment | .sPEnclosure
  | .sRule _ | .sOther _ => true
  | _ => false

/-- Constructor functions: value determines the constructed element. -/
def Vocab.isCtor : Vocab → Bool
  | .fTVar | .fTConst | .fTAdd | .fTMul | .fTSub | .fTNeg | .fTIdx
  | .fTHole
  | .fFAtom _ | .fFInRegion | .fFAnd | .fFOr | .fFTrue | .fFFalse
  | .fFSpH
  | .fPathHere | .fPathL | .fPathR
  | .fMkDtype | .fShapeEmpty | .fShapeCons | .fMkTensorType
  | .fKindC _ | .fSignC _ | .fExtC _ => true
  | _ => false

/-- Field functions: one element subject, one value. -/
def Vocab.isField : Vocab → Bool
  | .fJudgPre | .fJudgPost | .fProofConcludes
  | .fCertRoot | .fCertRootEnc | .fCertTheta | .fCertNWires | .fCertNApps
  | .fCertNComplexes
  | .fEncFunc | .fEncN | .fEncR | .fEncCap | .fPEncConcludes
  | .fWireIndex | .fWireType
  | .fSimpCIndex | .fSimpCNVert | .fSimpCAmbDim | .fSimpCNSimp
  | .fSimpCNCells
  | .fSimplexComplex | .fExtSetSimplex
  | .fRuleProof _ | .fRF _ _ => true
  | _ => false

/-- Keyed record functions (dense-index or component families). -/
def Vocab.isRec : Vocab → Bool
  | .fSimpCCoord | .fCplxSimpAt | .rPromIface | .rSyzComp => true
  | _ => false

/-- Ordinary relations of the accepted fragment. -/
def Vocab.isRel : Vocab → Bool
  | .rSimplexContains | .rExtSetContains
  | .rCellSimpHasV | .rCellExtHasV => true
  | _ => false

/-- Rule tags of the first-order certificate fragment. -/
def v0fragTag (r : Nat) : Bool :=
  r ≤ 12 || r == 14 || (23 ≤ r && r ≤ 26)

/-- Content hashes of the pinned theory revisions. -/
def chid_blstack : List Nat :=
  [91, 237, 73, 180, 116, 43, 47, 11, 226, 10, 84, 149, 1, 174, 44, 41, 59, 161, 34, 10, 112, 207, 105, 91, 221, 63, 116, 88, 6, 248, 242, 84]

def chid_groundFormats : List Nat :=
  [54, 145, 8, 123, 152, 53, 236, 144, 106, 190, 26, 237, 161, 107, 65, 34, 221, 255, 127, 187, 9, 113, 70, 140, 38, 102, 138, 211, 249, 166, 46, 105]

def chid_certTheory : List Nat :=
  [181, 140, 163, 94, 199, 42, 90, 4, 33, 84, 80, 94, 86, 102, 155, 174, 172, 101, 115, 102, 50, 148, 71, 132, 113, 132, 243, 32, 70, 138, 219, 234]

/-- The pinned vocabulary: ((theory content hash, declaration counter) -> vocabulary). Generated from the staged theory revisions; regenerate with the producer tooling after any re-stage. -/
def stagedPins : List ((List Nat × Nat) × Vocab) :=
  [((chid_groundFormats, 0), .sOther "F16"),
   ((chid_groundFormats, 1), .sOther "BF16"),
   ((chid_groundFormats, 2), .sOther "F32"),
   ((chid_groundFormats, 3), .sOther "F64"),
   ((chid_groundFormats, 4), .sOther "F8E4M3"),
   ((chid_groundFormats, 5), .sOther "F8E5M2"),
   ((chid_groundFormats, 6), .sOther "E2M1"),
   ((chid_groundFormats, 8), .fOther "Sort/byte_width"),
   ((chid_groundFormats, 9), .fOther "Sort/exp_bits"),
   ((chid_groundFormats, 10), .fOther "Sort/man_bits"),
   ((chid_groundFormats, 11), .fOther "Sort/exp_bias"),
   ((chid_groundFormats, 12), .fOther "Sort/nan_discipline"),
   ((chid_groundFormats, 13), .fOther "f16_lt"),
   ((chid_groundFormats, 14), .fOther "f16_le"),
   ((chid_groundFormats, 15), .fOther "f16_ne"),
   ((chid_groundFormats, 16), .fOther "bf16_lt"),
   ((chid_groundFormats, 17), .fOther "bf16_le"),
   ((chid_groundFormats, 18), .fOther "bf16_ne"),
   ((chid_groundFormats, 19), .fOther "f32_lt"),
   ((chid_groundFormats, 20), .fOther "f32_le"),
   ((chid_groundFormats, 21), .fOther "f32_ne"),
   ((chid_groundFormats, 22), .fOther "f64_lt"),
   ((chid_groundFormats, 23), .fOther "f64_le"),
   ((chid_groundFormats, 24), .fOther "f64_ne"),
   ((chid_groundFormats, 25), .fOther "f8e4m3_lt"),
   ((chid_groundFormats, 26), .fOther "f8e4m3_le"),
   ((chid_groundFormats, 27), .fOther "f8e4m3_ne"),
   ((chid_groundFormats, 28), .fOther "f8e5m2_lt"),
   ((chid_groundFormats, 29), .fOther "f8e5m2_le"),
   ((chid_groundFormats, 30), .fOther "f8e5m2_ne"),
   ((chid_groundFormats, 31), .fOther "e2m1_lt"),
   ((chid_groundFormats, 32), .fOther "e2m1_le"),
   ((chid_groundFormats, 33), .fOther "e2m1_ne"),
   ((chid_blstack, 0), .sKind),
   ((chid_blstack, 1), .sSign),
   ((chid_blstack, 2), .sExt),
   ((chid_blstack, 3), .sDtype),
   ((chid_blstack, 4), .sShape),
   ((chid_blstack, 5), .sTensorType),
   ((chid_blstack, 6), .sOther "Primitive"),
   ((chid_blstack, 7), .sOther "RoundMode"),
   ((chid_blstack, 8), .sWire),
   ((chid_blstack, 9), .sOther "PrimApp"),
   ((chid_blstack, 10), .sOther "InputPort"),
   ((chid_blstack, 11), .sOther "OutputPort"),
   ((chid_blstack, 12), .sOther "ContractIndex"),
   ((chid_blstack, 13), .sOther "ContractBinding"),
   ((chid_blstack, 14), .sOther "ContractOutputBinding"),
   ((chid_blstack, 15), .sSimpC),
   ((chid_blstack, 16), .sSimplex),
   ((chid_blstack, 17), .sExtSet),
   ((chid_blstack, 18), .sTerm),
   ((chid_blstack, 19), .sFormula),
   ((chid_blstack, 20), .sJudgment),
   ((chid_blstack, 21), .sProof),
   ((chid_blstack, 22), .sRule 0),
   ((chid_blstack, 23), .sRule 1),
   ((chid_blstack, 24), .sRule 2),
   ((chid_blstack, 25), .sRule 3),
   ((chid_blstack, 26), .sRule 4),
   ((chid_blstack, 27), .sRule 5),
   ((chid_blstack, 28), .sRule 6),
   ((chid_blstack, 29), .sRule 7),
   ((chid_blstack, 30), .sRule 23),
   ((chid_blstack, 31), .sRule 24),
   ((chid_blstack, 32), .sRule 8),
   ((chid_blstack, 33), .sRule 9),
   ((chid_blstack, 34), .sRule 10),
   ((chid_blstack, 35), .sRule 11),
   ((chid_blstack, 36), .sRule 25),
   ((chid_blstack, 37), .sRule 26),
   ((chid_blstack, 38), .sRule 12),
   ((chid_blstack, 39), .sRule 13),
   ((chid_blstack, 40), .sRule 14),
   ((chid_blstack, 41), .sRule 15),
   ((chid_blstack, 42), .sRule 16),
   ((chid_blstack, 43), .sRule 17),
   ((chid_blstack, 44), .sRule 18),
   ((chid_blstack, 45), .sRule 19),
   ((chid_blstack, 46), .sRule 20),
   ((chid_blstack, 47), .sRule 21),
   ((chid_blstack, 48), .sRule 22),
   ((chid_blstack, 49), .sCtxPath),
   ((chid_blstack, 50), .sOther "PConstExact"),
   ((chid_blstack, 51), .sOther "PBound"),
   ((chid_blstack, 52), .sOther "PPsdCertT"),
   ((chid_blstack, 53), .sOther "PPsdCertDD"),
   ((chid_blstack, 54), .sOther "PPsdCertK"),
   ((chid_blstack, 55), .sOther "BlockLattice"),
   ((chid_blstack, 56), .sOther "BLAxis"),
   ((chid_blstack, 57), .sOther "FamBlock"),
   ((chid_blstack, 58), .sOther "FamJudgment"),
   ((chid_blstack, 59), .sOther "PProductLattice"),
   ((chid_blstack, 60), .sEncJudgment),
   ((chid_blstack, 61), .sPEnclosure),
   ((chid_blstack, 72), .fOther "q_add"),
   ((chid_blstack, 73), .fOther "q_mul"),
   ((chid_blstack, 74), .fOther "q_lt"),
   ((chid_blstack, 75), .fOther "q_le"),
   ((chid_blstack, 76), .fOther "q_ne"),
   ((chid_blstack, 77), .fOther "nat_lt"),
   ((chid_blstack, 78), .fOther "nat_ne"),
   ((chid_blstack, 79), .fKindC 0),
   ((chid_blstack, 80), .fKindC 1),
   ((chid_blstack, 81), .fKindC 2),
   ((chid_blstack, 82), .fKindC 3),
   ((chid_blstack, 83), .fKindC 4),
   ((chid_blstack, 84), .fKindC 5),
   ((chid_blstack, 85), .fKindC 6),
   ((chid_blstack, 86), .fSignC 0),
   ((chid_blstack, 87), .fSignC 1),
   ((chid_blstack, 88), .fExtC 0),
   ((chid_blstack, 89), .fExtC 1),
   ((chid_blstack, 90), .fOther "Dtype/kind"),
   ((chid_blstack, 91), .fOther "Dtype/sign"),
   ((chid_blstack, 92), .fOther "Dtype/ext"),
   ((chid_blstack, 93), .fMkDtype),
   ((chid_blstack, 94), .fOther "Q"),
   ((chid_blstack, 95), .fOther "Z"),
   ((chid_blstack, 96), .fOther "Nat"),
   ((chid_blstack, 97), .fOther "B"),
   ((chid_blstack, 98), .fOther "F64"),
   ((chid_blstack, 99), .fShapeEmpty),
   ((chid_blstack, 100), .fShapeCons),
   ((chid_blstack, 101), .fOther "Shape/rank"),
   ((chid_blstack, 102), .fOther "TensorType/shape"),
   ((chid_blstack, 103), .fOther "TensorType/dtype"),
   ((chid_blstack, 104), .fMkTensorType),
   ((chid_blstack, 105), .fOther "PConst"),
   ((chid_blstack, 106), .fOther "PContract"),
   ((chid_blstack, 107), .fOther "PCast"),
   ((chid_blstack, 108), .fOther "PCell"),
   ((chid_blstack, 109), .fOther "PReshape"),
   ((chid_blstack, 110), .fOther "PBroadcast"),
   ((chid_blstack, 111), .fOther "PCopy"),
   ((chid_blstack, 112), .fOther "PDelete"),
   ((chid_blstack, 113), .fOther "PSwap"),
   ((chid_blstack, 114), .fOther "Rrne"),
   ((chid_blstack, 115), .fOther "Rrtz"),
   ((chid_blstack, 116), .fOther "Rrup"),
   ((chid_blstack, 117), .fOther "Rrdn"),
   ((chid_blstack, 118), .fOther "Rexact"),
   ((chid_blstack, 119), .fWireType),
   ((chid_blstack, 120), .fOther "PrimApp/prim"),
   ((chid_blstack, 121), .fOther "PrimApp/round"),
   ((chid_blstack, 122), .fOther "InputPort/app"),
   ((chid_blstack, 123), .fOther "InputPort/pos"),
   ((chid_blstack, 124), .fOther "InputPort/wire"),
   ((chid_blstack, 125), .fOther "OutputPort/app"),
   ((chid_blstack, 126), .fOther "OutputPort/pos"),
   ((chid_blstack, 127), .fOther "OutputPort/wire"),
   ((chid_blstack, 128), .fOther "reaches"),
   ((chid_blstack, 129), .fOther "ContractIndex/app"),
   ((chid_blstack, 130), .fOther "ContractIndex/extent"),
   ((chid_blstack, 131), .fOther "PortRank"),
   ((chid_blstack, 132), .fOther "ContractBinding/app"),
   ((chid_blstack, 133), .fOther "ContractBinding/port"),
   ((chid_blstack, 134), .fOther "ContractBinding/axis"),
   ((chid_blstack, 135), .fOther "ContractBinding/index"),
   ((chid_blstack, 136), .fOther "OutputRank"),
   ((chid_blstack, 137), .fOther "ContractOutputBinding/app"),
   ((chid_blstack, 138), .fOther "ContractOutputBinding/port"),
   ((chid_blstack, 139), .fOther "ContractOutputBinding/axis"),
   ((chid_blstack, 140), .fOther "ContractOutputBinding/index"),
   ((chid_blstack, 141), .fOther "ShapeAxisExtent"),
   ((chid_blstack, 142), .fSimpCNVert),
   ((chid_blstack, 143), .fSimpCAmbDim),
   ((chid_blstack, 144), .fSimpCCoord),
   ((chid_blstack, 145), .fSimplexComplex),
   ((chid_blstack, 146), .rSimplexContains),
   ((chid_blstack, 147), .fOther "CellSchema"),
   ((chid_blstack, 148), .fExtSetSimplex),
   ((chid_blstack, 149), .rExtSetContains),
   ((chid_blstack, 150), .fOther "simplexSameMembers"),
   ((chid_blstack, 151), .fOther "simplexIsFaceMinus"),
   ((chid_blstack, 152), .fOther "simplexIsIntersection"),
   ((chid_blstack, 153), .fOther "extensionSetOmits"),
   ((chid_blstack, 154), .fOther "extensionSetSameMembers"),
   ((chid_blstack, 155), .fTVar),
   ((chid_blstack, 156), .fTConst),
   ((chid_blstack, 157), .fTAdd),
   ((chid_blstack, 158), .fTMul),
   ((chid_blstack, 159), .fTSub),
   ((chid_blstack, 160), .fTNeg),
   ((chid_blstack, 161), .fTIdx),
   ((chid_blstack, 162), .fOther "Term/type"),
   ((chid_blstack, 163), .fFAtom 1),
   ((chid_blstack, 164), .fFAtom 0),
   ((chid_blstack, 165), .fFAtom 2),
   ((chid_blstack, 166), .fFAtom 3),
   ((chid_blstack, 167), .fFAtom 4),
   ((chid_blstack, 168), .fFAtom 5),
   ((chid_blstack, 169), .fFInRegion),
   ((chid_blstack, 170), .fFAnd),
   ((chid_blstack, 171), .fFOr),
   ((chid_blstack, 172), .fFTrue),
   ((chid_blstack, 173), .fFFalse),
   ((chid_blstack, 174), .fJudgPre),
   ((chid_blstack, 175), .fJudgPost),
   ((chid_blstack, 176), .fOther "FreeInTerm"),
   ((chid_blstack, 177), .fOther "FreeInFormula"),
   ((chid_blstack, 178), .fProofConcludes),
   ((chid_blstack, 179), .fOther "WFTerm"),
   ((chid_blstack, 180), .fOther "WFTermFin"),
   ((chid_blstack, 181), .fOther "WFFormula"),
   ((chid_blstack, 182), .fOther "WFJudgment"),
   ((chid_blstack, 183), .fRuleProof 0),
   ((chid_blstack, 184), .fRuleProof 1),
   ((chid_blstack, 185), .fRuleProof 2),
   ((chid_blstack, 186), .fRuleProof 3),
   ((chid_blstack, 187), .fRuleProof 4),
   ((chid_blstack, 188), .fRuleProof 5),
   ((chid_blstack, 189), .fRuleProof 6),
   ((chid_blstack, 190), .fRuleProof 7),
   ((chid_blstack, 191), .fRuleProof 23),
   ((chid_blstack, 192), .fRuleProof 24),
   ((chid_blstack, 193), .fRuleProof 8),
   ((chid_blstack, 194), .fRuleProof 9),
   ((chid_blstack, 195), .fRuleProof 10),
   ((chid_blstack, 196), .fRuleProof 11),
   ((chid_blstack, 197), .fRuleProof 25),
   ((chid_blstack, 198), .fRuleProof 26),
   ((chid_blstack, 199), .fRuleProof 12),
   ((chid_blstack, 200), .fOther "PBernConeIntv/proof"),
   ((chid_blstack, 201), .fRuleProof 14),
   ((chid_blstack, 202), .fOther "PSubdivide/proof"),
   ((chid_blstack, 203), .fOther "PLiRPA/proof"),
   ((chid_blstack, 204), .fOther "PReLUPos/proof"),
   ((chid_blstack, 205), .fOther "PReLUNeg/proof"),
   ((chid_blstack, 206), .fOther "PReLUNN/proof"),
   ((chid_blstack, 207), .fOther "PReLUAbove/proof"),
   ((chid_blstack, 208), .fOther "PCellInInterior/proof"),
   ((chid_blstack, 209), .fOther "PCellOut/proof"),
   ((chid_blstack, 210), .fRF 1 0),
   ((chid_blstack, 211), .fRF 1 1),
   ((chid_blstack, 212), .fRF 2 0),
   ((chid_blstack, 213), .fRF 2 1),
   ((chid_blstack, 214), .fRF 2 2),
   ((chid_blstack, 215), .fRF 3 0),
   ((chid_blstack, 216), .fRF 3 1),
   ((chid_blstack, 217), .fRF 4 0),
   ((chid_blstack, 218), .fRF 4 1),
   ((chid_blstack, 219), .fRF 5 0),
   ((chid_blstack, 220), .fRF 5 2),
   ((chid_blstack, 221), .fRF 5 1),
   ((chid_blstack, 222), .fPathHere),
   ((chid_blstack, 223), .fPathL),
   ((chid_blstack, 224), .fPathR),
   ((chid_blstack, 225), .fOther "conjunctAt"),
   ((chid_blstack, 226), .fOther "conjReplace"),
   ((chid_blstack, 227), .fRF 6 0),
   ((chid_blstack, 228), .fRF 6 1),
   ((chid_blstack, 229), .fRF 6 2),
   ((chid_blstack, 230), .fOther "POrE/disjL"),
   ((chid_blstack, 231), .fOther "POrE/disjR"),
   ((chid_blstack, 232), .fRF 7 0),
   ((chid_blstack, 233), .fRF 7 1),
   ((chid_blstack, 234), .fRF 7 2),
   ((chid_blstack, 235), .fRF 7 3),
   ((chid_blstack, 236), .fRF 7 4),
   ((chid_blstack, 237), .fRF 7 5),
   ((chid_blstack, 238), .fOther "substituteInFormula"),
   ((chid_blstack, 239), .fRF 23 0),
   ((chid_blstack, 240), .fRF 24 0),
   ((chid_blstack, 241), .fRF 24 1),
   ((chid_blstack, 242), .fRF 24 2),
   ((chid_blstack, 243), .fOther "barycentricHalfspaceForm"),
   ((chid_blstack, 244), .fRF 8 0),
   ((chid_blstack, 245), .fRF 8 1),
   ((chid_blstack, 246), .fRF 8 2),
   ((chid_blstack, 247), .fRF 8 3),
   ((chid_blstack, 248), .fRF 9 0),
   ((chid_blstack, 249), .fRF 9 1),
   ((chid_blstack, 250), .fRF 9 2),
   ((chid_blstack, 251), .fRF 9 3),
   ((chid_blstack, 252), .fRF 10 0),
   ((chid_blstack, 253), .fRF 10 1),
   ((chid_blstack, 254), .fRF 10 2),
   ((chid_blstack, 255), .fRF 10 3),
   ((chid_blstack, 256), .fRF 10 4),
   ((chid_blstack, 257), .fOther "atomicCompareForm"),
   ((chid_blstack, 258), .fOther "atomicCompareZero"),
   ((chid_blstack, 259), .fRF 11 0),
   ((chid_blstack, 260), .fRF 11 1),
   ((chid_blstack, 261), .fRF 11 2),
   ((chid_blstack, 262), .fRF 11 3),
   ((chid_blstack, 263), .fRF 11 4),
   ((chid_blstack, 264), .fRF 11 5),
   ((chid_blstack, 265), .fRF 11 6),
   ((chid_blstack, 266), .fOther "allForwardDiffBernCoeffsSatisfyP"),
   ((chid_blstack, 267), .fOther "isConicPredicate"),
   ((chid_blstack, 268), .fOther "isConvexPredicate"),
   ((chid_blstack, 269), .fOther "isExtensionSetEmpty"),
   ((chid_blstack, 270), .fOther "applyPredicateToTerm"),
   ((chid_blstack, 271), .fRF 12 0),
   ((chid_blstack, 272), .fRF 12 1),
   ((chid_blstack, 273), .fOther "polynomialCanonicalEq"),
   ((chid_blstack, 274), .fOther "PBernConeIntv/regionProof"),
   ((chid_blstack, 275), .fOther "PBernConeIntv/termX"),
   ((chid_blstack, 276), .fOther "PBernConeIntv/simplex"),
   ((chid_blstack, 277), .fOther "PBernConeIntv/S"),
   ((chid_blstack, 278), .fOther "PBernConeIntv/degree"),
   ((chid_blstack, 279), .fOther "PBernConeIntv/polynomial"),
   ((chid_blstack, 280), .fOther "PBernConeIntv/predicate"),
   ((chid_blstack, 281), .fOther "PBernConeIntv/dtype"),
   ((chid_blstack, 282), .fOther "isUpwardClosedConicPredicate"),
   ((chid_blstack, 283), .fOther "allForwardDiffBernIntvEnclosuresSatisfyP"),
   ((chid_blstack, 284), .fRF 25 0),
   ((chid_blstack, 285), .fRF 25 1),
   ((chid_blstack, 286), .fRF 25 2),
   ((chid_blstack, 287), .fRF 25 3),
   ((chid_blstack, 288), .fRF 25 4),
   ((chid_blstack, 289), .rPromIface),
   ((chid_blstack, 290), .fOther "promiseContractConfined"),
   ((chid_blstack, 291), .fOther "promiseWiresSeparated"),
   ((chid_blstack, 292), .fRF 26 0),
   ((chid_blstack, 293), .rSyzComp),
   ((chid_blstack, 294), .fRF 26 1),
   ((chid_blstack, 295), .fRF 26 2),
   ((chid_blstack, 296), .fRF 26 3),
   ((chid_blstack, 297), .fRF 26 4),
   ((chid_blstack, 298), .fOther "syzygyCombinationValid"),
   ((chid_blstack, 299), .fOther "premiseContains"),
   ((chid_blstack, 300), .fOther "positiveSizeWiresForm"),
   ((chid_blstack, 301), .fRF 14 0),
   ((chid_blstack, 302), .fRF 14 2),
   ((chid_blstack, 303), .fRF 14 1),
   ((chid_blstack, 304), .fOther "farkasCombinationValid"),
   ((chid_blstack, 305), .fOther "positiveSizeWires"),
   ((chid_blstack, 306), .fOther "PSubdivide/regionProof"),
   ((chid_blstack, 307), .fOther "PSubdivide/termX"),
   ((chid_blstack, 308), .fOther "PSubdivide/simplex"),
   ((chid_blstack, 309), .fOther "PSubdivide/S"),
   ((chid_blstack, 310), .fOther "PSubdivide/nBranches"),
   ((chid_blstack, 311), .fOther "PSubdivide/branchSimplex"),
   ((chid_blstack, 312), .fOther "PSubdivide/branchS"),
   ((chid_blstack, 313), .fOther "PSubdivide/branchProof"),
   ((chid_blstack, 314), .fOther "PSubdivide/coverCertificate"),
   ((chid_blstack, 315), .fOther "PSubdivide/denBoundLog2"),
   ((chid_blstack, 316), .fOther "coverInfeasibilityValid"),
   ((chid_blstack, 317), .fOther "PLiRPA/lowerBoundProof"),
   ((chid_blstack, 318), .fOther "PLiRPA/upperBoundProof"),
   ((chid_blstack, 319), .fOther "PLiRPA/preact"),
   ((chid_blstack, 320), .fOther "PLiRPA/post"),
   ((chid_blstack, 321), .fOther "PLiRPA/a"),
   ((chid_blstack, 322), .fOther "PLiRPA/b_endpt"),
   ((chid_blstack, 323), .fOther "PLiRPA/alpha"),
   ((chid_blstack, 324), .fOther "PLiRPA/beta"),
   ((chid_blstack, 325), .fOther "PLiRPA/gamma"),
   ((chid_blstack, 326), .fOther "PLiRPA/delta"),
   ((chid_blstack, 327), .fOther "PLiRPA/denBoundLog2"),
   ((chid_blstack, 328), .fOther "lirpaConclusionForm"),
   ((chid_blstack, 329), .fOther "PReLUPos/premise"),
   ((chid_blstack, 330), .fOther "PReLUPos/preact"),
   ((chid_blstack, 331), .fOther "PReLUPos/post"),
   ((chid_blstack, 332), .fOther "PReLUNeg/premise"),
   ((chid_blstack, 333), .fOther "PReLUNeg/preact"),
   ((chid_blstack, 334), .fOther "PReLUNeg/post"),
   ((chid_blstack, 335), .fOther "PReLUNN/post"),
   ((chid_blstack, 336), .fOther "PReLUAbove/preact"),
   ((chid_blstack, 337), .fOther "PReLUAbove/post"),
   ((chid_blstack, 338), .fOther "cellStrictInteriorForm"),
   ((chid_blstack, 339), .fOther "cellOneHotForm"),
   ((chid_blstack, 340), .fOther "cellOutWitnessForm"),
   ((chid_blstack, 341), .fOther "cellOutZeroForm"),
   ((chid_blstack, 342), .fOther "PCellInInterior/premise"),
   ((chid_blstack, 343), .fOther "PCellInInterior/cellApp"),
   ((chid_blstack, 344), .fOther "PCellInInterior/schema"),
   ((chid_blstack, 345), .fOther "PCellInInterior/whichI"),
   ((chid_blstack, 346), .fOther "PCellOut/premise"),
   ((chid_blstack, 347), .fOther "PCellOut/cellApp"),
   ((chid_blstack, 348), .fOther "PCellOut/schema"),
   ((chid_blstack, 349), .fOther "PCellOut/whichJ"),
   ((chid_blstack, 350), .fOther "PCellOut/witnessVertex"),
   ((chid_blstack, 351), .fOther "PConstExact/proof"),
   ((chid_blstack, 352), .fOther "PConstExact/termL"),
   ((chid_blstack, 353), .fOther "PConstExact/termR"),
   ((chid_blstack, 354), .fOther "PConstExact/bowtie"),
   ((chid_blstack, 355), .fOther "constExactEvalTrue"),
   ((chid_blstack, 356), .fOther "PBound/proof"),
   ((chid_blstack, 357), .fOther "PBound/nComponents"),
   ((chid_blstack, 358), .fOther "PBound/component"),
   ((chid_blstack, 359), .fOther "PBound/combinationCoeffs"),
   ((chid_blstack, 360), .fOther "PBound/conclusion"),
   ((chid_blstack, 361), .fOther "PBound/denBoundLog2"),
   ((chid_blstack, 362), .fOther "pBoundCombinationValid"),
   ((chid_blstack, 363), .fOther "syzygyConclusionFormRel"),
   ((chid_blstack, 364), .fOther "PPsdCertT/proof"),
   ((chid_blstack, 365), .fOther "PPsdCertT/n"),
   ((chid_blstack, 366), .fOther "PPsdCertT/A"),
   ((chid_blstack, 367), .fOther "PPsdCertT/Z"),
   ((chid_blstack, 368), .fOther "PPsdCertT/term"),
   ((chid_blstack, 369), .fOther "PPsdCertT/conclusion"),
   ((chid_blstack, 370), .fOther "psdCertTriWitness"),
   ((chid_blstack, 371), .fOther "psdCertTriConcl"),
   ((chid_blstack, 372), .fOther "PPsdCertDD/proof"),
   ((chid_blstack, 373), .fOther "PPsdCertDD/n"),
   ((chid_blstack, 374), .fOther "PPsdCertDD/A"),
   ((chid_blstack, 375), .fOther "PPsdCertDD/Z"),
   ((chid_blstack, 376), .fOther "PPsdCertDD/term"),
   ((chid_blstack, 377), .fOther "PPsdCertDD/conclusion"),
   ((chid_blstack, 378), .fOther "psdCertDiagWitness"),
   ((chid_blstack, 379), .fOther "psdCertDiagConcl"),
   ((chid_blstack, 380), .fOther "PPsdCertK/proof"),
   ((chid_blstack, 381), .fOther "PPsdCertK/m"),
   ((chid_blstack, 382), .fOther "PPsdCertK/k"),
   ((chid_blstack, 383), .fOther "PPsdCertK/nTotal"),
   ((chid_blstack, 384), .fOther "PPsdCertK/A"),
   ((chid_blstack, 385), .fOther "PPsdCertK/N"),
   ((chid_blstack, 386), .fOther "PPsdCertK/B"),
   ((chid_blstack, 387), .fOther "PPsdCertK/innerT"),
   ((chid_blstack, 388), .fOther "PPsdCertK/Z"),
   ((chid_blstack, 389), .fOther "PPsdCertK/term"),
   ((chid_blstack, 390), .fOther "PPsdCertK/conclusion"),
   ((chid_blstack, 391), .fOther "psdCertKernelWitness"),
   ((chid_blstack, 392), .fOther "psdCertKernelConcl"),
   ((chid_blstack, 393), .fOther "positiveSizeWiresTerm"),
   ((chid_blstack, 394), .fOther "BlockLattice/nAxes"),
   ((chid_blstack, 395), .fOther "BlockLattice/nBlocks"),
   ((chid_blstack, 396), .fOther "BLAxis/lattice"),
   ((chid_blstack, 397), .fOther "BLAxis/index"),
   ((chid_blstack, 398), .fOther "BLAxis/wire"),
   ((chid_blstack, 399), .fOther "BLAxis/drift"),
   ((chid_blstack, 400), .fOther "BLAxis/nGridlines"),
   ((chid_blstack, 401), .fOther "BLAxis/gridline"),
   ((chid_blstack, 402), .fOther "FamBlock/lattice"),
   ((chid_blstack, 403), .fOther "FamBlock/index"),
   ((chid_blstack, 404), .fOther "FamBlock/nCells"),
   ((chid_blstack, 405), .fOther "FamBlock/cell"),
   ((chid_blstack, 406), .fOther "FamBlock/nFacets"),
   ((chid_blstack, 407), .fOther "FamBlock/facetProof"),
   ((chid_blstack, 408), .fOther "blockLatticeWF"),
   ((chid_blstack, 409), .fOther "FamJudgment/lattice"),
   ((chid_blstack, 410), .fOther "PProductLattice/concludes"),
   ((chid_blstack, 411), .fOther "PProductLattice/left"),
   ((chid_blstack, 412), .fOther "PProductLattice/right"),
   ((chid_blstack, 413), .fOther "PProductLattice/flowsOnly"),
   ((chid_blstack, 414), .fOther "productLatticeChecks"),
   ((chid_blstack, 415), .fEncFunc),
   ((chid_blstack, 416), .fEncN),
   ((chid_blstack, 417), .fEncR),
   ((chid_blstack, 418), .fEncCap),
   ((chid_blstack, 419), .fPEncConcludes),
   ((chid_blstack, 420), .fOther "enclosureWitnessValid"),
   ((chid_certTheory, 0), .sCert),
   ((chid_certTheory, 1), .sOther "EinIn"),
   ((chid_certTheory, 2), .sOther "PSup"),
   ((chid_certTheory, 4), .fCertRoot),
   ((chid_certTheory, 5), .fOther "Cert/rootFam"),
   ((chid_certTheory, 6), .fCertRootEnc),
   ((chid_certTheory, 7), .fCertTheta),
   ((chid_certTheory, 8), .fCertNWires),
   ((chid_certTheory, 9), .fCertNApps),
   ((chid_certTheory, 10), .fCertNComplexes),
   ((chid_certTheory, 11), .fWireIndex),
   ((chid_certTheory, 12), .fOther "PrimApp/index"),
   ((chid_certTheory, 13), .fSimpCIndex),
   ((chid_certTheory, 14), .fOther "Wire/payloadQ"),
   ((chid_certTheory, 15), .fOther "Wire/payloadZ"),
   ((chid_certTheory, 16), .fOther "Wire/payloadB"),
   ((chid_certTheory, 17), .fOther "Wire/payloadF16"),
   ((chid_certTheory, 18), .fOther "Wire/payloadBF16"),
   ((chid_certTheory, 19), .fOther "Wire/payloadF32"),
   ((chid_certTheory, 20), .fOther "Wire/payloadF64"),
   ((chid_certTheory, 21), .fTHole),
   ((chid_certTheory, 22), .fFSpH),
   ((chid_certTheory, 23), .fRF 4 2),
   ((chid_certTheory, 24), .fOther "PReLUNN/preact"),
   ((chid_certTheory, 25), .fOther "ContractIndex/pos"),
   ((chid_certTheory, 26), .fSimpCNSimp),
   ((chid_certTheory, 27), .fSimpCNCells),
   ((chid_certTheory, 28), .fCplxSimpAt),
   ((chid_certTheory, 29), .rCellSimpHasV),
   ((chid_certTheory, 30), .rCellExtHasV),
   ((chid_certTheory, 31), .fOther "einNil"),
   ((chid_certTheory, 32), .fOther "einCons"),
   ((chid_certTheory, 33), .fOther "TEinsum"),
   ((chid_certTheory, 34), .fOther "psupNil"),
   ((chid_certTheory, 35), .fOther "psupW"),
   ((chid_certTheory, 36), .fOther "psupIdx"),
   ((chid_certTheory, 37), .fOther "TPolyMono"),
   ((chid_certTheory, 38), .fOther "TPolyBern"),
   ((chid_certTheory, 39), .fOther "TPoly/entry")]

/-- The dependency list
 a sealed certificate commit is expected to
pin, in order. -/
def stagedDeps : List (List Nat) :=
  [chid_blstack, chid_groundFormats, chid_certTheory]

/-- Resolve an external element reference against the pin table. -/
def resolveRef (pins : List ((List Nat × Nat) × Vocab))
    (deps : List Bytes) (r : ElemRef) : Option Vocab :=
  match r with
  | .loc _ => none
  | .ext d c =>
    match deps[d]? with
    | none => none
    | some chid => (pins.lookup (chid, c))

end Geolog
end PPLC
