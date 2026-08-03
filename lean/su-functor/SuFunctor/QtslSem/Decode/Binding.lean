import SuFunctor.QtslSem.Decode.Pins
import Qtsl.Soundness
import Qtsl.ReluSplit
import Qtsl.TimedCore
import QtslAux.QStreett
import QtslAux.QtslAliases

/-!
# The binding table: row vocabulary → lemma names → components

The census join's finding, made first-class data: the catalogue's Lean
column binds the original development tree exclusively, QtslSem wires
this repository's lemmas, and **this table is where the vocabularies
meet** — one
row per catalogue entry, carrying the catalogue-bound lemma spines,
the verified cross-tree naming-drift map (original-tree name →
this repository's name; the census seed, merged with its three
`q_missing`-listed
statement-identical pairs `sound_QInvRelativize → sound_u10f`,
`sound_QFirstService → sound_firstService`, `sound_QFirstServiceSplit
→ sound_fsResidual`), the spines with no home in this repository, and
the wired QtslSem component constructors.

Provenance and cache discipline: generated from a census join of the
two trees, pinned at a fixed commit of this repository, with the
component column patched to THIS tree as later landings wired
`Subdivide`/`PBound`/`Syzygy`, ported `sound_antisym`, and wired
`antisym`/`reluSplit` — those rows updated here accordingly.  Rows
are caches; the live tree outranks them.

The drift map's tooth: the `#check` block at the end of this module
forces every drift target to resolve against the qtsl repo's actual
declarations at compile time — a renamed lemma breaks this module,
not a downstream wiring leg.
-/

namespace SuFunctor

namespace QtslSem

namespace Decode

/-- Which stratum a catalogue entry belongs to (the dashboard's
source column). -/
inductive BindStratum where
  | bl | qtsl
  deriving Repr, DecidableEq

/-- One catalogue entry's binding row: catalogue-bound lemma spines,
the cross-tree drift pairs, the spines with no home in this
repository, and the wired QtslSem component constructors. -/
structure RuleBinding where
  entry : String
  stratum : BindStratum
  tier : String
  spines : List String
  drift : List (String × String)
  qtslMissing : List String
  components : List String
  deriving Repr, DecidableEq

/-- The qtsl-repo spelling of a catalogue-bound lemma name: the drift
map applied where it carries the name, the identity elsewhere. -/
def RuleBinding.qtslName (b : RuleBinding) (n : String) : String :=
  match b.drift.find? (fun p => p.1 == n) with
  | some p => p.2
  | none => n

/-- A row is wired iff it carries at least one component constructor. -/
def RuleBinding.wired (b : RuleBinding) : Bool := !b.components.isEmpty

/-- The binding table (generated; see the module header). -/
def qtslBindingTable : List RuleBinding :=
  [
    ⟨"Ax", .bl, "core", ["sound_ax"],
      [], [], ["ax"]⟩,
    ⟨"Weaken", .bl, "core", ["sound_weaken"],
      [], [], ["weaken"]⟩,
    ⟨"Cut", .bl, "core", ["sound_cut"],
      [], [], ["cut"]⟩,
    ⟨"AndI", .bl, "core", ["sound_andI"],
      [], [], ["andI"]⟩,
    ⟨"AndE", .bl, "core", ["sound_andE_left", "sound_andE_right"],
      [], [], ["andELeft", "andERight"]⟩,
    ⟨"OrI", .bl, "core", ["sound_orI_left", "sound_orI_right"],
      [], [], ["orILeft", "orIRight"]⟩,
    ⟨"OrE", .bl, "core", ["sound_orECtx", "sound_orE"],
      [], [], ["orE"]⟩,
    ⟨"EqElim", .bl, "core", ["sound_eqElim"],
      [], [], ["eqElim"]⟩,
    ⟨"EqRefl", .bl, "core", ["sound_eqRefl"],
      [], [], ["eqRefl"]⟩,
    ⟨"EqSym", .bl, "core", ["sound_eqSym"],
      [], [], ["eqSym"]⟩,
    ⟨"Antisym", .bl, "core", ["sound_antisym"],
      [], [], ["antisym"]⟩,
    ⟨"ConvElim", .bl, "core", ["sound_convElim"],
      [], [], ["convElim"]⟩,
    ⟨"ConvIntro", .bl, "core", ["sound_convIntro"],
      [], [], ["convIntro"]⟩,
    ⟨"ArithAtom", .bl, "core", ["sound_arithAtom_fold", "sound_arithAtom_unfold"],
      [], [], ["arithAtomFold", "arithAtomUnfold"]⟩,
    ⟨"BernCone", .bl, "core", ["sound_bernCone", "sound_bernCone_empty"],
      [], [], ["bernCone", "bernConeEmpty"]⟩,
    ⟨"Syzygy", .bl, "core", ["atomLeZeroPolys_sound_entryC", "sound_syzygy"],
      [], [], ["syzygy"]⟩,
    ⟨"QSafetyBattery", .qtsl, "core", ["sound_QSafetyBattery", "sound_QSafetyBattery_failClosed", "sound_GSHS_safety_battery", "sound_QSafetyBattery_staged", "sound_GSHS_safety_battery_mp", "sound_GSHS_safety_mp"],
      [], ["exitDebut_le_family_of_isClosed_cell", "isStoppingTime_debut", "GshsSegmentVille.ofDischarge", "measure_sup_ge_le_of_supermartingale"], []⟩,
    ⟨"QDeadlineBattery", .qtsl, "core", ["sound_QDeadline", "sound_QDeadline_hit", "sound_GSHS_deadline", "sound_GSHS_deadline_battery", "sound_GSHS_deadline_offTarget", "sound_QDeadlineBattery", "sound_GSHS_deadline_battery_mp", "sound_GSHS_deadline_mp"],
      [], [], []⟩,
    ⟨"QUnionBound", .qtsl, "core", ["sound_QUnionBound", "sound_QUnionBound_ofReal"],
      [], [], []⟩,
    ⟨"QStreettBattery", .qtsl, "core", ["sound_GSHS_streett_bundle", "sound_GSHS_streett_bundle_confined", "sound_QStreettBattery", "sound_QStreettBattery_carved_discharged"],
      [("sound_QStreettBattery", "sound_QStreettBundle"), ("sound_QStreettBattery_carved_discharged", "sound_QStreettBundle_carved_discharged")], [], []⟩,
    ⟨"QMorseDischarge", .qtsl, "core", ["qMorseDischarge_sound_cellCover", "qMorseDischarge_sound_modelClass", "qMorseDischarge_sound_eventualMember", "qMorseDischarge_sound_orderAssembled", "qMorseDischarge_sound"],
      [], [], []⟩,
    ⟨"QMorseProduct", .qtsl, "core", ["qMorseProduct_sound"],
      [], [], []⟩,
    ⟨"QBlockInv", .qtsl, "core", ["qBlockInv_sound_of_dwell", "qBlockInv_sound_of_facetRows", "qBlockInv_sound_of_grid", "qBlockInv_sound_of_pointwiseRows", "qBlockInv_sound_of_rows", "qBlockInv_sound"],
      [], [], []⟩,
    ⟨"QBasin", .qtsl, "core", ["qBasin_sound"],
      [], [], []⟩,
    ⟨"QWireCompose", .qtsl, "core", ["sound_GSHS_safety_barrier"],
      [], [], []⟩,
    ⟨"QWireCertDischarge", .qtsl, "core", [],
      [], [], []⟩,
    ⟨"QSimTransport", .qtsl, "core", [],
      [], [], []⟩,
    ⟨"QAggReduce", .qtsl, "core", [],
      [], [], []⟩,
    ⟨"QCoupleDrift", .qtsl, "core", ["sound_QRelExpGap", "sound_QRelTV", "sound_QRelTV_measure"],
      [], ["exists_hahn", "sound_QRelTV_measure", "tvDist_le_coupling", "tvDist_ofFn"], []⟩,
    ⟨"QFixBall", .qtsl, "core", ["sound_QFixBall", "sound_QFixBall_affine", "sound_QFixBall_wasserstein"],
      [], [], []⟩,
    ⟨"QDistTransport", .qtsl, "core", ["sound_QDistSelfTransport", "sound_QDistTransport_eps"],
      [], [], []⟩,
    ⟨"QInvRelativize", .qtsl, "core", ["sound_QInvRelativize"],
      [("sound_QInvRelativize", "sound_u10f")], [], []⟩,
    ⟨"QFirstService", .qtsl, "core", ["sound_QFirstService"],
      [("sound_QFirstService", "sound_firstService")], ["qFirstService_attainment_necessary"], []⟩,
    ⟨"QFirstServiceSplit", .qtsl, "core", ["sound_QFirstServiceSplit"],
      [("sound_QFirstServiceSplit", "sound_fsResidual")], [], []⟩,
    ⟨"Norm", .bl, "adm.", ["sound_norm"],
      [], [], ["norm"]⟩,
    ⟨"Farkas", .bl, "adm.", ["sound_farkas"],
      [], [], ["farkas"]⟩,
    ⟨"Subdivide", .bl, "adm.", ["sound_subdivide"],
      [], [], ["subdivide"]⟩,
    ⟨"LiRPA", .bl, "adm.", ["sound_lirpa"],
      [], [], ["lirpa"]⟩,
    ⟨"ReLUPos", .bl, "adm.", ["sound_reluPos"],
      [], [], ["reluPos"]⟩,
    ⟨"ReLUNeg", .bl, "adm.", ["sound_reluNeg"],
      [], [], ["reluNeg"]⟩,
    ⟨"ReLUNN", .bl, "adm.", ["sound_reluNN"],
      [], [], ["reluNN"]⟩,
    ⟨"ReLUAbove", .bl, "adm.", ["sound_reluAbove"],
      [], [], ["reluAbove"]⟩,
    ⟨"CellInInterior", .bl, "adm.", ["sound_cellInInterior"],
      [], [], ["cellInInterior"]⟩,
    ⟨"CellOut", .bl, "adm.", ["sound_cellOut"],
      [], [], ["cellOut"]⟩,
    ⟨"PConstExact", .bl, "adm.", ["sound_pConstExact"],
      [], [], ["pConstExact"]⟩,
    ⟨"PsdCertTri", .bl, "adm.", ["sound_psdCertOf", "sound_psdCertTri"],
      [("sound_psdCertTri", "sound_psdCertT")], ["checkTri", "checkTri_posDef", "checkTri_quadForm_nonneg"], ["psdCertT"]⟩,
    ⟨"PsdCertDiag", .bl, "adm.", ["sound_psdCertDiag"],
      [("sound_psdCertDiag", "sound_psdCertDD")], ["checkDiag", "checkDiag_posDef", "checkDiag_quadForm_nonneg"], ["psdCertDD"]⟩,
    ⟨"PsdCertKernel", .bl, "adm.", ["sound_psdCertKernel"],
      [("sound_psdCertKernel", "sound_psdCertK")], ["checkKernel", "checkKernel_posSemidef", "checkKernel_quadForm_nonneg"], ["psdCertK"]⟩,
    ⟨"ReLUSplit", .bl, "adm.", ["sound_reluSplit"],
      [], [], ["reluSplit"]⟩,
    ⟨"Promise", .bl, "adm.", ["sound_promise"],
      [], [], ["promise"]⟩,
    ⟨"ProductLattice", .bl, "adm.", ["sound_productLattice", "sound_productLattice_citeLeft", "sound_productLattice_citeRight"],
      [], [], []⟩,
    ⟨"QUntilBattery", .qtsl, "adm.", ["sound_GSHS_avoid_timed", "sound_GSHS_until", "sound_GSHS_until_battery", "sound_QUntilBattery", "sound_QUntilBattery_firstHit", "sound_GSHS_until_battery_mp", "sound_GSHS_until_mp"],
      [], [], []⟩,
    ⟨"QStreettCmplRequest", .qtsl, "adm.", ["sound_GSHS_streett_bundle_carved_discharged", "sound_GSHS_streett_bundle_carved_discharged_confined", "sound_QStreettBattery_tie"],
      [("sound_QStreettBattery_tie", "sound_QStreettBundle_tie")], [], []⟩,
    ⟨"HypMultiplier", .qtsl, "adm.", ["hypMultiplier_sound"],
      [], [], []⟩,
    ⟨"QVerifiedCover", .qtsl, "adm.", ["verifiedCover_components_sound", "verifiedCover_sound"],
      [], [], []⟩,
    ⟨"QPositiveCombinationRoot", .qtsl, "adm.", ["positiveCombinationAnd_sound", "positiveCombinationInter_sound", "positiveCombinationOr_sound", "positiveCombinationUnion_sound"],
      [], [], []⟩,
    ⟨"QClosureOutward", .qtsl, "adm.", ["closureOutwardGe_sound", "closureOutward_sound"],
      [], [], []⟩,
    ⟨"QClosureInwardEps", .qtsl, "adm.", ["closureInwardEpsGt_sound", "closureInwardEpsLt_sound"],
      [], [], []⟩,
    ⟨"BoxBern", .qtsl, "adm.", [],
      [], [], []⟩,
    ⟨"PExpTypeEnclosure", .qtsl, "adm.", ["encCheck_sound", "encCheck_sound_bracket", "encCheck_sound", "encCheck_sound_bracket"],
      [], [], []⟩,
    ⟨"QFlatten", .qtsl, "adm.", [],
      [], [], []⟩,
    ⟨"PBound", .bl, "alias", ["sound_pBound", "sound_syzygy"],
      [], [], ["pBound"]⟩,
    ⟨"SmallGain", .bl, "alias", ["sound_smallGain"],
      [], [], []⟩,
    ⟨"QSatFromRegion", .qtsl, "alias", ["qsatFromRegionElab_sound", "sound_QSatFromRegion", "sound_QSatFromRegion_sublevel"],
      [], ["qsatFromRegionElab", "qsatFromRegionElab_sat", "qsatFromRegionElab_sound"], []⟩,
    ⟨"QStreettDegenerate", .qtsl, "alias", ["sound_GSHS_streett_bundle_confined", "sound_QStreettDegenerate"],
      [("sound_QStreettDegenerate", "sound_StreettDegenerate")], [], []⟩,
    ⟨"QStreettTargetCellCollapse", .qtsl, "alias", [],
      [], [], []⟩,
    ⟨"QNnfRewrite", .qtsl, "alias", [],
      [], [], []⟩,
    ⟨"QStreettRequestNnf", .qtsl, "alias", [],
      [], [], []⟩,
    ⟨"QAvoid", .qtsl, "alias", [],
      [], [], []⟩,
    ⟨"QStreettGF", .qtsl, "alias", [],
      [], [], []⟩,
    ⟨"QStreettFG", .qtsl, "alias", [],
      [], [], []⟩,
    ⟨"QNegFAlias", .qtsl, "alias", ["sound_QNegFAlias"],
      [("sound_QNegFAlias", "sound_NegFAlias")], [], []⟩,
    ⟨"QFullDomainWeaken", .qtsl, "alias", ["fullDomainWeaken_sound"],
      [], [], []⟩,
    ⟨"QClosureExact", .qtsl, "alias", ["closureExactGt_sound", "closureExactLt_sound"],
      [], [], []⟩,
    ⟨"TaylorBound", .qtsl, "alias", ["taylorElab_sound"],
      [], ["taylorElab", "taylorElab_le_exp", "taylorElab_sound", "taylorFormula_true_iff", "taylorPartialSum"], []⟩,
    ⟨"RootEval", .qtsl, "alias", ["rootEvalElab_sound"],
      [], ["polyClosedTerm", "polyClosedTerm_evalQ", "rootEvalElab", "rootEvalElab_sound", "rootEvalFormula", "rootEvalFormula_true_iff"], []⟩,
    ⟨"QLatticeInv", .qtsl, "alias", ["Behavior.qLatticeInv_sound_elab", "Semiflow.qLatticeInv_sound_elab", "Behavior.qLatticeInv_sound", "Behavior.qLatticeInv_sound_of_blockInv", "Semiflow.qLatticeInv_sound", "Semiflow.qLatticeInv_sound_of_blockInv"],
      [], ["Behavior.qLatticeInv_sound_elab", "BlockInvPayload", "LatticeInvPayload", "LatticeInvPayload.unpack", "Semiflow.qLatticeInv_sound_elab"], []⟩,
    ⟨"QCountAtomRounding", .qtsl, "alias", ["countAtomRounding_sound"],
      [], [], []⟩,
    ⟨"ProofWellFormedness", .qtsl, "glue", ["citeCmpl_sound", "citePos_sound", "towerCitation_sound", "towerCitation_sound_of_wf"],
      [], [], []⟩]

/-- Rows by entry name. -/
def bindingOf (entry : String) : Option RuleBinding :=
  qtslBindingTable.find? (fun b => b.entry == entry)

/-- Table well-formedness, checked at compile time: 79 rows, no
duplicate entries. -/
theorem qtslBindingTable_wf :
    (qtslBindingTable.length = 79
      ∧ (qtslBindingTable.map RuleBinding.entry).eraseDups.length = 79) := by
  decide

/-!
## The drift map's compile-time witnesses

Every qtsl-repo drift target the table cites resolves against a real
declaration of this tree — the `#check` commands below hard-fail on an
unknown name, so a rename anywhere in the drifted families breaks this
module, not a downstream wiring leg.  (`#check` rather than a witness
theorem: several targets are universe-polymorphic, and a command
tolerates the unassigned universe variables a tactic-block `have`
would refuse.)
-/

#check @PPLC.Qtsl.sound_u10f
#check @PPLC.Qtsl.sound_firstService
#check @PPLC.Qtsl.sound_fsResidual
#check @PPLC.sound_psdCertT
#check @PPLC.sound_psdCertDD
#check @PPLC.sound_psdCertK
#check @PPLC.sound_antisym
#check @PPLC.sound_reluSplit
#check @Qtsl.QStreett.sound_QStreettBundle
#check @Qtsl.QStreett.sound_QStreettBundle_carved_discharged
#check @Qtsl.QStreett.sound_QStreettBundle_tie
#check @Qtsl.QStreett.sound_StreettDegenerate
#check @Qtsl.Aliases.sound_NegFAlias

end Decode

end QtslSem

end SuFunctor
