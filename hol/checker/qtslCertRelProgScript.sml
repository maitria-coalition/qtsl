(*
  CakeML translation of the relational checker — readColumns, the
  directory builder, well-formedness, the six families, checkJoins and
  the verdict — translation only. Extends the flat chain's translated
  prog state, which already carries the shared parser surface and
  library functions.
*)
Theory qtslCertRelProg
Ancestors
  basis_ffi qtsl_dyadic qtsl_qarith qtsl_catalogue qtsl_cert qtsl_cols
  qtsl_wf qtsl_fam_ax qtsl_fam_ande qtsl_fam_ore qtsl_fam_cone
  qtsl_fam_syz qtsl_fam_resid qtsl_joins qtsl_rc qtsl_colread
  qtslCertProg
Libs
  preamble basis

val _ = translation_extends "qtslCertProg";

fun tryt th = (ignore (translate th)) handle HOL_ERR _ => ();

val _ = tryt listTheory.FILTER;
val _ = tryt listTheory.EVERY_DEF;
val _ = tryt listTheory.MAP;
val _ = tryt listTheory.REVERSE_DEF;
val _ = tryt listTheory.GENLIST_AUX;
val _ = tryt listTheory.GENLIST_GENLIST_AUX;
val _ = tryt listTheory.SUM;
val _ = tryt listTheory.REPLICATE;
val _ = tryt arithmeticTheory.MIN_DEF;

val r = translate sortedLt_def;
val r = translate (escContains_def
                   |> SIMP_RULE std_ss [ml_translatorTheory.MEMBER_INTRO]);
val r = translate escRank_def;
val r = translate tagDec_def;
val r = translate tagOf_def;
val r = translate tagDecD_def;
val r = translate ruleOfD_def;
val r = translate varOfD_def;
val r = translate isTermTag_def;
val r = translate isFormulaTag_def;
val r = translate poolTagOK_def;
val r = translate poolRefCnt_def;
val r = translate poolElemCnt_def;
val r = translate poolMiscCnt_def;
val r = translate ruleArity_def;
val r = translate prefCntR_def;
val r = translate scalCntR_def;
val r = translate hasPathR_def;
val r = translate hasArityR_def;
val r = translate nodeLenR_def;
val r = translate pathRankN_def;
val r = translate arityRankN_def;
val r = translate recLenP_def;
val r = translate miscBaseP_def;
val r = translate elemNumBase_def;
val r = translate childOrd_def;
val r = translate arityOf_def;
val r = translate nodeArityAt_def;
val r = translate scalField_def;
val r = translate pathOf_def;
val r = translate denOf_def;
val r = translate poolTagAt_def;
val r = translate refAt_def;
val r = translate poolField_def;
val r = translate ratOfElem_def;

val ratofelem_side = Q.prove(
  ‘∀cols e. ratofelem_side cols e’,
  rw[fetch "-" "ratofelem_side_def"]) |> update_precondition;

val r = translate ratAt_def;
val r = translate pvF_def;
val r = translate pv_def;
val r = translate pvEq_def;
val r = translate andeDerive_def;
val r = translate andeOther_def;
val r = translate convTriple_def;
val r = translate childConcl_def;
val r = translate conclStep_def;
val r = translate conclDir_def;
val r = translate conclRef_def;
val r = translate readPrefs_def;
val r = translate prefStep_def;
val r = translate prefDir_def;
val r = translate prefField_def;

val _ = PolyML.fullGC ();

val r = translate peekPrfLen_def;
val r = translate pInit_def;
val r = translate poolRecLen_def;
val r = translate poolStep_def;
val r = translate poolFold_def;
val r = translate nInit_def;
val r = translate nodeStep_def;
val r = translate nodeFold_def;
val r = translate rpnStep_def;
val r = translate rpnReplay_def;
val r = translate explChildren_def;
val r = translate explStep_def;
val r = translate explRows_def;
val r = translate prefExplCnt_def;
val r = translate prefBaseOf_def;
val r = translate mkCtx_def;
val r = translate isTermAt_def;
val r = translate isFormulaAt_def;
val r = translate isSimplexAt_def;
val r = translate isExtSetAt_def;
val r = translate isJudgAt_def;
val r = translate isConstAt_def;
val r = translate fwNoSphRef_def;
val r = translate wf1_def;
val r = translate wf2_def;
val r = translate wf3_def;
val r = translate wf4_def;
val r = translate wf5_def;
val r = translate wf6rec_def;
val r = translate wf6_def;
val r = translate wf7elem_def;
val r = translate fuStep_def;
val r = translate wf7_def;
val r = translate pfIs_def;
val r = translate wf8node_def;
val r = translate wf8_def;
val r = translate wf9_def;
val r = translate escPre_def;
val r = translate escPre2_def;
val r = translate wf10_def;
val r = translate wf11_def;
val r = translate wf12_def;
val r = translate wfColumns_def;

val _ = PolyML.fullGC ();

val r = translate checkFam_ax_def;
val r = translate checkFam_ande_def;
val r = translate nodeSq_def;
val r = translate pathArgs_def;
val r = translate conjGetSteps_def;
val r = translate conjReplaceSteps_def;
val r = translate checkFam_ore_def;
val r = translate checkFam_conv_def;
val r = translate checkFam_berncone_def;
val r = translate childSeqAt_def;
val r = translate checkFam_farkas_def;
val r = translate checkFam_syz_def;
val r = translate frSeq_def;
val r = translate frChildSeq_def;
val r = translate frFormula_def;
val r = translate frTerm_def;
val r = translate checkFam_weaken_def;
val r = translate checkFam_cut_def;
val r = translate checkFam_andi_def;
val r = translate checkFam_ori_def;
val r = translate checkFam_eqelim_def;
val r = translate checkFam_arith_def;
val r = translate checkFam_norm_def;
val r = translate checkFam_eqrefl_def;
val r = translate checkFam_eqsym_def;
val r = translate checkFam_promise_def;

val _ = PolyML.fullGC ();

val r = translate checkNode_def;
val r = translate checkNodes_def;
val r = translate checkJoins_def;

val r = translate rdVarF_def;
val r = translate rdVar_def;
val r = translate dApp_def;
val r = translate rdU16s_def;
val r = translate rdTables_def;
val r = translate deserModel_def;
val r = translate rcByte_def;
val r = translate rcInit_def;
val r = translate findSymF_def;
val r = translate renormF_def;
val r = translate rcDecode1_def;
val r = translate rcDecodeN_def;
val r = translate decompressO01_def;
val r = translate rdBlockIdx_def;
val r = translate decBlocks_def;
val r = translate decompressBlocks_def;
val r = translate rdLens_def;
val r = translate blockedRaw_def;

val r = translate rdU32At_def;
val r = translate rdU64At_def;
val r = translate rdDirEnts_def;
val r = translate dirFind_def;
val r = translate streamDec_def;
val r = translate rdDeltasF_def;
val r = translate rdDeltas_def;
val r = translate rdDenPairsF_def;
val r = translate rdDenPairs_def;
val r = translate rdDictF_def;
val r = translate rdDict_def;
val r = translate rdVarsK_def;
val r = translate pInitR_def;
val r = translate rdRef1_def;
val r = translate rdRefsK_def;
val r = translate rdElem1_def;
val r = translate rdMiscV_def;
val r = translate rdMiscBytes_def;
val r = translate poolRdStep_def;
val r = translate poolRdFold_def;
val r = translate nInitR_def;
val r = translate rdConclE_def;
val r = translate rdPrefsE_def;
val r = translate rdChildConcl_def;
val r = translate nodeRdStep_def;
val r = translate nodeRdFold_def;
val r = translate emptyCols_def;
val r = translate sgcMagic_def;
val r = translate readColumns_def;

val r = translate unreadable_string_def;
val r = translate qtsl_rel_result_def;
val r = translate qtsl_rel_verdict_strI_def;

val _ = PolyML.fullGC ();
