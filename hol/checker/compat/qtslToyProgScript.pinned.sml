(*
  A pinned generation of qtslToyProgScript.sml (the receipt-table
  program without the enclosure slice), kept as a committed, auditable
  object so the certificate-checker chains' translator-environment
  ancestor is reproducible independently of later additions to the
  default script.
*)
Theory qtslToyProg
Ancestors
  basis_ffi qtsl_dyadic qtsl_qarith qtsl_catalogue
Libs
  preamble basis

val _ = translation_extends "basisProg";

val r = translate nchoose_def;
val r = translate log2f_def;
val r = translate clog2_def;
val r = translate ratFloor_def;
val r = translate ratCeil_def;
val r = translate ratAbs_def;
val r = translate ceilInvPos_def;

val ceilinvpos_side = Q.prove(
  ‘∀q. ceilinvpos_side q’,
  rw[fetch "-" "ceilinvpos_side_def"]
  \\ gvs[ratTheory.RAT_LES_LEQ]
  \\ ‘RATD q ≠ 0’ by simp[ratTheory.RATD_NZERO]
  \\ simp[]
  \\ metis_tac[ratTheory.RAT_LES_IMP_LEQ, ratTheory.RAT_LES_REF])
  |> update_precondition;

val r = translate intLog2_def;

val intlog2_side = Q.prove(
  ‘∀q. intlog2_side q’,
  rw[fetch "-" "intlog2_side_def"]
  \\ gvs[ratTheory.RATN_SIGN, ratTheory.RATD_NZERO]
  \\ metis_tac[ratTheory.RAT_LEQ_TRANS, ratTheory.RAT_LES_IMP_LEQ,
               ratTheory.RAT_LES_01]) |> update_precondition;

val r = translate roundNQ_def;

val r = translate pow2i_def;

val pow2i_side = Q.prove(
  ‘∀e. pow2i_side e’,
  rw[fetch "-" "pow2i_side_def"] \\ intLib.ARITH_TAC) |> update_precondition;

val r = translate maxFin_def;
val r = translate intMax_def;
val r = translate gridExp_def;
val r = translate rdnRaw_def;

val rdnraw_side = Q.prove(
  ‘∀fmt q. rdnraw_side fmt q’,
  rw[fetch "-" "rdnraw_side_def", pow2i_nonzero]) |> update_precondition;

val r = translate rdn_def;
val r = translate rup_def;
val r = translate rtz_def;
val r = translate rne_def;

val rne_side = Q.prove(
  ‘∀fmt q. rne_side fmt q’,
  rw[fetch "-" "rne_side_def", pow2i_nonzero]) |> update_precondition;
val r = translate f16_def;
val r = translate bf16_def;
val r = translate f32_def;
val r = translate f64_def;

val r = translate eratLe_def;
val r = translate eratAdd_def;
val r = translate eratMul_def;
val r = translate listTheory.FOLDL;
val r = translate eratSum_def;
val r = translate eratProd_def;

val r = translate ratEq_def;
val r = translate eratEq_def;
val r = translate oeratEq_def;
val r = translate receipts_def;
val r = translate receipt_line_def;
val r = translate receipts_string_def;

val r = translate natCmp_def;
val r = translate ratPow_def;
val r = translate pfind_def;
val r = translate nubL_def;
val r = translate rangeL_def;
val r = translate getD_def;
val r = translate zipL_def;
val r = translate monoCmp_def;
val r = translate insertVar_def;
val r = translate monoCanon_def;
val r = translate monoMul_def;
val r = translate monoDeg_def;
val r = translate insertTerm_def;
val r = translate polyCanon_def;
val r = translate polyAdd_def;
val r = translate polyNeg_def;
val r = translate polySub_def;
val r = translate polyScale_def;
val r = translate polyMul_def;
val r = translate polyConst_def;
val r = translate polyVar_def;
val r = translate polyPow_def;
val r = translate arithmeticTheory.MAX_DEF;
val r = translate polyTotalDeg_def;
val r = translate polyCoeffOf_def;
val r = translate polyVars_def;
val r = translate polyEval_def;
val r = translate multinomial_def;
val r = translate compositions_def;

val compositions_side = Q.prove(
  ‘∀parts total. compositions_side parts total’,
  Induct >> rw[Once (fetch "-" "compositions_side_def")] >>
  gvs[MEM_rangeL, arithmeticTheory.SUC_SUB1]) |> update_precondition;

val r = translate compositionsUpTo_def;
val r = translate subCompositions_def;
val r = translate vecToMono_def;
val r = translate assembleVec_def;
val r = translate sumVars_def;
val r = translate coordPoly_def;
val r = translate polySubst_def;
val r = translate homogenize_def;
val r = translate bernCoeffRows_def;

val berncoeffrows_side = Q.prove(
  ‘∀m d hp. berncoeffrows_side m d hp’,
  rw[fetch "-" "berncoeffrows_side_def", rat_multinomial_nz, multinomial_nz])
  |> update_precondition;

val r = translate fdBernstein_def;

val fdbernstein_side = Q.prove(
  ‘∀verts smask d p. fdbernstein_side verts smask d p’,
  rw[Once (fetch "-" "fdbernstein_side_def")] >>
  gvs[rat_multinomial_nz, multinomial_nz] >>
  metis_tac[LENGTH_FILTER_LEQ])
  |> update_precondition;

val r = translate gridAll_def;
val r = translate assembleVecQ_def;
val r = translate starIdentityCheck_def;
val r = translate qreceipts_def;
val r = translate qreceipts_string_def;

val r = translate kindFmt_def;
val r = translate ratMax_def;
val r = translate kindRoundQ_def;
val r = translate dtypeRoundE_def;
val r = translate dtB_def;
val r = translate dtN_def;
val r = translate dtZ_def;
val r = translate dtQ_def;
val r = translate dtQnn_def;
val r = translate dtF64_def;
val r = translate shapeRank_def;
val r = translate shapeTotalSize_def;
val r = translate simplexContainsNat_def;
val r = translate extContainsNat_def;
val r = translate extIsEmptyB_def;
val r = translate chainAnd_def;
val r = translate chainOr_def;
val r = translate termToPoly_def;
val r = translate termEvalQ_def;
val r = translate bowtieEvalQ_def;
val r = translate formulaEvalClosed_def;
val r = translate baryLambdas1D_def;

val r = translate termFreeWires_def;
val r = translate termIdxFree_def;
val r = translate termIdxBounded_def;
val r = translate formulaFreeWires_def;
val r = translate termVarHead_def;
val r = translate termSubst_def;
val r = translate formulaSubst_def;
val r = translate atomicCompareFormB_def;
val r = translate atomicCompareZeroB_def;
val r = translate substituteInFormulaB_def;
val r = translate predicateHole_def;
val r = translate applyPredicateToTermB_def;

val r = translate gcdTheory.gcd_def;
val r = translate gcdTheory.lcm_def;
val r = translate baryCoeffs1D_def;
val r = translate intAbsNum_def;

val intabsnum_side = Q.prove(
  ‘∀i. intabsnum_side i’,
  rw[fetch "-" "intabsnum_side_def"] \\ intLib.ARITH_TAC)
  |> update_precondition;

val r = translate primAffine_def;
val r = translate f4Lhs_def;
val r = translate f4VertexAtom_def;
val r = translate barycentricHalfspaceBuild_def;
val r = translate barycentricHalfspaceFormB_def;
val r = translate bowtieFlip_def;
val r = translate parseHoleSide_def;
val r = translate classifyOriented2_def;
val r = translate classifyOriented_def;
val r = translate classifyPredAtom_def;
val r = translate classifyPred_def;
val r = translate isConicPredicateB_def;
val r = translate isConvexPredicateB_def;
val r = translate isUpwardClosedConicPredicateB_def;
val r = translate polynomialCanonicalEqB_def;
val r = translate satisfiesPredQ_def;
val r = translate termAsCoordPolyIdx_def;
val r = translate termAsCoordPoly_def;
val r = translate bernConeCoeffCheck_def;
val r = translate bernConeIntvCheck_def;
val r = translate conjunctList_def;
val r = translate atomLeZeroPolys_def;
val r = translate farkasEntries_def;
val r = translate atomSidesIdxFree_def;
val r = translate farkasCheckCore_def;
val r = translate wireCoordKey_def;
val r = translate asCoordPolyIdxW_def;
val r = translate atomLeZeroPolysW_def;
val r = translate farkasEntriesW_def;
val r = translate farkasCheckW_def;
val r = translate farkasCheck_def;
val r = translate conjGet_def;
val r = translate conjReplace_def;
val r = translate isEqAtom_def;
val r = translate syzygyCheckCore_def;
val r = translate syzygyCheckW_def;
val r = translate syzygyCheck_def;
val r = translate extInterval1D_def;
val r = translate coverExtendPass_def;
val r = translate coverReach_def;
val r = translate coverChainCheck_def;
val r = translate coverCheck_def;
val r = translate cxB_def;
val r = translate simplexB_def;
val r = translate Sempty_def;
val r = translate demoW0_def;
val r = translate polyB_def;
val r = translate predP1_def;
val r = translate simplexPt_def;
val r = translate SemptyPt_def;
val r = translate cxL_def;
val r = translate simplexL_def;
val r = translate SemptyL_def;
val r = translate cxR_def;
val r = translate simplexR_def;
val r = translate SemptyR_def;
val r = translate cxG_def;
val r = translate simplexG_def;
val r = translate SemptyG_def;
val r = translate SextB_def;
val r = translate subBranches_def;
val r = translate creceipts_def;
val r = translate creceipts_string_def;

Definition full_output_def:
  full_output = concat [receipts_string; qreceipts_string; creceipts_string]
End
val r = translate full_output_def;

Quote add_cakeml:
  fun main u = TextIO.print full_output
End

val st = get_ml_prog_state ()

Theorem main_spec:
  app (p:'ffi ffi_proj) ^(fetch_v "main" st)
      [Conv NONE []]
      (STDIO fs)
      (POSTv uv. &UNIT_TYPE () uv * STDIO (add_stdout fs full_output))
Proof
  xcf "main" st \\ xapp \\ xsimpl
  \\ simp[fetch "-" "full_output_v_thm"]
QED

Theorem qtsl_toy_whole_prog_spec:
  whole_prog_spec ^(fetch_v "main" st) cl fs NONE
    ((=) (add_stdout fs full_output))
Proof
  rw[whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac`fs1`
  \\ simp[Abbr`fs1`,GSYM add_stdo_with_numchars,with_same_numchars]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe main_spec))
  \\ xsimpl
QED

val spec = qtsl_toy_whole_prog_spec
val name = "main";

val (call_thm_qtsl_toy, qtsl_toy_prog_tm) = whole_prog_thm st name spec;

Definition qtsl_toy_prog_def:
  qtsl_toy_prog = ^qtsl_toy_prog_tm
End

Theorem qtsl_toy_semantics =
  call_thm_qtsl_toy |> ONCE_REWRITE_RULE[GSYM qtsl_toy_prog_def]
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]
