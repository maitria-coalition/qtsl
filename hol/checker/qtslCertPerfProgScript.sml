(*
  CakeML translation of the performance implementation (qtsl_certPerf)
  — translation only. Extends the receipt-table prog state rather than
  the flat chain's: the spec-side parser and checker are deliberately
  not translated, keeping the prog state and the whole-program
  evaluation small.
*)
Theory qtslCertPerfProg
Ancestors
  basis_ffi qtsl_dyadic qtsl_qarith qtsl_catalogue qtsl_cert qtsl_certPerf
  qtslToyProg
Libs
  preamble basis

val _ = translation_extends "qtslToyProg";

val r = translate listTheory.oEL_def;
val r = translate listTheory.TAKE_def;
val r = translate listTheory.DROP_def;

val r = translate sptreeTheory.lookup_def;
val r = translate sptreeTheory.insert_def;

val r = translate leN_def;
val r = translate denMinimal_def;
val r = translate numMinimal_def;
val r = translate egcd_def;
val r = translate byteBit_def;
val r = translate bitsOf_def;
val r = translate padOK_def;
val r = translate optSeq_def;
val r = translate chunksOf_def;
val r = translate kindOf_def;
val r = translate signOf_def;
val r = translate extOf_def;
val r = translate bowtieOf_def;
val r = translate bernMagic_def;
val r = translate sectionOK_def;
val r = translate stepsToPath_def;
val r = translate rootShapeOK_def;
val r = translate verified_string_def;
val r = translate reject_string_def;

val r = translate byteAt_def;
val r = translate subBytes_def;
val r = translate leAt_def;
val r = translate rdU8I_def;
val r = translate takeNI_def;
val r = translate rdLEI_def;
val r = translate rdRatI_def;

val rdrati_side = Q.prove(
  ‘∀s lim i. rdrati_side s lim i’,
  rw[fetch "-" "rdrati_side_def"]
  \\ imp_res_tac leN_lt
  \\ gvs[]) |> update_precondition;

val r = translate rdBitsetI_def;
val r = translate rdRatsNI_def;
val r = translate rdBitsetsNI_def;
val r = translate rdCellsNI_def;
val r = translate rdLEsNI_def;

val r = translate parseHeaderI_def;
val r = translate parseSymRecI_def;
val r = translate parseSymtabI_def;
val r = translate parseComplexI_def;
val r = translate parseComplexesNI_def;
val r = translate parseDiagramI_def;

val r = translate pobjAbs_def;
val r = translate lookTermI_def;
val r = translate lookSimplexI_def;
val r = translate lookExtSetI_def;
val r = translate lookFormulaI_def;
val r = translate lookJudgI_def;
val r = translate parsePoolRecI_def;
val r = translate poolPassI_def;

val r = translate wireTy_def;
val r = translate bshapeJoin_def;
val r = translate termBshape_def;
val r = translate finWiresB_def;
val r = translate wirePosB_def;
val r = translate wiresPosB_def;
val r = translate (premiseContainsB_def
                   |> SIMP_RULE std_ss [ml_translatorTheory.MEMBER_INTRO]);
val r = translate polyTieB_def;

val r = translate lookNodeI_def;
val r = translate lookNodesI_def;
val r = translate (parseNodeI_def
                   |> PURE_REWRITE_RULE [ml_translatorTheory.MEMBER_INTRO]);
val r = translate nodePassI_def;

val r = translate parseProofSectionI_def;
val r = translate checkTopI_def;
val r = translate qtsl_verdict_strI_def;

val _ = PolyML.fullGC ();
