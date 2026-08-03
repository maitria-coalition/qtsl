(*
  CakeML translation of the qtsl_cert parser and checker (translation
  only, no characteristic-formula proofs). The program, its CF spec and
  the whole-program spec live in the successor theories; the chain is
  staged so each expensive step banks its result to disk and restarts
  from a compact loaded theory.
*)
Theory qtslCertProg
Ancestors
  basis_ffi qtsl_dyadic qtsl_qarith qtsl_catalogue qtsl_cert qtslToyProg
Libs
  preamble basis

val _ = translation_extends "qtslToyProg";

val r = translate listTheory.oEL_def;
val r = translate alistTheory.ALOOKUP_def;
val r = translate listTheory.TAKE_def;
val r = translate listTheory.DROP_def;

val r = translate takeN_def;
val r = translate leN_def;
val r = translate rdU8_def;
val r = translate rdLE_def;
val r = translate denMinimal_def;
val r = translate numMinimal_def;
val r = translate egcd_def;
val r = translate rdRat_def;

val rdrat_side = Q.prove(
  ‘∀xs. rdrat_side xs’,
  rw[fetch "-" "rdrat_side_def"]
  \\ imp_res_tac leN_lt
  \\ gvs[]) |> update_precondition;
val r = translate byteBit_def;
val r = translate bitsOf_def;
val r = translate padOK_def;
val r = translate rdBitset_def;
val r = translate rdRatsN_def;
val r = translate rdBitsetsN_def;
val r = translate rdCellsN_def;
val r = translate rdLEsN_def;
val r = translate optSeq_def;
val r = translate chunksOf_def;

val r = translate kindOf_def;
val r = translate signOf_def;
val r = translate extOf_def;
val r = translate bowtieOf_def;
val r = translate bernMagic_def;
val r = translate sectionOK_def;
val r = translate parseHeader_def;

val r = translate parseSymRec_def;
val r = translate parseSymtab_def;
val r = translate parseComplex_def;
val r = translate parseComplexesN_def;
val r = translate parseDiagram_def;

val r = translate expandSph_def;
val r = translate fwNoSph_def;
val r = translate lookTerm_def;
val r = translate lookSimplex_def;
val r = translate lookExtSet_def;
val r = translate lookFormula_def;
val r = translate lookJudg_def;
val r = translate parsePoolRec_def;
val r = translate poolPass_def;

val r = translate certConcl_def;
val r = translate stepsToPath_def;
val r = translate judgSeq_def;
val r = translate lookNodePf_def;
val r = translate parseNode_def;
val r = translate nodePass_def;
val r = translate rootShapeOK_def;
val r = translate parseProofSection_def;
val r = translate parseCert_def;

val r = translate wireTy_def;
val r = translate bshapeJoin_def;
val r = translate termBshape_def;
val r = translate finWiresB_def;
val r = translate wirePosB_def;
val r = translate wiresPosB_def;
val r = translate ml_translatorTheory.MEMBER_def;
val r = translate (premiseContainsB_def
                   |> SIMP_RULE std_ss [ml_translatorTheory.MEMBER_INTRO]);
val r = translate polyTieB_def;
val r = translate (checkPf1_def
                   |> PURE_REWRITE_RULE [ml_translatorTheory.MEMBER_INTRO]);
val r = translate checkPf_def;

val r = translate qtslCheckBytes_def;
val r = translate verified_string_def;
val r = translate reject_string_def;
val r = translate qtsl_verdict_def;
val r = translate consStep_def;
val r = translate qtsl_verdict_rev_def;
