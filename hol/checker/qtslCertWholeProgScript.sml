(*
  The whole-program theorem for the certificate checker: the program
  definition and its semantics theorem (qtsl_cert_semantics), evaluated
  from the smallest possible loaded base.
*)
Theory qtslCertWholeProg
Ancestors
  basis_ffi qtsl_cert qtslCertWPSpec
Libs
  preamble basis

val _ = translation_extends "qtslCertWPSpec";

val st = get_ml_prog_state ()

val _ = PolyML.fullGC ();

val spec = certmain_whole_prog_spec |> UNDISCH_ALL
val name = "certmain";

val (call_thm_qtsl_cert, qtsl_cert_prog_tm) = whole_prog_thm st name spec;

Definition qtsl_cert_prog_def:
  qtsl_cert_prog = ^qtsl_cert_prog_tm
End

Theorem qtsl_cert_semantics =
  call_thm_qtsl_cert |> ONCE_REWRITE_RULE[GSYM qtsl_cert_prog_def]
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]

val _ = PolyML.fullGC ();
