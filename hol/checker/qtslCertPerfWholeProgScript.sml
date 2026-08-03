(*
  The whole-program theorem for the performance checker
  (qtsl_cert_perf_semantics), evaluated from the smallest possible
  loaded base.
*)
Theory qtslCertPerfWholeProg
Ancestors
  basis_ffi qtsl_cert qtsl_certPerf qtslCertPerfWPSpec
Libs
  preamble basis

val _ = translation_extends "qtslCertPerfWPSpec";

val st = get_ml_prog_state ()

val _ = PolyML.fullGC ();

val spec = certmain_whole_prog_spec |> UNDISCH_ALL
val name = "certmain";

val (call_thm_qtsl_cert_perf, qtsl_cert_perf_prog_tm) =
  whole_prog_thm st name spec;

Definition qtsl_cert_perf_prog_def:
  qtsl_cert_perf_prog = ^qtsl_cert_perf_prog_tm
End

Theorem qtsl_cert_perf_semantics =
  call_thm_qtsl_cert_perf
  |> ONCE_REWRITE_RULE[GSYM qtsl_cert_perf_prog_def]
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]

val _ = PolyML.fullGC ();
