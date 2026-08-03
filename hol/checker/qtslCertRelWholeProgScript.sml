(*
  The whole-program theorem for the relational checker
  (qtsl_cert_rel_semantics), evaluated from the smallest possible
  loaded base.
*)
Theory qtslCertRelWholeProg
Ancestors
  basis_ffi qtsl_cert qtsl_colread qtslCertRelWPSpec
Libs
  preamble basis

val _ = translation_extends "qtslCertRelWPSpec";

val st = get_ml_prog_state ()

val _ = PolyML.fullGC ();

val spec = certmain_whole_prog_spec |> UNDISCH_ALL
val name = "certmain";

val (call_thm_qtsl_cert_rel, qtsl_cert_rel_prog_tm) =
  whole_prog_thm st name spec;

Definition qtsl_cert_rel_prog_def:
  qtsl_cert_rel_prog = ^qtsl_cert_rel_prog_tm
End

Theorem qtsl_cert_rel_semantics =
  call_thm_qtsl_cert_rel
  |> ONCE_REWRITE_RULE[GSYM qtsl_cert_rel_prog_def]
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]

val _ = PolyML.fullGC ();
