(*
  Compile the diagnostic binary (UNVERIFIED instrument; see
  qtslCertDiagScript.sml). Same in-logic compiler; no proofs consumed.
*)
Theory qtslCertDiagCompile
Ancestors
  qtslCertDiag
Libs
  preamble eval_cake_compile_arm8Lib

Theorem qtsl_diag_compiled =
  eval_cake_compile_arm8 "" qtsl_diag_prog_def "qtsl_diag_arm8.S";
