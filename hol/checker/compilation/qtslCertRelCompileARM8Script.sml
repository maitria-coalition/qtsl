(*
  Compile the relational certificate checker to ARM8 by in-logic
  evaluation (eval_cake_compile_arm8).
*)
Theory qtslCertRelCompileARM8
Ancestors
  qtslCertRelWholeProg
Libs
  preamble eval_cake_compile_arm8Lib

Theorem qtsl_cert_rel_compiled =
  eval_cake_compile_arm8 "" qtsl_cert_rel_prog_def "qtsl_cert_rel_arm8.S";
