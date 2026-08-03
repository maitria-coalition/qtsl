(*
  Compile the performance certificate checker to ARM8 by in-logic
  evaluation (eval_cake_compile_arm8).
*)
Theory qtslCertPerfCompileARM8
Ancestors
  qtslCertPerfWholeProg
Libs
  preamble eval_cake_compile_arm8Lib

Theorem qtsl_cert_perf_compiled =
  eval_cake_compile_arm8 "" qtsl_cert_perf_prog_def "qtsl_cert_perf_arm8.S";
