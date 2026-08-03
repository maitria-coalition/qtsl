(*
  Compile the certificate checker (bytes on stdin, verdict on stdout)
  to ARM8 by in-logic evaluation (eval_cake_compile_arm8).
*)
Theory qtslCertCompileARM8
Ancestors
  qtslCertWholeProg
Libs
  preamble eval_cake_compile_arm8Lib

Theorem qtsl_cert_compiled =
  eval_cake_compile_arm8 "" qtsl_cert_prog_def "qtsl_cert_arm8.S";
