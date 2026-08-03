(*
  Compile the receipt-table program to ARM8 by in-logic evaluation
  (eval_cake_compile_arm8).
*)
Theory qtslToyCompileARM8
Ancestors
  qtslToyProg
Libs
  preamble eval_cake_compile_arm8Lib

Theorem qtsl_toy_compiled =
  eval_cake_compile_arm8 "" qtsl_toy_prog_def "qtsl_toy_arm8.S";
