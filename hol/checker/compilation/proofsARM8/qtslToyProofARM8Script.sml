(*
  The end-to-end machine-code theorem for the receipt-table program
  on ARM8: the program semantics theorem, the compiler correctness
  theorem and the in-logic compile theorem composed against the
  ASL-derived (official Arm specification) machine model.
*)
Theory qtslToyProofARM8
Ancestors
  semanticsProps backendProof arm8_asl_configProof TextIOProof
  qtsl_dyadic qtsl_qarith qtslToyProg qtslToyCompileARM8
Libs
  preamble

val qtsl_toy_io_events_def = new_specification("qtsl_toy_io_events_def",
  ["qtsl_toy_io_events"],
  qtsl_toy_semantics |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (qtsl_toy_sem,qtsl_toy_output) =
  qtsl_toy_io_events_def |> SPEC_ALL |> UNDISCH
  |> SIMP_RULE std_ss [GSYM PULL_EXISTS] |> CONJ_PAIR

val (qtsl_toy_not_fail,qtsl_toy_sem_sing) = qtsl_toy_sem
  |> SRULE [qtsl_toy_compiled,ml_progTheory.prog_syntax_ok_semantics]
  |> MATCH_MP semantics_prog_Terminate_not_Fail |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct (cj 1 qtsl_toy_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,
                         GSYM AND_IMP_INTRO]
  |> C MATCH_MP qtsl_toy_not_fail
  |> C MATCH_MP arm8_configProofTheory.arm8_backend_config_ok
  |> REWRITE_RULE[qtsl_toy_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH arm8_asl_machine_config_ok)
                     (UNDISCH arm8_asl_init_ok))
  |> DISCH(#1(dest_imp(concl arm8_asl_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

Theorem qtsl_toy_compiled_thm =
  CONJ compile_correct_applied qtsl_toy_output |> DISCH_ALL

Definition installed_arm8_asl_def:
  installed_arm8_asl ((code, data, cfg) :
      (word8 list # word64 list # backend$config))
    mc ms
  <=>
    ?cbspace data_sp.
      is_arm8_asl_machine_config mc /\
      installed
        code cbspace
        data data_sp
        cfg.lab_conf.ffi_names
        (heap_regs arm8_backend_config.stack_conf.reg_names) mc
        cfg.lab_conf.shmem_extra ms
End

Definition qtsl_toy_code_def:
  qtsl_toy_code = (code, data, info)
End

Definition qtsl_toy_run_def:
  qtsl_toy_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧
  installed_arm8_asl qtsl_toy_code mc ms
End

Theorem machine_code_sound:
  qtsl_toy_run cl fs mc ms ⇒
  machine_sem mc (basis_ffi cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (qtsl_toy_io_events cl fs)} ∧
  extract_fs fs (qtsl_toy_io_events cl fs) =
    SOME (add_stdout fs full_output)
Proof
  strip_tac>>
  fs[installed_arm8_asl_def,qtsl_toy_code_def,qtsl_toy_run_def]>>
  drule qtsl_toy_compiled_thm>>
  simp[AND_IMP_INTRO]>>
  disch_then drule>>
  disch_then (qspecl_then [`ms`,`mc`,`data_sp`,`cbspace`] mp_tac)>>
  simp[]
QED
