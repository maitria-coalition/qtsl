(*
  The end-to-end machine-code theorem for the certificate checker on
  ARM8 (ASL-derived machine model), with the verdict string bound to
  the checker's acceptance: any standard run of the compiled bytes,
  with a certificate on stdin, terminates successfully, and its stdout
  is the VERIFIED string iff the bytes parse as a v0-fragment
  certificate whose every rule side condition re-checks.
*)
Theory qtslCertProofARM8
Ancestors
  semanticsProps backendProof arm8_asl_configProof TextIOProof
  qtsl_dyadic qtsl_qarith qtsl_catalogue qtsl_cert qtslCertWholeProg
  qtslCertCompileARM8
Libs
  preamble

val qtsl_cert_io_events_def = new_specification("qtsl_cert_io_events_def",
  ["qtsl_cert_io_events"],
  qtsl_cert_semantics |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (qtsl_cert_sem,qtsl_cert_output) =
  qtsl_cert_io_events_def |> SPEC_ALL |> UNDISCH
  |> SIMP_RULE std_ss [GSYM PULL_EXISTS] |> CONJ_PAIR

val (qtsl_cert_not_fail,qtsl_cert_sem_sing) = qtsl_cert_sem
  |> SRULE [qtsl_cert_compiled,ml_progTheory.prog_syntax_ok_semantics]
  |> MATCH_MP semantics_prog_Terminate_not_Fail |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct (cj 1 qtsl_cert_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,
                         GSYM AND_IMP_INTRO]
  |> C MATCH_MP qtsl_cert_not_fail
  |> C MATCH_MP arm8_configProofTheory.arm8_backend_config_ok
  |> REWRITE_RULE[qtsl_cert_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH arm8_asl_machine_config_ok)
                     (UNDISCH arm8_asl_init_ok))
  |> DISCH(#1(dest_imp(concl arm8_asl_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

Theorem qtsl_cert_compiled_thm =
  CONJ compile_correct_applied qtsl_cert_output |> DISCH_ALL

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

Definition qtsl_cert_code_def:
  qtsl_cert_code = (code, data, info)
End

Definition qtsl_cert_run_def:
  qtsl_cert_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ IS_SOME (stdin_content fs) ∧
  installed_arm8_asl qtsl_cert_code mc ms
End

Theorem machine_code_sound:
  qtsl_cert_run cl fs mc ms ⇒
  machine_sem mc (basis_ffi cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (qtsl_cert_io_events cl fs)} ∧
  extract_fs fs (qtsl_cert_io_events cl fs) =
    SOME (add_stdout (fastForwardFD fs 0)
            (qtsl_verdict (THE (stdin_content fs))))
Proof
  strip_tac>>
  fs[installed_arm8_asl_def,qtsl_cert_code_def,qtsl_cert_run_def]>>
  drule qtsl_cert_compiled_thm>>
  simp[AND_IMP_INTRO]>>
  disch_then drule>>
  disch_then (qspecl_then [`ms`,`mc`,`data_sp`,`cbspace`] mp_tac)>>
  simp[]
QED

Theorem machine_code_sound_verdict:
  qtsl_cert_run cl fs mc ms ⇒
  machine_sem mc (basis_ffi cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (qtsl_cert_io_events cl fs)} ∧
  ∃out.
    extract_fs fs (qtsl_cert_io_events cl fs) =
      SOME (add_stdout (fastForwardFD fs 0) out) ∧
    (out = verified_string ⇔
     ∃ws pf. parseCert (MAP ORD (THE (stdin_content fs))) = SOME (ws, pf) ∧
             checkPf ws pf)
Proof
  strip_tac
  \\ drule machine_code_sound
  \\ strip_tac
  \\ simp[]
  \\ qexists_tac‘qtsl_verdict (THE (stdin_content fs))’
  \\ simp[qtsl_verdict_verified, qtslCheckBytes_eq_parse]
QED
