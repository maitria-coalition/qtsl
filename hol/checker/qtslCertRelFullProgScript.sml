(*
  The relational checker's main program: succinct certificate bytes
  on stdin read once, verdict on stdout (VERIFIED / REJECT /
  UNREADABLE). The CF specification is stated via the spec-side verdict
  function so downstream stages keep their statements verbatim.
*)
Theory qtslCertRelFullProg
Ancestors
  basis_ffi qtsl_cert qtsl_colread qtslCertRelProg
Libs
  preamble basis

val _ = translation_extends "qtslCertRelProg";

Quote add_cakeml:
  fun certmain u =
    TextIO.print (qtsl_rel_verdict_stri (TextIO.inputAll (TextIO.openStdIn ())))
End

val st = get_ml_prog_state ()

Theorem stdin_content_get_file_content[local]:
  stdin_content fs = SOME text ∧ STD_streams fs ∧ wfFS fs ⇒
  get_file_content fs 0 = SOME (text, 0) ∧ get_mode fs 0 = SOME ReadMode
Proof
  strip_tac
  \\ gvs[TextIOProofTheory.stdin_content_def, AllCaseEqs()]
  \\ simp[fsFFITheory.get_file_content_def,
          fsFFIPropsTheory.get_mode_def]
  \\ fs[fsFFIPropsTheory.wfFS_def]
  \\ imp_res_tac ALOOKUP_MEM
  \\ first_x_assum (qspec_then ‘0’ mp_tac)
  \\ simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD]
  \\ disch_then drule \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘ALOOKUP aa bb’
  \\ Cases_on ‘ALOOKUP aa bb’ \\ fs[Abbr‘aa’, Abbr‘bb’]
  \\ imp_res_tac ALOOKUP_FAILS \\ fs[]
QED

Theorem certmain_spec:
  stdin_content fs = SOME text ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "certmain" st)
      [Conv NONE []]
      (STDIO fs)
      (POSTv uv. &UNIT_TYPE () uv *
                 STDIO (add_stdout (fastForwardFD fs 0)
                          (qtsl_rel_verdict text)))
Proof
  strip_tac
  \\ xcf "certmain" st
  \\ reverse (Cases_on ‘STD_streams fs’)
  THEN1 (fs[TextIOProofTheory.STDIO_def] \\ xpull)
  \\ reverse (Cases_on ‘∃ll. wfFS (fs with numchars := ll)’)
  THEN1 (fs[TextIOProofTheory.STDIO_def, TextIOProofTheory.IOFS_def] \\ xpull)
  \\ pop_assum (qx_choose_then ‘ll’ assume_tac)
  \\ ‘get_file_content fs 0 = SOME (text, 0) ∧ get_mode fs 0 = SOME ReadMode’
       by (‘get_file_content (fs with numchars := ll) 0 = SOME (text, 0) ∧
            get_mode (fs with numchars := ll) 0 = SOME ReadMode’
             by (irule stdin_content_get_file_content
                 \\ fs[TextIOProofTheory.stdin_content_def,
                       GSYM fsFFIPropsTheory.STD_streams_numchars])
           \\ metis_tac[fsFFIPropsTheory.get_file_content_numchars,
                        fsFFIPropsTheory.get_mode_with_numchars])
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ xlet ‘POSTv is. STDIO fs * INSTREAM_BUFFERED_FD [] 0 is’
  THEN1 (xapp_spec TextIOProofTheory.openStdIn_STDIO_spec
         \\ qexistsl_tac [‘emp’, ‘fs’] \\ xsimpl)
  \\ xlet ‘POSTv sv. &STRING_TYPE (implode (DROP 0 text)) sv *
                     STDIO (fastForwardFD fs 0)’
  THEN1 (xapp_spec (GEN_ALL TextIOProofTheory.inputAll_spec)
         \\ first_assum (irule_at Any)
         \\ first_assum (irule_at Any)
         \\ qexists_tac ‘[]’
         \\ xsimpl)
  \\ xlet_auto THEN1 xsimpl
  \\ xapp
  \\ xsimpl
  \\ gvs[qtsl_rel_verdict_strI_correct]
QED

val _ = PolyML.fullGC ();
