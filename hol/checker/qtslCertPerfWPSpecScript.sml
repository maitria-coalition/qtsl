(*
  The whole-program specification for the performance checker, proved
  alone from the banked certmain_spec theory.
*)
Theory qtslCertPerfWPSpec
Ancestors
  basis_ffi qtsl_cert qtsl_certPerf qtslCertPerfFullProg
Libs
  preamble basis

val _ = translation_extends "qtslCertPerfFullProg";

val st = get_ml_prog_state ()

val _ = PolyML.fullGC ();

Theorem certmain_whole_prog_spec:
  IS_SOME (stdin_content fs) ⇒
  whole_prog_spec ^(fetch_v "certmain" st) cl fs NONE
    ((=) (add_stdout (fastForwardFD fs 0)
            (qtsl_verdict (THE (stdin_content fs)))))
Proof
  strip_tac
  \\ gvs[optionTheory.IS_SOME_EXISTS]
  \\ rw[whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac‘fs1 = _ with numchars := _’
  \\ qexists_tac‘fs1’
  \\ ‘fs.numchars = (fastForwardFD fs 0).numchars’
       by simp[fsFFIPropsTheory.fastForwardFD_numchars]

  \\ pop_assum SUBST_ALL_TAC
  \\ simp[Abbr‘fs1’, GSYM add_stdo_with_numchars, with_same_numchars]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe
       (UNDISCH (Q.INST [‘text’ |-> ‘x’] certmain_spec))))
  \\ xsimpl
QED

val _ = PolyML.fullGC ();
