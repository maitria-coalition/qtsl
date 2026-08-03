(*
  The certificate-checker main program: certificate bytes on stdin,
  verdict on stdout, with the standard stdin-consuming CF specification
  (certmain_spec). Extends the banked translation theory
  (qtslCertProg); the whole-program spec and semantics theorem follow
  in the successor stages.
*)
Theory qtslCertFullProg
Ancestors
  basis_ffi qtsl_cert qtslCertProg
Libs
  preamble basis

val _ = translation_extends "qtslCertProg";

Quote add_cakeml:
  fun certmain u =
    case TextIO.foldChars consstep [] None of
      Some rcs => TextIO.print (qtsl_verdict_rev rcs)
    | None => TextIO.print (qtsl_verdict_rev [])
End

val st = get_ml_prog_state ()

Theorem certmain_spec:
  stdin_content fs = SOME text ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "certmain" st)
      [Conv NONE []]
      (STDIO fs)
      (POSTv uv. &UNIT_TYPE () uv *
                 STDIO (add_stdout (fastForwardFD fs 0) (qtsl_verdict text)))
Proof
  strip_tac
  \\ xcf "certmain" st
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ assume_tac (fetch "qtslCertProg" "consstep_v_thm")
  \\ xlet ‘POSTv retv.
             STDIO (fastForwardFD fs 0) *
             &OPTION_TYPE (LIST_TYPE CHAR)
               (SOME (mllist$foldl consStep [] text)) retv’
  THEN1 (xapp_spec (GEN_ALL foldChars_NONE) \\ xsimpl
         \\ simp[ml_translatorTheory.LIST_TYPE_def,
                 std_preludeTheory.OPTION_TYPE_def])
  \\ gvs[std_preludeTheory.OPTION_TYPE_def]
  \\ xmatch
  \\ xlet_auto THEN1 xsimpl
  \\ xapp
  \\ xsimpl
  \\ gvs[qtsl_verdict_rev_def, foldl_consStep]
QED

val _ = PolyML.fullGC ();
