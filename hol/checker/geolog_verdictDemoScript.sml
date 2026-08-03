(*
  Value-level demo of the composed verdict, both arms: an instance
  that REJECTS at checkJoins (a deliberately step-invalid leaf), and a
  valid variant carrying a genuinely step-valid two-node proof all the
  way to acceptance.
*)
Theory geolog_verdictDemo

Ancestors
  arithmetic list rich_list option pair rat
  geolog_read geolog_bind blake3 geolog_cert geolog_certDemo
  qtsl_cert qtsl_cols qtsl_wf qtsl_joins geolog_verdict

Definition validOps_def:
  validOps : gop list =
    TAKE 20 demoOps ++
    [GFuna (ERExt 0 20) [GVRef (ERLocal 5); GVRef (ERLocal 5)]
           (GVRef (ERLocal 7));
     GFuna (ERExt 0 11) [GVRef (ERLocal 3)] (GVRef (ERLocal 7))]

    ++ TAKE 9 (DROP 22 demoOps) ++
    [GFuna (ERExt 0 36) [GVRef (ERLocal 10)] (GVRef (ERLocal 5))]

End

Definition validG_def:
  validG : geolog = demoGWith validOps
End

Theorem valid_bind:
  ?b. bindChain validG = BindOk b /\ b.btip = blake3 demoSkelBytes
Proof
  EVAL_TAC >> simp[] >> metis_tac[]
QED

Theorem valid_sealed_roster:
  !b. bindChain validG = BindOk b ==>
      sealedBindCheckR demoPins validG b = NONE
Proof
  rpt strip_tac
  >> qpat_x_assum `_ = BindOk b` mp_tac
  >> CONV_TAC (LAND_CONV EVAL)
  >> strip_tac >> gvs[]
  >> EVAL_TAC
QED

Definition validCols_def:
  validCols : columns =
    case certOfRows demoPins validG of
    | COk cols => cols
    | CErr c t w => ARB
End

Theorem valid_transcode:
  certOfRows demoPins validG = COk validCols
Proof
  EVAL_TAC
QED

Theorem valid_checkJoins:
  checkJoins validCols = SOME T
Proof
  EVAL_TAC
QED

Theorem demoCols_checkJoins:
  checkJoins geolog_certDemo$demoCols = SOME F
Proof
  EVAL_TAC
QED
