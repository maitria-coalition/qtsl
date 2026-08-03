(*
  Demo and mutant battery for the geolog-to-columns transcode: a
  hand-built two-node certificate instance carried as geolog object
  rows, pushed through the bind chain, the roster-aware sealed check
  and certOfRows, with the emitted columns ACCEPTED by the frozen
  well-formedness predicate via EVAL. Each mutant violates one
  conformance point and must refuse with its named class and tag.
*)
Theory geolog_certDemo

Ancestors
  arithmetic list rich_list option pair rat
  geolog_read geolog_bind blake3 geolog_cert
  qtsl_cert qtsl_cols qtsl_wf

Definition chidA_def:
  chidA : num list = REPLICATE 32 1
End

Definition chidB_def:
  chidB : num list = REPLICATE 32 2
End

Definition demoPins_def:
  demoPins : ((num list # num) # vocab) list =
    [((chidA, 0), VsProof);
     ((chidA, 1), VsTerm);
     ((chidA, 2), VsFormula);
     ((chidA, 3), VsJudgment);
     ((chidA, 4), VsCtxPath);
     ((chidA, 10), VfProofConcludes);
     ((chidA, 11), VfJudgPre);
     ((chidA, 12), VfJudgPost);
     ((chidA, 20), VfFAnd);
     ((chidA, 21), VfFTrue);
     ((chidA, 22), VfFFalse);
     ((chidA, 23), VfFSpH);
     ((chidA, 30), VsRule 0);
     ((chidA, 31), VfRuleProof 0);
     ((chidA, 32), VsRule 4);
     ((chidA, 33), VfRuleProof 4);
     ((chidA, 34), VfRF 4 0);
     ((chidA, 35), VfRF 4 1);
     ((chidA, 36), VfRF 4 2);
     ((chidA, 40), VfOOF "PrimApp/index");
     ((chidB, 0), VsCert);
     ((chidB, 1), VfCertRoot);
     ((chidB, 2), VfCertTheta);
     ((chidB, 3), VfCertNWires);
     ((chidB, 4), VfCertNApps);
     ((chidB, 5), VfCertNComplexes)]
End

Definition nat0_def:
  nat0 : gvalue = GVLit 2 [0]
End

Definition demoOps_def:
  demoOps : gop list =
    [GElta (ERExt 1 0);
     GElta (ERExt 0 0);
     GElta (ERExt 0 30);
     GElta (ERExt 0 3);
     GElta (ERExt 0 2);
     GElta (ERExt 0 2);
     GElta (ERExt 0 2);
     GElta (ERExt 0 2);
     GElta (ERExt 0 2);
     GElta (ERExt 0 0);
     GElta (ERExt 0 32);
     GElta (ERExt 0 3);

     GFuna (ERExt 1 1) [GVRef (ERLocal 0)] (GVRef (ERLocal 9));
     GFuna (ERExt 1 3) [GVRef (ERLocal 0)] nat0;
     GFuna (ERExt 1 4) [GVRef (ERLocal 0)] nat0;
     GFuna (ERExt 1 5) [GVRef (ERLocal 0)] nat0;

     GFuna (ERExt 0 21) [] (GVRef (ERLocal 5));
     GFuna (ERExt 0 23) [] (GVRef (ERLocal 6));
     GFuna (ERExt 0 22) [] (GVRef (ERLocal 8));
     GFuna (ERExt 0 20) [GVRef (ERLocal 5); GVRef (ERLocal 6)]
           (GVRef (ERLocal 4));
     GFuna (ERExt 0 20) [GVRef (ERLocal 5); GVRef (ERLocal 8)]
           (GVRef (ERLocal 7));

     GFuna (ERExt 0 11) [GVRef (ERLocal 3)] (GVRef (ERLocal 4));
     GFuna (ERExt 0 12) [GVRef (ERLocal 3)] (GVRef (ERLocal 7));
     GFuna (ERExt 0 11) [GVRef (ERLocal 11)] (GVRef (ERLocal 4));
     GFuna (ERExt 0 12) [GVRef (ERLocal 11)] (GVRef (ERLocal 5));

     GFuna (ERExt 0 10) [GVRef (ERLocal 1)] (GVRef (ERLocal 3));
     GFuna (ERExt 0 31) [GVRef (ERLocal 2)] (GVRef (ERLocal 1));

     GFuna (ERExt 0 10) [GVRef (ERLocal 9)] (GVRef (ERLocal 11));
     GFuna (ERExt 0 33) [GVRef (ERLocal 10)] (GVRef (ERLocal 9));
     GFuna (ERExt 0 34) [GVRef (ERLocal 10)] (GVRef (ERLocal 1));
     GFuna (ERExt 0 35) [GVRef (ERLocal 10)] nat0;
     GFuna (ERExt 0 36) [GVRef (ERLocal 10)] (GVRef (ERLocal 8))]
End

Definition demoSkelBytes_def:
  demoSkelBytes : num list = REPLICATE 92 0
End

Definition demoCommit_def:
  demoCommit : gcommit =
    <| sigBytes := REPLICATE 64 0 ;
       skelBytes := demoSkelBytes ;
       cskel := <| author := REPLICATE 32 0 ;
                   deps := [chidA; chidB] ;
                   parentCount := 0 ;
                   tsClaim := 0 ;
                   message := NONE ;
                   bodyHash := blake3 [] |> ;
       bodyBytes := [] ;
       cbody := <| ops := demoOps ; zoneRuns := [] |> |>
End

Definition demoG_def:
  demoG : geolog =
    <| prereqs := [<| pflag := 1 ; pchid := chidA ; prosterId := SOME 0 |>;
                   <| pflag := 1 ; pchid := chidB ; prosterId := SOME 1 |>] ;
       commits := [demoCommit] |>
End

Theorem demo_bind:
  ?b. bindChain demoG = BindOk b /\ b.btip = blake3 demoSkelBytes
Proof
  EVAL_TAC >> simp[] >> metis_tac[]
QED

Theorem demo_sealed_roster:
  !b. bindChain demoG = BindOk b ==>
      sealedBindCheckR demoPins demoG b = NONE
Proof
  rpt strip_tac
  >> qpat_x_assum `_ = BindOk b` mp_tac
  >> CONV_TAC (LAND_CONV EVAL)
  >> strip_tac >> gvs[]
  >> EVAL_TAC
QED

Definition demoCols_def:
  demoCols : columns =
    case certOfRows demoPins demoG of
    | COk cols => cols
    | CErr c t w => ARB
End

Theorem demo_transcode:
  certOfRows demoPins demoG = COk demoCols
Proof
  EVAL_TAC
QED

Theorem demo_mkCtx:
  IS_SOME (mkCtx demoCols)
Proof
  EVAL_TAC >> simp[] >> metis_tac[]
QED

Theorem demo_escapes:
  demoCols.nodeEsc = [1] /\ demoCols.nodeEsc2 = [1] /\
  demoCols.nNodes = 2 /\ LENGTH demoCols.nodeConcl = 2
Proof
  EVAL_TAC >> simp[] >> metis_tac[]
QED

Theorem demo_wfColumns:
  wfColumns demoCols (THE (mkCtx demoCols))
Proof
  EVAL_TAC >> simp[] >> metis_tac[]
QED

Definition errCT_def:
  errCT (r:cres) : rclass # string =
    case r of
    | CErr c t w => (c, t)
    | COk cols => (CUnread, "ACCEPTED")
End

Definition demoGWith_def:
  demoGWith (ops:gop list) : geolog =
    demoG with commits :=
      [demoCommit with cbody := <| ops := ops ; zoneRuns := [] |>]
End

Theorem demo_mut_unpinned:
  errCT (certOfRows demoPins
        (demoGWith (demoOps ++ [GFuna (ERExt 0 99) [] (GVRef (ERLocal 5))])))
  = (CUnsupp, "schema_fun_unpinned")
Proof
  EVAL_TAC
QED

Theorem demo_mut_ambiguous_ctor:
  errCT (certOfRows demoPins
        (demoGWith (demoOps ++
           [GFuna (ERExt 0 20) [GVRef (ERLocal 5); GVRef (ERLocal 5)]
                  (GVRef (ERLocal 4))])))
  = (CUnread, "ambiguous_constructor")
Proof
  EVAL_TAC
QED

Theorem demo_mut_dup_field:
  errCT (certOfRows demoPins
        (demoGWith (demoOps ++
           [GFuna (ERExt 0 12) [GVRef (ERLocal 11)] (GVRef (ERLocal 8))])))
  = (CUnread, "duplicate_fun_row")
Proof
  EVAL_TAC
QED

Theorem demo_mut_eltd:
  errCT (certOfRows demoPins
        (demoGWith (demoOps ++ [GEltd (ERLocal 5)])))
  = (CUnsupp, "eltd_in_cert_body")
Proof
  EVAL_TAC
QED

Theorem demo_mut_app_row:
  errCT (certOfRows demoPins
        (demoGWith (demoOps ++ [GFuna (ERExt 0 40) [] nat0])))
  = (CUnsupp, "fun_outside_fragment")
Proof
  EVAL_TAC
QED

Definition demoOpsApps_def:
  demoOpsApps : gop list =
    TAKE 14 demoOps ++ [GFuna (ERExt 1 4) [GVRef (ERLocal 0)] (GVLit 2 [1])]
    ++ DROP 15 demoOps
End

Theorem demo_mut_napps:
  errCT (certOfRows demoPins (demoGWith demoOpsApps))
  = (CUnsupp, "apps_out_of_v0_fragment")
Proof
  EVAL_TAC
QED

Theorem demo_mut_two_certs:
  errCT (certOfRows demoPins
        (demoGWith (demoOps ++ [GElta (ERExt 1 0)])))
  = (CUnread, "cert_element")
Proof
  EVAL_TAC
QED

Definition demoOpsSph_def:
  demoOpsSph : gop list =
    TAKE 24 demoOps ++
    [GFuna (ERExt 0 12) [GVRef (ERLocal 11)] (GVRef (ERLocal 6))] ++
    DROP 25 demoOps
End

Theorem demo_mut_sph_post:
  errCT (certOfRows demoPins (demoGWith demoOpsSph))
  = (CUnread, "proof_tree")
Proof
  EVAL_TAC
QED

Definition demoOpsRoot_def:
  demoOpsRoot : gop list =
    TAKE 23 demoOps ++
    [GFuna (ERExt 0 11) [GVRef (ERLocal 11)] (GVRef (ERLocal 5))] ++
    DROP 24 demoOps
End

Theorem demo_mut_root_shape:
  errCT (certOfRows demoPins (demoGWith demoOpsRoot))
  = (CUnread, "root_shape")
Proof
  EVAL_TAC
QED

Definition demoB_def:
  demoB : bindinfo =
    case bindChain demoG of
    | BindOk b => b
    | BindErr c t w => ARB
End

Theorem demo_mut_prereq_flag0:
  OPTION_MAP FST
    (sealedBindCheckR demoPins
       (demoG with prereqs :=
          [<| pflag := 0 ; pchid := chidA ; prosterId := NONE |>;
           <| pflag := 1 ; pchid := chidB ; prosterId := SOME 1 |>])
       demoB)
  = SOME "prereq_content_assumed_held"
Proof
  EVAL_TAC
QED
