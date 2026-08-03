(*
  Family F3 (context OrE): checkFam_ore and famEq_ore, plus the
  path/conjunction helper surface the residual family's Promise arm
  reuses (the one inter-family dependency, acyclic). Includes the
  connecting lemma showing the reference checker's OrE case is child
  validity conjoined with the de-recursed arm.
*)
Theory qtsl_fam_ore
Ancestors
  rat integer mlstring mllist qtsl_dyadic qtsl_qarith qtsl_catalogue
  qtsl_cert qtsl_cols qtsl_wf
Libs
  preamble

Definition nodeSq_def:
  nodeSq (cols:columns) (ct:ctx) (i:num) : sequent option =
    case conclRef cols ct i of
    | NONE => NONE
    | SOME cj =>
      case pv cols ct cj of
      | SOME (PJudg prew postw) => SOME (judgSeq FTt prew postw)
      | _ => NONE
End

Definition pathArgs_def:
  pathArgs (cols:columns) (ct:ctx) (i:num) : (conjpath # num list) option =
    case pathOf cols ct i of
    | NONE => NONE
    | SOME (stps, ifc) => SOME (stepsToPath stps, ifc)
End

Definition conjGetSteps_def:
  conjGetSteps (fm:formula) ([]:num list) = SOME fm ∧
  conjGetSteps fm (s::ss) =
    case fm of
    | FAnd l r => conjGetSteps (if s = 0 then l else r) ss
    | _ => NONE
Termination
  WF_REL_TAC ‘measure (LENGTH o SND)’ >> rw[]
End

Definition conjReplaceSteps_def:
  conjReplaceSteps (fm:formula) ([]:num list) (g:formula) = SOME g ∧
  conjReplaceSteps fm (s::ss) g =
    case fm of
    | FAnd l r =>
        (if s = (0:num) then
           (case conjReplaceSteps l ss g of
            | NONE => NONE
            | SOME l' => SOME (FAnd l' r))
         else
           (case conjReplaceSteps r ss g of
            | NONE => NONE
            | SOME r' => SOME (FAnd l r')))
    | _ => NONE
Termination
  WF_REL_TAC ‘measure (LENGTH o FST o SND)’ >> rw[]
End

Theorem conjGetSteps_thm:
  ∀stps fm. conjGetSteps fm stps = conjGet fm (stepsToPath stps)
Proof
  Induct
  >- simp[conjGetSteps_def, stepsToPath_def, conjGet_def]
  >> rpt gen_tac
  >> simp[conjGetSteps_def, stepsToPath_def]
  >> Cases_on ‘fm’ >> rw[conjGet_def]
QED

Theorem conjReplaceSteps_thm:
  ∀stps fm g. conjReplaceSteps fm stps g = conjReplace fm (stepsToPath stps) g
Proof
  Induct
  >- simp[conjReplaceSteps_def, stepsToPath_def, conjReplace_def]
  >> rpt gen_tac
  >> simp[conjReplaceSteps_def, stepsToPath_def]
  >> Cases_on ‘fm’ >> rw[conjReplace_def]
QED

Definition checkFam_ore_def:
  checkFam_ore (cols:columns) (ct:ctx) (i:num) ⇔
    case nodeSq cols ct i of
    | NONE => F
    | SOME sq =>
      case childOrd ct i 0 of
      | NONE => F
      | SOME kl =>
        case childOrd ct i 1 of
        | NONE => F
        | SOME kr =>
          case nodeSq cols ct kl of
          | NONE => F
          | SOME ls =>
            case nodeSq cols ct kr of
            | NONE => F
            | SOME rs =>
              case pathArgs cols ct i of
              | NONE => F
              | SOME (path, ifc) =>
                case conjGet sq.pre path of
                | SOME (FOr d1 d2) =>
                    (conjReplace sq.pre path d1 = SOME ls.pre ∧
                     conjReplace sq.pre path d2 = SOME rs.pre ∧
                     ls.post = sq.post ∧ rs.post = sq.post)
                | _ => F
End

Definition oreArm_def:
  oreArm (ws:tensortype list) (sq:sequent) (nd:cnode) ⇔
    case nd of
    | CnOrE lp rp path =>
        (let ls = certConcl lp in
         let rs = certConcl rp in
           case conjGet sq.pre path of
           | SOME (FOr d1 d2) =>
               (conjReplace sq.pre path d1 = SOME ls.pre ∧
                conjReplace sq.pre path d2 = SOME rs.pre ∧
                ls.post = sq.post ∧ rs.post = sq.post)
           | _ => F)
    | _ => F
End

Theorem checkPf1_orE_arm:
  ∀ws sq lp rp path.
    checkPf1 ws (INL (CertPf sq (CnOrE lp rp path))) ⇔
    (checkPf1 ws (INL lp) ∧ checkPf1 ws (INL rp) ∧
     oreArm ws sq (CnOrE lp rp path))
Proof
  rw[Once checkPf1_def, oreArm_def] >> metis_tac[]
QED

Theorem nodeReconF_concl:
  ∀f cols ct i pf.
    nodeReconF cols ct f i = SOME pf ⇒
    nodeSq cols ct i = SOME (certConcl pf)
Proof
  Cases >- simp[nodeReconF_def]
  >> rpt gen_tac
  >> simp[nodeReconF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[nodeSq_def, certConcl_def]
QED

Theorem nodeCorr_concl:
  ∀cols ct i pf.
    nodeCorr cols ct i pf ⇒ nodeSq cols ct i = SOME (certConcl pf)
Proof
  rw[nodeCorr_def] >> metis_tac[nodeReconF_concl]
QED

Theorem famEq_ore:
  ∀cols ct i sq nd ws.
    wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
    nodeCorr cols ct i (CertPf sq nd) ∧
    FST (THE (tagOf cols i)) ∈ {6:num} ⇒
    (checkFam_ore cols ct i ⇔ oreArm ws sq nd)
Proof
  rpt gen_tac >> strip_tac
  >> gvs[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> Cases_on ‘tagOf cols i’ >> gvs[]
  >> rename [‘tagOf cols i = SOME rv’] >> Cases_on ‘rv’ >> gvs[]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[]
  >> ‘nodeSq cols ct i = SOME (judgSeq FTt prew postw)’
       by simp[nodeSq_def]
  >> imp_res_tac nodeReconF_concl
  >> simp[checkFam_ore_def, oreArm_def, pathArgs_def]
QED

Theorem nodeCorr_ore_inv:
  ∀cols ct i sq nd.
    nodeCorr cols ct i (CertPf sq nd) ∧
    FST (THE (tagOf cols i)) ∈ {6:num} ⇒
    ∃kl kr lp rp stps ifc.
      nd = CnOrE lp rp (stepsToPath stps) ∧
      childOrd ct i 0 = SOME kl ∧ childOrd ct i 1 = SOME kr ∧
      nodeReconF cols ct i kl = SOME lp ∧
      nodeReconF cols ct i kr = SOME rp ∧
      pathOf cols ct i = SOME (stps, ifc) ∧
      pathArgs cols ct i = SOME (stepsToPath stps, ifc) ∧
      nodeSq cols ct i = SOME sq ∧
      nodeSq cols ct kl = SOME (certConcl lp) ∧
      nodeSq cols ct kr = SOME (certConcl rp)
Proof
  rpt gen_tac >> strip_tac
  >> gvs[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> Cases_on ‘tagOf cols i’ >> gvs[]
  >> rename [‘tagOf cols i = SOME rv’] >> Cases_on ‘rv’ >> gvs[]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[]

  >> imp_res_tac nodeReconF_concl
  >> simp[nodeSq_def, pathArgs_def]
QED

Theorem checkFam_ore_elim:
  ∀cols ct i.
    checkFam_ore cols ct i ⇒
    ∃sq kl kr ls rs path ifc d1 d2.
      nodeSq cols ct i = SOME sq ∧
      childOrd ct i 0 = SOME kl ∧ childOrd ct i 1 = SOME kr ∧
      nodeSq cols ct kl = SOME ls ∧ nodeSq cols ct kr = SOME rs ∧
      pathArgs cols ct i = SOME (path, ifc) ∧
      conjGet sq.pre path = SOME (FOr d1 d2) ∧
      conjReplace sq.pre path d1 = SOME ls.pre ∧
      conjReplace sq.pre path d2 = SOME rs.pre ∧
      ls.post = sq.post ∧ rs.post = sq.post
Proof
  rpt gen_tac >> strip_tac
  >> gvs[checkFam_ore_def]
  >> every_case_tac >> gvs[]
QED

Theorem famEq_ore_slice:
  ∀cols ct i sq nd ws.
    wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
    nodeCorr cols ct i (CertPf sq nd) ∧
    FST (THE (tagOf cols i)) ∈ {6:num} ⇒
    ∃lp rp path.
      nd = CnOrE lp rp path ∧
      (checkPf1 ws (INL (CertPf sq nd)) ⇔
       checkPf1 ws (INL lp) ∧ checkPf1 ws (INL rp) ∧
       checkFam_ore cols ct i)
Proof
  rpt gen_tac >> strip_tac
  >> drule_all nodeCorr_ore_inv >> strip_tac
  >> gvs[]

  >> ‘checkFam_ore cols ct i ⇔ oreArm ws sq (CnOrE lp rp (stepsToPath stps))’
       by (irule famEq_ore >> simp[])
  >> simp[checkPf1_orE_arm]
QED

Definition oreDemoImg_def:
  oreDemoImg : num list =
    bernMagic ++ u32le 1 ++ u32le 0 ++
    u64le 128 ++ u64le 0 ++
    u64le 128 ++ u64le 0 ++
    u64le 128 ++ u64le 8 ++
    u64le 136 ++ u64le 100 ++
    u32le 0 ++ u32le 0 ++
    u32le 3 ++ u32le 0 ++
    u64le 71 ++
    u32le 4294967295 ++
    REPLICATE 20 0 ++
    u32le 0 ++ u32le 0
End

Definition oreDemoCols_def:
  oreDemoCols : columns =
    <| hdrImage := oreDemoImg ; topoMode := 0 ; denDefault := 731 ;
       nNodes := 3 ; nPool := 7 ; blockSize := 0 ;
       nodeTag := [0; 0; 6] ; nodeArity := [] ; nodeTopo := [] ;
       nodeConcl := [29; 29; 38] ; nodePref := [] ; nodeScal := [] ;
       nodeDen := [] ; nodePath := [([0], [])] ; nodeRat := [] ;
       nodeEsc := [] ; nodeEsc2 := [] ;

       poolTag := [36; 38; 35; 34; 34; 48; 48] ;
       poolRef := [0; 0; 2; 1; 0; 1; 20; 0; 11; 0] ;
       poolNumLen := [] ; poolDenId := [] ; poolDenDict := [] ;
       poolNum := [] ; poolMisc := [] |>
End

Theorem oreDemo_mkCtx:
  IS_SOME (mkCtx oreDemoCols)
Proof
  EVAL_TAC
QED

Theorem oreDemo_wfColumns:
  wfColumns oreDemoCols (THE (mkCtx oreDemoCols))
Proof
  EVAL_TAC
QED

Theorem oreDemo_nodeCorr:
  nodeCorr oreDemoCols (THE (mkCtx oreDemoCols)) 2
    (CertPf <| pre := FAnd (FOr FTt FTt) FTt ; post := FTt |>
       (CnOrE (CertPf <| pre := FAnd FTt FTt ; post := FTt |> CnAx)
              (CertPf <| pre := FAnd FTt FTt ; post := FTt |> CnAx)
              (CPLeft CPHere)))
Proof
  EVAL_TAC
QED

Theorem oreDemo_check:
  checkFam_ore oreDemoCols (THE (mkCtx oreDemoCols)) 2
Proof
  EVAL_TAC
QED

Theorem oreDemo_arm:
  oreArm [] <| pre := FAnd (FOr FTt FTt) FTt ; post := FTt |>
    (CnOrE (CertPf <| pre := FAnd FTt FTt ; post := FTt |> CnAx)
           (CertPf <| pre := FAnd FTt FTt ; post := FTt |> CnAx)
           (CPLeft CPHere))
Proof
  EVAL_TAC
QED

Theorem oreDemo_mut_path:
  ¬ checkFam_ore (oreDemoCols with nodePath := [([1], [])])
      (THE (mkCtx (oreDemoCols with nodePath := [([1], [])]))) 2
Proof
  EVAL_TAC
QED

Theorem oreDemo_mut_concl:
  ¬ checkFam_ore (oreDemoCols with nodeConcl := [29; 29; 29])
      (THE (mkCtx (oreDemoCols with nodeConcl := [29; 29; 29]))) 2
Proof
  EVAL_TAC
QED

Theorem oreDemo_slice:
  checkPf1 [] (INL (CertPf <| pre := FAnd (FOr FTt FTt) FTt ; post := FTt |>
       (CnOrE (CertPf <| pre := FAnd FTt FTt ; post := FTt |> CnAx)
              (CertPf <| pre := FAnd FTt FTt ; post := FTt |> CnAx)
              (CPLeft CPHere)))) ⇔
  (checkPf1 [] (INL (CertPf <| pre := FAnd FTt FTt ; post := FTt |> CnAx)) ∧
   checkPf1 [] (INL (CertPf <| pre := FAnd FTt FTt ; post := FTt |> CnAx)) ∧
   checkFam_ore oreDemoCols (THE (mkCtx oreDemoCols)) 2)
Proof
  EVAL_TAC
QED
