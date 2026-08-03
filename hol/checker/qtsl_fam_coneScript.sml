(*
  Family F4 (ConvIntro/ConvElim/BernCone, tags 8/9/11):
  checkFam_conv and checkFam_berncone with equivalence lemmas famEq_conv
  and famEq_berncone. Per-node work is a constant number of gathers
  plus bounded materialization and the banked leaf checks.
*)
Theory qtsl_fam_cone
Ancestors
  rat integer mlstring mllist qtsl_dyadic qtsl_qarith qtsl_catalogue
  qtsl_cert qtsl_cols qtsl_wf
Libs
  preamble

Definition checkFam_conv_def:
  checkFam_conv (cols:columns) (ct:ctx) (i:num) ⇔
    case tagOf cols i of
    | NONE => F
    | SOME (r, v) =>
      if ¬(r = 8 ∨ r = 9) then F else
      case conclRef cols ct i of
      | NONE => F
      | SOME cj =>
      case pv cols ct cj of
      | SOME (PJudg prew postw) =>
        (let sq = judgSeq FTt prew postw in
         case childOrd ct i 0 of
         | NONE => F
         | SOME k =>
         case conclRef cols ct k of
         | NONE => F
         | SOME ck =>
         case pv cols ct ck of
         | SOME (PJudg cprew cpostw) =>
           (let ps = judgSeq FTt cprew cpostw in
            case prefField cols ct i 0 of
            | NONE => F
            | SOME rt =>
            case prefField cols ct i 1 of
            | NONE => F
            | SOME rs =>
            case prefField cols ct i 2 of
            | NONE => F
            | SOME re =>
            case pv cols ct rt of
            | SOME (PTerm tt) =>
              (case pv cols ct rs of
               | SOME (PSimplex sx) =>
                 (case pv cols ct re of
                  | SOME (PExtSet es) =>
                      (sq.pre = ps.pre ∧
                       (if r = 8 then
                          termBshape ct.ws tt = SOME [sx.complex.ambDim] ∧
                          barycentricHalfspaceBuild tt sx es = SOME ps.post ∧
                          sq.post = FInRegion tt sx es
                        else
                          ps.post = FInRegion tt sx es ∧
                          barycentricHalfspaceBuild tt sx es = SOME sq.post))
                  | _ => F)
               | _ => F)
            | _ => F)
         | _ => F)
      | _ => F
End

Definition checkFam_berncone_def:
  checkFam_berncone (cols:columns) (ct:ctx) (i:num) ⇔
    case tagOf cols i of
    | NONE => F
    | SOME (r, v) =>
      if r ≠ 11 then F else
      case conclRef cols ct i of
      | NONE => F
      | SOME cj =>
      case pv cols ct cj of
      | SOME (PJudg prew postw) =>
        (let sq = judgSeq FTt prew postw in
         case childOrd ct i 0 of
         | NONE => F
         | SOME k =>
         case conclRef cols ct k of
         | NONE => F
         | SOME ck =>
         case pv cols ct ck of
         | SOME (PJudg cprew cpostw) =>
           (let ps = judgSeq FTt cprew cpostw in
            case prefField cols ct i 0 of
            | NONE => F
            | SOME rx =>
            case prefField cols ct i 1 of
            | NONE => F
            | SOME rs =>
            case prefField cols ct i 2 of
            | NONE => F
            | SOME re =>
            case prefField cols ct i 3 of
            | NONE => F
            | SOME rp0 =>
            case prefField cols ct i 4 of
            | NONE => F
            | SOME rd =>
            case scalField cols ct i 0 of
            | NONE => F
            | SOME deg =>
            case pv cols ct rx of
            | SOME (PTerm tX) =>
              (case pv cols ct rs of
               | SOME (PSimplex sx) =>
                 (case pv cols ct re of
                  | SOME (PExtSet es) =>
                    (case pv cols ct rp0 of
                     | SOME (PTerm poly) =>
                       (case pv cols ct rd of
                        | SOME (PFormula pdw) =>
                            (let pred = expandSph FTt pdw in
                               sq.pre = ps.pre ∧
                               ps.post = FInRegion tX sx es ∧
                               polyTieB tX poly ∧
                               (if extIsEmptyB es then isConvexPredicateB pred
                                else isConicPredicateB pred) ∧
                               bernConeCoeffCheck sx es deg poly pred ∧
                               sq.post = formulaSubst predicateHole poly pred)
                        | _ => F)
                     | _ => F)
                  | _ => F)
               | _ => F)
            | _ => F)
         | _ => F)
      | _ => F
End

Definition convArm_def:
  convArm (ws:tensortype list) (sq:sequent) (nd:cnode) ⇔
    case nd of
    | CnConvIntro p t sx es =>
        (let ps = certConcl p in
           sq.pre = ps.pre ∧
           termBshape ws t = SOME [sx.complex.ambDim] ∧
           barycentricHalfspaceBuild t sx es = SOME ps.post ∧
           sq.post = FInRegion t sx es)
    | CnConvElim p t sx es =>
        (let ps = certConcl p in
           sq.pre = ps.pre ∧
           ps.post = FInRegion t sx es ∧
           barycentricHalfspaceBuild t sx es = SOME sq.post)
    | _ => F
End

Definition bernConeArm_def:
  bernConeArm (sq:sequent) (nd:cnode) ⇔
    case nd of
    | CnBernCone p tX sx es deg poly pred =>
        (let ps = certConcl p in
           sq.pre = ps.pre ∧
           ps.post = FInRegion tX sx es ∧
           polyTieB tX poly ∧
           (if extIsEmptyB es then isConvexPredicateB pred
            else isConicPredicateB pred) ∧
           bernConeCoeffCheck sx es deg poly pred ∧
           sq.post = formulaSubst predicateHole poly pred)
    | _ => F
End

Theorem checkPf1_convIntro_recompose:
  checkPf1 ws (INL (CertPf sq (CnConvIntro p t sx es))) ⇔
  checkPf1 ws (INL p) ∧ convArm ws sq (CnConvIntro p t sx es)
Proof
  simp[Once checkPf1_def, convArm_def]
QED

Theorem checkPf1_convElim_recompose:
  checkPf1 ws (INL (CertPf sq (CnConvElim p t sx es))) ⇔
  checkPf1 ws (INL p) ∧ convArm ws sq (CnConvElim p t sx es)
Proof
  simp[Once checkPf1_def, convArm_def]
QED

Theorem checkPf1_bernCone_recompose:
  checkPf1 ws (INL (CertPf sq (CnBernCone p tX sx es deg poly pred))) ⇔
  checkPf1 ws (INL p) ∧ bernConeArm sq (CnBernCone p tX sx es deg poly pred)
Proof
  simp[Once checkPf1_def, bernConeArm_def]
QED

Triviality takeN_SOME:
  takeN n xs = SOME p ⇔ n ≤ LENGTH xs ∧ p = (TAKE n xs, DROP n xs)
Proof
  rw[takeN_def] >> metis_tac[]
QED

Triviality rdLE_SOME:
  rdLE k xs = SOME p ⇔ k ≤ LENGTH xs ∧ p = (leN (TAKE k xs), DROP k xs)
Proof
  rw[rdLE_def, takeN_SOME, AllCaseEqs()] >> metis_tac[]
QED

Triviality TAKE_le_prefix:
  ∀xs ys k. TAKE 128 xs = TAKE 128 ys ∧ k ≤ 128 ⇒ TAKE k xs = TAKE k ys
Proof
  rpt strip_tac
  >> ‘MIN k 128 = k’ by (rw[arithmeticTheory.MIN_DEF] >> decide_tac)
  >> metis_tac[listTheory.TAKE_TAKE_MIN]
QED

Triviality TAKE_DROP_within:
  ∀xs ys m n.
    TAKE 128 xs = TAKE 128 ys ∧ m + n ≤ 128 ⇒
    TAKE n (DROP m xs) = TAKE n (DROP m ys)
Proof
  rw[listTheory.TAKE_DROP_SWAP]
  >> ‘TAKE (m + n) xs = TAKE (m + n) ys’
       by (irule TAKE_le_prefix >> simp[])
  >> simp[]
QED

Triviality parseHeader_SOME_fields:
  ∀bytes h.
    parseHeader bytes = SOME h ⇒
    h = <| symOff := leN (TAKE 8 (DROP 16 bytes)) ;
           symLen := leN (TAKE 8 (DROP 24 bytes)) ;
           payOff := leN (TAKE 8 (DROP 32 bytes)) ;
           payLen := leN (TAKE 8 (DROP 40 bytes)) ;
           diaOff := leN (TAKE 8 (DROP 48 bytes)) ;
           diaLen := leN (TAKE 8 (DROP 56 bytes)) ;
           prfOff := leN (TAKE 8 (DROP 64 bytes)) ;
           prfLen := leN (TAKE 8 (DROP 72 bytes)) ;
           nWires := leN (TAKE 4 (DROP 80 bytes)) ;
           nApps  := leN (TAKE 4 (DROP 84 bytes)) ;
           nNodes := leN (TAKE 4 (DROP 88 bytes)) ;
           nCxs   := leN (TAKE 4 (DROP 92 bytes)) ;
           rootOff := leN (TAKE 8 (DROP 96 bytes)) ;
           thetaRef := leN (TAKE 4 (DROP 104 bytes)) |>
Proof
  rpt gen_tac
  >> simp[parseHeader_def, AllCaseEqs(), takeN_SOME, rdLE_SOME,
          rich_listTheory.DROP_DROP_T]
  >> strip_tac >> gvs[]
QED

Theorem parseHeader_TAKE128:
  ∀xs ys h1 h2.
    TAKE 128 xs = TAKE 128 ys ∧
    parseHeader xs = SOME h1 ∧ parseHeader ys = SOME h2 ⇒
    h1 = h2
Proof
  rpt gen_tac >> strip_tac
  >> ‘∀m n. m + n ≤ 128 ⇒ TAKE n (DROP m xs) = TAKE n (DROP m ys)’
       by metis_tac[TAKE_DROP_within]
  >> imp_res_tac parseHeader_SOME_fields
  >> gvs[]
QED

Triviality parseHeader_prfOff_lb:
  parseHeader bytes = SOME h ⇒ 128 ≤ h.prfOff
Proof
  rw[parseHeader_def] >> gvs[AllCaseEqs(), sectionOK_def]
QED

Triviality mkCtx_hdr_ws:
  mkCtx cols = SOME ct ⇒
    parseHeader (cols.hdrImage ++ REPLICATE (peekPrfLen cols.hdrImage) 0)
      = SOME ct.hdr ∧
    parseSymtab (TAKE ct.hdr.symLen (DROP ct.hdr.symOff cols.hdrImage))
                ct.hdr.symLen ct.hdr.nWires ct.hdr.payOff ct.hdr.payLen
      = SOME ct.ws
Proof
  rw[mkCtx_def] >> gvs[AllCaseEqs()]
QED

Theorem parseCert_ws_eq:
  ∀cols ct rest ws pf.
    mkCtx cols = SOME ct ∧ wfColumns cols ct ∧
    parseCert (cols.hdrImage ++ rest) = SOME (ws, pf) ⇒
    ws = ct.ws
Proof
  rpt gen_tac >> strip_tac
  >> drule mkCtx_hdr_ws >> strip_tac
  >> ‘128 ≤ ct.hdr.prfOff’ by metis_tac[parseHeader_prfOff_lb]
  >> ‘LENGTH cols.hdrImage = ct.hdr.prfOff ∧
      ct.hdr.symOff + ct.hdr.symLen ≤ ct.hdr.prfOff’
       by gvs[wfColumns_def, wf1_def]
  >> ‘TAKE 128 (cols.hdrImage ++ rest) =
      TAKE 128 (cols.hdrImage ++ REPLICATE (peekPrfLen cols.hdrImage) 0)’
       by simp[listTheory.TAKE_APPEND1]
  >> ‘∀h1. parseHeader (cols.hdrImage ++ rest) = SOME h1 ⇒ h1 = ct.hdr’
       by metis_tac[parseHeader_TAKE128]
  >> ‘DROP ct.hdr.symOff (cols.hdrImage ++ rest) =
      DROP ct.hdr.symOff cols.hdrImage ++ rest’
       by simp[listTheory.DROP_APPEND1]
  >> ‘TAKE ct.hdr.symLen (DROP ct.hdr.symOff cols.hdrImage ++ rest) =
      TAKE ct.hdr.symLen (DROP ct.hdr.symOff cols.hdrImage)’
       by simp[listTheory.TAKE_APPEND1, listTheory.LENGTH_DROP]
  >> gvs[parseCert_def, AllCaseEqs()]
QED

Theorem nodeReconF_concl:
  ∀f cols ct i p.
    nodeReconF cols ct f i = SOME p ⇒
    ∃cj prew postw nd0.
      conclRef cols ct i = SOME cj ∧
      pv cols ct cj = SOME (PJudg prew postw) ∧
      p = CertPf (judgSeq FTt prew postw) nd0
Proof
  Cases_on ‘f’ >- simp[nodeReconF_def]
  >> rpt gen_tac
  >> simp[Once nodeReconF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[]
QED

Theorem famEq_conv:
  ∀cols ct rest ws pf i sq nd.
    wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
    parseCert (cols.hdrImage ++ rest) = SOME (ws, pf) ∧
    nodeCorr cols ct i (CertPf sq nd) ∧
    FST (THE (tagOf cols i)) ∈ {8; 9} ⇒
    (checkFam_conv cols ct i ⇔ convArm ws sq nd)
Proof
  rpt gen_tac >> strip_tac
  >> ‘ws = ct.ws’ by metis_tac[parseCert_ws_eq]
  >> gvs[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = _’ mp_tac
  >> Cases_on ‘tagOf cols i’ >> simp[Once nodeReconF_def]
  >> rename [‘tagOf cols i = SOME rv’] >> PairCases_on ‘rv’
  >> gvs[]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[]
  >> drule nodeReconF_concl >> strip_tac >> gvs[]
  >> simp[checkFam_conv_def, convArm_def, certConcl_def]
QED

Theorem famEq_berncone:
  ∀cols ct rest ws pf i sq nd.
    wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
    parseCert (cols.hdrImage ++ rest) = SOME (ws, pf) ∧
    nodeCorr cols ct i (CertPf sq nd) ∧
    FST (THE (tagOf cols i)) ∈ {11} ⇒
    (checkFam_berncone cols ct i ⇔ bernConeArm sq nd)
Proof
  rpt gen_tac >> strip_tac
  >> gvs[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = _’ mp_tac
  >> Cases_on ‘tagOf cols i’ >> simp[Once nodeReconF_def]
  >> rename [‘tagOf cols i = SOME rv’] >> PairCases_on ‘rv’
  >> gvs[]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[]
  >> drule nodeReconF_concl >> strip_tac >> gvs[]
  >> simp[checkFam_berncone_def, bernConeArm_def, certConcl_def]
QED

Theorem oEL_lt:
  ∀l i x. oEL i l = SOME x ⇒ i < LENGTH l
Proof
  Induct >> Cases_on ‘i’ >> rw[listTheory.oEL_def] >> res_tac >> simp[]
QED

Theorem oEL_getD:
  ∀l i x d. oEL i l = SOME x ⇒ getD l i d = x
Proof
  Induct >> Cases_on ‘i’ >> rw[listTheory.oEL_def, getD_def] >> res_tac >> simp[]
QED

Theorem mkCtx_nodeTag_length:
  mkCtx cols = SOME ct ⇒ LENGTH cols.nodeTag = cols.nNodes
Proof
  rw[mkCtx_def] >> gvs[AllCaseEqs()]
QED

Theorem nodeReconF_nodeCorr_agree:
  nodeReconF cols ct f k = SOME p ∧ nodeCorr cols ct k p' ∧ k < f ⇒
  p' = p
Proof
  rw[nodeCorr_def]
  >> ‘SUC k ≤ f’ by decide_tac
  >> ‘nodeReconF cols ct f k = SOME p'’ by metis_tac[nodeReconF_fuel_mono]
  >> gvs[]
QED

Theorem nodeArityAt_f4:
  tagOf cols i = SOME (r, v) ∧ (r = 8 ∨ r = 9 ∨ r = 11) ⇒
  nodeArityAt cols i = 1
Proof
  rw[tagOf_def, AllCaseEqs()]
  >> drule oEL_getD >> disch_then (qspec_then ‘999’ assume_tac)
  >> gvs[nodeArityAt_def, ruleOfD_def, tagDecD_def, hasArityR_def,
         ruleArity_def, tagDec_def, AllCaseEqs()]
QED

Theorem childOrd0_lt_f4:
  mkCtx cols = SOME ct ∧ wf8 cols ct ∧
  tagOf cols i = SOME (r, v) ∧ (r = 8 ∨ r = 9 ∨ r = 11) ∧
  childOrd ct i 0 = SOME k ⇒
  k < i
Proof
  strip_tac
  >> ‘nodeArityAt cols i = 1’ by metis_tac[nodeArityAt_f4]
  >> ‘i < LENGTH cols.nodeTag’
       by (gvs[tagOf_def, AllCaseEqs()] >> metis_tac[oEL_lt])
  >> ‘LENGTH cols.nodeTag = cols.nNodes’ by metis_tac[mkCtx_nodeTag_length]
  >> ‘wf8node cols ct i’
       by gvs[wf8_def, listTheory.EVERY_MEM, MEM_rangeL]
  >> gvs[wf8node_def, EVAL “rangeL 1”, AllCaseEqs()]
QED

Theorem nodeCorr_convIntro_inv:
  nodeCorr cols ct i (CertPf sq nd) ∧ tagOf cols i = SOME (8, v) ⇒
  ∃p t sx es k.
    nd = CnConvIntro p t sx es ∧
    childOrd ct i 0 = SOME k ∧
    nodeReconF cols ct i k = SOME p
Proof
  rw[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> metis_tac[]
QED

Theorem nodeCorr_convElim_inv:
  nodeCorr cols ct i (CertPf sq nd) ∧ tagOf cols i = SOME (9, v) ⇒
  ∃p t sx es k.
    nd = CnConvElim p t sx es ∧
    childOrd ct i 0 = SOME k ∧
    nodeReconF cols ct i k = SOME p
Proof
  rw[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> metis_tac[]
QED

Theorem nodeCorr_berncone_inv:
  nodeCorr cols ct i (CertPf sq nd) ∧ tagOf cols i = SOME (11, v) ⇒
  ∃p tX sx es deg poly pred k.
    nd = CnBernCone p tX sx es deg poly pred ∧
    childOrd ct i 0 = SOME k ∧
    nodeReconF cols ct i k = SOME p
Proof
  rw[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> metis_tac[]
QED

Theorem famEq_conv_core:
  ∀cols ct i sq nd.
    nodeCorr cols ct i (CertPf sq nd) ∧
    FST (THE (tagOf cols i)) ∈ {8; 9} ⇒
    (checkFam_conv cols ct i ⇔ convArm ct.ws sq nd)
Proof
  rpt gen_tac >> strip_tac
  >> gvs[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = _’ mp_tac
  >> Cases_on ‘tagOf cols i’ >> simp[Once nodeReconF_def]
  >> rename [‘tagOf cols i = SOME rv’] >> PairCases_on ‘rv’
  >> gvs[]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[]
  >> drule nodeReconF_concl >> strip_tac >> gvs[]
  >> simp[checkFam_conv_def, convArm_def, certConcl_def]
QED

Theorem famEq_berncone_core:
  ∀cols ct i sq nd.
    nodeCorr cols ct i (CertPf sq nd) ∧
    FST (THE (tagOf cols i)) ∈ {11} ⇒
    (checkFam_berncone cols ct i ⇔ bernConeArm sq nd)
Proof
  rpt gen_tac >> strip_tac
  >> gvs[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = _’ mp_tac
  >> Cases_on ‘tagOf cols i’ >> simp[Once nodeReconF_def]
  >> rename [‘tagOf cols i = SOME rv’] >> PairCases_on ‘rv’
  >> gvs[]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[]
  >> drule nodeReconF_concl >> strip_tac >> gvs[]
  >> simp[checkFam_berncone_def, bernConeArm_def, certConcl_def]
QED

Theorem famTot_conv:
  checkFam_conv cols ct i ∧
  childOrd ct i 0 = SOME k ∧
  nodeReconF cols ct i k = SOME p ⇒
  ∃pf. nodeCorr cols ct i pf
Proof
  strip_tac
  >> qpat_x_assum ‘checkFam_conv cols ct i’ mp_tac
  >> simp[checkFam_conv_def]
  >> rpt (TOP_CASE_TAC >> simp[])
  >> strip_tac
  >> gvs[]
  >> simp[nodeCorr_def, Once nodeReconF_def]
QED

Theorem famTot_berncone:
  checkFam_berncone cols ct i ∧
  childOrd ct i 0 = SOME k ∧
  nodeReconF cols ct i k = SOME p ⇒
  ∃pf. nodeCorr cols ct i pf
Proof
  strip_tac
  >> qpat_x_assum ‘checkFam_berncone cols ct i’ mp_tac
  >> simp[checkFam_berncone_def]
  >> rpt (TOP_CASE_TAC >> simp[])
  >> strip_tac
  >> gvs[]
  >> simp[nodeCorr_def, Once nodeReconF_def]
QED

Theorem famSlice_convIntro:
  ∀cols ct i sq nd.
    wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
    nodeCorr cols ct i (CertPf sq nd) ∧
    FST (THE (tagOf cols i)) ∈ {8:num} ⇒
    ∃k p t sx es.
      nd = CnConvIntro p t sx es ∧
      childOrd ct i 0 = SOME k ∧ k < i ∧
      nodeReconF cols ct i k = SOME p ∧
      (∀p'. nodeCorr cols ct k p' ⇒ p' = p) ∧
      (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
         checkPf1 ct.ws (INL p) ∧ checkFam_conv cols ct i)
Proof
  rpt gen_tac >> strip_tac
  >> ‘∃v. tagOf cols i = SOME (8, v)’ by (
       Cases_on ‘tagOf cols i’
       >- gvs[nodeCorr_def, Once nodeReconF_def]
       >> rename [‘tagOf cols i = SOME rv’] >> Cases_on ‘rv’ >> gvs[])
  >> pop_assum strip_assume_tac
  >> ‘checkFam_conv cols ct i ⇔ convArm ct.ws sq nd’
       by (irule famEq_conv_core >> simp[])
  >> drule_all nodeCorr_convIntro_inv >> strip_tac
  >> rename [‘nd = CnConvIntro p t sx es’, ‘childOrd ct i 0 = SOME k’]
  >> ‘k < i’ by (‘wf8 cols ct’ by gvs[wfColumns_def]
                 >> metis_tac[childOrd0_lt_f4])
  >> qexistsl_tac [‘k’, ‘p’, ‘t’, ‘sx’, ‘es’]
  >> simp[]
  >> metis_tac[checkPf1_convIntro_recompose, nodeReconF_nodeCorr_agree]
QED

Theorem famSlice_convElim:
  ∀cols ct i sq nd ws.
    wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
    nodeCorr cols ct i (CertPf sq nd) ∧
    FST (THE (tagOf cols i)) ∈ {9:num} ⇒
    ∃k p t sx es.
      nd = CnConvElim p t sx es ∧
      childOrd ct i 0 = SOME k ∧ k < i ∧
      nodeReconF cols ct i k = SOME p ∧
      (∀p'. nodeCorr cols ct k p' ⇒ p' = p) ∧
      (checkPf1 ws (INL (CertPf sq nd)) ⇔
         checkPf1 ws (INL p) ∧ checkFam_conv cols ct i)
Proof
  rpt gen_tac >> strip_tac
  >> ‘∃v. tagOf cols i = SOME (9, v)’ by (
       Cases_on ‘tagOf cols i’
       >- gvs[nodeCorr_def, Once nodeReconF_def]
       >> rename [‘tagOf cols i = SOME rv’] >> Cases_on ‘rv’ >> gvs[])
  >> pop_assum strip_assume_tac
  >> ‘checkFam_conv cols ct i ⇔ convArm ct.ws sq nd’
       by (irule famEq_conv_core >> simp[])
  >> drule_all nodeCorr_convElim_inv >> strip_tac
  >> rename [‘nd = CnConvElim p t sx es’, ‘childOrd ct i 0 = SOME k’]
  >> ‘k < i’ by (‘wf8 cols ct’ by gvs[wfColumns_def]
                 >> metis_tac[childOrd0_lt_f4])
  >> ‘∀ws2. convArm ws2 sq (CnConvElim p t sx es) ⇔
            convArm ct.ws sq (CnConvElim p t sx es)’ by simp[convArm_def]
  >> qexistsl_tac [‘k’, ‘p’, ‘t’, ‘sx’, ‘es’]
  >> simp[]
  >> metis_tac[checkPf1_convElim_recompose, nodeReconF_nodeCorr_agree]
QED

Theorem famSlice_berncone:
  ∀cols ct i sq nd ws.
    wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
    nodeCorr cols ct i (CertPf sq nd) ∧
    FST (THE (tagOf cols i)) ∈ {11:num} ⇒
    ∃k p tX sx es deg poly pred.
      nd = CnBernCone p tX sx es deg poly pred ∧
      childOrd ct i 0 = SOME k ∧ k < i ∧
      nodeReconF cols ct i k = SOME p ∧
      (∀p'. nodeCorr cols ct k p' ⇒ p' = p) ∧
      (checkPf1 ws (INL (CertPf sq nd)) ⇔
         checkPf1 ws (INL p) ∧ checkFam_berncone cols ct i)
Proof
  rpt gen_tac >> strip_tac
  >> ‘∃v. tagOf cols i = SOME (11, v)’ by (
       Cases_on ‘tagOf cols i’
       >- gvs[nodeCorr_def, Once nodeReconF_def]
       >> rename [‘tagOf cols i = SOME rv’] >> Cases_on ‘rv’ >> gvs[])
  >> pop_assum strip_assume_tac
  >> ‘checkFam_berncone cols ct i ⇔ bernConeArm sq nd’
       by (irule famEq_berncone_core >> simp[])
  >> drule_all nodeCorr_berncone_inv >> strip_tac
  >> rename [‘nd = CnBernCone p tX sx es deg poly pred’,
             ‘childOrd ct i 0 = SOME k’]
  >> ‘k < i’ by (‘wf8 cols ct’ by gvs[wfColumns_def]
                 >> metis_tac[childOrd0_lt_f4])
  >> qexistsl_tac [‘k’, ‘p’, ‘tX’, ‘sx’, ‘es’, ‘deg’, ‘poly’, ‘pred’]
  >> simp[]
  >> metis_tac[checkPf1_bernCone_recompose, nodeReconF_nodeCorr_agree]
QED
