(*
  Family F2 (AndE): checkFam_ande and famEq_ande. The mass family of
  real certificate corpora, owning the derived-concludes path (elided
  nodes resolved via the lowest-offset-canonical judgement index), the
  escape/demotion path, and the derived pref-field path.
*)
Theory qtsl_fam_ande
Ancestors
  rat integer mlstring mllist qtsl_dyadic qtsl_qarith qtsl_catalogue
  qtsl_cert qtsl_cols qtsl_wf
Libs
  preamble

Definition checkFam_ande_def:
  checkFam_ande (cols:columns) (ct:ctx) (i:num) ⇔
    case tagOf cols i of
    | NONE => F
    | SOME (r, v) =>
        r = 4 ∧
        (case childOrd ct i 0 of
         | NONE => F
         | SOME k =>
           case conclRef cols ct i of
           | NONE => F
           | SOME cj =>
           case conclRef cols ct k of
           | NONE => F
           | SOME ccj =>
           case pv cols ct cj of
           | SOME (PJudg prew postw) =>
             (case pv cols ct ccj of
              | SOME (PJudg cprew cpostw) =>
                (case prefField cols ct i 0 of
                 | NONE => F
                 | SOME ot =>
                   case pv cols ct ot of
                   | SOME (PFormula otw) =>

                       expandSph FTt prew = expandSph FTt cprew ∧

                       expandSph FTt cpostw =
                         (if v = 0 then
                            FAnd (expandSph FTt postw) (expandSph FTt otw)
                          else
                            FAnd (expandSph FTt otw) (expandSph FTt postw))
                   | _ => F)
              | _ => F)
           | _ => F)
End

Definition checkPf1_ande_arm_def:
  checkPf1_ande_arm (ws:tensortype list) (sq:sequent) (nd:cnode) ⇔
    case nd of
    | CnAndEL p other =>
        (let ps = certConcl p in
           sq.pre = ps.pre ∧ ps.post = FAnd sq.post other)
    | CnAndER p other =>
        (let ps = certConcl p in
           sq.pre = ps.pre ∧ ps.post = FAnd other sq.post)
    | _ => F
End

Theorem checkPf1_ande_factor:
  (checkPf1 ws (INL (CertPf sq (CnAndEL p ow))) ⇔
     checkPf1 ws (INL p) ∧ checkPf1_ande_arm ws sq (CnAndEL p ow)) ∧
  (checkPf1 ws (INL (CertPf sq (CnAndER p ow))) ⇔
     checkPf1 ws (INL p) ∧ checkPf1_ande_arm ws sq (CnAndER p ow))
Proof
  conj_tac >> simp[Once checkPf1_def, checkPf1_ande_arm_def]
QED

Theorem expandSph_sph_tt_collapse:
  expandSph FTt FwSpH = expandSph FTt FwTt ∧ FwSpH ≠ FwTt
Proof
  simp[expandSph_def]
QED

Theorem pvEq_refl_fastpath:
  pv cols ct r = SOME x ⇒ pvEq cols ct r r = SOME T
Proof
  rw[pvEq_def]
QED

Theorem pvEq_T_values_eq:
  pvEq cols ct r1 r2 = SOME T ∧
  pv cols ct r1 = SOME a ∧ pv cols ct r2 = SOME b ⇒ a = b
Proof
  rw[pvEq_def] >> gvs[AllCaseEqs()]
QED

Theorem pvEq_T_expandEq:
  pvEq cols ct r1 r2 = SOME T ∧
  pv cols ct r1 = SOME (PFormula a) ∧ pv cols ct r2 = SOME (PFormula b) ⇒
  expandSph FTt a = expandSph FTt b
Proof
  strip_tac
  >> ‘PFormula a = PFormula b’ by metis_tac[pvEq_T_values_eq]
  >> gvs[]
QED

Theorem expandSph_noSph_11:
  ∀fw1 fw2 sp. fwNoSph fw1 ∧ fwNoSph fw2 ∧
               expandSph sp fw1 = expandSph sp fw2 ⇒ fw1 = fw2
Proof
  Induct >> rpt gen_tac >> Cases_on ‘fw2’
  >> simp[expandSph_def, fwNoSph_def]
  >> metis_tac[]
QED

Theorem expandSph_inj_noSph:
  ∀a b sp. fwNoSph a ∧ fwNoSph b ⇒
           (expandSph sp a = expandSph sp b ⇔ a = b)
Proof
  metis_tac[expandSph_noSph_11]
QED

Theorem nodeReconF_concl:
  ∀cols ct f i pf.
    nodeReconF cols ct f i = SOME pf ⇒
    ∃cj prew postw.
      conclRef cols ct i = SOME cj ∧
      pv cols ct cj = SOME (PJudg prew postw) ∧
      certConcl pf = judgSeq FTt prew postw
Proof
  rpt gen_tac >> Cases_on ‘f’ >> simp[nodeReconF_def]
  >> strip_tac >> gvs[AllCaseEqs(), certConcl_def] >> metis_tac[]
QED

Theorem famEq_ande:
  ∀cols ct i sq nd ws.
    wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
    nodeCorr cols ct i (CertPf sq nd) ∧
    FST (THE (tagOf cols i)) ∈ {4} ⇒
    (checkFam_ande cols ct i ⇔ checkPf1_ande_arm ws sq nd)
Proof
  rw[nodeCorr_def]
  >> Cases_on ‘tagOf cols i’ >- gvs[Once nodeReconF_def]
  >> rename [‘tagOf cols i = SOME rv’] >> Cases_on ‘rv’ >> gvs[]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> drule nodeReconF_concl >> strip_tac
  >> simp[checkFam_ande_def, checkPf1_ande_arm_def, certConcl_def,
          judgSeq_def]
QED

Theorem oEL_lt:
  ∀l i x. oEL i l = SOME x ⇒ i < LENGTH l
Proof
  rpt gen_tac >> simp[listTheory.oEL_THM]
  >> IF_CASES_TAC >> simp[]
QED

Theorem getD_EL:
  ∀l i d. i < LENGTH l ⇒ getD l i d = EL i l
Proof
  Induct >> simp[]
  >> rpt gen_tac >> Cases_on ‘i’ >> rw[getD_def]
QED

Theorem oEL_getD:
  ∀l i x d. oEL i l = SOME x ⇒ getD l i d = x
Proof
  rw[listTheory.oEL_THM, AllCaseEqs()] >> simp[getD_EL]
QED

Theorem rangeL_1:
  rangeL 1 = [0]
Proof
  EVAL_TAC
QED

Theorem mkCtx_nodeTag_length:
  mkCtx cols = SOME ct ⇒ LENGTH cols.nodeTag = cols.nNodes
Proof
  rw[mkCtx_def] >> gvs[AllCaseEqs()]
QED

Theorem nodeArityAt_ande:
  tagOf cols i = SOME (4, v) ⇒ nodeArityAt cols i = 1
Proof
  rw[tagOf_def, AllCaseEqs()]
  >> drule oEL_getD >> disch_then (qspec_then ‘999’ assume_tac)
  >> simp[nodeArityAt_def, ruleOfD_def, tagDecD_def, hasArityR_def,
          ruleArity_def]
QED

Theorem childOrd0_lt_ande:
  mkCtx cols = SOME ct ∧ wf8 cols ct ∧
  tagOf cols i = SOME (4, v) ∧ childOrd ct i 0 = SOME k ⇒
  k < i
Proof
  strip_tac
  >> ‘nodeArityAt cols i = 1’ by metis_tac[nodeArityAt_ande]
  >> ‘i < LENGTH cols.nodeTag’
       by (gvs[tagOf_def, AllCaseEqs()] >> metis_tac[oEL_lt])
  >> ‘LENGTH cols.nodeTag = cols.nNodes’ by metis_tac[mkCtx_nodeTag_length]
  >> ‘wf8node cols ct i’
       by gvs[wf8_def, listTheory.EVERY_MEM, MEM_rangeL]
  >> gvs[wf8node_def, rangeL_1, AllCaseEqs()]
QED

Theorem nodeCorr_ande_inv:
  nodeCorr cols ct i (CertPf sq nd) ∧ tagOf cols i = SOME (4, v) ⇒
  ∃k p ow.
    childOrd ct i 0 = SOME k ∧
    nodeReconF cols ct i k = SOME p ∧
    (nd = CnAndEL p ow ∨ nd = CnAndER p ow)
Proof
  rw[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> Cases_on ‘v = 0’ >> gvs[] >> metis_tac[]
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

Theorem famTot_ande:
  checkFam_ande cols ct i ∧
  childOrd ct i 0 = SOME k ∧
  nodeReconF cols ct i k = SOME p ⇒
  ∃pf. nodeCorr cols ct i pf
Proof
  rw[]

  >> qpat_x_assum ‘checkFam_ande _ _ _’ mp_tac
  >> simp[checkFam_ande_def]
  >> every_case_tac >> simp[]
  >> strip_tac >> gvs[]
  >> simp[nodeCorr_def, Once nodeReconF_def]
QED

Theorem famSlice_ande:
  ∀cols ct i sq nd ws.
    wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
    nodeCorr cols ct i (CertPf sq nd) ∧
    FST (THE (tagOf cols i)) ∈ {4} ⇒
    ∃k p.
      childOrd ct i 0 = SOME k ∧ k < i ∧
      nodeReconF cols ct i k = SOME p ∧
      (∀p'. nodeCorr cols ct k p' ⇒ p' = p) ∧
      (checkPf1 ws (INL (CertPf sq nd)) ⇔
         checkFam_ande cols ct i ∧ checkPf1 ws (INL p))
Proof
  rpt gen_tac >> strip_tac
  >> ‘∃v. tagOf cols i = SOME (4, v)’ by (
       Cases_on ‘tagOf cols i’
       >- gvs[nodeCorr_def, Once nodeReconF_def]
       >> rename [‘tagOf cols i = SOME rv’] >> Cases_on ‘rv’ >> gvs[])
  >> pop_assum strip_assume_tac
  >> drule_all famEq_ande
  >> disch_then (qspec_then ‘ws’ assume_tac)
  >> drule_all nodeCorr_ande_inv >> strip_tac

  >> (rename [‘childOrd ct i 0 = SOME k’]
      >> rename [‘nodeReconF cols ct i k = SOME p’]
      >> ‘wf8 cols ct’ by gvs[wfColumns_def]
      >> drule_all childOrd0_lt_ande >> strip_tac
      >> qexists_tac ‘k’ >> qexists_tac ‘p’
      >> gvs[]
      >> conj_tac
      >- (rpt strip_tac >> drule_all nodeReconF_nodeCorr_agree >> simp[])
      >> simp[checkPf1_ande_factor]
      >> metis_tac[checkPf1_ande_factor])
QED
