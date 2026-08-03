(*
  Family F5 (Syzygy/Farkas, tags 26/14): checkFam_syz and
  checkFam_farkas with their equivalence lemmas, and the de-recursion
  witnesses proving each arm reassembles the reference checker's own
  case body.
*)
Theory qtsl_fam_syz
Ancestors
  rat integer mlstring mllist qtsl_dyadic qtsl_qarith qtsl_catalogue
  qtsl_cert qtsl_cols qtsl_wf
Libs
  preamble

Definition checkPf1Arm_farkas_def:
  checkPf1Arm_farkas (ws:tensortype list) (sq:sequent) (nd:cnode) ⇔
    case nd of
    | CnFarkas cc concl dbl =>
        IS_SOME (termBshape ws concl) ∧
        finWiresB ws concl ∧
        wiresPosB ws (formulaFreeWires sq.pre ++ termFreeWires concl) ∧
        farkasCheck cc sq.pre concl ∧
        sq.post = FAtom BowLe concl (TmConst 0)
    | _ => F
End

Definition checkPf1Arm_syz_def:
  checkPf1Arm_syz (ws:tensortype list) (sq:sequent) (nd:cnode) ⇔
    case nd of
    | CnSyzygy comps cc concl dbl thq =>
        (let cseqs = MAP certConcl comps in
           EVERY (λc. premiseContainsB sq.pre c.pre) cseqs ∧
           IS_SOME (termBshape ws concl) ∧
           finWiresB ws concl ∧
           wiresPosB ws (formulaFreeWires sq.pre ++ termFreeWires concl) ∧
           EVERY (λc. wiresPosB ws (formulaFreeWires c.post)) cseqs ∧
           syzygyCheck cc cseqs sq.pre concl ∧
           sq.post = FAtom BowLe concl (TmConst 0))
    | _ => F
End

Theorem checkPf1_farkas_arm:
  ∀ws sq cc concl dbl.
    checkPf1 ws (INL (CertPf sq (CnFarkas cc concl dbl))) ⇔
    checkPf1Arm_farkas ws sq (CnFarkas cc concl dbl)
Proof
  simp[Once checkPf1_def, checkPf1Arm_farkas_def]
QED

Theorem checkPf1_syz_arm:
  ∀ws sq comps cc concl dbl thq.
    checkPf1 ws (INL (CertPf sq (CnSyzygy comps cc concl dbl thq))) ⇔
    (checkPf1 ws (INR comps) ∧
     checkPf1Arm_syz ws sq (CnSyzygy comps cc concl dbl thq))
Proof
  simp[Once checkPf1_def, checkPf1Arm_syz_def]
QED

Definition childSeqAt_def:
  childSeqAt (cols:columns) (ct:ctx) (i:num) (k:num) : sequent option =
    case childOrd ct i k of
    | NONE => NONE
    | SOME c =>
      case conclRef cols ct c of
      | NONE => NONE
      | SOME cj =>
        case pv cols ct cj of
        | SOME (PJudg prew postw) => SOME (judgSeq FTt prew postw)
        | _ => NONE
End

Definition checkFam_farkas_def:
  checkFam_farkas (cols:columns) (ct:ctx) (i:num) ⇔
    case conclRef cols ct i of
    | NONE => F
    | SOME cj =>
      case pv cols ct cj of
      | SOME (PJudg prew postw) =>
        (case prefField cols ct i 0 of
         | NONE => F
         | SOME rc =>
           case prefField cols ct i 1 of
           | NONE => F
           | SOME ro =>
             case pv cols ct rc of
             | SOME (PTerm ccT) =>
               (case pv cols ct ro of
                | SOME (PTerm coT) =>
                    IS_SOME (termBshape ct.ws coT) ∧
                    finWiresB ct.ws coT ∧
                    wiresPosB ct.ws
                      (formulaFreeWires (expandSph FTt prew) ++
                       termFreeWires coT) ∧
                    farkasCheck ccT (expandSph FTt prew) coT ∧
                    expandSph FTt postw = FAtom BowLe coT (TmConst 0)
                | _ => F)
             | _ => F)
      | _ => F
End

Definition checkFam_syz_def:
  checkFam_syz (cols:columns) (ct:ctx) (i:num) ⇔
    case conclRef cols ct i of
    | NONE => F
    | SOME cj =>
      case pv cols ct cj of
      | SOME (PJudg prew postw) =>
        (case arityOf cols ct i of
         | NONE => F
         | SOME nc =>
           case optSeq (MAP (childSeqAt cols ct i) (rangeL nc)) of
           | NONE => F
           | SOME cseqs =>
             case prefField cols ct i 0 of
             | NONE => F
             | SOME rc =>
               case prefField cols ct i 1 of
               | NONE => F
               | SOME ro =>
                 case scalField cols ct i 0 of
                 | NONE => F
                 | SOME thv =>
                   case pv cols ct rc of
                   | SOME (PTerm ccT) =>
                     (case pv cols ct ro of
                      | SOME (PTerm coT) =>
                          (thv = 4294967295 ∨
                           (case pv cols ct thv of
                            | SOME (PTerm (TmConst _)) => T
                            | _ => F)) ∧
                          EVERY (λc. premiseContainsB (expandSph FTt prew)
                                                      c.pre) cseqs ∧
                          IS_SOME (termBshape ct.ws coT) ∧
                          finWiresB ct.ws coT ∧
                          wiresPosB ct.ws
                            (formulaFreeWires (expandSph FTt prew) ++
                             termFreeWires coT) ∧
                          EVERY (λc. wiresPosB ct.ws
                                       (formulaFreeWires c.post)) cseqs ∧
                          syzygyCheck ccT cseqs (expandSph FTt prew) coT ∧
                          expandSph FTt postw = FAtom BowLe coT (TmConst 0)
                      | _ => F)
                   | _ => F)
      | _ => F
End

Theorem nodeReconF_concl:
  ∀f k pf.
    nodeReconF cols ct f k = SOME pf ⇒
    ∃cj prew postw nd0.
      conclRef cols ct k = SOME cj ∧
      pv cols ct cj = SOME (PJudg prew postw) ∧
      pf = CertPf (judgSeq FTt prew postw) nd0
Proof
  Cases_on ‘f’
  >- simp[nodeReconF_def]
  >> rpt gen_tac
  >> simp[Once nodeReconF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[]
QED

Theorem childSeqAt_optSeq:
  ∀ks comps.
    optSeq (MAP (λk. case childOrd ct i k of
                     | NONE => NONE
                     | SOME c => nodeReconF cols ct f c) ks) = SOME comps ⇒
    optSeq (MAP (childSeqAt cols ct i) ks) = SOME (MAP certConcl comps)
Proof
  Induct
  >- simp[optSeq_def]
  >> rpt gen_tac
  >> Cases_on ‘childOrd ct i h’
  >- simp[optSeq_def]
  >> simp[]
  >> Cases_on ‘nodeReconF cols ct f x’
  >- simp[optSeq_def]
  >> simp[optSeq_def, AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac
  >> drule nodeReconF_concl >> strip_tac
  >> first_x_assum drule >> strip_tac
  >> gvs[childSeqAt_def, certConcl_def, optSeq_def]
QED

Theorem famEq_farkas_core:
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) = 14 ⇒
  (checkFam_farkas cols ct i ⇔ checkPf1Arm_farkas ct.ws sq nd)
Proof
  strip_tac
  >> gvs[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> Cases_on ‘tagOf cols i’ >> simp[]
  >> PairCases_on ‘x’ >> gvs[]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac
  >> gvs[checkFam_farkas_def, checkPf1Arm_farkas_def, judgSeq_def]
QED

Theorem famEq_syz_core:
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) = 26 ⇒
  (checkFam_syz cols ct i ⇔ checkPf1Arm_syz ct.ws sq nd)
Proof
  strip_tac
  >> gvs[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> Cases_on ‘tagOf cols i’ >> simp[]
  >> PairCases_on ‘x’ >> gvs[]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac
  >> drule childSeqAt_optSeq >> strip_tac
  >> gvs[checkFam_syz_def, checkPf1Arm_syz_def, judgSeq_def,
         certConcl_def]
QED

Theorem famEq_farkas:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ ws = ct.ws ∧
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) ∈ {14:num} ⇒
  (checkFam_farkas cols ct i ⇔ checkPf1Arm_farkas ws sq nd)
Proof
  rw[]
  >> irule famEq_farkas_core
  >> simp[]
QED

Theorem famEq_syz:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ ws = ct.ws ∧
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) ∈ {26:num} ⇒
  (checkFam_syz cols ct i ⇔ checkPf1Arm_syz ws sq nd)
Proof
  rw[]
  >> irule famEq_syz_core
  >> simp[]
QED

Theorem optSeq_LENGTH:
  ∀xs ys. optSeq xs = SOME ys ⇒ LENGTH ys = LENGTH xs
Proof
  Induct >- simp[optSeq_def]
  >> Cases >> simp[optSeq_def, AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[]
QED

Theorem optSeq_EL:
  ∀xs ys k. optSeq xs = SOME ys ∧ k < LENGTH xs ⇒ EL k xs = SOME (EL k ys)
Proof
  Induct >- simp[optSeq_def]
  >> Cases >> simp[optSeq_def, AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> Cases_on ‘k’ >> gvs[]
QED

Theorem LENGTH_rangeL:
  ∀n. LENGTH (rangeL n) = n
Proof
  Induct >> simp[rangeL_def]
QED

Theorem EL_rangeL:
  ∀n k. k < n ⇒ EL k (rangeL n) = k
Proof
  Induct >> rw[rangeL_def]
  >> Cases_on ‘k < n’
  >- simp[rich_listTheory.EL_APPEND1, LENGTH_rangeL]
  >> ‘k = n’ by decide_tac
  >> simp[rich_listTheory.EL_APPEND2, LENGTH_rangeL]
QED

Theorem checkPf1_INR_every:
  ∀ps ws. checkPf1 ws (INR ps) ⇔ EVERY (λp. checkPf1 ws (INL p)) ps
Proof
  Induct >> simp[Once checkPf1_def]
QED

Theorem nodeCorr_farkas_shape:
  nodeCorr cols ct i (CertPf sq nd) ∧ FST (THE (tagOf cols i)) = 14 ⇒
  ∃cc concl. nd = CnFarkas cc concl (denOf cols i)
Proof
  strip_tac
  >> gvs[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> Cases_on ‘tagOf cols i’ >> simp[]
  >> PairCases_on ‘x’ >> gvs[]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[]
QED

Theorem nodeCorr_syz_shape:
  nodeCorr cols ct i (CertPf sq nd) ∧ FST (THE (tagOf cols i)) = 26 ⇒
  ∃comps cc concl th. nd = CnSyzygy comps cc concl (denOf cols i) th
Proof
  strip_tac
  >> gvs[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> Cases_on ‘tagOf cols i’ >> simp[]
  >> PairCases_on ‘x’ >> gvs[]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[]
QED

Theorem nodeCorr_syz_children:
  nodeCorr cols ct i (CertPf sq (CnSyzygy comps cc concl dbl th)) ∧
  FST (THE (tagOf cols i)) = 26 ⇒
  ∃nc. arityOf cols ct i = SOME nc ∧ LENGTH comps = nc ∧
       ∀k. k < nc ⇒
           ∃c. childOrd ct i k = SOME c ∧
               nodeReconF cols ct i c = SOME (EL k comps)
Proof
  strip_tac
  >> gvs[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> Cases_on ‘tagOf cols i’ >> simp[]
  >> PairCases_on ‘x’ >> gvs[]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[]
  >> drule optSeq_LENGTH
  >> simp[LENGTH_rangeL]
  >> strip_tac
  >> rpt strip_tac
  >> drule optSeq_EL
  >> disch_then (qspec_then ‘k’ mp_tac)
  >> simp[LENGTH_rangeL, listTheory.EL_MAP, EL_rangeL]
  >> simp[AllCaseEqs()]
QED

Theorem nodeCorr_syz_theta:
  nodeCorr cols ct i (CertPf sq (CnSyzygy comps cc concl dbl th)) ∧
  FST (THE (tagOf cols i)) = 26 ⇒
  ∃thv. scalField cols ct i 0 = SOME thv ∧
        (th = NONE ⇔ thv = 4294967295) ∧
        (∀q. th = SOME q ⇒ pv cols ct thv = SOME (PTerm (TmConst q)))
Proof
  strip_tac
  >> gvs[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> Cases_on ‘tagOf cols i’ >> simp[]
  >> PairCases_on ‘x’ >> gvs[]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[]
QED

Theorem famSlice_farkas:
  nodeCorr cols ct i (CertPf sq nd) ∧ FST (THE (tagOf cols i)) = 14 ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔ checkFam_farkas cols ct i)
Proof
  strip_tac
  >> drule_all nodeCorr_farkas_shape
  >> strip_tac >> gvs[]
  >> simp[checkPf1_farkas_arm]
  >> drule_all famEq_farkas_core
  >> simp[]
QED

Theorem famSlice_syz:
  nodeCorr cols ct i (CertPf sq (CnSyzygy comps cc concl dbl th)) ∧
  FST (THE (tagOf cols i)) = 26 ⇒
  (checkPf1 ct.ws (INL (CertPf sq (CnSyzygy comps cc concl dbl th))) ⇔
   (EVERY (λp. checkPf1 ct.ws (INL p)) comps ∧ checkFam_syz cols ct i))
Proof
  strip_tac
  >> simp[checkPf1_syz_arm, checkPf1_INR_every]
  >> drule_all famEq_syz_core
  >> simp[]
QED
