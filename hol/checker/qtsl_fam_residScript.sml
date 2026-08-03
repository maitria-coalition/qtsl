(*
  Family F6 (the v0-fragment residual): one bounded checkFam per
  remaining rule tag (weaken, cut, andI, orI, eqElim, arithAtom, norm,
  eqRefl, eqSym, promise), each with a proven faithfulness witness
  against the reference checker so the de-recursion contract is
  checked, not assumed.
*)
Theory qtsl_fam_resid
Ancestors
  rat integer mlstring mllist qtsl_dyadic qtsl_qarith qtsl_catalogue
  qtsl_cert qtsl_cols qtsl_wf
Libs
  preamble

Definition frSeq_def:
  frSeq (cols:columns) (ct:ctx) (i:num) : sequent option =
    case conclRef cols ct i of
    | NONE => NONE
    | SOME cj =>
      case pv cols ct cj of
      | SOME (PJudg prew postw) => SOME (judgSeq FTt prew postw)
      | _ => NONE
End

Definition frChildSeq_def:
  frChildSeq (cols:columns) (ct:ctx) (i:num) (k:num) : sequent option =
    case childOrd ct i k of
    | NONE => NONE
    | SOME c => frSeq cols ct c
End

Definition frFormula_def:
  frFormula (cols:columns) (ct:ctx) (i:num) (k:num) : formula option =
    case prefField cols ct i k of
    | NONE => NONE
    | SOME r =>
      case pv cols ct r of
      | SOME (PFormula fw) => SOME (expandSph FTt fw)
      | _ => NONE
End

Definition frTerm_def:
  frTerm (cols:columns) (ct:ctx) (i:num) (k:num) : term option =
    case prefField cols ct i k of
    | NONE => NONE
    | SOME r =>
      case pv cols ct r of
      | SOME (PTerm t) => SOME t
      | _ => NONE
End

Definition checkFam_weaken_def:
  checkFam_weaken (cols:columns) (ct:ctx) (i:num) ⇔
    case frSeq cols ct i of
    | NONE => F
    | SOME sq =>
      case frChildSeq cols ct i 0 of
      | NONE => F
      | SOME ps =>
        case frFormula cols ct i 0 of
        | NONE => F
        | SOME extra =>
            sq.pre = FAnd ps.pre extra ∧ sq.post = ps.post
End

Definition checkFam_cut_def:
  checkFam_cut (cols:columns) (ct:ctx) (i:num) ⇔
    case frSeq cols ct i of
    | NONE => F
    | SOME sq =>
      case frChildSeq cols ct i 0 of
      | NONE => F
      | SOME ls =>
        case frChildSeq cols ct i 1 of
        | NONE => F
        | SOME rs =>
          case frFormula cols ct i 0 of
          | NONE => F
          | SOME cutf =>
              sq.pre = ls.pre ∧ sq.post = rs.post ∧
              ls.post = cutf ∧ rs.pre = FAnd ls.pre cutf
End

Definition checkFam_andi_def:
  checkFam_andi (cols:columns) (ct:ctx) (i:num) ⇔
    case frSeq cols ct i of
    | NONE => F
    | SOME sq =>
      case frChildSeq cols ct i 0 of
      | NONE => F
      | SOME ls =>
        case frChildSeq cols ct i 1 of
        | NONE => F
        | SOME rs =>
            ls.pre = rs.pre ∧ sq.pre = ls.pre ∧
            sq.post = FAnd ls.post rs.post
End

Definition checkFam_ori_def:
  checkFam_ori (cols:columns) (ct:ctx) (i:num) ⇔
    case tagOf cols i of
    | NONE => F
    | SOME (r, v) =>
      case frSeq cols ct i of
      | NONE => F
      | SOME sq =>
        case frChildSeq cols ct i 0 of
        | NONE => F
        | SOME ps =>
          case frFormula cols ct i 0 of
          | NONE => F
          | SOME other =>
              sq.pre = ps.pre ∧
              sq.post = (if v = 0 then FOr ps.post other
                         else FOr other ps.post)
End

Definition checkFam_eqelim_def:
  checkFam_eqelim (cols:columns) (ct:ctx) (i:num) ⇔
    case frSeq cols ct i of
    | NONE => F
    | SOME sq =>
      case frChildSeq cols ct i 0 of
      | NONE => F
      | SOME es =>
        case frChildSeq cols ct i 1 of
        | NONE => F
        | SOME bs =>
          case scalField cols ct i 0 of
          | NONE => F
          | SOME w =>
            case frTerm cols ct i 0 of
            | NONE => F
            | SOME tT =>
              case frTerm cols ct i 1 of
              | NONE => F
              | SOME tU =>
                case frFormula cols ct i 2 of
                | NONE => F
                | SOME bodyForm =>
                    sq.pre = es.pre ∧ es.pre = bs.pre ∧
                    es.post = FAtom BowEq tT tU ∧
                    termBshape ct.ws tT = termBshape ct.ws tU ∧
                    IS_SOME (termBshape ct.ws tT) ∧
                    bs.post = formulaSubst w tT bodyForm ∧
                    sq.post = formulaSubst w tU bodyForm
End

Definition checkFam_arith_def:
  checkFam_arith (cols:columns) (ct:ctx) (i:num) ⇔
    case tagOf cols i of
    | NONE => F
    | SOME (r, v) =>
      case frSeq cols ct i of
      | NONE => F
      | SOME sq =>
        case frChildSeq cols ct i 0 of
        | NONE => F
        | SOME ps =>
          case frTerm cols ct i 0 of
          | NONE => F
          | SOME tl =>
            case frTerm cols ct i 1 of
            | NONE => F
            | SOME tr =>
              case scalField cols ct i 0 of
              | NONE => F
              | SOME bb =>
                case bowtieOf bb of
                | NONE => F
                | SOME b =>
                    b ≠ BowNe ∧ sq.pre = ps.pre ∧
                    (if v = 0 then
                       ps.post = FAtom b (TmSub tl tr) (TmConst 0) ∧
                       sq.post = FAtom b tl tr
                     else
                       ps.post = FAtom b tl tr ∧
                       sq.post = FAtom b (TmSub tl tr) (TmConst 0))
End

Definition checkFam_norm_def:
  checkFam_norm (cols:columns) (ct:ctx) (i:num) ⇔
    case frSeq cols ct i of
    | NONE => F
    | SOME sq =>
      case frTerm cols ct i 0 of
      | NONE => F
      | SOME tl =>
        case frTerm cols ct i 1 of
        | NONE => F
        | SOME tr =>
            polynomialCanonicalEqB tl tr ∧
            termBshape ct.ws tl = termBshape ct.ws tr ∧
            IS_SOME (termBshape ct.ws tl) ∧
            finWiresB ct.ws tl ∧ finWiresB ct.ws tr ∧
            sq.post = FAtom BowEq tl tr
End

Definition checkFam_eqrefl_def:
  checkFam_eqrefl (cols:columns) (ct:ctx) (i:num) ⇔
    case frSeq cols ct i of
    | NONE => F
    | SOME sq =>
      case frTerm cols ct i 0 of
      | NONE => F
      | SOME t =>
          IS_SOME (termBshape ct.ws t) ∧ finWiresB ct.ws t ∧
          sq.post = FAtom BowEq t t
End

Definition checkFam_eqsym_def:
  checkFam_eqsym (cols:columns) (ct:ctx) (i:num) ⇔
    case frSeq cols ct i of
    | NONE => F
    | SOME sq =>
      case frChildSeq cols ct i 0 of
      | NONE => F
      | SOME ps =>
        case frTerm cols ct i 0 of
        | NONE => F
        | SOME tT =>
          case frTerm cols ct i 1 of
          | NONE => F
          | SOME tU =>
              sq.pre = ps.pre ∧
              ps.post = FAtom BowEq tT tU ∧
              sq.post = FAtom BowEq tU tT
End

Definition checkFam_promise_def:
  checkFam_promise (cols:columns) (ct:ctx) (i:num) ⇔
    case frSeq cols ct i of
    | NONE => F
    | SOME sq =>
      case frChildSeq cols ct i 0 of
      | NONE => F
      | SOME ss =>
        case frChildSeq cols ct i 1 of
        | NONE => F
        | SOME cs =>
          case frFormula cols ct i 0 of
          | NONE => F
          | SOME ctr =>
            case pathOf cols ct i of
            | NONE => F
            | SOME (stps, ifc) =>
              let pth = stepsToPath stps in
                ss.post = ctr ∧
                conjGet cs.pre pth = SOME ctr ∧
                conjReplace cs.pre pth ss.pre = SOME sq.pre ∧
                sq.post = cs.post ∧
                (case conjReplace cs.pre pth FTt of
                 | SOME cx0 =>
                     (EVERY (λw. MEM w ifc) (formulaFreeWires ctr) ∧
                      EVERY (λw. (MEM w (formulaFreeWires cx0) ∨
                                  MEM w (formulaFreeWires sq.post)) ⇒
                                 MEM w ifc)
                            (formulaFreeWires ss.pre))
                 | NONE => F)
End

Definition armWeaken_def:
  armWeaken (ws:tensortype list) (sq:sequent) (nd:cnode) ⇔
    case nd of
    | CnWeaken p extra =>
        (let ps = certConcl p in
           sq.pre = FAnd ps.pre extra ∧ sq.post = ps.post)
    | _ => F
End

Definition armCut_def:
  armCut (ws:tensortype list) (sq:sequent) (nd:cnode) ⇔
    case nd of
    | CnCut cutf lp rp =>
        (let ls = certConcl lp in
         let rs = certConcl rp in
           sq.pre = ls.pre ∧ sq.post = rs.post ∧
           ls.post = cutf ∧ rs.pre = FAnd ls.pre cutf)
    | _ => F
End

Definition armAndI_def:
  armAndI (ws:tensortype list) (sq:sequent) (nd:cnode) ⇔
    case nd of
    | CnAndI lp rp =>
        (let ls = certConcl lp in
         let rs = certConcl rp in
           ls.pre = rs.pre ∧ sq.pre = ls.pre ∧
           sq.post = FAnd ls.post rs.post)
    | _ => F
End

Definition armOrI_def:
  armOrI (ws:tensortype list) (sq:sequent) (nd:cnode) ⇔
    case nd of
    | CnOrIL p other =>
        (let ps = certConcl p in
           sq.pre = ps.pre ∧ sq.post = FOr ps.post other)
    | CnOrIR p other =>
        (let ps = certConcl p in
           sq.pre = ps.pre ∧ sq.post = FOr other ps.post)
    | _ => F
End

Definition armEqElim_def:
  armEqElim (ws:tensortype list) (sq:sequent) (nd:cnode) ⇔
    case nd of
    | CnEqElim ep bp w tT tU bodyForm =>
        (let es = certConcl ep in
         let bs = certConcl bp in
           sq.pre = es.pre ∧ es.pre = bs.pre ∧
           es.post = FAtom BowEq tT tU ∧
           termBshape ws tT = termBshape ws tU ∧
           IS_SOME (termBshape ws tT) ∧
           bs.post = formulaSubst w tT bodyForm ∧
           sq.post = formulaSubst w tU bodyForm)
    | _ => F
End

Definition armArith_def:
  armArith (ws:tensortype list) (sq:sequent) (nd:cnode) ⇔
    case nd of
    | CnArithFold p tl tr b =>
        (b ≠ BowNe ∧
         let ps = certConcl p in
           sq.pre = ps.pre ∧
           ps.post = FAtom b (TmSub tl tr) (TmConst 0) ∧
           sq.post = FAtom b tl tr)
    | CnArithUnfold p tl tr b =>
        (b ≠ BowNe ∧
         let ps = certConcl p in
           sq.pre = ps.pre ∧
           ps.post = FAtom b tl tr ∧
           sq.post = FAtom b (TmSub tl tr) (TmConst 0))
    | _ => F
End

Definition armNorm_def:
  armNorm (ws:tensortype list) (sq:sequent) (nd:cnode) ⇔
    case nd of
    | CnNorm tl tr =>
        (polynomialCanonicalEqB tl tr ∧
         termBshape ws tl = termBshape ws tr ∧
         IS_SOME (termBshape ws tl) ∧
         finWiresB ws tl ∧ finWiresB ws tr ∧
         sq.post = FAtom BowEq tl tr)
    | _ => F
End

Definition armEqRefl_def:
  armEqRefl (ws:tensortype list) (sq:sequent) (nd:cnode) ⇔
    case nd of
    | CnEqRefl t =>
        (IS_SOME (termBshape ws t) ∧ finWiresB ws t ∧
         sq.post = FAtom BowEq t t)
    | _ => F
End

Definition armEqSym_def:
  armEqSym (ws:tensortype list) (sq:sequent) (nd:cnode) ⇔
    case nd of
    | CnEqSym p tT tU =>
        (let ps = certConcl p in
           sq.pre = ps.pre ∧
           ps.post = FAtom BowEq tT tU ∧
           sq.post = FAtom BowEq tU tT)
    | _ => F
End

Definition armPromise_def:
  armPromise (ws:tensortype list) (sq:sequent) (nd:cnode) ⇔
    case nd of
    | CnPromise sp cp ctr pth ifc =>
        (let ss = certConcl sp in
         let cs = certConcl cp in
           ss.post = ctr ∧
           conjGet cs.pre pth = SOME ctr ∧
           conjReplace cs.pre pth ss.pre = SOME sq.pre ∧
           sq.post = cs.post ∧
           (case conjReplace cs.pre pth FTt of
            | SOME cx0 =>
                (EVERY (λw. MEM w ifc) (formulaFreeWires ctr) ∧
                 EVERY (λw. (MEM w (formulaFreeWires cx0) ∨
                             MEM w (formulaFreeWires sq.post)) ⇒
                            MEM w ifc)
                       (formulaFreeWires ss.pre))
            | NONE => F))
    | _ => F
End

Theorem armWeaken_faithful:
  checkPf1 ws (INL (CertPf sq (CnWeaken p extra))) ⇔
  checkPf1 ws (INL p) ∧ armWeaken ws sq (CnWeaken p extra)
Proof
  simp[Once checkPf1_def, armWeaken_def]
QED

Theorem armCut_faithful:
  checkPf1 ws (INL (CertPf sq (CnCut cutf lp rp))) ⇔
  checkPf1 ws (INL lp) ∧ checkPf1 ws (INL rp) ∧
  armCut ws sq (CnCut cutf lp rp)
Proof
  simp[Once checkPf1_def, armCut_def] >> metis_tac[]
QED

Theorem armAndI_faithful:
  checkPf1 ws (INL (CertPf sq (CnAndI lp rp))) ⇔
  checkPf1 ws (INL lp) ∧ checkPf1 ws (INL rp) ∧
  armAndI ws sq (CnAndI lp rp)
Proof
  simp[Once checkPf1_def, armAndI_def] >> metis_tac[]
QED

Theorem armOrIL_faithful:
  checkPf1 ws (INL (CertPf sq (CnOrIL p other))) ⇔
  checkPf1 ws (INL p) ∧ armOrI ws sq (CnOrIL p other)
Proof
  simp[Once checkPf1_def, armOrI_def]
QED

Theorem armOrIR_faithful:
  checkPf1 ws (INL (CertPf sq (CnOrIR p other))) ⇔
  checkPf1 ws (INL p) ∧ armOrI ws sq (CnOrIR p other)
Proof
  simp[Once checkPf1_def, armOrI_def]
QED

Theorem armEqElim_faithful:
  checkPf1 ws (INL (CertPf sq (CnEqElim ep bp w tT tU bodyForm))) ⇔
  checkPf1 ws (INL ep) ∧ checkPf1 ws (INL bp) ∧
  armEqElim ws sq (CnEqElim ep bp w tT tU bodyForm)
Proof
  simp[Once checkPf1_def, armEqElim_def] >> metis_tac[]
QED

Theorem armArithFold_faithful:
  checkPf1 ws (INL (CertPf sq (CnArithFold p tl tr b))) ⇔
  checkPf1 ws (INL p) ∧ armArith ws sq (CnArithFold p tl tr b)
Proof
  simp[Once checkPf1_def, armArith_def] >> metis_tac[]
QED

Theorem armArithUnfold_faithful:
  checkPf1 ws (INL (CertPf sq (CnArithUnfold p tl tr b))) ⇔
  checkPf1 ws (INL p) ∧ armArith ws sq (CnArithUnfold p tl tr b)
Proof
  simp[Once checkPf1_def, armArith_def] >> metis_tac[]
QED

Theorem armNorm_faithful:
  checkPf1 ws (INL (CertPf sq (CnNorm tl tr))) ⇔
  armNorm ws sq (CnNorm tl tr)
Proof
  simp[Once checkPf1_def, armNorm_def]
QED

Theorem armEqRefl_faithful:
  checkPf1 ws (INL (CertPf sq (CnEqRefl t))) ⇔
  armEqRefl ws sq (CnEqRefl t)
Proof
  simp[Once checkPf1_def, armEqRefl_def]
QED

Theorem armEqSym_faithful:
  checkPf1 ws (INL (CertPf sq (CnEqSym p tT tU))) ⇔
  checkPf1 ws (INL p) ∧ armEqSym ws sq (CnEqSym p tT tU)
Proof
  simp[Once checkPf1_def, armEqSym_def]
QED

Theorem armPromise_faithful:
  checkPf1 ws (INL (CertPf sq (CnPromise sp cp ctr pth ifc))) ⇔
  checkPf1 ws (INL sp) ∧ checkPf1 ws (INL cp) ∧
  armPromise ws sq (CnPromise sp cp ctr pth ifc)
Proof
  simp[Once checkPf1_def, armPromise_def] >> metis_tac[]
QED

Theorem frRecon_seq:
  ∀f i pf.
    nodeReconF cols ct f i = SOME pf ⇒
    frSeq cols ct i = SOME (certConcl pf)
Proof
  Cases >- simp[nodeReconF_def]
  >> rpt strip_tac
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[frSeq_def, certConcl_def]
QED

Theorem frChildSeq_recon:
  childOrd ct i k = SOME c ∧ nodeReconF cols ct f c = SOME p ⇒
  frChildSeq cols ct i k = SOME (certConcl p)
Proof
  rw[frChildSeq_def] >> metis_tac[frRecon_seq]
QED

Theorem frTakeN_eq:
  takeN n xs = SOME (a, b) ⇔ n ≤ LENGTH xs ∧ a = TAKE n xs ∧ b = DROP n xs
Proof
  rw[takeN_def] >> metis_tac[]
QED

Theorem frRdLE_eq:
  rdLE k xs = SOME (v, r) ⇔
  k ≤ LENGTH xs ∧ v = leN (TAKE k xs) ∧ r = DROP k xs
Proof
  simp[rdLE_def, AllCaseEqs(), frTakeN_eq, PULL_EXISTS]
  >> eq_tac >> rw[] >> gvs[]
QED

Theorem parseHeader_fields:
  parseHeader b = SOME h ⇒
    128 ≤ LENGTH b ∧ 128 ≤ h.prfOff ∧
    h.symOff = leN (TAKE 8 (DROP 16 b)) ∧
    h.symLen = leN (TAKE 8 (DROP 24 b)) ∧
    h.payOff = leN (TAKE 8 (DROP 32 b)) ∧
    h.payLen = leN (TAKE 8 (DROP 40 b)) ∧
    h.diaOff = leN (TAKE 8 (DROP 48 b)) ∧
    h.diaLen = leN (TAKE 8 (DROP 56 b)) ∧
    h.prfOff = leN (TAKE 8 (DROP 64 b)) ∧
    h.prfLen = leN (TAKE 8 (DROP 72 b)) ∧
    h.nWires = leN (TAKE 4 (DROP 80 b)) ∧
    h.nApps = leN (TAKE 4 (DROP 84 b)) ∧
    h.nNodes = leN (TAKE 4 (DROP 88 b)) ∧
    h.nCxs = leN (TAKE 4 (DROP 92 b)) ∧
    h.rootOff = leN (TAKE 8 (DROP 96 b)) ∧
    h.thetaRef = leN (TAKE 4 (DROP 104 b))
Proof
  strip_tac
  >> gvs[parseHeader_def, AllCaseEqs(), frRdLE_eq, frTakeN_eq, sectionOK_def]
  >> gvs[rich_listTheory.DROP_DROP_T]
QED

Theorem parseHeader_128:
  parseHeader b = SOME h ⇒ 128 ≤ h.prfOff
Proof
  strip_tac >> drule_then strip_assume_tac parseHeader_fields >> simp[]
QED

Theorem frTakeDrop128:
  pos + k ≤ 128 ∧ TAKE 128 (b1:num list) = TAKE 128 (b2:num list) ⇒
  TAKE k (DROP pos b1) = TAKE k (DROP pos b2)
Proof
  strip_tac
  >> ‘∀b:num list. TAKE k (DROP pos b) = TAKE k (DROP pos (TAKE 128 b))’
       by (gen_tac
           >> simp[listTheory.DROP_TAKE, listTheory.TAKE_TAKE_MIN]
           >> ‘MIN k (128 − pos) = k’ by simp[arithmeticTheory.MIN_DEF]
           >> simp[])
  >> metis_tac[]
QED

Theorem parseHeader_agree:
  parseHeader b1 = SOME h1 ∧ parseHeader b2 = SOME h2 ∧
  TAKE 128 b1 = TAKE 128 b2 ⇒
  h1 = h2
Proof
  strip_tac
  >> imp_res_tac parseHeader_fields
  >> ‘∀pos k. pos + k ≤ 128 ⇒ TAKE k (DROP pos b1) = TAKE k (DROP pos b2)’
       by metis_tac[frTakeDrop128]
  >> rw[fetch "qtsl_cert" "bhdr_component_equality"] >> simp[]
QED

Theorem mkCtx_hdr_ws:
  mkCtx cols = SOME ct ⇒
  parseHeader (cols.hdrImage ++ REPLICATE (peekPrfLen cols.hdrImage) 0)
    = SOME ct.hdr ∧
  parseSymtab (TAKE ct.hdr.symLen (DROP ct.hdr.symOff cols.hdrImage))
              ct.hdr.symLen ct.hdr.nWires ct.hdr.payOff ct.hdr.payLen
    = SOME ct.ws
Proof
  simp[mkCtx_def, AllCaseEqs(), PULL_EXISTS] >> rpt strip_tac >> gvs[]
QED

Theorem frWsEq:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ws, pf) ⇒
  ws = ct.ws
Proof

  strip_tac
  >> drule_then strip_assume_tac mkCtx_hdr_ws
  >> qpat_x_assum ‘wfColumns _ _’ mp_tac
  >> simp[wfColumns_def, wf1_def, wf2_def] >> strip_tac
  >> qpat_x_assum ‘parseCert _ = _’ mp_tac
  >> simp[parseCert_def, AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac
  >> ‘128 ≤ ct.hdr.prfOff’ by imp_res_tac parseHeader_128
  >> ‘128 ≤ LENGTH cols.hdrImage’ by gvs[]
  >> ‘TAKE 128 (cols.hdrImage ++ rest) =
      TAKE 128 (cols.hdrImage ++ REPLICATE (peekPrfLen cols.hdrImage) 0)’
       by simp[listTheory.TAKE_APPEND1]
  >> qpat_x_assum ‘parseHeader (_ ++ rest) = SOME _’ (fn thR =>
     qpat_assum ‘parseHeader (_ ++ REPLICATE _ _) = SOME _’ (fn thP =>
     qpat_assum ‘TAKE 128 _ = TAKE 128 _’ (fn thT =>
       assume_tac thR
       >> assume_tac (MATCH_MP parseHeader_agree (LIST_CONJ [thR, thP, thT])))))
  >> pop_assum SUBST_ALL_TAC
  >> ‘ct.hdr.symOff ≤ LENGTH cols.hdrImage’ by gvs[]
  >> ‘ct.hdr.symLen ≤ LENGTH cols.hdrImage − ct.hdr.symOff’ by gvs[]
  >> ‘TAKE ct.hdr.symLen (DROP ct.hdr.symOff (cols.hdrImage ++ rest)) =
      TAKE ct.hdr.symLen (DROP ct.hdr.symOff cols.hdrImage)’
       by simp[listTheory.DROP_APPEND1, listTheory.TAKE_APPEND1]
  >> gvs[]
QED

Theorem famEq_weaken:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ws, pf) ∧
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) = 1 ⇒
  (checkFam_weaken cols ct i ⇔ armWeaken ws sq nd)
Proof
  strip_tac
  >> qpat_x_assum ‘wfColumns _ _’ kall_tac
  >> qpat_x_assum ‘mkCtx _ = _’ kall_tac
  >> qpat_x_assum ‘parseCert _ = _’ kall_tac
  >> gvs[nodeCorr_def]
  >> drule_then assume_tac frRecon_seq
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[certConcl_def]
  >> imp_res_tac frChildSeq_recon
  >> gvs[checkFam_weaken_def, frFormula_def, armWeaken_def]
QED

Theorem famEq_cut:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ws, pf) ∧
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) = 2 ⇒
  (checkFam_cut cols ct i ⇔ armCut ws sq nd)
Proof
  strip_tac
  >> qpat_x_assum ‘wfColumns _ _’ kall_tac
  >> qpat_x_assum ‘mkCtx _ = _’ kall_tac
  >> qpat_x_assum ‘parseCert _ = _’ kall_tac
  >> gvs[nodeCorr_def]
  >> drule_then assume_tac frRecon_seq
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[certConcl_def]
  >> imp_res_tac frChildSeq_recon
  >> gvs[checkFam_cut_def, frFormula_def, armCut_def, certConcl_def]
QED

Theorem famEq_andi:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ws, pf) ∧
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) = 3 ⇒
  (checkFam_andi cols ct i ⇔ armAndI ws sq nd)
Proof
  strip_tac
  >> qpat_x_assum ‘wfColumns _ _’ kall_tac
  >> qpat_x_assum ‘mkCtx _ = _’ kall_tac
  >> qpat_x_assum ‘parseCert _ = _’ kall_tac
  >> gvs[nodeCorr_def]
  >> drule_then assume_tac frRecon_seq
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[certConcl_def]
  >> imp_res_tac frChildSeq_recon
  >> gvs[checkFam_andi_def, armAndI_def, certConcl_def]
QED

Theorem famEq_ori:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ws, pf) ∧
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) = 5 ⇒
  (checkFam_ori cols ct i ⇔ armOrI ws sq nd)
Proof
  strip_tac
  >> qpat_x_assum ‘wfColumns _ _’ kall_tac
  >> qpat_x_assum ‘mkCtx _ = _’ kall_tac
  >> qpat_x_assum ‘parseCert _ = _’ kall_tac
  >> gvs[nodeCorr_def]
  >> drule_then assume_tac frRecon_seq
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[certConcl_def]
  >> imp_res_tac frChildSeq_recon
  >> Cases_on ‘v = 0’
  >> gvs[checkFam_ori_def, frFormula_def, armOrI_def, certConcl_def]
QED

Theorem famEq_eqelim:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ws, pf) ∧
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) = 7 ⇒
  (checkFam_eqelim cols ct i ⇔ armEqElim ws sq nd)
Proof
  strip_tac
  >> ‘ws = ct.ws’ by metis_tac[frWsEq]
  >> pop_assum SUBST_ALL_TAC
  >> qpat_x_assum ‘wfColumns _ _’ kall_tac
  >> qpat_x_assum ‘mkCtx _ = _’ kall_tac
  >> qpat_x_assum ‘parseCert _ = _’ kall_tac
  >> gvs[nodeCorr_def]
  >> drule_then assume_tac frRecon_seq
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[certConcl_def]
  >> imp_res_tac frChildSeq_recon
  >> gvs[checkFam_eqelim_def, frTerm_def, frFormula_def, armEqElim_def,
         certConcl_def]
QED

Theorem famEq_arith:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ws, pf) ∧
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) = 10 ⇒
  (checkFam_arith cols ct i ⇔ armArith ws sq nd)
Proof
  strip_tac
  >> qpat_x_assum ‘wfColumns _ _’ kall_tac
  >> qpat_x_assum ‘mkCtx _ = _’ kall_tac
  >> qpat_x_assum ‘parseCert _ = _’ kall_tac
  >> gvs[nodeCorr_def]
  >> drule_then assume_tac frRecon_seq
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[certConcl_def]
  >> imp_res_tac frChildSeq_recon
  >> Cases_on ‘v = 0’
  >> gvs[checkFam_arith_def, frTerm_def, armArith_def, certConcl_def]
  >> metis_tac[]
QED

Theorem famEq_norm:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ws, pf) ∧
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) = 12 ⇒
  (checkFam_norm cols ct i ⇔ armNorm ws sq nd)
Proof
  strip_tac
  >> ‘ws = ct.ws’ by metis_tac[frWsEq]
  >> pop_assum SUBST_ALL_TAC
  >> qpat_x_assum ‘wfColumns _ _’ kall_tac
  >> qpat_x_assum ‘mkCtx _ = _’ kall_tac
  >> qpat_x_assum ‘parseCert _ = _’ kall_tac
  >> gvs[nodeCorr_def]
  >> drule_then assume_tac frRecon_seq
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[certConcl_def]
  >> gvs[checkFam_norm_def, frTerm_def, armNorm_def]
QED

Theorem famEq_eqrefl:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ws, pf) ∧
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) = 23 ⇒
  (checkFam_eqrefl cols ct i ⇔ armEqRefl ws sq nd)
Proof
  strip_tac
  >> ‘ws = ct.ws’ by metis_tac[frWsEq]
  >> pop_assum SUBST_ALL_TAC
  >> qpat_x_assum ‘wfColumns _ _’ kall_tac
  >> qpat_x_assum ‘mkCtx _ = _’ kall_tac
  >> qpat_x_assum ‘parseCert _ = _’ kall_tac
  >> gvs[nodeCorr_def]
  >> drule_then assume_tac frRecon_seq
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[certConcl_def]
  >> gvs[checkFam_eqrefl_def, frTerm_def, armEqRefl_def]
QED

Theorem famEq_eqsym:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ws, pf) ∧
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) = 24 ⇒
  (checkFam_eqsym cols ct i ⇔ armEqSym ws sq nd)
Proof
  strip_tac
  >> qpat_x_assum ‘wfColumns _ _’ kall_tac
  >> qpat_x_assum ‘mkCtx _ = _’ kall_tac
  >> qpat_x_assum ‘parseCert _ = _’ kall_tac
  >> gvs[nodeCorr_def]
  >> drule_then assume_tac frRecon_seq
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[certConcl_def]
  >> imp_res_tac frChildSeq_recon
  >> gvs[checkFam_eqsym_def, frTerm_def, armEqSym_def, certConcl_def]
QED

Theorem famEq_promise:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ws, pf) ∧
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) = 25 ⇒
  (checkFam_promise cols ct i ⇔ armPromise ws sq nd)
Proof
  strip_tac
  >> qpat_x_assum ‘wfColumns _ _’ kall_tac
  >> qpat_x_assum ‘mkCtx _ = _’ kall_tac
  >> qpat_x_assum ‘parseCert _ = _’ kall_tac
  >> gvs[nodeCorr_def]
  >> drule_then assume_tac frRecon_seq
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[certConcl_def]
  >> imp_res_tac frChildSeq_recon
  >> gvs[checkFam_promise_def, frFormula_def, armPromise_def, certConcl_def]
QED
