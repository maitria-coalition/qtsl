(*
  The relational checker's top level: checkJoins/checkNodes over the
  succinct columns, and the composition theorem checkJoins_eq_checkPf —
  a complete induction over node ordinals with a per-tag case split
  that re-introduces the child recursion the per-family lemmas
  de-recursed, consuming all six family legs.
*)
Theory qtsl_joins
Ancestors
  rat integer mlstring mllist qtsl_dyadic qtsl_qarith qtsl_catalogue
  qtsl_cert qtsl_cols qtsl_wf qtsl_fam_ax qtsl_fam_axEq qtsl_fam_ande
  qtsl_fam_ore qtsl_fam_cone qtsl_fam_syz qtsl_fam_resid
Libs
  preamble

Definition checkNode_def:
  checkNode (cols:columns) (ct:ctx) (i:num) ⇔
    case tagOf cols i of
    | NONE => F
    | SOME (r, v) =>
        if r = (0:num) then checkFam_ax cols ct i
        else if r = 1 then checkFam_weaken cols ct i
        else if r = 2 then checkFam_cut cols ct i
        else if r = 3 then checkFam_andi cols ct i
        else if r = 4 then checkFam_ande cols ct i
        else if r = 5 then checkFam_ori cols ct i
        else if r = 6 then checkFam_ore cols ct i
        else if r = 7 then checkFam_eqelim cols ct i
        else if r = 8 ∨ r = 9 then checkFam_conv cols ct i
        else if r = 10 then checkFam_arith cols ct i
        else if r = 11 then checkFam_berncone cols ct i
        else if r = 12 then checkFam_norm cols ct i
        else if r = 14 then checkFam_farkas cols ct i
        else if r = 23 then checkFam_eqrefl cols ct i
        else if r = 24 then checkFam_eqsym cols ct i
        else if r = 25 then checkFam_promise cols ct i
        else if r = 26 then checkFam_syz cols ct i
        else F
End

Definition checkNodes_def:
  checkNodes (cols:columns) (ct:ctx) ⇔
    EVERY (checkNode cols ct) (rangeL cols.nNodes)
End

Definition checkJoins_def:
  checkJoins (cols:columns) : bool option =
    case mkCtx cols of
    | NONE => NONE
    | SOME ct => SOME (wfColumns cols ct ∧ checkNodes cols ct)
End

Theorem checkNodes_all:
  checkNodes cols ct ⇔ ∀i. i < cols.nNodes ⇒ checkNode cols ct i
Proof
  simp[checkNodes_def, listTheory.EVERY_MEM, MEM_rangeL]
QED

Definition reconTotal_def:
  reconTotal (cols:columns) (ct:ctx) ⇔
    ∀i. i < cols.nNodes ⇒ ∃pf. nodeCorr cols ct i pf
End

Theorem nodeCorr_tag:
  nodeCorr cols ct i pf ⇒
  ∃r v. tagOf cols i = SOME (r, v) ∧
        (r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨
         r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 14 ∨
         r = 23 ∨ r = 24 ∨ r = 25 ∨ r = 26)
Proof
  rw[nodeCorr_def]
  >> pop_assum mp_tac
  >> simp[Once nodeReconF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[]
  >> metis_tac[]
QED

Theorem childOrd_lt:
  wf8 cols ct ∧ i < cols.nNodes ∧
  k < nodeArityAt cols i ∧ childOrd ct i k = SOME c ⇒
  c < i
Proof
  strip_tac
  >> ‘wf8node cols ct i’
       by gvs[wf8_def, listTheory.EVERY_MEM, MEM_rangeL]
  >> qpat_x_assum ‘wf8node _ _ _’ mp_tac
  >> simp[wf8node_def]
  >> Cases_on ‘tagOf cols i’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> strip_tac
  >> qpat_x_assum ‘EVERY _ (rangeL (nodeArityAt cols i))’ mp_tac
  >> simp[listTheory.EVERY_MEM, MEM_rangeL]
  >> disch_then (qspec_then ‘k’ mp_tac)
  >> simp[]
QED

Theorem nodeArityAt_rule:
  tagOf cols i = SOME (r, v) ∧ ¬hasArityR r ⇒
  nodeArityAt cols i = ruleArity r
Proof
  rw[tagOf_def, AllCaseEqs()]
  >> gvs[listTheory.oEL_THM, nodeArityAt_def, ruleOfD_def, tagDecD_def,
         getD_EL]
QED

Theorem nodeArityAt_syz:
  tagOf cols i = SOME (26, v) ∧ arityOf cols ct i = SOME nc ⇒
  nodeArityAt cols i = nc
Proof
  rw[tagOf_def, arityOf_def, AllCaseEqs()]
  >> gvs[listTheory.oEL_THM, nodeArityAt_def, ruleOfD_def, tagDecD_def,
         hasArityR_def, getD_EL]
QED

Theorem child_reanchor:
  reconTotal cols ct ∧ nodeReconF cols ct f k = SOME p ∧
  k < f ∧ k < cols.nNodes ⇒
  nodeCorr cols ct k p
Proof
  rw[reconTotal_def]
  >> first_x_assum (qspec_then ‘k’ mp_tac) >> simp[]
  >> strip_tac
  >> drule_all nodeReconF_nodeCorr_agree
  >> strip_tac >> gvs[]
QED

Theorem nodeCorr_weaken_inv:
  nodeCorr cols ct i (CertPf sq nd) ∧ tagOf cols i = SOME (1, v) ⇒
  ∃k p ex.
    childOrd ct i 0 = SOME k ∧ nodeReconF cols ct i k = SOME p ∧
    nd = CnWeaken p ex
Proof
  rw[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> metis_tac[]
QED

Theorem nodeCorr_cut_inv:
  nodeCorr cols ct i (CertPf sq nd) ∧ tagOf cols i = SOME (2, v) ⇒
  ∃kl kr lp rp cf.
    childOrd ct i 0 = SOME kl ∧ childOrd ct i 1 = SOME kr ∧
    nodeReconF cols ct i kl = SOME lp ∧
    nodeReconF cols ct i kr = SOME rp ∧
    nd = CnCut cf lp rp
Proof
  rw[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> metis_tac[]
QED

Theorem nodeCorr_andi_inv:
  nodeCorr cols ct i (CertPf sq nd) ∧ tagOf cols i = SOME (3, v) ⇒
  ∃kl kr lp rp.
    childOrd ct i 0 = SOME kl ∧ childOrd ct i 1 = SOME kr ∧
    nodeReconF cols ct i kl = SOME lp ∧
    nodeReconF cols ct i kr = SOME rp ∧
    nd = CnAndI lp rp
Proof
  rw[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> metis_tac[]
QED

Theorem nodeCorr_ori_inv:
  nodeCorr cols ct i (CertPf sq nd) ∧ tagOf cols i = SOME (5, v) ⇒
  ∃k p ow.
    childOrd ct i 0 = SOME k ∧ nodeReconF cols ct i k = SOME p ∧
    (nd = CnOrIL p ow ∨ nd = CnOrIR p ow)
Proof
  rw[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> Cases_on ‘v = 0’ >> gvs[] >> metis_tac[]
QED

Theorem nodeCorr_eqelim_inv:
  nodeCorr cols ct i (CertPf sq nd) ∧ tagOf cols i = SOME (7, v) ⇒
  ∃ke kb ep bp w tT tU bf.
    childOrd ct i 0 = SOME ke ∧ childOrd ct i 1 = SOME kb ∧
    nodeReconF cols ct i ke = SOME ep ∧
    nodeReconF cols ct i kb = SOME bp ∧
    nd = CnEqElim ep bp w tT tU bf
Proof
  rw[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> metis_tac[]
QED

Theorem nodeCorr_arith_inv:
  nodeCorr cols ct i (CertPf sq nd) ∧ tagOf cols i = SOME (10, v) ⇒
  ∃k p tl tr b.
    childOrd ct i 0 = SOME k ∧ nodeReconF cols ct i k = SOME p ∧
    (nd = CnArithFold p tl tr b ∨ nd = CnArithUnfold p tl tr b)
Proof
  rw[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> Cases_on ‘v = 0’ >> gvs[] >> metis_tac[]
QED

Theorem nodeCorr_norm_inv:
  nodeCorr cols ct i (CertPf sq nd) ∧ tagOf cols i = SOME (12, v) ⇒
  ∃tl tr. nd = CnNorm tl tr
Proof
  rw[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> metis_tac[]
QED

Theorem nodeCorr_eqrefl_inv:
  nodeCorr cols ct i (CertPf sq nd) ∧ tagOf cols i = SOME (23, v) ⇒
  ∃t. nd = CnEqRefl t
Proof
  rw[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> metis_tac[]
QED

Theorem nodeCorr_eqsym_inv:
  nodeCorr cols ct i (CertPf sq nd) ∧ tagOf cols i = SOME (24, v) ⇒
  ∃k p tT tU.
    childOrd ct i 0 = SOME k ∧ nodeReconF cols ct i k = SOME p ∧
    nd = CnEqSym p tT tU
Proof
  rw[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> metis_tac[]
QED

Theorem nodeCorr_promise_inv:
  nodeCorr cols ct i (CertPf sq nd) ∧ tagOf cols i = SOME (25, v) ⇒
  ∃ks kc sp cp ctw stps ifc.
    childOrd ct i 0 = SOME ks ∧ childOrd ct i 1 = SOME kc ∧
    nodeReconF cols ct i ks = SOME sp ∧
    nodeReconF cols ct i kc = SOME cp ∧
    nd = CnPromise sp cp ctw (stepsToPath stps) ifc
Proof
  rw[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = SOME _’ mp_tac
  >> simp[Once nodeReconF_def]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> metis_tac[]
QED

Theorem clause_one_child:
  nodeArityAt cols i = 1 ∧ childOrd ct i 0 = SOME k ∧
  nodeCorr cols ct k p ⇒
  ((∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
          ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ws (INL pc)) ⇔
   checkPf1 ws (INL p))
Proof
  strip_tac >> eq_tac
  >- (disch_then (qspecl_then [‘0’, ‘k’] mp_tac) >> simp[]
      >> strip_tac
      >> metis_tac[nodeCorr_unique])
  >> rpt strip_tac
  >> ‘s = 0’ by (‘s < 1’ by gvs[] >> decide_tac)
  >> gvs[]
  >> metis_tac[]
QED

Theorem clause_two_children:
  nodeArityAt cols i = 2 ∧
  childOrd ct i 0 = SOME kl ∧ nodeCorr cols ct kl lp ∧
  childOrd ct i 1 = SOME kr ∧ nodeCorr cols ct kr rp ⇒
  ((∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
          ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ws (INL pc)) ⇔
   checkPf1 ws (INL lp) ∧ checkPf1 ws (INL rp))
Proof
  strip_tac >> eq_tac
  >- (strip_tac
      >> ‘∃pl. nodeCorr cols ct kl pl ∧ checkPf1 ws (INL pl)’
           by (first_x_assum irule >> qexists_tac ‘0’ >> simp[])
      >> ‘∃pr. nodeCorr cols ct kr pr ∧ checkPf1 ws (INL pr)’
           by (first_x_assum irule >> qexists_tac ‘1’ >> simp[])
      >> metis_tac[nodeCorr_unique])
  >> rpt strip_tac
  >> ‘s = 0 ∨ s = 1’ by (‘s < 2’ by gvs[] >> decide_tac)
  >> gvs[]
  >> metis_tac[]
QED

Theorem clause_children_list:
  nodeArityAt cols i = LENGTH comps ∧
  (∀j. j < LENGTH comps ⇒
       ∃c. childOrd ct i j = SOME c ∧ nodeCorr cols ct c (EL j comps)) ⇒
  ((∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
          ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ws (INL pc)) ⇔
   EVERY (λp. checkPf1 ws (INL p)) comps)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >> simp[listTheory.EVERY_EL]
      >> rpt strip_tac
      >> rename [‘n0 < LENGTH comps’]
      >> ‘∃c. childOrd ct i n0 = SOME c ∧ nodeCorr cols ct c (EL n0 comps)’
           by simp[]
      >> ‘∃pc. nodeCorr cols ct c pc ∧ checkPf1 ws (INL pc)’
           by (first_x_assum irule >> qexists_tac ‘n0’ >> simp[])
      >> ‘pc = EL n0 comps’ by metis_tac[nodeCorr_unique]
      >> gvs[])
  >> strip_tac >> rpt strip_tac
  >> ‘s < LENGTH comps’ by gvs[]
  >> ‘∃c'. childOrd ct i s = SOME c' ∧ nodeCorr cols ct c' (EL s comps)’
       by simp[]
  >> gvs[]
  >> qexists_tac ‘EL s comps’ >> simp[]
  >> gvs[listTheory.EVERY_EL]
QED

Theorem node_bicond_ax:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (0, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> ‘FST (THE (tagOf cols i)) ∈ {0:num}’ by simp[]
  >> drule_all famEq_ax_checkPf1
  >> disch_then (qspec_then ‘ct.ws’ assume_tac)
  >> ‘nodeArityAt cols i = ruleArity 0’
       by (irule nodeArityAt_rule >> simp[hasArityR_def] >> metis_tac[])
  >> gvs[ruleArity_def, checkNode_def]
  >> metis_tac[]
QED

Theorem node_bicond_weaken:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (1, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> ‘wf8 cols ct’ by gvs[wfColumns_def]
  >> drule_all nodeCorr_weaken_inv >> strip_tac >> gvs[]
  >> ‘nodeArityAt cols i = 1’
       by (‘nodeArityAt cols i = ruleArity 1’
             by (irule nodeArityAt_rule >> simp[hasArityR_def] >> metis_tac[])
           >> gvs[ruleArity_def])
  >> ‘k < i’ by (‘0 < nodeArityAt cols i’ by simp[]
                 >> metis_tac[childOrd_lt])
  >> ‘k < cols.nNodes’ by decide_tac
  >> ‘nodeCorr cols ct k p’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘FST (THE (tagOf cols i)) = 1’ by simp[]
  >> drule_all famEq_weaken >> strip_tac
  >> ‘(∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
            ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc)) ⇔
      checkPf1 ct.ws (INL p)’
       by (irule clause_one_child >> simp[] >> metis_tac[])
  >> simp[checkNode_def]
  >> metis_tac[armWeaken_faithful]
QED

Theorem node_bicond_cut:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (2, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> ‘wf8 cols ct’ by gvs[wfColumns_def]
  >> drule_all nodeCorr_cut_inv >> strip_tac >> gvs[]
  >> ‘nodeArityAt cols i = 2’
       by (‘nodeArityAt cols i = ruleArity 2’
             by (irule nodeArityAt_rule >> simp[hasArityR_def] >> metis_tac[])
           >> gvs[ruleArity_def])
  >> ‘kl < i’ by (‘0 < nodeArityAt cols i’ by simp[]
                  >> metis_tac[childOrd_lt])
  >> ‘kr < i’ by (‘1 < nodeArityAt cols i’ by simp[]
                  >> metis_tac[childOrd_lt])
  >> ‘kl < cols.nNodes ∧ kr < cols.nNodes’ by decide_tac
  >> ‘nodeCorr cols ct kl lp’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘nodeCorr cols ct kr rp’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘FST (THE (tagOf cols i)) = 2’ by simp[]
  >> drule_all famEq_cut >> strip_tac
  >> ‘(∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
            ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc)) ⇔
      checkPf1 ct.ws (INL lp) ∧ checkPf1 ct.ws (INL rp)’
       by (irule clause_two_children >> simp[] >> metis_tac[])
  >> simp[checkNode_def]
  >> metis_tac[armCut_faithful]
QED

Theorem node_bicond_andi:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (3, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> ‘wf8 cols ct’ by gvs[wfColumns_def]
  >> drule_all nodeCorr_andi_inv >> strip_tac >> gvs[]
  >> ‘nodeArityAt cols i = 2’
       by (‘nodeArityAt cols i = ruleArity 3’
             by (irule nodeArityAt_rule >> simp[hasArityR_def] >> metis_tac[])
           >> gvs[ruleArity_def])
  >> ‘kl < i’ by (‘0 < nodeArityAt cols i’ by simp[]
                  >> metis_tac[childOrd_lt])
  >> ‘kr < i’ by (‘1 < nodeArityAt cols i’ by simp[]
                  >> metis_tac[childOrd_lt])
  >> ‘kl < cols.nNodes ∧ kr < cols.nNodes’ by decide_tac
  >> ‘nodeCorr cols ct kl lp’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘nodeCorr cols ct kr rp’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘FST (THE (tagOf cols i)) = 3’ by simp[]
  >> drule_all famEq_andi >> strip_tac
  >> ‘(∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
            ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc)) ⇔
      checkPf1 ct.ws (INL lp) ∧ checkPf1 ct.ws (INL rp)’
       by (irule clause_two_children >> simp[] >> metis_tac[])
  >> simp[checkNode_def]
  >> metis_tac[armAndI_faithful]
QED

Theorem node_bicond_ande:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (4, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> ‘wf8 cols ct’ by gvs[wfColumns_def]
  >> ‘FST (THE (tagOf cols i)) ∈ {4:num}’ by simp[]
  >> drule_all famSlice_ande
  >> disch_then (qspec_then ‘ct.ws’ strip_assume_tac)
  >> ‘nodeArityAt cols i = 1’
       by (‘nodeArityAt cols i = ruleArity 4’
             by (irule nodeArityAt_rule >> simp[hasArityR_def] >> metis_tac[])
           >> gvs[ruleArity_def])
  >> ‘k < cols.nNodes’ by decide_tac
  >> ‘nodeCorr cols ct k p’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘(∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
            ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc)) ⇔
      checkPf1 ct.ws (INL p)’
       by (irule clause_one_child >> simp[] >> metis_tac[])
  >> simp[checkNode_def]
  >> metis_tac[]
QED

Theorem node_bicond_ori:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (5, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> ‘wf8 cols ct’ by gvs[wfColumns_def]
  >> drule_all nodeCorr_ori_inv >> strip_tac
  >> ‘nodeArityAt cols i = 1’
       by (‘nodeArityAt cols i = ruleArity 5’
             by (irule nodeArityAt_rule >> simp[hasArityR_def] >> metis_tac[])
           >> gvs[ruleArity_def])
  >> ‘k < i’ by (‘0 < nodeArityAt cols i’ by simp[]
                 >> metis_tac[childOrd_lt])
  >> ‘k < cols.nNodes’ by decide_tac
  >> ‘nodeCorr cols ct k p’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘FST (THE (tagOf cols i)) = 5’ by simp[]
  >> drule_all famEq_ori >> strip_tac
  >> ‘(∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
            ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc)) ⇔
      checkPf1 ct.ws (INL p)’
       by (irule clause_one_child >> simp[] >> metis_tac[])
  >> gvs[]
  >> simp[checkNode_def]
  >> metis_tac[armOrIL_faithful, armOrIR_faithful]
QED

Theorem node_bicond_ore:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (6, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> ‘wf8 cols ct’ by gvs[wfColumns_def]
  >> ‘FST (THE (tagOf cols i)) ∈ {6:num}’ by simp[]
  >> drule_all famEq_ore_slice
  >> disch_then (qspec_then ‘ct.ws’ strip_assume_tac)
  >> drule_all nodeCorr_ore_inv >> strip_tac
  >> gvs[]
  >> ‘nodeArityAt cols i = 2’
       by (‘nodeArityAt cols i = ruleArity 6’
             by (irule nodeArityAt_rule >> simp[hasArityR_def] >> metis_tac[])
           >> gvs[ruleArity_def])
  >> ‘kl < i’ by (‘0 < nodeArityAt cols i’ by simp[]
                  >> metis_tac[childOrd_lt])
  >> ‘kr < i’ by (‘1 < nodeArityAt cols i’ by simp[]
                  >> metis_tac[childOrd_lt])
  >> ‘kl < cols.nNodes ∧ kr < cols.nNodes’ by decide_tac
  >> ‘nodeCorr cols ct kl lp’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘nodeCorr cols ct kr rp’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘(∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
            ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc)) ⇔
      checkPf1 ct.ws (INL lp) ∧ checkPf1 ct.ws (INL rp)’
       by (irule clause_two_children >> simp[] >> metis_tac[])
  >> simp[checkNode_def]
  >> metis_tac[]
QED

Theorem node_bicond_eqelim:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (7, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> ‘wf8 cols ct’ by gvs[wfColumns_def]
  >> drule_all nodeCorr_eqelim_inv >> strip_tac >> gvs[]
  >> ‘nodeArityAt cols i = 2’
       by (‘nodeArityAt cols i = ruleArity 7’
             by (irule nodeArityAt_rule >> simp[hasArityR_def] >> metis_tac[])
           >> gvs[ruleArity_def])
  >> ‘ke < i’ by (‘0 < nodeArityAt cols i’ by simp[]
                  >> metis_tac[childOrd_lt])
  >> ‘kb < i’ by (‘1 < nodeArityAt cols i’ by simp[]
                  >> metis_tac[childOrd_lt])
  >> ‘ke < cols.nNodes ∧ kb < cols.nNodes’ by decide_tac
  >> ‘nodeCorr cols ct ke ep’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘nodeCorr cols ct kb bp’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘FST (THE (tagOf cols i)) = 7’ by simp[]
  >> drule_all famEq_eqelim >> strip_tac
  >> ‘(∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
            ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc)) ⇔
      checkPf1 ct.ws (INL ep) ∧ checkPf1 ct.ws (INL bp)’
       by (irule clause_two_children >> simp[] >> metis_tac[])
  >> simp[checkNode_def]
  >> metis_tac[armEqElim_faithful]
QED

Theorem node_bicond_convIntro:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (8, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> ‘wf8 cols ct’ by gvs[wfColumns_def]
  >> ‘FST (THE (tagOf cols i)) ∈ {8:num}’ by simp[]
  >> drule_all famSlice_convIntro >> strip_tac
  >> ‘nodeArityAt cols i = 1’
       by (‘nodeArityAt cols i = ruleArity 8’
             by (irule nodeArityAt_rule >> simp[hasArityR_def] >> metis_tac[])
           >> gvs[ruleArity_def])
  >> ‘k < cols.nNodes’ by decide_tac
  >> ‘nodeCorr cols ct k p’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘(∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
            ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc)) ⇔
      checkPf1 ct.ws (INL p)’
       by (irule clause_one_child >> simp[] >> metis_tac[])
  >> simp[checkNode_def]
  >> metis_tac[]
QED

Theorem node_bicond_convElim:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (9, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> ‘wf8 cols ct’ by gvs[wfColumns_def]
  >> ‘FST (THE (tagOf cols i)) ∈ {9:num}’ by simp[]
  >> drule_all famSlice_convElim
  >> disch_then (qspec_then ‘ct.ws’ strip_assume_tac)
  >> ‘nodeArityAt cols i = 1’
       by (‘nodeArityAt cols i = ruleArity 9’
             by (irule nodeArityAt_rule >> simp[hasArityR_def] >> metis_tac[])
           >> gvs[ruleArity_def])
  >> ‘k < cols.nNodes’ by decide_tac
  >> ‘nodeCorr cols ct k p’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘(∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
            ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc)) ⇔
      checkPf1 ct.ws (INL p)’
       by (irule clause_one_child >> simp[] >> metis_tac[])
  >> simp[checkNode_def]
  >> metis_tac[]
QED

Theorem node_bicond_arith:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (10, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> ‘wf8 cols ct’ by gvs[wfColumns_def]
  >> drule_all nodeCorr_arith_inv >> strip_tac
  >> ‘nodeArityAt cols i = 1’
       by (‘nodeArityAt cols i = ruleArity 10’
             by (irule nodeArityAt_rule >> simp[hasArityR_def] >> metis_tac[])
           >> gvs[ruleArity_def])
  >> ‘k < i’ by (‘0 < nodeArityAt cols i’ by simp[]
                 >> metis_tac[childOrd_lt])
  >> ‘k < cols.nNodes’ by decide_tac
  >> ‘nodeCorr cols ct k p’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘FST (THE (tagOf cols i)) = 10’ by simp[]
  >> drule_all famEq_arith >> strip_tac
  >> ‘(∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
            ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc)) ⇔
      checkPf1 ct.ws (INL p)’
       by (irule clause_one_child >> simp[] >> metis_tac[])
  >> gvs[]
  >> simp[checkNode_def]
  >> metis_tac[armArithFold_faithful, armArithUnfold_faithful]
QED

Theorem node_bicond_berncone:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (11, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> ‘wf8 cols ct’ by gvs[wfColumns_def]
  >> ‘FST (THE (tagOf cols i)) ∈ {11:num}’ by simp[]
  >> drule_all famSlice_berncone
  >> disch_then (qspec_then ‘ct.ws’ strip_assume_tac)
  >> ‘nodeArityAt cols i = 1’
       by (‘nodeArityAt cols i = ruleArity 11’
             by (irule nodeArityAt_rule >> simp[hasArityR_def] >> metis_tac[])
           >> gvs[ruleArity_def])
  >> ‘k < cols.nNodes’ by decide_tac
  >> ‘nodeCorr cols ct k p’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘(∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
            ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc)) ⇔
      checkPf1 ct.ws (INL p)’
       by (irule clause_one_child >> simp[] >> metis_tac[])
  >> simp[checkNode_def]
  >> metis_tac[]
QED

Theorem node_bicond_norm:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (12, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> drule_all nodeCorr_norm_inv >> strip_tac
  >> ‘nodeArityAt cols i = ruleArity 12’
       by (irule nodeArityAt_rule >> simp[hasArityR_def] >> metis_tac[])
  >> gvs[ruleArity_def]
  >> ‘FST (THE (tagOf cols i)) = 12’ by simp[]
  >> drule_all famEq_norm >> strip_tac
  >> simp[checkNode_def, armNorm_faithful]
QED

Theorem node_bicond_farkas:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (14, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> ‘FST (THE (tagOf cols i)) = 14’ by simp[]
  >> drule_all famSlice_farkas >> strip_tac
  >> ‘nodeArityAt cols i = ruleArity 14’
       by (irule nodeArityAt_rule >> simp[hasArityR_def] >> metis_tac[])
  >> gvs[ruleArity_def, checkNode_def]
  >> metis_tac[]
QED

Theorem node_bicond_eqrefl:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (23, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> drule_all nodeCorr_eqrefl_inv >> strip_tac
  >> ‘nodeArityAt cols i = ruleArity 23’
       by (irule nodeArityAt_rule >> simp[hasArityR_def] >> metis_tac[])
  >> gvs[ruleArity_def]
  >> ‘FST (THE (tagOf cols i)) = 23’ by simp[]
  >> drule_all famEq_eqrefl >> strip_tac
  >> simp[checkNode_def, armEqRefl_faithful]
QED

Theorem node_bicond_eqsym:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (24, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> ‘wf8 cols ct’ by gvs[wfColumns_def]
  >> drule_all nodeCorr_eqsym_inv >> strip_tac >> gvs[]
  >> ‘nodeArityAt cols i = 1’
       by (‘nodeArityAt cols i = ruleArity 24’
             by (irule nodeArityAt_rule >> simp[hasArityR_def] >> metis_tac[])
           >> gvs[ruleArity_def])
  >> ‘k < i’ by (‘0 < nodeArityAt cols i’ by simp[]
                 >> metis_tac[childOrd_lt])
  >> ‘k < cols.nNodes’ by decide_tac
  >> ‘nodeCorr cols ct k p’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘FST (THE (tagOf cols i)) = 24’ by simp[]
  >> drule_all famEq_eqsym >> strip_tac
  >> ‘(∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
            ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc)) ⇔
      checkPf1 ct.ws (INL p)’
       by (irule clause_one_child >> simp[] >> metis_tac[])
  >> simp[checkNode_def]
  >> metis_tac[armEqSym_faithful]
QED

Theorem node_bicond_promise:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (25, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> ‘wf8 cols ct’ by gvs[wfColumns_def]
  >> drule_all nodeCorr_promise_inv >> strip_tac >> gvs[]
  >> ‘nodeArityAt cols i = 2’
       by (‘nodeArityAt cols i = ruleArity 25’
             by (irule nodeArityAt_rule >> simp[hasArityR_def] >> metis_tac[])
           >> gvs[ruleArity_def])
  >> ‘ks < i’ by (‘0 < nodeArityAt cols i’ by simp[]
                  >> metis_tac[childOrd_lt])
  >> ‘kc < i’ by (‘1 < nodeArityAt cols i’ by simp[]
                  >> metis_tac[childOrd_lt])
  >> ‘ks < cols.nNodes ∧ kc < cols.nNodes’ by decide_tac
  >> ‘nodeCorr cols ct ks sp’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘nodeCorr cols ct kc cp’
       by (irule child_reanchor >> simp[] >> metis_tac[])
  >> ‘FST (THE (tagOf cols i)) = 25’ by simp[]
  >> drule_all famEq_promise >> strip_tac
  >> ‘(∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
            ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc)) ⇔
      checkPf1 ct.ws (INL sp) ∧ checkPf1 ct.ws (INL cp)’
       by (irule clause_two_children >> simp[] >> metis_tac[])
  >> simp[checkNode_def]
  >> metis_tac[armPromise_faithful]
QED

Theorem node_bicond_syz:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ct.ws, pfP) ∧
  i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ∧
  tagOf cols i = SOME (26, v) ⇒
  (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
     checkNode cols ct i ∧
     ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
           ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  strip_tac
  >> ‘wf8 cols ct’ by gvs[wfColumns_def]
  >> ‘FST (THE (tagOf cols i)) = 26’ by simp[]
  >> drule_all nodeCorr_syz_shape >> strip_tac
  >> gvs[]

  >> ‘FST (THE (tagOf cols i)) = 26’ by simp[]
  >> drule_all nodeCorr_syz_children >> strip_tac
  >> drule_all famSlice_syz >> strip_tac
  >> ‘nodeArityAt cols i = LENGTH comps’ by metis_tac[nodeArityAt_syz]
  >> ‘∀j. j < LENGTH comps ⇒
          ∃c. childOrd ct i j = SOME c ∧ nodeCorr cols ct c (EL j comps)’
       by (rpt strip_tac
           >> ‘∃c. childOrd ct i j = SOME c ∧
                   nodeReconF cols ct i c = SOME (EL j comps)’
                by (first_x_assum irule >> gvs[])
           >> ‘j < nodeArityAt cols i’ by gvs[]
           >> ‘c < i’ by metis_tac[childOrd_lt]
           >> ‘c < cols.nNodes’ by decide_tac
           >> ‘nodeCorr cols ct c (EL j comps)’
                by (irule child_reanchor >> simp[] >> metis_tac[])
           >> metis_tac[])
  >> ‘(∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
            ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc)) ⇔
      EVERY (λp. checkPf1 ct.ws (INL p)) comps’
       by (irule clause_children_list >> simp[])
  >> simp[checkNode_def]
  >> metis_tac[]
QED

Theorem node_bicond:
  ∀i sq nd.
    wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
    parseCert (cols.hdrImage ++ rest) = SOME (ws, pfP) ∧
    i < cols.nNodes ∧ nodeCorr cols ct i (CertPf sq nd) ⇒
    (checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
       checkNode cols ct i ∧
       ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
             ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc))
Proof
  rpt gen_tac >> strip_tac
  >> ‘ws = ct.ws’ by metis_tac[frWsEq]
  >> pop_assum SUBST_ALL_TAC

  >> drule nodeCorr_tag >> strip_tac
  >> gvs[]
  >| [metis_tac[node_bicond_ax],
      metis_tac[node_bicond_weaken],
      metis_tac[node_bicond_cut],
      metis_tac[node_bicond_andi],
      metis_tac[node_bicond_ande],
      metis_tac[node_bicond_ori],
      metis_tac[node_bicond_ore],
      metis_tac[node_bicond_eqelim],
      metis_tac[node_bicond_convIntro],
      metis_tac[node_bicond_convElim],
      metis_tac[node_bicond_arith],
      metis_tac[node_bicond_berncone],
      metis_tac[node_bicond_norm],
      metis_tac[node_bicond_farkas],
      metis_tac[node_bicond_eqrefl],
      metis_tac[node_bicond_eqsym],
      metis_tac[node_bicond_promise],
      metis_tac[node_bicond_syz]]
QED

Theorem joins_imp_walk:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ws, pfP) ∧
  (∀j. j < cols.nNodes ⇒ checkNode cols ct j) ⇒
  ∀i pf. i < cols.nNodes ∧ nodeCorr cols ct i pf ⇒
         checkPf1 ct.ws (INL pf)
Proof
  strip_tac
  >> gen_tac
  >> completeInduct_on ‘i’
  >> rpt strip_tac
  >> Cases_on ‘pf’
  >> rename [‘CertPf sq nd’]
  >> ‘wf8 cols ct’ by gvs[wfColumns_def]
  >> ‘checkPf1 ct.ws (INL (CertPf sq nd)) ⇔
        checkNode cols ct i ∧
        ∀s c. s < nodeArityAt cols i ∧ childOrd ct i s = SOME c ⇒
              ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc)’
       by (irule node_bicond >> simp[] >> metis_tac[])
  >> simp[]
  >> rpt strip_tac
  >> ‘c < i’ by metis_tac[childOrd_lt]
  >> ‘c < cols.nNodes’ by decide_tac
  >> ‘∃pc. nodeCorr cols ct c pc’
       by (qpat_x_assum ‘reconTotal _ _’ mp_tac >> simp[reconTotal_def])
  >> qexists_tac ‘pc’ >> simp[]
  >> first_x_assum (qspec_then ‘c’ mp_tac)
  >> impl_tac >- simp[]
  >> disch_then (qspec_then ‘pc’ mp_tac)
  >> simp[]
QED

Theorem rpnFold_inv:
  ∀n cols rows stk.
    FOLDL (rpnStep cols) (SOME ([], [])) (rangeL n) = SOME (rows, stk) ⇒
    LENGTH rows = n ∧
    (∀x. MEM x stk ⇒ x < n) ∧
    (0 < n ⇒ stk ≠ [] ∧ HD stk = n − 1) ∧
    (∀i. i < n ⇒ LENGTH (EL i rows) = nodeArityAt cols i) ∧
    (∀i c. i < n ∧ MEM c (EL i rows) ⇒ c < i) ∧
    (∀j. j < n ⇒ MEM j stk ∨ ∃q. q < n ∧ MEM j (EL q rows))
Proof
  Induct
  >- (rpt gen_tac >> simp[rangeL_def] >> strip_tac >> gvs[])
  >> rpt gen_tac
  >> simp[rangeL_def, GSYM listTheory.SNOC_APPEND, listTheory.FOLDL_SNOC]
  >> Cases_on ‘FOLDL (rpnStep cols) (SOME ([], [])) (rangeL n)’
  >- simp[rpnStep_def]
  >> rename [‘_ = SOME acc’] >> Cases_on ‘acc’
  >> rename [‘FOLDL _ _ _ = SOME (rows0, stk0)’]
  >> simp[rpnStep_def, AllCaseEqs()]
  >> strip_tac >> gvs[]
  >> first_x_assum (qspecl_then [‘cols’, ‘rows0’, ‘stk0’] mp_tac)
  >> simp[] >> strip_tac

  >> rpt conj_tac
  >- (
      rpt strip_tac >> gvs[]
      >> ‘MEM x stk0’ by metis_tac[rich_listTheory.MEM_DROP_IMP]
      >> res_tac >> decide_tac)
  >- (
      rpt strip_tac
      >> Cases_on ‘i < n’
      >- simp[rich_listTheory.EL_APPEND1]
      >> ‘i = n’ by decide_tac
      >> gvs[rich_listTheory.EL_APPEND2, listTheory.LENGTH_TAKE])
  >- (
      rpt strip_tac
      >> Cases_on ‘i < n’
      >- (gvs[rich_listTheory.EL_APPEND1] >> res_tac >> simp[])
      >> ‘i = n’ by decide_tac
      >> gvs[rich_listTheory.EL_APPEND2, listTheory.MEM_REVERSE]
      >> ‘MEM c stk0’ by metis_tac[rich_listTheory.MEM_TAKE]
      >> res_tac >> decide_tac)
  >>
     rpt strip_tac
  >> Cases_on ‘j = n’ >- simp[]
  >> ‘j < n’ by decide_tac
  >> ‘MEM j stk0 ∨ ∃q. q < n ∧ MEM j (EL q rows0)’ by metis_tac[]
  >- (
      ‘MEM j (TAKE (nodeArityAt cols n) stk0) ∨
       MEM j (DROP (nodeArityAt cols n) stk0)’
        by metis_tac[listTheory.MEM_APPEND, listTheory.TAKE_DROP]
      >- (‘n < SUC n’ by decide_tac
          >> ‘MEM j (EL n (rows0 ++
                           [REVERSE (TAKE (nodeArityAt cols n) stk0)]))’
               by simp[rich_listTheory.EL_APPEND2, listTheory.MEM_REVERSE]
          >> metis_tac[])
      >> metis_tac[])
  >> ‘q < SUC n’ by decide_tac
  >> ‘MEM j (EL q (rows0 ++ [REVERSE (TAKE (nodeArityAt cols n) stk0)]))’
       by simp[rich_listTheory.EL_APPEND1]
  >> metis_tac[]
QED

Theorem explChildren_length:
  ∀a cols nidx myoff base cs.
    explChildren cols nidx myoff base a = SOME cs ⇒ LENGTH cs = a
Proof
  Induct >> simp[explChildren_def]
  >> rpt gen_tac
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> res_tac >> gvs[]
QED

Theorem explFold_inv:
  ∀n cols noffs nidx rows tb.
    FOLDL (explStep cols noffs nidx) (SOME ([], 0)) (rangeL n)
      = SOME (rows, tb) ⇒
    LENGTH rows = n ∧
    (∀i. i < n ⇒ LENGTH (EL i rows) = nodeArityAt cols i)
Proof
  Induct
  >- (rpt gen_tac >> simp[rangeL_def] >> strip_tac >> gvs[])
  >> rpt gen_tac
  >> simp[rangeL_def, GSYM listTheory.SNOC_APPEND, listTheory.FOLDL_SNOC]
  >> Cases_on ‘FOLDL (explStep cols noffs nidx) (SOME ([], 0)) (rangeL n)’
  >- simp[explStep_def]
  >> rename [‘_ = SOME acc’] >> Cases_on ‘acc’
  >> rename [‘FOLDL _ _ _ = SOME (rows0, tb0)’]
  >> simp[explStep_def]
  >> simp[AllCaseEqs(), PULL_EXISTS]

  >> rpt gen_tac >> strip_tac >> gvs[]
  >> first_x_assum (qspecl_then [‘cols’, ‘noffs’, ‘nidx’, ‘rows0’, ‘tb0’]
                    mp_tac)
  >> simp[] >> strip_tac

  >> rpt strip_tac
  >> Cases_on ‘i < n’
  >- simp[rich_listTheory.EL_APPEND1]
  >> ‘i = n’ by decide_tac
  >> gvs[rich_listTheory.EL_APPEND2]
  >> metis_tac[explChildren_length]
QED

Theorem mkCtx_childTbl:
  mkCtx cols = SOME ct ⇒
  (cols.topoMode = 0 ⇒
     ∃rows stk. rpnReplay cols = SOME (rows, stk) ∧ ct.childTbl = rows) ∧
  (cols.topoMode ≠ 0 ⇒
     cols.topoMode = 1 ∧
     ∃nst rows tb.
       explRows cols nst.noffs nst.nidx = SOME rows ∧ ct.childTbl = rows)
Proof
  simp[mkCtx_def, AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[]
  >> metis_tac[]
QED

Theorem parenthood:
  mkCtx cols = SOME ct ∧ wf5 cols ct ∧
  j < cols.nNodes ∧ j ≠ cols.nNodes − 1 ⇒
  ∃p s. p < cols.nNodes ∧ j < p ∧ s < nodeArityAt cols p ∧
        childOrd ct p s = SOME j
Proof
  strip_tac
  >> drule mkCtx_childTbl >> strip_tac
  >> qpat_x_assum ‘wf5 _ _’ mp_tac >> simp[wf5_def, LET_THM]
  >> Cases_on ‘cols.topoMode = 0’ >> gvs[]
  >- (
      strip_tac
      >> gvs[rpnReplay_def]
      >> drule rpnFold_inv >> strip_tac
      >> ‘0 < cols.nNodes’ by decide_tac
      >> ‘stk = [cols.nNodes − 1]’
           by (Cases_on ‘stk’ >> gvs[]
               >> Cases_on ‘t’ >> gvs[])
      >> first_x_assum (qspec_then ‘j’ mp_tac) >> simp[]
      >> strip_tac >> gvs[]
      >> ‘∃s. s < LENGTH (EL q ct.childTbl) ∧ EL s (EL q ct.childTbl) = j’
           by metis_tac[listTheory.MEM_EL]
      >> ‘j < q’ by metis_tac[]
      >> qexistsl_tac [‘q’, ‘s’]
      >> gvs[childOrd_def, listTheory.oEL_THM])
  >>
     strip_tac
  >> gvs[explRows_def, AllCaseEqs()]
  >> drule explFold_inv >> strip_tac
  >> ‘j < cols.nNodes − 1’ by decide_tac
  >> ‘MEM j (FLAT ct.childTbl)’
       by (qpat_x_assum ‘EVERY _ (rangeL (cols.nNodes − 1))’ mp_tac
           >> simp[listTheory.EVERY_MEM, MEM_rangeL]
           >> disch_then (qspec_then ‘j’ mp_tac) >> simp[]
           >> strip_tac
           >> spose_not_then assume_tac
           >> ‘FILTER (λx. x = j) (FLAT ct.childTbl) = []’
                by (simp[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM]
                    >> metis_tac[])
           >> gvs[])
  >> ‘∃row. MEM row ct.childTbl ∧ MEM j row’
       by metis_tac[listTheory.MEM_FLAT]
  >> ‘∃q. q < LENGTH ct.childTbl ∧ EL q ct.childTbl = row’
       by metis_tac[listTheory.MEM_EL]
  >> ‘∃s. s < LENGTH row ∧ EL s row = j’ by metis_tac[listTheory.MEM_EL]
  >> ‘q < cols.nNodes’ by gvs[]
  >> ‘EVERY (λc. c < q) (getD ct.childTbl q [])’
       by (qpat_x_assum ‘EVERY _ (rangeL cols.nNodes)’ mp_tac
           >> simp[listTheory.EVERY_MEM, MEM_rangeL])
  >> ‘getD ct.childTbl q [] = EL q ct.childTbl’
       by (irule getD_EL >> simp[])
  >> ‘j < q’ by (gvs[listTheory.EVERY_MEM] >> metis_tac[listTheory.MEM_EL])
  >> ‘s < nodeArityAt cols q’ by metis_tac[]
  >> qexistsl_tac [‘q’, ‘s’]
  >> simp[childOrd_def, listTheory.oEL_THM]
QED

Theorem walk_imp_joins:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ws, pfP) ∧
  nodeCorr cols ct (cols.nNodes − 1) pfR ∧
  checkPf1 ct.ws (INL pfR) ⇒
  ∀j. j < cols.nNodes ⇒ checkNode cols ct j
Proof
  strip_tac
  >> ‘wf5 cols ct ∧ wf8 cols ct’ by gvs[wfColumns_def]

  >> ‘∀k j. j + k = cols.nNodes − 1 ∧ j < cols.nNodes ⇒
            ∃pfj. nodeCorr cols ct j pfj ∧ checkPf1 ct.ws (INL pfj)’
       by (gen_tac
           >> completeInduct_on ‘k’
           >> rpt strip_tac
           >> Cases_on ‘j = cols.nNodes − 1’
           >- (qexists_tac ‘pfR’ >> gvs[])
           >> ‘∃p s. p < cols.nNodes ∧ j < p ∧ s < nodeArityAt cols p ∧
                     childOrd ct p s = SOME j’
                by (irule parenthood >> simp[])
           >> ‘∃pfp. nodeCorr cols ct p pfp ∧ checkPf1 ct.ws (INL pfp)’
                by (first_x_assum (qspec_then ‘cols.nNodes − 1 − p’ mp_tac)
                    >> impl_tac >- decide_tac
                    >> disch_then (qspec_then ‘p’ mp_tac)
                    >> impl_tac >- decide_tac
                    >> strip_tac >> metis_tac[])
           >> Cases_on ‘pfp’
           >> rename [‘nodeCorr cols ct p (CertPf sqp ndp)’]
           >> ‘checkPf1 ct.ws (INL (CertPf sqp ndp)) ⇔
                 checkNode cols ct p ∧
                 ∀s c. s < nodeArityAt cols p ∧ childOrd ct p s = SOME c ⇒
                       ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc)’
                by (irule node_bicond >> simp[] >> metis_tac[])
           >> gvs[]
           >> first_x_assum (qspecl_then [‘s’, ‘j’] mp_tac)
           >> simp[])
  >> rpt strip_tac
  >> ‘∃pfj. nodeCorr cols ct j pfj ∧ checkPf1 ct.ws (INL pfj)’
       by (first_x_assum (qspecl_then [‘cols.nNodes − 1 − j’, ‘j’] mp_tac)
           >> impl_tac >- decide_tac
           >> simp[])
  >> Cases_on ‘pfj’
  >> rename [‘nodeCorr cols ct j (CertPf sqj ndj)’]
  >> ‘checkPf1 ct.ws (INL (CertPf sqj ndj)) ⇔
        checkNode cols ct j ∧
        ∀s c. s < nodeArityAt cols j ∧ childOrd ct j s = SOME c ⇒
              ∃pc. nodeCorr cols ct c pc ∧ checkPf1 ct.ws (INL pc)’
       by (irule node_bicond >> simp[] >> metis_tac[])
  >> gvs[]
QED

Theorem checkJoins_eq_checkPf:
  mkCtx cols = SOME ct ∧ wfColumns cols ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ws, pf) ⇒
  (checkJoins cols = SOME T ⇔
   ∃pfR. nodeCorr cols ct (cols.nNodes − 1) pfR ∧ checkPf ws pfR)
Proof
  strip_tac
  >> ‘ws = ct.ws’ by metis_tac[frWsEq]
  >> pop_assum SUBST_ALL_TAC
  >> ‘0 < cols.nNodes’ by gvs[wfColumns_def, wf1_def]
  >> simp[checkJoins_def, checkPf_def, checkNodes_all]
  >> eq_tac
  >- (
      strip_tac
      >> ‘∃pfR. nodeCorr cols ct (cols.nNodes − 1) pfR’
           by (qpat_x_assum ‘reconTotal _ _’ mp_tac
               >> simp[reconTotal_def]
               >> disch_then (qspec_then ‘cols.nNodes − 1’ mp_tac)
               >> simp[])
      >> qexists_tac ‘pfR’ >> simp[]
      >> ‘cols.nNodes − 1 < cols.nNodes’ by decide_tac
      >> metis_tac[joins_imp_walk])
  >>
     strip_tac
  >> simp[]
  >> metis_tac[walk_imp_joins]
QED

Theorem checkJoins_eq_checkPf_root:
  mkCtx cols = SOME ct ∧ wfColumns cols ct ∧ reconTotal cols ct ∧
  parseCert (cols.hdrImage ++ rest) = SOME (ws, pf) ∧
  nodeCorr cols ct (cols.nNodes − 1) pf ⇒
  (checkJoins cols = SOME T ⇔ checkPf ws pf)
Proof
  strip_tac
  >> drule_all checkJoins_eq_checkPf >> strip_tac
  >> simp[]
  >> eq_tac
  >- (strip_tac >> gvs[]
      >> ‘pfR = pf’ by metis_tac[nodeCorr_unique]
      >> gvs[])
  >> strip_tac
  >> qexists_tac ‘pf’ >> simp[]
QED

Theorem checkJoins_NONE:
  checkJoins cols = NONE ⇔ mkCtx cols = NONE
Proof
  simp[checkJoins_def, AllCaseEqs()]
QED

Theorem checkJoins_reject_wf:
  mkCtx cols = SOME ct ∧ ¬wfColumns cols ct ⇒ checkJoins cols = SOME F
Proof
  simp[checkJoins_def]
QED

Theorem demo_checkJoins:
  checkJoins demoCols = SOME F
Proof
  EVAL_TAC
QED

Theorem oreDemo_checkJoins:
  checkJoins oreDemoCols = SOME F
Proof
  EVAL_TAC
QED
