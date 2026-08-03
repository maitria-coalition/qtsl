(*
  Family F1 (Ax, tag 0): the per-node column-side check checkFam_ax
  and its equivalence lemma famEq_ax against the reference checker's Ax
  arm. Includes the sph-expansion analysis (expandSph at the top symbol
  is not injective; the witness theorem and the fuel-indexed
  formula-materialization bridge live here).
*)
Theory qtsl_fam_ax
Ancestors
  rat integer mlstring mllist qtsl_dyadic qtsl_qarith qtsl_catalogue
  qtsl_cert qtsl_cols qtsl_wf
Libs
  preamble

Definition checkFam_ax_def:
  checkFam_ax (cols:columns) (ct:ctx) (i:num) ⇔
    case conclRef cols ct i of
    | NONE => F
    | SOME cj =>
      case poolTagAt cols ct cj of
      | NONE => F
      | SOME t =>
        if t ≠ (48:num) then F else
        case poolField cols ct cj 0 of
        | NONE => F
        | SOME preR =>
          case poolField cols ct cj 1 of
          | NONE => F
          | SOME postR =>
            if preR = postR then T
            else
              case pv cols ct cj of
              | SOME (PJudg prew postw) =>
                  (expandSph FTt prew = expandSph FTt postw)
              | _ => F
End

Theorem expandSph_FTt_not_injective:
  expandSph FTt FwSpH = expandSph FTt FwTt ∧ FwSpH ≠ FwTt
Proof
  simp[expandSph_def]
QED

Theorem pv_judg_fields:
  pv cols ct cj = SOME (PJudg prew postw) ⇒
  ∃j preR postR.
    ALOOKUP ct.poolIdx cj = SOME j ∧
    oEL j cols.poolTag = SOME (48:num) ∧
    refAt cols ct j 0 = SOME preR ∧
    refAt cols ct j 1 = SOME postR ∧
    pvF cols ct j preR = SOME (PFormula prew) ∧
    pvF cols ct j postR = SOME (PFormula postw) ∧
    fwNoSph postw
Proof
  strip_tac
  >> gvs[pv_def, AllCaseEqs()]
  >> qpat_x_assum ‘pvF _ _ _ _ = _’ mp_tac
  >> simp[pvF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS, LET_THM]
  >> rpt strip_tac >> gvs[]
  >> metis_tac[]
QED

Theorem pv_judg_kit:
  pv cols ct cj = SOME (PJudg prew postw) ⇒
  ∃preR postR.
    poolTagAt cols ct cj = SOME (48:num) ∧
    poolField cols ct cj 0 = SOME preR ∧
    poolField cols ct cj 1 = SOME postR ∧
    (preR = postR ⇒ prew = postw)
Proof
  strip_tac
  >> drule pv_judg_fields
  >> strip_tac
  >> qexists_tac ‘preR’ >> qexists_tac ‘postR’
  >> simp[poolTagAt_def, poolField_def, poolRefCnt_def]
  >> rpt strip_tac >> gvs[]
QED

Theorem nodeCorr_ax_inv:
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) ∈ {0} ⇒
  ∃cj prew postw.
    conclRef cols ct i = SOME cj ∧
    pv cols ct cj = SOME (PJudg prew postw) ∧
    sq = judgSeq FTt prew postw ∧
    nd = CnAx
Proof
  strip_tac
  >> gvs[nodeCorr_def]
  >> qpat_x_assum ‘nodeReconF _ _ _ _ = _’ mp_tac
  >> simp[nodeReconF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS, LET_THM]
  >> rpt strip_tac >> gvs[]
  >> metis_tac[]
QED

Theorem famEq_ax:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) ∈ {0}
  ⇒
  (checkFam_ax cols ct i ⇔ (sq.pre = sq.post))
Proof
  strip_tac
  >> drule_all nodeCorr_ax_inv
  >> strip_tac
  >> gvs[]
  >> drule pv_judg_kit
  >> strip_tac
  >> simp[checkFam_ax_def, judgSeq_def]
  >> Cases_on ‘preR = postR’ >> gvs[]
QED

Theorem famEq_ax_shape:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) ∈ {0}
  ⇒
  nd = CnAx
Proof
  strip_tac
  >> drule_all nodeCorr_ax_inv
  >> strip_tac
  >> simp[]
QED

Theorem famEq_ax_checkPf1:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) ∈ {0}
  ⇒
  (checkFam_ax cols ct i ⇔ checkPf1 ws (INL (CertPf sq nd)))
Proof
  strip_tac
  >> drule_all famEq_ax_shape >> strip_tac
  >> drule_all famEq_ax >> strip_tac
  >> gvs[Once checkPf1_def]
QED

Theorem pvF_fuel_mono:
  ∀f cols ct off x f2.
    pvF cols ct f off = SOME x ∧ f ≤ f2 ⇒
    pvF cols ct f2 off = SOME x
Proof
  Induct >- simp[pvF_def]
  >> rpt gen_tac >> strip_tac
  >> Cases_on ‘f2’ >- gvs[]
  >> rename [‘SUC f ≤ SUC f2’]
  >> ‘f ≤ f2’ by decide_tac
  >> qpat_x_assum ‘pvF _ _ (SUC f) _ = _’ mp_tac
  >> simp[pvF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS, LET_THM]
  >> rpt strip_tac >> gvs[]
  >> res_tac >> gvs[]
QED

Theorem pvF_agree:
  pvF cols ct f1 off = SOME x ∧ pvF cols ct f2 off = SOME y ⇒ x = y
Proof
  strip_tac
  >> ‘f1 ≤ f2 ∨ f2 ≤ f1’ by decide_tac
  >> metis_tac[pvF_fuel_mono, optionTheory.SOME_11]
QED

Theorem pv_pvF_agree:
  pv cols ct off = SOME x ∧ pvF cols ct f off = SOME y ⇒ x = y
Proof
  simp[pv_def, AllCaseEqs()] >> rpt strip_tac >> metis_tac[pvF_agree]
QED

Theorem pv_judg_sides_agree:
  pv cols ct cj = SOME (PJudg prew postw) ∧
  poolField cols ct cj 0 = SOME preR ∧
  poolField cols ct cj 1 = SOME postR ∧
  pv cols ct preR = SOME x ∧
  pv cols ct postR = SOME y ⇒
  x = PFormula prew ∧ y = PFormula postw
Proof
  strip_tac
  >> drule pv_judg_fields >> strip_tac
  >> gvs[poolField_def, poolTagAt_def, poolRefCnt_def, AllCaseEqs()]
  >> metis_tac[pv_pvF_agree]
QED

Theorem pvEq_refl_fastpath:
  pv cols ct r = SOME x ⇒ pvEq cols ct r r = SOME T
Proof
  rw[pvEq_def]
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

