(*
  Family F1 (Ax) successor theory: the pvEq alignment consumers and
  the arm factoring against the reference checker, banked separately
  from the proof-heavy parent so the iterating lemmas rebuild in
  seconds.
*)
Theory qtsl_fam_axEq
Ancestors
  rat integer mlstring mllist qtsl_dyadic qtsl_qarith qtsl_catalogue
  qtsl_cert qtsl_cols qtsl_wf qtsl_fam_ax
Libs
  preamble

Theorem pvEq_ax_sound:
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) ∈ {0} ∧
  conclRef cols ct i = SOME cj ∧
  poolField cols ct cj 0 = SOME preR ∧
  poolField cols ct cj 1 = SOME postR ∧
  pvEq cols ct preR postR = SOME T ⇒
  (sq.pre = sq.post) ∧ checkFam_ax cols ct i
Proof
  strip_tac
  >> drule_all nodeCorr_ax_inv >> strip_tac
  >> gvs[]
  >> qpat_x_assum ‘pvEq _ _ _ _ = _’ mp_tac
  >> simp[pvEq_def, AllCaseEqs(), PULL_EXISTS]
  >> rpt gen_tac >> strip_tac
  >> drule_all pv_judg_sides_agree >> strip_tac
  >> gvs[]
  >> conj_tac >- simp[judgSeq_def]
  >> drule pv_judg_kit >> strip_tac
  >> gvs[]
  >> simp[checkFam_ax_def]
  >> Cases_on ‘preR = postR’ >> gvs[]
QED

Theorem pvEq_ax_exact_noSph:
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) ∈ {0} ∧
  conclRef cols ct i = SOME cj ∧
  poolField cols ct cj 0 = SOME preR ∧
  poolField cols ct cj 1 = SOME postR ∧
  pv cols ct preR = SOME (PFormula a) ∧ fwNoSph a ∧
  pv cols ct postR = SOME (PFormula b) ⇒
  pvEq cols ct preR postR = SOME (sq.pre = sq.post)
Proof
  strip_tac
  >> drule_all nodeCorr_ax_inv >> strip_tac
  >> gvs[]
  >> drule pv_judg_fields >> strip_tac
  >> drule_all pv_judg_sides_agree >> strip_tac
  >> gvs[]
  >> simp[pvEq_def, judgSeq_def]
  >> metis_tac[expandSph_inj_noSph]
QED

Definition checkPf1_ax_arm_def:
  checkPf1_ax_arm (ws:tensortype list) (sq:sequent) (nd:cnode) ⇔
    (sq.pre = sq.post)
End

Theorem checkPf1_ax_factor:
  checkPf1 ws (INL (CertPf sq CnAx)) ⇔ checkPf1_ax_arm ws sq CnAx
Proof
  simp[Once checkPf1_def, checkPf1_ax_arm_def]
QED

Theorem famEq_ax_arm:
  wfColumns cols ct ∧ mkCtx cols = SOME ct ∧
  nodeCorr cols ct i (CertPf sq nd) ∧
  FST (THE (tagOf cols i)) ∈ {0}
  ⇒
  (checkFam_ax cols ct i ⇔ checkPf1_ax_arm ws sq nd)
Proof
  strip_tac
  >> drule_all famEq_ax >> strip_tac
  >> simp[checkPf1_ax_arm_def]
QED
