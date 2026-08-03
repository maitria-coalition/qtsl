(*
  Imprecise-certificate soundness, the per-element core, at finite
  state and finite horizon (induction and finite sums; no measure
  theory). Certificate rows are pointwise inequalities carrying the
  credal parameters symbolically; fixing any compatible precise process
  (a history-dependent scheduler over the credal set), the rows make
  the value function a supermartingale along the process, bounding the
  hitting probability per element and hence the lower prevision.
*)
open HolKernel Parse boolLib bossLib;
open arithmeticTheory pred_setTheory listTheory;
open realTheory realLib real_sigmaTheory;

val _ = new_theory "qtsl_imprec";

Definition subkernel_def:
  subkernel (k : 'st -> 'st -> real) <=>
    (!x y. 0 <= k x y) /\ (!x. SIGMA (k x) UNIV <= 1)
End

Definition scheduler_def:
  scheduler (cs : ('st -> 'st -> real) set) sg <=> !h:'st list. sg h IN cs
End

Definition hitP_def:
  (hitP sg bad 0 h (x:'st) = if x IN bad then (1:real) else 0) /\
  (hitP sg bad (SUC n) h x =
     if x IN bad then 1
     else SIGMA (\y. sg (x::h) x y * hitP sg bad n (x::h) y) UNIV)
End

Definition cert_rows_def:
  cert_rows (cs : ('st -> 'st -> real) set) bad (V : 'st -> real) c x0 <=>
    (!x. 0 <= V x) /\
    (!x. x IN bad ==> 1 <= V x) /\
    (!k x. k IN cs /\ x NOTIN bad ==>
           SIGMA (\y. k x y * V y) UNIV <= V x) /\
    V x0 <= c
End

Theorem hitP_bounds:
  !sg bad. FINITE (UNIV:'st set) /\ (!h:'st list. subkernel (sg h)) ==>
    !n h (x:'st). 0 <= hitP sg bad n h x /\ hitP sg bad n h x <= 1
Proof
  rpt gen_tac >> strip_tac >>
  Induct >- rw[hitP_def, REAL_LE_01, REAL_LE_REFL] >>
  rw[hitP_def, REAL_LE_01, REAL_LE_REFL]
  >- (irule REAL_SUM_IMAGE_POS >> rw[] >>
      irule REAL_LE_MUL >> metis_tac[subkernel_def]) >>
  irule REAL_LE_TRANS >>
  qexists_tac `SIGMA (sg (x::h) x) UNIV` >>
  conj_tac
  >- (irule REAL_SUM_IMAGE_MONO >> rw[] >>
      metis_tac[subkernel_def, REAL_LE_LMUL_IMP, REAL_MUL_RID]) >>
  metis_tac[subkernel_def]
QED

Theorem hitP_le_V:
  !cs sg bad V c (x0:'st).
    FINITE (UNIV:'st set) /\ (!k. k IN cs ==> subkernel k) /\
    scheduler cs sg /\ cert_rows cs bad V c x0 ==>
    !n h x. hitP sg bad n h x <= V x
Proof
  rpt gen_tac >> strip_tac >>
  fs[cert_rows_def, scheduler_def] >>
  Induct >- (rw[hitP_def] >> metis_tac[]) >>
  rw[hitP_def] >>

  qpat_x_assum `!k x. k IN cs /\ _ ==> _`
    (qspecl_then [`sg (x::h)`, `x`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >>
  irule REAL_LE_TRANS >>
  qexists_tac `SIGMA (\y. V y * sg (x::h) x y) UNIV` >>
  reverse conj_tac >- asm_rewrite_tac[] >>
  irule REAL_SUM_IMAGE_MONO >> rw[] >>
  metis_tac[REAL_LE_LMUL_IMP, REAL_MUL_COMM, subkernel_def]
QED

Theorem certificate_sound_per_element:
  !cs sg bad V c (x0:'st).
    FINITE (UNIV:'st set) /\ (!k. k IN cs ==> subkernel k) /\
    scheduler cs sg /\ cert_rows cs bad V c x0 ==>
    !n. hitP sg bad n [] x0 <= c
Proof
  rw[] >>
  irule REAL_LE_TRANS >> qexists_tac `V x0` >>
  conj_tac >- metis_tac[hitP_le_V] >>
  fs[cert_rows_def]
QED

Theorem certificate_sound_sup_horizon:
  !cs sg bad V c (x0:'st).
    FINITE (UNIV:'st set) /\ (!k. k IN cs ==> subkernel k) /\
    scheduler cs sg /\ cert_rows cs bad V c x0 ==>
    sup (IMAGE (\n. hitP sg bad n [] x0) UNIV) <= c
Proof
  rw[] >>
  irule REAL_IMP_SUP_LE' >> rw[IMAGE_EQ_EMPTY, IN_IMAGE] >>
  metis_tac[certificate_sound_per_element, UNIV_NOT_EMPTY, IN_UNIV]
QED

Definition lower_safe_def:
  lower_safe (cs : ('st -> 'st -> real) set) bad n (x0:'st) =
    inf (IMAGE (\sg. 1 - hitP sg bad n [] x0) (scheduler cs))
End

Theorem certificate_lower_prevision:
  !cs bad V c (x0:'st).
    FINITE (UNIV:'st set) /\ cs <> {} /\
    (!k. k IN cs ==> subkernel k) /\ cert_rows cs bad V c x0 ==>
    !n. 1 - c <= lower_safe cs bad n x0
Proof
  rw[lower_safe_def] >>
  `(\h:'st list. CHOICE cs) IN scheduler cs` by
    (rw[IN_APP, scheduler_def] >> metis_tac[CHOICE_DEF, IN_APP]) >>
  irule REAL_IMP_LE_INF' >> conj_tac >>
  TRY (rw[IMAGE_EQ_EMPTY] >> metis_tac[MEMBER_NOT_EMPTY] >> NO_TAC) >>
  rw[IN_IMAGE] >>
  `hitP sg bad n [] x0 <= c` suffices_by REAL_ARITH_TAC >>
  metis_tac[certificate_sound_per_element, IN_APP]
QED

val _ = export_theory ();
