(*
  Stopping times and optional stopping over HOL4's martingaleTheory
  (set-integral formulation): stopping_time (num-valued adapted times),
  the stopped process, finite-horizon optional stopping
  (martingale_stopped_integral, by induction on the horizon), and
  bounded optional stopping at an everywhere-finite stopping time
  (optional_stopping_bounded, via dominated convergence — the stopped
  process is eventually constant pointwise). The distribution's
  martingaleTheory carries filtrations and martingales but no
  stopping-time vocabulary; this theory is the gap-fill.
*)
open HolKernel Parse boolLib bossLib;
open hurdUtils;
open arithmeticTheory pred_setTheory;
open realTheory realLib metricTheory netsTheory real_topologyTheory;
open extrealTheory sigma_algebraTheory measureTheory borelTheory
     lebesgueTheory martingaleTheory;

val _ = new_theory "qtsl_stop";

Definition stopping_time_def :
    stopping_time (a :num -> 'a algebra) (t :'a -> num) <=>
      !n. {x | x IN space (a n) /\ t x <= n} IN subsets (a n)
End

Definition stopped_def :
    stopped (u :num -> 'a -> extreal) (t :'a -> num) n x = u (MIN n (t x)) x
End

Theorem filtered_space_eq :
    !m a n. filtered_measure_space m a ==> (space (a n) = m_space m)
Proof
    rw [filtered_measure_space_def, filtration_def, sub_sigma_algebra_def]
 >> POP_ASSUM (MP_TAC o Q.SPEC `n`)
 >> rw [space_def]
QED

Theorem filtered_subsets_measurable :
    !m a n s. filtered_measure_space m a /\ s IN subsets (a n) ==>
              s IN measurable_sets m
Proof
    rw [filtered_measure_space_def, filtration_def, sub_sigma_algebra_def]
 >> Q.PAT_X_ASSUM `!n. sigma_algebra (a n) /\ _` (MP_TAC o Q.SPEC `n`)
 >> rw [subsets_def]
 >> METIS_TAC [SUBSET_DEF]
QED

Theorem filtered_sigma_algebra :
    !m a n. filtered_measure_space m a ==> sigma_algebra (a n)
Proof
    rw [filtered_measure_space_def, filtration_def, sub_sigma_algebra_def]
QED

Theorem stopping_time_compl :
    !m a t n. filtered_measure_space m a /\ stopping_time a t ==>
              {x | x IN m_space m /\ n < t x} IN subsets (a n)
Proof
    rpt STRIP_TAC
 >> `space (a n) = m_space m` by METIS_TAC [filtered_space_eq]
 >> `sigma_algebra (a n)` by METIS_TAC [filtered_sigma_algebra]
 >> `{x | x IN m_space m /\ n < t x} =
     space (a n) DIFF {x | x IN space (a n) /\ t x <= n}`
      by (rw [EXTENSION, IN_DIFF, GSPECIFICATION] >> METIS_TAC [NOT_LESS_EQUAL])
 >> POP_ORW
 >> MATCH_MP_TAC ALGEBRA_COMPL
 >> fs [stopping_time_def, SIGMA_ALGEBRA_ALGEBRA]
QED

Theorem stopping_time_le_measurable :
    !m a t n. filtered_measure_space m a /\ stopping_time a t ==>
              {x | x IN m_space m /\ t x <= n} IN subsets (a n)
Proof
    rpt STRIP_TAC
 >> `space (a n) = m_space m` by METIS_TAC [filtered_space_eq]
 >> POP_ASSUM (fn th => ONCE_REWRITE_TAC [GSYM th])
 >> fs [stopping_time_def]
QED

Theorem stopped_zero :
    !u t x. stopped u t 0 x = u 0 x
Proof
    rw [stopped_def, MIN_0]
QED

Theorem stopped_suc_decomp :
    !u t n sp x. x IN sp ==>
      (stopped u t (SUC n) x =
        stopped u t n x * indicator_fn {y | y IN sp /\ t y <= n} x +
        u (SUC n) x * indicator_fn {y | y IN sp /\ n < t y} x)
Proof
    rpt STRIP_TAC
 >> Cases_on `t x <= n`
 >- (`~(n < t x)` by FULL_SIMP_TAC arith_ss []
     >> `(MIN (SUC n) (t x) = t x) /\ (MIN n (t x) = t x)`
          by FULL_SIMP_TAC arith_ss [MIN_DEF]
     >> rw [stopped_def, indicator_fn_def, GSPECIFICATION]
     >> FULL_SIMP_TAC std_ss [mul_rone, mul_rzero, add_rzero])
 >> `n < t x` by FULL_SIMP_TAC arith_ss []
 >> `(MIN (SUC n) (t x) = SUC n) /\ (MIN n (t x) = n)`
      by FULL_SIMP_TAC arith_ss [MIN_DEF]
 >> rw [stopped_def, indicator_fn_def, GSPECIFICATION]
 >> FULL_SIMP_TAC std_ss [mul_rone, mul_rzero, add_lzero]
QED

Theorem stopped_same_decomp :
    !u t n sp x. x IN sp ==>
      (stopped u t n x =
        stopped u t n x * indicator_fn {y | y IN sp /\ t y <= n} x +
        u n x * indicator_fn {y | y IN sp /\ n < t y} x)
Proof
    rpt STRIP_TAC
 >> Cases_on `t x <= n`
 >- (`~(n < t x)` by FULL_SIMP_TAC arith_ss []
     >> rw [stopped_def, indicator_fn_def, GSPECIFICATION]
     >> FULL_SIMP_TAC std_ss [mul_rone, mul_rzero, add_rzero])
 >> `n < t x` by FULL_SIMP_TAC arith_ss []
 >> `MIN n (t x) = n` by FULL_SIMP_TAC arith_ss [MIN_DEF]
 >> rw [stopped_def, indicator_fn_def, GSPECIFICATION]
 >> FULL_SIMP_TAC std_ss [mul_rone, mul_rzero, add_lzero]
QED

Theorem stopped_finite :
    !u t n x sp.
       (!k y. y IN sp ==> u k y <> PosInf /\ u k y <> NegInf) /\ x IN sp ==>
       stopped u t n x <> PosInf /\ stopped u t n x <> NegInf
Proof
    rw [stopped_def]
QED

Theorem stopped_integrable :
    !m a u t.
       martingale m a u /\ stopping_time a t /\
       (!n x. x IN m_space m ==> u n x <> PosInf /\ u n x <> NegInf) ==>
       !n. integrable m (stopped u t n)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> `filtered_measure_space m a`
      by fs [martingale_def, sigma_finite_filtered_measure_space_def]
 >> `measure_space m` by fs [filtered_measure_space_def]
 >> `!n. integrable m (u n)` by fs [martingale_def]
 >> Induct_on `n`
 >- (`integrable m (u 0)` by rw []
     >> Suff `integrable m (stopped u t 0) <=> integrable m (u 0)` >- rw []
     >> MATCH_MP_TAC integrable_cong >> rw [stopped_zero])
 >> Q.ABBREV_TAC `B = {y | y IN m_space m /\ t y <= n}`
 >> Q.ABBREV_TAC `C = {y | y IN m_space m /\ n < t y}`
 >> `B IN measurable_sets m`
      by METIS_TAC [stopping_time_le_measurable, filtered_subsets_measurable]
 >> `C IN measurable_sets m`
      by METIS_TAC [stopping_time_compl, filtered_subsets_measurable]
 >> Know `integrable m (\x. stopped u t n x * indicator_fn B x)`
 >- (MATCH_MP_TAC integrable_mul_indicator >> rw []) >> DISCH_TAC
 >> Know `integrable m (\x. u (SUC n) x * indicator_fn C x)`
 >- (MATCH_MP_TAC integrable_mul_indicator >> rw []) >> DISCH_TAC
 >> Know `integrable m (\x. stopped u t n x * indicator_fn B x +
                            u (SUC n) x * indicator_fn C x)`
 >- (HO_MATCH_MP_TAC integrable_add >> rw []
     >> DISJ1_TAC
     >> `stopped u t n x <> PosInf /\ stopped u t n x <> NegInf`
          by METIS_TAC [stopped_finite]
     >> `u (SUC n) x <> PosInf /\ u (SUC n) x <> NegInf` by METIS_TAC []
     >> rw [indicator_fn_def, mul_rone, mul_rzero, num_not_infty])
 >> DISCH_TAC
 >> Suff `integrable m (stopped u t (SUC n)) <=>
          integrable m (\x. stopped u t n x * indicator_fn B x +
                            u (SUC n) x * indicator_fn C x)` >- rw []
 >> MATCH_MP_TAC integrable_cong >> rw []
 >> rw [Abbr `B`, Abbr `C`]
 >> MATCH_MP_TAC stopped_suc_decomp >> rw []
QED

Theorem martingale_stopped_integral :
    !m a u t.
       martingale m a u /\ stopping_time a t /\
       (!n x. x IN m_space m ==> u n x <> PosInf /\ u n x <> NegInf) ==>
       !n. integral m (stopped u t n) = integral m (u 0)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> `filtered_measure_space m a`
      by fs [martingale_def, sigma_finite_filtered_measure_space_def]
 >> `measure_space m` by fs [filtered_measure_space_def]
 >> `!n. integrable m (u n)` by fs [martingale_def]
 >> `!n. integrable m (stopped u t n)` by METIS_TAC [stopped_integrable]
 >> Induct_on `n`
 >- (MATCH_MP_TAC integral_cong >> rw [stopped_zero])
 >> Q.ABBREV_TAC `B = {y | y IN m_space m /\ t y <= n}`
 >> Q.ABBREV_TAC `C = {y | y IN m_space m /\ n < t y}`
 >> `B IN measurable_sets m`
      by METIS_TAC [stopping_time_le_measurable, filtered_subsets_measurable]
 >> `C IN measurable_sets m`
      by METIS_TAC [stopping_time_compl, filtered_subsets_measurable]
 >> `C IN subsets (a n)` by METIS_TAC [stopping_time_compl]
 >> `integrable m (\x. stopped u t n x * indicator_fn B x)`
      by (MATCH_MP_TAC integrable_mul_indicator >> rw [])
 >> `integrable m (\x. u (SUC n) x * indicator_fn C x)`
      by (MATCH_MP_TAC integrable_mul_indicator >> rw [])
 >> `integrable m (\x. u n x * indicator_fn C x)`
      by (MATCH_MP_TAC integrable_mul_indicator >> rw [])

 >> Know `integral m (stopped u t (SUC n)) =
          integral m (\x. stopped u t n x * indicator_fn B x +
                          u (SUC n) x * indicator_fn C x)`
 >- (MATCH_MP_TAC integral_cong >> rw []
     >> rw [Abbr `B`, Abbr `C`]
     >> MATCH_MP_TAC stopped_suc_decomp >> rw [])
 >> Rewr'

 >> Know `integral m (\x. stopped u t n x * indicator_fn B x +
                          u (SUC n) x * indicator_fn C x) =
          integral m (\x. stopped u t n x * indicator_fn B x) +
          integral m (\x. u (SUC n) x * indicator_fn C x)`
 >- (HO_MATCH_MP_TAC integral_add >> rw []
     >> DISJ1_TAC
     >> `stopped u t n x <> PosInf /\ stopped u t n x <> NegInf`
          by METIS_TAC [stopped_finite]
     >> `u (SUC n) x <> PosInf /\ u (SUC n) x <> NegInf` by METIS_TAC []
     >> rw [indicator_fn_def, mul_rone, mul_rzero, num_not_infty])
 >> Rewr'

 >> Know `integral m (\x. u (SUC n) x * indicator_fn C x) =
          integral m (\x. u n x * indicator_fn C x)`
 >- fs [martingale_def]
 >> Rewr'

 >> Know `integral m (\x. stopped u t n x * indicator_fn B x) +
          integral m (\x. u n x * indicator_fn C x) =
          integral m (\x. stopped u t n x * indicator_fn B x +
                          u n x * indicator_fn C x)`
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ]
     >> HO_MATCH_MP_TAC integral_add >> rw []
     >> DISJ1_TAC
     >> `stopped u t n x <> PosInf /\ stopped u t n x <> NegInf`
          by METIS_TAC [stopped_finite]
     >> `u n x <> PosInf /\ u n x <> NegInf` by METIS_TAC []
     >> rw [indicator_fn_def, mul_rone, mul_rzero, num_not_infty])
 >> Rewr'

 >> Know `integral m (\x. stopped u t n x * indicator_fn B x +
                          u n x * indicator_fn C x) =
          integral m (stopped u t n)`
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ]
     >> MATCH_MP_TAC integral_cong >> rw []
     >> rw [Abbr `B`, Abbr `C`]
     >> MATCH_MP_TAC stopped_same_decomp >> rw [])
 >> Rewr'
 >> rw []
QED

Theorem stopped_limit_measurable :
    !m a u t.
       martingale m a u /\ stopping_time a t /\
       (!n x. x IN m_space m ==> u n x <> PosInf /\ u n x <> NegInf) ==>
       (\x. u (t x) x) IN measurable (m_space m, measurable_sets m) Borel
Proof
    rpt STRIP_TAC
 >> `filtered_measure_space m a`
      by fs [martingale_def, sigma_finite_filtered_measure_space_def]
 >> `measure_space m` by fs [filtered_measure_space_def]
 >> `sigma_algebra (measurable_space m)`
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> `!n. integrable m (u n)` by fs [martingale_def]
 >> `!n. u n IN measurable (m_space m, measurable_sets m) Borel`
      by METIS_TAC [integrable_def]

 >> Know `!k. {x | x IN m_space m /\ (t x = k)} IN measurable_sets m`
 >- (GEN_TAC
     >> Cases_on `k`
     >- (`{x | x IN m_space m /\ (t x = 0)} =
          {x | x IN m_space m /\ t x <= 0}`
           by (rw [EXTENSION] >> FULL_SIMP_TAC arith_ss [])
         >> METIS_TAC [stopping_time_le_measurable,
                       filtered_subsets_measurable])
     >> `{x | x IN m_space m /\ (t x = SUC n)} =
         {x | x IN m_space m /\ t x <= SUC n} DIFF
         {x | x IN m_space m /\ t x <= n}`
          by (rw [EXTENSION, IN_DIFF] >> EQ_TAC >> rw []
              >> FULL_SIMP_TAC arith_ss [])
     >> POP_ORW
     >> MATCH_MP_TAC MEASURE_SPACE_DIFF >> rw []
     >> METIS_TAC [stopping_time_le_measurable, filtered_subsets_measurable])
 >> DISCH_TAC
 >> `sigma_algebra (m_space m, measurable_sets m)` by fs [measure_space_def]
 >> rw [IN_MEASURABLE_BOREL, IN_FUNSET, space_def, subsets_def]

 >> Know `{x | u (t x) x < Normal c} INTER m_space m =
          BIGUNION (IMAGE (\k. {x | x IN m_space m /\ (t x = k)} INTER
                               ({x | u k x < Normal c} INTER m_space m))
                          univ(:num))`
 >- (rw [EXTENSION, IN_BIGUNION_IMAGE] >> EQ_TAC >> rw [] >> METIS_TAC [])
 >> Rewr'
 >> MATCH_MP_TAC MEASURE_SPACE_BIGUNION >> rw []
 >> MATCH_MP_TAC MEASURE_SPACE_INTER >> rw []
 >> Q.PAT_X_ASSUM `!n. u n IN measurable _ Borel` MP_TAC
 >> rw [IN_MEASURABLE_BOREL, space_def, subsets_def]
QED

Theorem optional_stopping_bounded :
    !m a u t c.
       martingale m a u /\ stopping_time a t /\
       measure m (m_space m) < PosInf /\
       (!n x. x IN m_space m ==> abs (u n x) <= Normal c) ==>
       (integral m (\x. u (t x) x) = integral m (u 0))
Proof
    rpt STRIP_TAC
 >> `filtered_measure_space m a`
      by fs [martingale_def, sigma_finite_filtered_measure_space_def]
 >> `measure_space m` by fs [filtered_measure_space_def]
 >> `!n. integrable m (u n)` by fs [martingale_def]

 >> Know `!n x. x IN m_space m ==> u n x <> PosInf /\ u n x <> NegInf`
 >- (rpt GEN_TAC >> DISCH_TAC
     >> `abs (u n x) <= Normal c` by rw []
     >> fs [abs_bounds]
     >> CONJ_TAC
     >- (CCONTR_TAC >> fs [] >> METIS_TAC [le_infty, extreal_not_infty])
     >> CCONTR_TAC >> fs []
     >> `-Normal c <= NegInf` by METIS_TAC []
     >> fs [extreal_ainv_def, le_infty, extreal_not_infty])
 >> DISCH_TAC
 >> `!n. integrable m (stopped u t n)` by METIS_TAC [stopped_integrable]
 >> `!n. integral m (stopped u t n) = integral m (u 0)`
      by METIS_TAC [martingale_stopped_integral]

 >> `(\x. u (t x) x) IN measurable (m_space m, measurable_sets m) Borel`
      by METIS_TAC [stopped_limit_measurable]
 >> `!x. x IN m_space m ==>
         u (t x) x <> PosInf /\ u (t x) x <> NegInf` by rw []
 >> Know `integrable m (\x. u (t x) x)`
 >- (MATCH_MP_TAC integrable_bounded
     >> Q.EXISTS_TAC `\x. Normal c` >> rw []
     >- (MATCH_MP_TAC integrable_const >> rw [])
     >> rw [])
 >> DISCH_TAC

 >> Know `!x. x IN m_space m ==>
              ((\n. real (stopped u t n x)) --> real (u (t x) x))
                sequentially`
 >- (rpt STRIP_TAC
     >> rw [LIM_SEQUENTIALLY]
     >> Q.EXISTS_TAC `t x` >> rpt STRIP_TAC
     >> `MIN n (t x) = t x` by FULL_SIMP_TAC arith_ss [MIN_DEF]
     >> rw [stopped_def, metricTheory.DIST_REFL])
 >> DISCH_TAC

 >> Know `((\n. real (integral m (stopped u t n))) -->
             real (integral m (\x. u (t x) x))) sequentially`
 >- (MATCH_MP_TAC lebesgue_dominated_convergence
     >> rpt CONJ_TAC
     >- rw []
     >- rw []
     >- rw []
     >- (rpt GEN_TAC >> DISCH_TAC >> METIS_TAC [stopped_finite])
     >- rw []
     >- rw []
     >> Q.EXISTS_TAC `\x. Normal c` >> rw [extreal_not_infty]
     >- (MATCH_MP_TAC integrable_const >> rw [])
     >- (`abs (u 0 x) <= Normal c` by rw []
         >> `(0:extreal) <= Normal c` by METIS_TAC [abs_pos, le_trans]
         >> fs [extreal_of_num_def, extreal_le_eq])
     >> rw [stopped_def])
 >> DISCH_TAC

 >> Know `((\n. real (integral m (stopped u t n))) -->
             real (integral m (u 0))) sequentially`
 >- rw [LIM_CONST]
 >> DISCH_TAC

 >> Know `real (integral m (\x. u (t x) x)) = real (integral m (u 0))`
 >- (Q.PAT_X_ASSUM `(_ --> real (integral m (u 0))) sequentially` MP_TAC
     >> Q.PAT_X_ASSUM `(_ --> real (integral m (\x. u (t x) x))) sequentially`
          MP_TAC
     >> MP_TAC (Q.ISPECL
          [`sequentially`,
           `\n. real (integral m (stopped (u:num -> 'a -> extreal)
                                          (t:'a -> num) n))`,
           `real (integral m (\x. (u:num -> 'a -> extreal)
                                  ((t:'a -> num) x) x))`,
           `real (integral m ((u:num -> 'a -> extreal) 0))`] LIM_UNIQUE)
     >> REWRITE_TAC [netsTheory.TRIVIAL_LIMIT_SEQUENTIALLY]
     >> rpt STRIP_TAC >> FIRST_X_ASSUM MATCH_MP_TAC >> rw [])
 >> DISCH_TAC
 >> `integral m (\x. u (t x) x) <> PosInf /\
     integral m (\x. u (t x) x) <> NegInf /\
     integral m (u 0) <> PosInf /\ integral m (u 0) <> NegInf`
      by METIS_TAC [integrable_finite_integral]
 >> Know `integral m (\x. u (t x) x) =
          Normal (real (integral m (\x. u (t x) x)))`
 >- rw [normal_real]
 >> Rewr'
 >> Know `integral m (u 0) = Normal (real (integral m (u 0)))`
 >- rw [normal_real]
 >> Rewr'
 >> rw []
QED

val _ = export_theory ();
