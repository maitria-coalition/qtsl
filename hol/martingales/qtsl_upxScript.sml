(*
  Doob's upcrossing inequality and almost-sure martingale convergence
  over the set-integral martingale formulation, building on
  qtsl_stopTheory: capped hitting times and their stopping-time-ness,
  the alternating crossing-time ladder, completed-upcrossing counts,
  two-time optional sampling for submartingales
  (optional_sampling_sub), the positive-part submartingale lemma, the
  upcrossing bound and the convergence theorem.
*)
open HolKernel Parse boolLib bossLib;
open hurdUtils numLib;
open arithmeticTheory pred_setTheory;
open realTheory realLib metricTheory netsTheory real_topologyTheory;
open extrealTheory sigma_algebraTheory measureTheory borelTheory
     lebesgueTheory martingaleTheory;
open qtsl_stopTheory;

val _ = new_theory "qtsl_upx";

Definition hitting_def :
    hitting (P :extreal -> bool) (u :num -> 'a -> extreal) n N (x :'a) =
      if (?j. n <= j /\ j <= N /\ P (u j x)) then
        (LEAST j. n <= j /\ j <= N /\ P (u j x))
      else N
End

Theorem hitting_le_cap :
    !P u n N x. hitting P u n N x <= N
Proof
    rw [hitting_def]
 >> LEAST_ELIM_TAC
 >> rw []
 >> Q.EXISTS_TAC `j` >> rw []
QED

Theorem hitting_ge_start :
    !P u n N x. n <= N ==> n <= hitting P u n N x
Proof
    rw [hitting_def]
 >> LEAST_ELIM_TAC
 >> rw []
 >> Q.EXISTS_TAC `j` >> rw []
QED

Theorem hitting_hit :
    !P u n N x. hitting P u n N x < N ==>
                n <= hitting P u n N x /\ P (u (hitting P u n N x) x)
Proof
    rpt GEN_TAC
 >> Cases_on `?j. n <= j /\ j <= N /\ P (u j x)`
 >- (ASM_SIMP_TAC std_ss [hitting_def]
     >> LEAST_ELIM_TAC
     >> CONJ_TAC >- METIS_TAC []
     >> rw [])
 >> ASM_SIMP_TAC arith_ss [hitting_def]
QED

Theorem hitting_least :
    !P u n N x j. n <= j /\ j <= N /\ P (u j x) ==>
                  hitting P u n N x <= j
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> `?i. n <= i /\ i <= N /\ P (u i x)` by METIS_TAC []
 >> ASM_SIMP_TAC std_ss [hitting_def]
 >> LEAST_ELIM_TAC
 >> CONJ_TAC >- METIS_TAC []
 >> rw []
 >> CCONTR_TAC
 >> FULL_SIMP_TAC arith_ss [NOT_LESS_EQUAL]
 >> METIS_TAC [NOT_LESS]
QED

Theorem hitting_min :
    !P u n N x i. hitting P u n N x < N /\
                  n <= i /\ i < hitting P u n N x ==> ~P (u i x)
Proof
    rpt GEN_TAC
 >> Cases_on `?j. n <= j /\ j <= N /\ P (u j x)`
 >- (ASM_SIMP_TAC std_ss [hitting_def]
     >> LEAST_ELIM_TAC
     >> CONJ_TAC >- METIS_TAC []
     >> rw []
     >> CCONTR_TAC
     >> `~(n <= i /\ i <= N /\ P (u i x))` by METIS_TAC []
     >> `i <= N` by FULL_SIMP_TAC arith_ss []
     >> METIS_TAC [])
 >> ASM_SIMP_TAC std_ss [hitting_def]
 >> FULL_SIMP_TAC arith_ss []
QED

Theorem hitting_stopping_time :
    !m a u P t N.
       filtered_measure_space m a /\ stopping_time a t /\
       (!k. {x | x IN m_space m /\ P (u k x)} IN subsets (a k)) ==>
       stopping_time a (\x. hitting P u (t x) N x)
Proof
    rw [stopping_time_def]
 >> `space (a n) = m_space m` by METIS_TAC [filtered_space_eq]
 >> `sigma_algebra (a n)` by METIS_TAC [filtered_sigma_algebra]
 >> Cases_on `N <= n`
 >- (Know `!y. hitting P u (t y) N y <= n`
     >- (GEN_TAC
         >> MATCH_MP_TAC LESS_EQ_TRANS
         >> Q.EXISTS_TAC `N` >> rw [hitting_le_cap])
     >> DISCH_TAC
     >> Know `{x | x IN space (a n) /\ hitting P u (t x) N x <= n} = space (a n)`
     >- rw [EXTENSION]
     >> Rewr'
     >> METIS_TAC [ALGEBRA_SPACE, SIGMA_ALGEBRA_ALGEBRA])
 >> `n < N` by FULL_SIMP_TAC arith_ss []
 >> Know `{x | x IN space (a n) /\ hitting P u (t x) N x <= n} =
          BIGUNION (IMAGE
            (\j. {x | x IN space (a n) /\ t x <= j} INTER
                 {x | x IN space (a n) /\ P (u j x)})
            (count (SUC n)))`
 >- (rw [EXTENSION, IN_BIGUNION_IMAGE, IN_COUNT]
     >> EQ_TAC >> rw []
     >- (Q.EXISTS_TAC `hitting P u (t x) N x`
         >> `hitting P u (t x) N x < N` by FULL_SIMP_TAC arith_ss []
         >> `t x <= hitting P u (t x) N x /\ P (u (hitting P u (t x) N x) x)`
              by METIS_TAC [hitting_hit]
         >> FULL_SIMP_TAC arith_ss [])
     >> `j <= N` by FULL_SIMP_TAC arith_ss []
     >> `hitting P u (t x) N x <= j` by METIS_TAC [hitting_least]
     >> FULL_SIMP_TAC arith_ss [])
 >> Rewr'
 >> MATCH_MP_TAC SIGMA_ALGEBRA_FINITE_UNION
 >> rw [SUBSET_DEF]
 >> MATCH_MP_TAC ALGEBRA_INTER
 >> rw [SIGMA_ALGEBRA_ALGEBRA]
 >- (`space (a j) = m_space m` by METIS_TAC [filtered_space_eq]
     >> Know `{x | x IN space (a n) /\ t x <= j} =
              {x | x IN space (a j) /\ t x <= j}`
     >- rw [EXTENSION]
     >> Rewr'
     >> Suff `subsets (a j) SUBSET subsets (a n)`
     >- (rw [] >> fs [stopping_time_def] >> METIS_TAC [SUBSET_DEF])
     >> fs [filtered_measure_space_def, filtration_def]
     >> FIRST_X_ASSUM MATCH_MP_TAC
     >> FULL_SIMP_TAC arith_ss [])
 >> Know `{x | x IN space (a n) /\ P (u j x)} =
          {x | x IN m_space m /\ P (u j x)}`
 >- rw [EXTENSION]
 >> Rewr'
 >> Suff `subsets (a j) SUBSET subsets (a n)`
 >- METIS_TAC [SUBSET_DEF]
 >> fs [filtered_measure_space_def, filtration_def]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> FULL_SIMP_TAC arith_ss []
QED

Theorem adapted_le_event :
    !m a u k b. filtered_measure_space m a /\
                u k IN measurable (a k) Borel ==>
                {x | x IN m_space m /\ u k x <= Normal b} IN subsets (a k)
Proof
    rpt STRIP_TAC
 >> `space (a k) = m_space m` by METIS_TAC [filtered_space_eq]
 >> `sigma_algebra (a k)` by METIS_TAC [filtered_sigma_algebra]
 >> `{x | x IN m_space m /\ u k x <= Normal b} =
     {x | u k x <= Normal b} INTER space (a k)`
      by (rw [EXTENSION] >> METIS_TAC [])
 >> POP_ORW
 >> METIS_TAC [IN_MEASURABLE_BOREL_ALL]
QED

Theorem adapted_ge_event :
    !m a u k c. filtered_measure_space m a /\
                u k IN measurable (a k) Borel ==>
                {x | x IN m_space m /\ Normal c <= u k x} IN subsets (a k)
Proof
    rpt STRIP_TAC
 >> `space (a k) = m_space m` by METIS_TAC [filtered_space_eq]
 >> `sigma_algebra (a k)` by METIS_TAC [filtered_sigma_algebra]
 >> `{x | x IN m_space m /\ Normal c <= u k x} =
     {x | Normal c <= u k x} INTER space (a k)`
      by (rw [EXTENSION] >> METIS_TAC [])
 >> POP_ORW
 >> METIS_TAC [IN_MEASURABLE_BOREL_ALL]
QED

Definition crossUT_def :
   (crossUT u b c N 0 (x :'a) = (0 :num)) /\
   (crossUT u b c N (SUC k) x =
      hitting (\v. Normal c <= v) u
        (hitting (\v. v <= Normal b) u (crossUT u b c N k x) N x) N x)
End

Definition crossLT_def :
    crossLT u b c N k (x :'a) =
      hitting (\v. v <= Normal b) u (crossUT u b c N k x) N x
End

Definition upcrossings_def :
    upcrossings u b c N (x :'a) =
      CARD {k | 0 < k /\ crossUT u b c N k x < N}
End

Theorem crossUT_le_cap :
    !u b c N k x. crossUT u b c N k x <= N
Proof
    rpt GEN_TAC
 >> Cases_on `k` >> rw [crossUT_def, hitting_le_cap]
QED

Theorem crossLT_le_cap :
    !u b c N k x. crossLT u b c N k x <= N
Proof
    rw [crossLT_def, hitting_le_cap]
QED

Theorem crossUT_le_crossLT :
    !u b c N k x. crossUT u b c N k x <= crossLT u b c N k x
Proof
    rw [crossLT_def]
 >> MATCH_MP_TAC hitting_ge_start
 >> rw [crossUT_le_cap]
QED

Theorem crossLT_le_crossUT_SUC :
    !u b c N k x. crossLT u b c N k x <= crossUT u b c N (SUC k) x
Proof
    rw [crossUT_def, GSYM crossLT_def]
 >> MATCH_MP_TAC hitting_ge_start
 >> rw [crossLT_le_cap]
QED

Theorem crossUT_mono :
    !u b c N x j k. j <= k ==> crossUT u b c N j x <= crossUT u b c N k x
Proof
    NTAC 6 GEN_TAC
 >> Induct_on `k`
 >- (rw [] >> `j = 0` by FULL_SIMP_TAC arith_ss [] >> rw [])
 >> STRIP_TAC
 >> Cases_on `j = SUC k` >- rw []
 >> `j <= k` by FULL_SIMP_TAC arith_ss []
 >> MATCH_MP_TAC LESS_EQ_TRANS
 >> Q.EXISTS_TAC `crossUT u b c N k x`
 >> rw []
 >> MATCH_MP_TAC LESS_EQ_TRANS
 >> Q.EXISTS_TAC `crossLT u b c N k x`
 >> rw [crossUT_le_crossLT, crossLT_le_crossUT_SUC]
QED

Theorem crossLT_hit :
    !u b c N k x. crossLT u b c N k x < N ==>
                  u (crossLT u b c N k x) x <= Normal b
Proof
    rw [crossLT_def]
 >> MP_TAC (Q.SPECL [`\v. v <= Normal b`,
                     `u :num -> 'a -> extreal`,
                     `crossUT u b c N k (x :'a)`, `N`, `x`] hitting_hit)
 >> rw []
QED

Theorem crossUT_SUC_hit :
    !u b c N k x. crossUT u b c N (SUC k) x < N ==>
                  Normal c <= u (crossUT u b c N (SUC k) x) x
Proof
    rw [crossUT_def, GSYM crossLT_def]
 >> MP_TAC (Q.SPECL [`\v. Normal c <= v`,
                     `u :num -> 'a -> extreal`,
                     `crossLT u b c N k (x :'a)`, `N`, `x`] hitting_hit)
 >> rw []
QED

Theorem crossLT_lt_crossUT_SUC :
    !u b c N k x. b < c /\ crossUT u b c N (SUC k) x < N ==>
                  crossLT u b c N k x < crossUT u b c N (SUC k) x
Proof
    rpt STRIP_TAC
 >> `crossLT u b c N k x <= crossUT u b c N (SUC k) x`
      by rw [crossLT_le_crossUT_SUC]
 >> `crossLT u b c N k x < N` by FULL_SIMP_TAC arith_ss []
 >> `u (crossLT u b c N k x) x <= Normal b` by METIS_TAC [crossLT_hit]
 >> `Normal c <= u (crossUT u b c N (SUC k) x) x`
      by METIS_TAC [crossUT_SUC_hit]
 >> CCONTR_TAC
 >> `crossLT u b c N k x = crossUT u b c N (SUC k) x`
      by FULL_SIMP_TAC arith_ss []
 >> `Normal c <= Normal b` by METIS_TAC [le_trans]
 >> fs [extreal_le_eq]
 >> METIS_TAC [REAL_LTE_ANTISYM]
QED

Theorem crossUT_lower :
    !u b c N k x. b < c /\ crossUT u b c N k x < N ==>
                  k <= crossUT u b c N k x
Proof
    rpt GEN_TAC
 >> Induct_on `k` >- rw []
 >> STRIP_TAC
 >> `crossLT u b c N k x < crossUT u b c N (SUC k) x`
      by METIS_TAC [crossLT_lt_crossUT_SUC]
 >> `crossUT u b c N k x <= crossLT u b c N k x` by rw [crossUT_le_crossLT]
 >> `crossUT u b c N k x < N` by FULL_SIMP_TAC arith_ss []
 >> `k <= crossUT u b c N k x` by METIS_TAC []
 >> FULL_SIMP_TAC arith_ss []
QED

Theorem crossUT_cap :
    !u b c N x. b < c ==> crossUT u b c N N x = N
Proof
    rpt STRIP_TAC
 >> `crossUT u b c N N x <= N` by rw [crossUT_le_cap]
 >> Cases_on `crossUT u b c N N x < N`
 >- (`N <= crossUT u b c N N x` by METIS_TAC [crossUT_lower]
     >> FULL_SIMP_TAC arith_ss [])
 >> FULL_SIMP_TAC arith_ss []
QED

Theorem crossUT_stopping_time :
    !m a u b c N.
       filtered_measure_space m a /\
       (!n. u n IN measurable (a n) Borel) ==>
       !k. stopping_time a (\x. crossUT u b c N k x)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Induct_on `k`
 >- (rw [stopping_time_def, crossUT_def]
     >> Know `{x | x IN space (a n) /\ (0 :num) <= n} = space (a n)`
     >- rw [EXTENSION]
     >> Rewr'
     >> METIS_TAC [ALGEBRA_SPACE, SIGMA_ALGEBRA_ALGEBRA,
                   filtered_sigma_algebra])
 >> rw [crossUT_def]
 >> HO_MATCH_MP_TAC hitting_stopping_time
 >> Q.EXISTS_TAC `m`
 >> rw []
 >- (HO_MATCH_MP_TAC hitting_stopping_time
     >> Q.EXISTS_TAC `m`
     >> rw []
     >> MATCH_MP_TAC adapted_le_event >> rw [])
 >> MATCH_MP_TAC adapted_ge_event >> rw []
QED

Theorem crossLT_stopping_time :
    !m a u b c N.
       filtered_measure_space m a /\
       (!n. u n IN measurable (a n) Borel) ==>
       !k. stopping_time a (\x. crossLT u b c N k x)
Proof
    rw [crossLT_def]
 >> HO_MATCH_MP_TAC hitting_stopping_time
 >> Q.EXISTS_TAC `m`
 >> rw []
 >- (MP_TAC (Q.SPECL [`m`, `a`, `u`, `b`, `c`, `N`] crossUT_stopping_time)
     >> rw [])
 >> MATCH_MP_TAC adapted_le_event >> rw []
QED

Theorem stopped_integrable' :
    !m a u t.
       filtered_measure_space m a /\ (!n. integrable m (u n)) /\
       stopping_time a t /\
       (!n x. x IN m_space m ==> u n x <> PosInf /\ u n x <> NegInf) ==>
       !n. integrable m (stopped u t n)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> `measure_space m` by fs [filtered_measure_space_def]
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

Theorem stopped_eval_le :
    !u t N x. t x <= N ==> (stopped u t N x = u (t x) x)
Proof
    rw [stopped_def, MIN_DEF]
 >> `t x = N` by FULL_SIMP_TAC arith_ss [] >> rw []
QED

Theorem sampled_integrable :
    !m a u t N.
       filtered_measure_space m a /\ (!n. integrable m (u n)) /\
       stopping_time a t /\ (!x. x IN m_space m ==> t x <= N) /\
       (!n x. x IN m_space m ==> u n x <> PosInf /\ u n x <> NegInf) ==>
       integrable m (\x. u (t x) x)
Proof
    rpt STRIP_TAC
 >> `measure_space m` by fs [filtered_measure_space_def]
 >> `!n. integrable m (stopped u t n)` by METIS_TAC [stopped_integrable']
 >> Suff `integrable m (\x. u (t x) x) <=> integrable m (stopped u t N)`
 >- rw []
 >> MATCH_MP_TAC integrable_cong >> rw []
 >> METIS_TAC [stopped_eval_le]
QED

Theorem telescope_zero[local] :
    !w s t N. (s :num) = t /\
              (!j. (w :num -> extreal) j <> PosInf /\ w j <> NegInf) ==>
              (EXTREAL_SUM_IMAGE
                 (\j. (w (SUC j) - w j) * (if s <= j /\ j < t then 1 else 0))
                 (count N) = w t - w s)
Proof
    rpt STRIP_TAC
 >> Know `EXTREAL_SUM_IMAGE
            (\j. (w (SUC j) - w j) * (if s <= j /\ j < t then 1 else 0))
            (count N) =
          EXTREAL_SUM_IMAGE (\j. (0 :extreal)) (count N)`
 >- (irule EXTREAL_SUM_IMAGE_EQ >> rw [])
 >> Rewr'
 >> rw [EXTREAL_SUM_IMAGE_0]
 >> METIS_TAC [sub_refl]
QED

Theorem telescope_count :
    !w s t N. (s :num) <= t /\ t <= N /\
              (!j. (w :num -> extreal) j <> PosInf /\ w j <> NegInf) ==>
              (EXTREAL_SUM_IMAGE
                 (\j. (w (SUC j) - w j) * (if s <= j /\ j < t then 1 else 0))
                 (count N) = w t - w s)
Proof
    NTAC 2 GEN_TAC
 >> Suff `!N t. s <= t /\ t <= N /\
                (!j. w j <> PosInf /\ w j <> NegInf) ==>
                (EXTREAL_SUM_IMAGE
                   (\j. (w (SUC j) - w j) * (if s <= j /\ j < t then 1 else 0))
                   (count N) = w t - w s)`
 >- METIS_TAC []
 >> Induct_on `N`
 >- (rw [EXTREAL_SUM_IMAGE_EMPTY]
     >> `s = 0` by FULL_SIMP_TAC arith_ss []
     >> rw []
     >> METIS_TAC [sub_refl])
 >> GEN_TAC >> STRIP_TAC
 >> Cases_on `s = t`
 >- (MP_TAC (Q.SPECL [`w`, `s`, `t`, `SUC N`] telescope_zero) >> rw [])
 >> Know `EXTREAL_SUM_IMAGE
            (\j. (w (SUC j) - w j) * (if s <= j /\ j < t then 1 else 0))
            (count (SUC N)) =
          EXTREAL_SUM_IMAGE
            (\j. (w (SUC j) - w j) * (if s <= j /\ j < t then 1 else 0))
            (count N) +
          (w (SUC N) - w N) * (if s <= N /\ N < t then 1 else 0)`
 >- (HO_MATCH_MP_TAC EXTREAL_SUM_IMAGE_COUNT_SUC
     >> DISJ1_TAC >> rw []
     >> Cases_on `s <= m /\ m < t` >> rw [mul_rzero, mul_rone]
     >> METIS_TAC [sub_not_infty])
 >> Rewr'
 >> Cases_on `t = SUC N`
 >- (`s <= N /\ N < t` by FULL_SIMP_TAC arith_ss []
     >> rw [mul_rone]
     >> Know `EXTREAL_SUM_IMAGE
                (\j. (w (SUC j) - w j) * (if s <= j /\ j < SUC N then 1 else 0))
                (count N) =
              EXTREAL_SUM_IMAGE
                (\j. (w (SUC j) - w j) * (if s <= j /\ j < N then 1 else 0))
                (count N)`
     >- (irule EXTREAL_SUM_IMAGE_EQ >> rw []
         >> DISJ1_TAC >> rw []
         >> Cases_on `s <= x` >> rw [mul_rzero, mul_rone, num_not_infty]
         >> METIS_TAC [sub_not_infty])
     >> Rewr'
     >> Know `EXTREAL_SUM_IMAGE
                (\j. (w (SUC j) - w j) * (if s <= j /\ j < N then 1 else 0))
                (count N) = w N - w s`
     >- (Q.PAT_X_ASSUM `!t. _ ==> _` (MP_TAC o Q.SPEC `N`)
         >> rw [])
     >> Rewr'
     >> `?wa. w N = Normal wa` by METIS_TAC [extreal_cases]
     >> `?wb. w s = Normal wb` by METIS_TAC [extreal_cases]
     >> `?wc. w (SUC N) = Normal wc` by METIS_TAC [extreal_cases]
     >> rw [extreal_sub_def, extreal_add_def, extreal_11]
     >> REAL_ARITH_TAC)
 >> `t <= N` by FULL_SIMP_TAC arith_ss []
 >> `~(s <= N /\ N < t)` by FULL_SIMP_TAC arith_ss []
 >> rw [mul_rzero, add_rzero]
 >> Q.PAT_X_ASSUM `!t. _ ==> _` (MP_TAC o Q.SPEC `t`)
 >> rw []
QED

Theorem optional_sampling_sub :
    !m a v s t N.
       sub_martingale m a v /\ stopping_time a s /\ stopping_time a t /\
       (!n x. x IN m_space m ==> v n x <> PosInf /\ v n x <> NegInf) /\
       (!x. x IN m_space m ==> s x <= t x) /\
       (!x. x IN m_space m ==> t x <= N) ==>
       integral m (\x. v (s x) x) <= integral m (\x. v (t x) x)
Proof
    rpt STRIP_TAC
 >> `filtered_measure_space m a`
      by fs [sub_martingale_def, sigma_finite_filtered_measure_space_def]
 >> `measure_space m` by fs [filtered_measure_space_def]
 >> `!n. integrable m (v n)` by fs [sub_martingale_def]
 >> Q.ABBREV_TAC `A = \j. {x | x IN m_space m /\ s x <= j} INTER
                          {x | x IN m_space m /\ j < t x}`
 >> Know `!j. A j IN subsets (a j)`
 >- (rw [Abbr `A`]
     >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER
     >> METIS_TAC [stopping_time_le_measurable, stopping_time_compl,
                   filtered_sigma_algebra])
 >> DISCH_TAC
 >> `!j. A j IN measurable_sets m` by METIS_TAC [filtered_subsets_measurable]

 >> Q.ABBREV_TAC `D = \j x. (v (SUC j) x - v j x) * indicator_fn (A j) x`
 >> Know `!j. integrable m (D j)`
 >- (rw [Abbr `D`]
     >> HO_MATCH_MP_TAC integrable_mul_indicator >> rw []
     >> HO_MATCH_MP_TAC integrable_sub >> rw []
     >> `!k. (\x. v k x) = v k` by rw [FUN_EQ_THM]
     >> rw [])
 >> DISCH_TAC
 >> Know `!j x. x IN m_space m ==> D j x <> PosInf /\ D j x <> NegInf`
 >- (rw [Abbr `D`, indicator_fn_def, mul_rone, mul_rzero, num_not_infty]
     >> METIS_TAC [sub_not_infty])
 >> DISCH_TAC

 >> Know `!x. x IN m_space m ==>
              (v (t x) x = v (s x) x +
                 EXTREAL_SUM_IMAGE (\j. D j x) (count N))`
 >- (rpt STRIP_TAC
     >> Know `EXTREAL_SUM_IMAGE (\j. D j x) (count N) =
              EXTREAL_SUM_IMAGE
                (\j. ((\i. v i x) (SUC j) - (\i. v i x) j) *
                     (if s x <= j /\ j < t x then 1 else 0)) (count N)`
     >- (irule EXTREAL_SUM_IMAGE_EQ >> rw []
         >> ((DISJ1_TAC >> rw []
              >> Cases_on `s x <= x' /\ x' < t x`
              >> rw [mul_rone, mul_rzero, num_not_infty]
              >> METIS_TAC [sub_not_infty])
             ORELSE
             (rw [Abbr `D`, Abbr `A`, indicator_fn_def, mul_rone, mul_rzero]
              >> FULL_SIMP_TAC arith_ss [NOT_LESS_EQUAL]
              >> METIS_TAC [NOT_LESS])))
     >> Rewr'
     >> Know `EXTREAL_SUM_IMAGE
                (\j. ((\i. v i x) (SUC j) - (\i. v i x) j) *
                     (if s x <= j /\ j < t x then 1 else 0)) (count N) =
              (\i. v i x) (t x) - (\i. v i x) (s x)`
     >- (MATCH_MP_TAC telescope_count >> rw [] >> METIS_TAC [])
     >> Rewr'
     >> SIMP_TAC std_ss []
     >> `?p. v (t x) x = Normal p` by METIS_TAC [extreal_cases]
     >> `?q. v (s x) x = Normal q` by METIS_TAC [extreal_cases]
     >> rw [extreal_sub_def, extreal_add_def, extreal_11]
     >> REAL_ARITH_TAC)
 >> DISCH_TAC

 >> `integrable m (\x. v (s x) x)`
      by (HO_MATCH_MP_TAC sampled_integrable
          >> Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `N`
          >> rw [] >> METIS_TAC [LESS_EQ_TRANS])
 >> `integrable m (\x. v (t x) x)`
      by (HO_MATCH_MP_TAC sampled_integrable
          >> Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `N`
          >> rw [])
 >> Know `integrable m (\x. EXTREAL_SUM_IMAGE (\j. D j x) (count N))`
 >- (HO_MATCH_MP_TAC integrable_sum >> rw [] >> METIS_TAC [])
 >> DISCH_TAC

 >> Know `integral m (\x. v (t x) x) =
          integral m (\x. v (s x) x +
                          EXTREAL_SUM_IMAGE (\j. D j x) (count N))`
 >- (MATCH_MP_TAC integral_cong >> rw [])
 >> Rewr'
 >> Know `integral m (\x. v (s x) x +
                          EXTREAL_SUM_IMAGE (\j. D j x) (count N)) =
          integral m (\x. v (s x) x) +
          integral m (\x. EXTREAL_SUM_IMAGE (\j. D j x) (count N))`
 >- (HO_MATCH_MP_TAC integral_add >> rw []
     >> ((DISJ1_TAC >> rw []
          >> METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY, FINITE_COUNT, IN_COUNT])
         ORELSE METIS_TAC []))
 >> Rewr'
 >> Know `integral m (\x. EXTREAL_SUM_IMAGE (\j. D j x) (count N)) =
          EXTREAL_SUM_IMAGE (\j. integral m (D j)) (count N)`
 >- (HO_MATCH_MP_TAC integral_sum >> rw [] >> METIS_TAC [])
 >> Rewr'

 >> Know `!j. 0 <= integral m (D j)`
 >- (GEN_TAC
     >> Know `integral m (D j) =
              integral m (\x. v (SUC j) x * indicator_fn (A j) x) -
              integral m (\x. v j x * indicator_fn (A j) x)`
     >- (Know `integral m (D j) =
               integral m (\x. v (SUC j) x * indicator_fn (A j) x -
                               v j x * indicator_fn (A j) x)`
         >- (MATCH_MP_TAC integral_cong >> rw []
             >> rw [Abbr `D`, indicator_fn_def, mul_rone, mul_rzero])
         >> Rewr'
         >> HO_MATCH_MP_TAC integral_sub >> rw []
         >> ((HO_MATCH_MP_TAC integrable_mul_indicator >> rw []
              >> `!k. (\x. v k x) = v k` by rw [FUN_EQ_THM]
              >> rw [])
             ORELSE
             (DISJ1_TAC
              >> rw [indicator_fn_def, mul_rone, mul_rzero, num_not_infty]
              >> METIS_TAC [])))
     >> Rewr'
     >> Know `integral m (\x. v j x * indicator_fn (A j) x) <=
              integral m (\x. v (SUC j) x * indicator_fn (A j) x)`
     >- (fs [sub_martingale_def]
         >> FIRST_X_ASSUM MATCH_MP_TAC >> rw [])
     >> DISCH_TAC
     >> Know `integral m (\x. v j x * indicator_fn (A j) x) <> PosInf /\
              integral m (\x. v j x * indicator_fn (A j) x) <> NegInf`
     >- (MATCH_MP_TAC integrable_finite_integral >> rw []
         >> HO_MATCH_MP_TAC integrable_mul_indicator >> rw []
         >> `!k. (\x. v k x) = v k` by rw [FUN_EQ_THM]
         >> rw [])
     >> STRIP_TAC
     >> METIS_TAC [sub_zero_le])
 >> DISCH_TAC
 >> Know `0 <= EXTREAL_SUM_IMAGE (\j. integral m (D j)) (count N)`
 >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> rw [])
 >> DISCH_TAC
 >> Know `integral m (\x. v (s x) x) <> PosInf /\
          integral m (\x. v (s x) x) <> NegInf`
 >- (MATCH_MP_TAC integrable_finite_integral >> rw [])
 >> STRIP_TAC
 >> METIS_TAC [le_addr]
QED

Theorem adapted_gt_event :
    !m a u k c. filtered_measure_space m a /\
                u k IN measurable (a k) Borel ==>
                {x | x IN m_space m /\ Normal c < u k x} IN subsets (a k)
Proof
    rpt STRIP_TAC
 >> `space (a k) = m_space m` by METIS_TAC [filtered_space_eq]
 >> `sigma_algebra (a k)` by METIS_TAC [filtered_sigma_algebra]
 >> `{x | x IN m_space m /\ Normal c < u k x} =
     {x | Normal c < u k x} INTER space (a k)`
      by (rw [EXTENSION] >> METIS_TAC [])
 >> POP_ORW
 >> METIS_TAC [IN_MEASURABLE_BOREL_ALL]
QED

Theorem fn_plus_sub_hit[local] :
    !(y :extreal) b. y <> PosInf /\ y <> NegInf /\ Normal b < y ==>
                     (fn_plus (\z. z - Normal b) y = y - Normal b)
Proof
    rw [fn_plus_def]
 >> METIS_TAC [sub_zero_lt, extreal_lt_def]
QED

Theorem fn_plus_sub_miss[local] :
    !(y :extreal) b. y <> PosInf /\ y <> NegInf /\ y <= Normal b ==>
                     (fn_plus (\z. z - Normal b) y = 0)
Proof
    rw [fn_plus_def]
 >> `y - Normal b <= 0` by METIS_TAC [sub_le_zero, extreal_not_infty]
 >> METIS_TAC [let_antisym]
QED

Theorem sub_martingale_fn_plus :
    !m a u b.
       sub_martingale m a u /\
       (!n. u n IN measurable (a n) Borel) /\
       measure m (m_space m) < PosInf /\
       (!n x. x IN m_space m ==> u n x <> PosInf /\ u n x <> NegInf) ==>
       sub_martingale m a (\n x. fn_plus (\y. u n y - Normal b) x)
Proof
    rpt STRIP_TAC
 >> `filtered_measure_space m a`
      by fs [sub_martingale_def, sigma_finite_filtered_measure_space_def]
 >> `measure_space m` by fs [filtered_measure_space_def]
 >> `!n. integrable m (u n)` by fs [sub_martingale_def]

 >> Know `!n. integrable m (\x. u n x - Normal b)`
 >- (GEN_TAC
     >> HO_MATCH_MP_TAC integrable_sub >> rw []
     >- (`!k. (\x. u k x) = u k` by rw [FUN_EQ_THM] >> rw [])
     >- (MATCH_MP_TAC integrable_const >> rw [])
     >> DISJ1_TAC >> rw [extreal_not_infty])
 >> DISCH_TAC
 >> Know `!n. integrable m (\x. fn_plus (\y. u n y - Normal b) x)`
 >- (GEN_TAC
     >> `(\x. fn_plus (\y. u n y - Normal b) x) =
         fn_plus (\y. u n y - Normal b)` by rw [FUN_EQ_THM]
     >> POP_ORW
     >> MATCH_MP_TAC integrable_fn_plus >> rw []
     >> `(\y. u n y - Normal b) = (\x. u n x - Normal b)` by rw [FUN_EQ_THM]
     >> rw [])
 >> DISCH_TAC

 >> Know `!n x. x IN m_space m ==>
                fn_plus (\y. u n y - Normal b) x <> PosInf /\
                fn_plus (\y. u n y - Normal b) x <> NegInf`
 >- (rw [fn_plus_def, num_not_infty]
     >> METIS_TAC [sub_not_infty, extreal_not_infty])
 >> DISCH_TAC
 >> rw [sub_martingale_def]
 >> TRY (fs [sub_martingale_def] >> NO_TAC)

 >> Q.ABBREV_TAC `B = {x | x IN m_space m /\ Normal b < u n x}`
 >> `B IN subsets (a n)`
      by (rw [Abbr `B`] >> MATCH_MP_TAC adapted_gt_event >> rw [])
 >> `sigma_algebra (a n)` by METIS_TAC [filtered_sigma_algebra]
 >> `s INTER B IN subsets (a n)` by METIS_TAC [SIGMA_ALGEBRA_INTER]
 >> `s INTER B IN measurable_sets m /\ s IN measurable_sets m`
      by METIS_TAC [filtered_subsets_measurable]
 >> `space (a n) = m_space m` by METIS_TAC [filtered_space_eq]
 >> Know `s SUBSET m_space m`
 >- (`subset_class (space (a n)) (subsets (a n))`
       by fs [sigma_algebra_def, algebra_def]
     >> METIS_TAC [subset_class_def])
 >> DISCH_TAC

 >> Know `integral m (\x. fn_plus (\y. u n y - Normal b) x * indicator_fn s x) =
          integral m (\x. (u n x - Normal b) * indicator_fn (s INTER B) x)`
 >- (MATCH_MP_TAC integral_cong >> rw []
     >> Cases_on `x IN s` >> rw [indicator_fn_def, mul_rone, mul_rzero]
     >| [ rw [fn_plus_def]
          >> fs [Abbr `B`]
          >> METIS_TAC [sub_zero_lt],
          rw [fn_plus_def]
          >> fs [Abbr `B`]
          >> `x IN m_space m` by METIS_TAC [SUBSET_DEF]
          >> `u n x <= Normal b` by METIS_TAC [extreal_lt_def]
          >> `u n x - Normal b <= 0`
               by METIS_TAC [sub_le_zero, extreal_not_infty]
          >> METIS_TAC [let_antisym] ])
 >> Rewr'

 >> Know `!k. integral m (\x. (u k x - Normal b) * indicator_fn (s INTER B) x) =
              integral m (\x. u k x * indicator_fn (s INTER B) x) -
              integral m (\x. Normal b * indicator_fn (s INTER B) x)`
 >- (GEN_TAC
     >> Know `integral m (\x. (u k x - Normal b) * indicator_fn (s INTER B) x) =
              integral m (\x. u k x * indicator_fn (s INTER B) x -
                              Normal b * indicator_fn (s INTER B) x)`
     >- (MATCH_MP_TAC integral_cong >> rw []
         >> rw [indicator_fn_def, mul_rone, mul_rzero]
         >> METIS_TAC [sub_rzero])
     >> Rewr'
     >> HO_MATCH_MP_TAC integral_sub >> rw []
     >> ((HO_MATCH_MP_TAC integrable_mul_indicator >> rw []
          >> ((`!j. (\x. u j x) = u j` by rw [FUN_EQ_THM] >> rw [] >> NO_TAC)
              ORELSE (MATCH_MP_TAC integrable_const >> rw []))
          >> NO_TAC)
         ORELSE
         (DISJ1_TAC
          >> rw [indicator_fn_def, mul_rone, mul_rzero, num_not_infty,
                 extreal_not_infty]
          >> METIS_TAC [])))
 >> DISCH_TAC

 >> Know `!k. integrable m (\x. u k x * indicator_fn (s INTER B) x)`
 >- (GEN_TAC >> HO_MATCH_MP_TAC integrable_mul_indicator >> rw []
     >> `!j. (\x. u j x) = u j` by rw [FUN_EQ_THM] >> rw [])
 >> DISCH_TAC
 >> Know `integrable m (\x. Normal b * indicator_fn (s INTER B) x)`
 >- (HO_MATCH_MP_TAC integrable_mul_indicator >> rw []
     >> MATCH_MP_TAC integrable_const >> rw [])
 >> DISCH_TAC

 >> Know `integral m (\x. (u n x - Normal b) * indicator_fn (s INTER B) x) <=
          integral m (\x. (u (SUC n) x - Normal b) * indicator_fn (s INTER B) x)`
 >- (rw []
     >> `integral m (\x. u n x * indicator_fn (s INTER B) x) <=
         integral m (\x. u (SUC n) x * indicator_fn (s INTER B) x)`
          by (Q.PAT_X_ASSUM `sub_martingale m a u`
                (MP_TAC o REWRITE_RULE [sub_martingale_def])
              >> STRIP_TAC
              >> FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`, `s INTER B`])
              >> rw [])
     >> Know `integral m (\x. u n x * indicator_fn (s INTER B) x) <> PosInf /\
              integral m (\x. u n x * indicator_fn (s INTER B) x) <> NegInf`
     >- (MATCH_MP_TAC integrable_finite_integral >> rw [])
     >> STRIP_TAC
     >> Know `integral m (\x. u (SUC n) x * indicator_fn (s INTER B) x) <> PosInf /\
              integral m (\x. u (SUC n) x * indicator_fn (s INTER B) x) <> NegInf`
     >- (MATCH_MP_TAC integrable_finite_integral >> rw [])
     >> STRIP_TAC
     >> Know `integral m (\x. Normal b * indicator_fn (s INTER B) x) <> PosInf /\
              integral m (\x. Normal b * indicator_fn (s INTER B) x) <> NegInf`
     >- (MATCH_MP_TAC integrable_finite_integral >> rw [])
     >> STRIP_TAC
     >> `?p. integral m (\x. u n x * indicator_fn (s INTER B) x) = Normal p`
          by METIS_TAC [extreal_cases]
     >> `?q. integral m (\x. u (SUC n) x * indicator_fn (s INTER B) x) = Normal q`
          by METIS_TAC [extreal_cases]
     >> `?r. integral m (\x. Normal b * indicator_fn (s INTER B) x) = Normal r`
          by METIS_TAC [extreal_cases]
     >> fs [extreal_sub_def, extreal_le_eq]
     >> REAL_ASM_ARITH_TAC)
 >> DISCH_TAC

 >> Know `integral m (\x. (u (SUC n) x - Normal b) * indicator_fn (s INTER B) x) <=
          integral m (\x. fn_plus (\y. u (SUC n) y - Normal b) x *
                          indicator_fn (s INTER B) x)`
 >- (MATCH_MP_TAC integral_mono >> rw []
     >- (HO_MATCH_MP_TAC integrable_mul_indicator >> rw [])
     >- (HO_MATCH_MP_TAC integrable_mul_indicator >> rw [])
     >> Cases_on `x IN s INTER B` >> rw [indicator_fn_def, mul_rone, mul_rzero]
     >> rw [FN_PLUS_ALT, le_max1])
 >> DISCH_TAC

 >> Know `integral m (\x. fn_plus (\y. u (SUC n) y - Normal b) x *
                          indicator_fn (s INTER B) x) <=
          integral m (\x. fn_plus (\y. u (SUC n) y - Normal b) x *
                          indicator_fn s x)`
 >- (MATCH_MP_TAC integral_mono >> rw []
     >- (HO_MATCH_MP_TAC integrable_mul_indicator >> rw [])
     >- (HO_MATCH_MP_TAC integrable_mul_indicator >> rw [])
     >> Cases_on `x IN s` >> Cases_on `x IN B`
     >> rw [indicator_fn_def, mul_rone, mul_rzero, le_refl]
     >> rw [FN_PLUS_ALT, le_max2])
 >> DISCH_TAC
 >> METIS_TAC [le_trans]
QED

Theorem card_pos_interval[local] :
    !M. CARD {i | 0 < i /\ i <= M} = M
Proof
    GEN_TAC
 >> Know `{i | 0 < i /\ i <= M} = IMAGE SUC (count M)`
 >- (rw [EXTENSION, IN_COUNT]
     >> EQ_TAC >> rw []
     >- (Q.EXISTS_TAC `PRE x` >> FULL_SIMP_TAC arith_ss [])
     >> FULL_SIMP_TAC arith_ss [])
 >> Rewr'
 >> Know `CARD (IMAGE SUC (count M)) = CARD (count M)`
 >- (MATCH_MP_TAC CARD_IMAGE_INJ >> rw [])
 >> Rewr'
 >> rw [CARD_COUNT]
QED

Theorem upcrossings_le_horizon :
    !u b c N x. b < c ==> upcrossings u b c N x <= N
Proof
    rw [upcrossings_def]
 >> Know `{k | 0 < k /\ crossUT u b c N k x < N} SUBSET count N`
 >- (rw [SUBSET_DEF, IN_COUNT]
     >> `x' <= crossUT u b c N x' x` by METIS_TAC [crossUT_lower]
     >> FULL_SIMP_TAC arith_ss [])
 >> DISCH_TAC
 >> `FINITE {k | 0 < k /\ crossUT u b c N k x < N}`
      by METIS_TAC [SUBSET_FINITE, FINITE_COUNT]
 >> `CARD {k | 0 < k /\ crossUT u b c N k x < N} <= CARD (count N)`
      by METIS_TAC [CARD_SUBSET, FINITE_COUNT]
 >> FULL_SIMP_TAC arith_ss [CARD_COUNT]
QED

Theorem upcrossings_iff :
    !u b c N x k. b < c /\ 0 < k ==>
                  (crossUT u b c N k x < N <=> k <= upcrossings u b c N x)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC `cset = {k | 0 < k /\ crossUT u b c N k x < N}`
 >> Know `cset SUBSET count N`
 >- (rw [Abbr `cset`, SUBSET_DEF, IN_COUNT]
     >> `x' <= crossUT u b c N x' x` by METIS_TAC [crossUT_lower]
     >> FULL_SIMP_TAC arith_ss [])
 >> DISCH_TAC
 >> `FINITE cset` by METIS_TAC [SUBSET_FINITE, FINITE_COUNT]
 >> Know `!i j. 0 < i /\ i <= j /\ j IN cset ==> i IN cset`
 >- (rw [Abbr `cset`]
     >> `crossUT u b c N i x <= crossUT u b c N j x`
          by METIS_TAC [crossUT_mono]
     >> FULL_SIMP_TAC arith_ss [])
 >> DISCH_TAC
 >> `upcrossings u b c N x = CARD cset` by rw [upcrossings_def, Abbr `cset`]
 >> POP_ORW
 >> Cases_on `cset = {}`
 >- (`~(k IN cset)` by rw []
     >> fs [Abbr `cset`]
     >> FULL_SIMP_TAC arith_ss [CARD_EMPTY]
     >> METIS_TAC [])
 >> `MAX_SET cset IN cset /\ !y. y IN cset ==> y <= MAX_SET cset`
      by METIS_TAC [MAX_SET_DEF]
 >> Know `cset = {i | 0 < i /\ i <= MAX_SET cset}`
 >- (rw [EXTENSION]
     >> EQ_TAC >> rw []
     >- (fs [Abbr `cset`])
     >> METIS_TAC [])
 >> DISCH_TAC
 >> `CARD cset = MAX_SET cset` by METIS_TAC [card_pos_interval]
 >> POP_ORW
 >> EQ_TAC >> rw []
 >- (`k IN cset` by rw [Abbr `cset`] >> METIS_TAC [])
 >> `k IN cset` by METIS_TAC []
 >> fs [Abbr `cset`]
QED

Theorem sum_indicator_min[local] :
    !N U. EXTREAL_SUM_IMAGE (\k. if k < U then (1 :extreal) else 0) (count N) =
          &(MIN U N)
Proof
    Induct_on `N`
 >- rw [EXTREAL_SUM_IMAGE_EMPTY, MIN_DEF]
 >> GEN_TAC
 >> Know `EXTREAL_SUM_IMAGE (\k. if k < U then (1 :extreal) else 0)
            (count (SUC N)) =
          EXTREAL_SUM_IMAGE (\k. if k < U then (1 :extreal) else 0)
            (count N) + (if N < U then 1 else 0)`
 >- (HO_MATCH_MP_TAC EXTREAL_SUM_IMAGE_COUNT_SUC
     >> DISJ1_TAC >> rw [num_not_infty])
 >> Rewr'
 >> ASM_REWRITE_TAC []
 >> Cases_on `N < U`
 >- (`MIN U N = N /\ MIN U (SUC N) = SUC N` by FULL_SIMP_TAC arith_ss [MIN_DEF]
     >> ASM_REWRITE_TAC []
     >> rw [extreal_of_num_def, extreal_add_def, extreal_11, ADD1, REAL_ADD])
 >> `MIN U N = MIN U (SUC N)` by FULL_SIMP_TAC arith_ss [MIN_DEF]
 >> ASM_REWRITE_TAC [add_rzero]
QED

Theorem upcrossings_sum[local] :
    !m u b c N x. b < c /\ x IN m_space m ==>
       (&(upcrossings u b c N x) =
        EXTREAL_SUM_IMAGE
          (\k. indicator_fn
                 {y | y IN m_space m /\ crossUT u b c N (SUC k) y < N} x)
          (count N))
Proof
    rpt STRIP_TAC
 >> Know `EXTREAL_SUM_IMAGE
            (\k. indicator_fn
                   {y | y IN m_space m /\ crossUT u b c N (SUC k) y < N} x)
            (count N) =
          EXTREAL_SUM_IMAGE
            (\k. if k < upcrossings u b c N x then (1 :extreal) else 0)
            (count N)`
 >- (irule EXTREAL_SUM_IMAGE_EQ >> rw []
     >> ((DISJ1_TAC >> rw [indicator_fn_def, num_not_infty] >> NO_TAC)
         ORELSE ALL_TAC)
     >> rw [indicator_fn_def]
     >> `crossUT u b c N (SUC x') x < N <=>
         SUC x' <= upcrossings u b c N x`
          by (MATCH_MP_TAC upcrossings_iff >> rw [])
     >> FULL_SIMP_TAC arith_ss [])
 >> Rewr'
 >> rw [sum_indicator_min]
 >> `upcrossings u b c N x <= N` by METIS_TAC [upcrossings_le_horizon]
 >> `MIN (upcrossings u b c N x) N = upcrossings u b c N x`
      by FULL_SIMP_TAC arith_ss [MIN_DEF]
 >> rw []
QED

Theorem stopping_time_lt_measurable :
    !m a t N. filtered_measure_space m a /\ stopping_time a t ==>
              {x | x IN m_space m /\ t x < N} IN measurable_sets m
Proof
    rpt STRIP_TAC
 >> `measure_space m` by fs [filtered_measure_space_def]
 >> Cases_on `N`
 >- (`{x | x IN m_space m /\ t x < 0} = {}` by rw [EXTENSION]
     >> rw [MEASURE_SPACE_EMPTY_MEASURABLE])
 >> `{x | x IN m_space m /\ t x < SUC n} =
     {x | x IN m_space m /\ t x <= n}` by rw [EXTENSION, LT_SUC_LE]
 >> POP_ORW
 >> METIS_TAC [stopping_time_le_measurable, filtered_subsets_measurable]
QED

Theorem upcross_episode[local] :
    !m a u b c N k.
       sub_martingale m a u /\
       (!n. u n IN measurable (a n) Borel) /\
       measure m (m_space m) < PosInf /\
       (!n x. x IN m_space m ==> u n x <> PosInf /\ u n x <> NegInf) /\
       b < c ==>
       integral m (\x. fn_plus (\y. u (crossLT u b c N k x) y - Normal b) x) +
       Normal (c - b) *
         measure m {x | x IN m_space m /\ crossUT u b c N (SUC k) x < N} <=
       integral m (\x. fn_plus (\y. u (crossUT u b c N (SUC k) x) y - Normal b) x)
Proof
    rpt STRIP_TAC
 >> `filtered_measure_space m a`
      by fs [sub_martingale_def, sigma_finite_filtered_measure_space_def]
 >> `measure_space m` by fs [filtered_measure_space_def]
 >> Q.ABBREV_TAC `G = \n x. fn_plus (\y. u n y - Normal b) x`
 >> `sub_martingale m a G`
      by (rw [Abbr `G`] >> MATCH_MP_TAC sub_martingale_fn_plus >> rw [])
 >> `!n. integrable m (G n)` by fs [sub_martingale_def]
 >> Know `!n x. x IN m_space m ==> G n x <> PosInf /\ G n x <> NegInf`
 >- (rw [Abbr `G`, fn_plus_def, num_not_infty]
     >> METIS_TAC [sub_not_infty, extreal_not_infty])
 >> DISCH_TAC
 >> Know `!n x. 0 <= G n x`
 >- (rw [Abbr `G`] >> rw [FN_PLUS_POS])
 >> DISCH_TAC
 >> `!j. stopping_time a (\x. crossUT u b c N j x)`
      by METIS_TAC [crossUT_stopping_time]
 >> `!j. stopping_time a (\x. crossLT u b c N j x)`
      by METIS_TAC [crossLT_stopping_time]
 >> Q.ABBREV_TAC `Bk = {x | x IN m_space m /\ crossUT u b c N (SUC k) x < N}`
 >> Know `Bk IN measurable_sets m`
 >- (rw [Abbr `Bk`]
     >> HO_MATCH_MP_TAC stopping_time_lt_measurable
     >> Q.EXISTS_TAC `a` >> rw [])
 >> DISCH_TAC

 >> Know `integrable m (\x. G (crossLT u b c N k x) x)`
 >- (HO_MATCH_MP_TAC sampled_integrable
     >> Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `N`
     >> rw [crossLT_le_cap])
 >> DISCH_TAC
 >> Know `integrable m (\x. G (crossUT u b c N (SUC k) x) x)`
 >- (HO_MATCH_MP_TAC sampled_integrable
     >> Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `N`
     >> rw [crossUT_le_cap])
 >> DISCH_TAC
 >> Know `integrable m (\x. Normal (c - b) * indicator_fn Bk x)`
 >- (HO_MATCH_MP_TAC integrable_mul_indicator >> rw []
     >> MATCH_MP_TAC integrable_const >> rw [])
 >> DISCH_TAC

 >> Know `!x. x IN m_space m ==>
              G (crossLT u b c N k x) x + Normal (c - b) * indicator_fn Bk x <=
              G (crossUT u b c N (SUC k) x) x`
 >- (rpt STRIP_TAC
     >> Cases_on `x IN Bk`
     >- (`crossUT u b c N (SUC k) x < N` by fs [Abbr `Bk`]
         >> `crossLT u b c N k x < N`
              by (`crossLT u b c N k x <= crossUT u b c N (SUC k) x`
                    by rw [crossLT_le_crossUT_SUC]
                  >> FULL_SIMP_TAC arith_ss [])
         >> `u (crossLT u b c N k x) x <= Normal b` by METIS_TAC [crossLT_hit]
         >> `Normal c <= u (crossUT u b c N (SUC k) x) x`
              by METIS_TAC [crossUT_SUC_hit]
         >> Know `G (crossLT u b c N k x) x = 0`
         >- (rw [Abbr `G`, fn_plus_def]
             >> `u (crossLT u b c N k x) x - Normal b <= 0`
                  by METIS_TAC [sub_le_zero, extreal_not_infty]
             >> METIS_TAC [let_antisym])
         >> Rewr'
         >> rw [indicator_fn_def, mul_rone, add_lzero]
         >> Know `Normal (c - b) <= u (crossUT u b c N (SUC k) x) x - Normal b`
         >- (`?r. u (crossUT u b c N (SUC k) x) x = Normal r`
               by METIS_TAC [extreal_cases]
             >> fs [extreal_sub_def, extreal_le_eq]
             >> REAL_ASM_ARITH_TAC)
         >> DISCH_TAC
         >> MATCH_MP_TAC le_trans
         >> Q.EXISTS_TAC `u (crossUT u b c N (SUC k) x) x - Normal b`
         >> rw [Abbr `G`]
         >> rw [FN_PLUS_ALT, le_max1])
     >> rw [indicator_fn_def, mul_rzero, add_rzero]
     >> Cases_on `crossLT u b c N k x < N`
     >- (`u (crossLT u b c N k x) x <= Normal b` by METIS_TAC [crossLT_hit]
         >> Know `G (crossLT u b c N k x) x = 0`
         >- (rw [Abbr `G`, fn_plus_def]
             >> `u (crossLT u b c N k x) x - Normal b <= 0`
                  by METIS_TAC [sub_le_zero, extreal_not_infty]
             >> METIS_TAC [let_antisym])
         >> Rewr'
         >> rw [])
     >> `crossLT u b c N k x = N`
          by (`crossLT u b c N k x <= N` by rw [crossLT_le_cap]
              >> FULL_SIMP_TAC arith_ss [])
     >> `crossUT u b c N (SUC k) x = N`
          by (`crossLT u b c N k x <= crossUT u b c N (SUC k) x`
                by rw [crossLT_le_crossUT_SUC]
              >> `crossUT u b c N (SUC k) x <= N` by rw [crossUT_le_cap]
              >> FULL_SIMP_TAC arith_ss [])
     >> rw [le_refl])
 >> DISCH_TAC

 >> Know `integral m (\x. G (crossLT u b c N k x) x +
                          Normal (c - b) * indicator_fn Bk x) <=
          integral m (\x. G (crossUT u b c N (SUC k) x) x)`
 >- (MATCH_MP_TAC integral_mono >> rw []
     >> HO_MATCH_MP_TAC integrable_add >> rw []
     >> DISJ1_TAC >> rw [indicator_fn_def, mul_rone, mul_rzero, num_not_infty,
                         extreal_not_infty]
     >> METIS_TAC [])
 >> DISCH_TAC
 >> Know `integral m (\x. G (crossLT u b c N k x) x +
                          Normal (c - b) * indicator_fn Bk x) =
          integral m (\x. G (crossLT u b c N k x) x) +
          integral m (\x. Normal (c - b) * indicator_fn Bk x)`
 >- (HO_MATCH_MP_TAC integral_add >> rw []
     >> DISJ1_TAC >> rw [indicator_fn_def, mul_rone, mul_rzero, num_not_infty,
                         extreal_not_infty]
     >> METIS_TAC [])
 >> DISCH_TAC
 >> Know `integral m (\x. Normal (c - b) * indicator_fn Bk x) =
          Normal (c - b) * measure m Bk`
 >- (Know `integral m (\x. Normal (c - b) * indicator_fn Bk x) =
           pos_fn_integral m (\x. Normal (c - b) * indicator_fn Bk x)`
     >- (MATCH_MP_TAC integral_pos_fn >> rw []
         >> MATCH_MP_TAC le_mul
         >> rw [INDICATOR_FN_POS, extreal_of_num_def, extreal_le_eq]
         >> REAL_ASM_ARITH_TAC)
     >> Rewr'
     >> MATCH_MP_TAC pos_fn_integral_cmul_indicator >> rw []
     >> REAL_ASM_ARITH_TAC)
 >> DISCH_TAC
 >> Know `(\x. fn_plus (\y. u (crossLT u b c N k x) y - Normal b) x) =
          (\x. G (crossLT u b c N k x) x)`
 >- rw [Abbr `G`, FUN_EQ_THM]
 >> Rewr'
 >> Know `(\x. fn_plus (\y. u (crossUT u b c N (SUC k) x) y - Normal b) x) =
          (\x. G (crossUT u b c N (SUC k) x) x)`
 >- rw [Abbr `G`, FUN_EQ_THM]
 >> Rewr'
 >> METIS_TAC []
QED

Theorem upcross_partial[local] :
    !m a u b c N j.
       sub_martingale m a u /\
       (!n. u n IN measurable (a n) Borel) /\
       measure m (m_space m) < PosInf /\
       (!n x. x IN m_space m ==> u n x <> PosInf /\ u n x <> NegInf) /\
       b < c ==>
       integral m (\x. fn_plus (\y. u 0 y - Normal b) x) +
       Normal (c - b) *
         EXTREAL_SUM_IMAGE
           (\k. measure m {x | x IN m_space m /\ crossUT u b c N (SUC k) x < N})
           (count j) <=
       integral m (\x. fn_plus (\y. u (crossUT u b c N j x) y - Normal b) x)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> `filtered_measure_space m a`
      by fs [sub_martingale_def, sigma_finite_filtered_measure_space_def]
 >> `measure_space m` by fs [filtered_measure_space_def]
 >> Q.ABBREV_TAC `G = \n x. fn_plus (\y. u n y - Normal b) x`
 >> `sub_martingale m a G`
      by (rw [Abbr `G`] >> MATCH_MP_TAC sub_martingale_fn_plus >> rw [])
 >> `!n. integrable m (G n)` by fs [sub_martingale_def]
 >> Know `!n x. x IN m_space m ==> G n x <> PosInf /\ G n x <> NegInf`
 >- (rw [Abbr `G`, fn_plus_def, num_not_infty]
     >> METIS_TAC [sub_not_infty, extreal_not_infty])
 >> DISCH_TAC
 >> `!i. stopping_time a (\x. crossUT u b c N i x)`
      by METIS_TAC [crossUT_stopping_time]
 >> `!i. stopping_time a (\x. crossLT u b c N i x)`
      by METIS_TAC [crossLT_stopping_time]

 >> Q.ABBREV_TAC `MU = \k. measure m {x | x IN m_space m /\
                                          crossUT u b c N (SUC k) x < N}`
 >> Know `!k. {x | x IN m_space m /\ crossUT u b c N (SUC k) x < N}
              IN measurable_sets m`
 >- (GEN_TAC
     >> HO_MATCH_MP_TAC stopping_time_lt_measurable
     >> Q.EXISTS_TAC `a` >> rw [])
 >> DISCH_TAC
 >> Know `!k. 0 <= MU k /\ MU k <> PosInf /\ MU k <> NegInf`
 >- (GEN_TAC
     >> `0 <= MU k`
          by (rw [Abbr `MU`]
              >> METIS_TAC [MEASURE_SPACE_POSITIVE, positive_def])
     >> `MU k <= measure m (m_space m)`
          by (rw [Abbr `MU`]
              >> MATCH_MP_TAC INCREASING >> rw [SUBSET_DEF]
              >- METIS_TAC [MEASURE_SPACE_INCREASING]
              >> METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE])
     >> `MU k <> PosInf`
          by (CCONTR_TAC >> fs []
              >> METIS_TAC [le_infty, lt_infty, let_trans, lt_refl])
     >> rw []
     >> METIS_TAC [lt_infty, extreal_of_num_def, extreal_not_infty,
                   lte_trans, lt_refl]
 )
 >> DISCH_TAC

 >> Know `!t. stopping_time a t /\ (!x. t x <= N) ==>
              integrable m (\x. G (t x) x)`
 >- (rpt STRIP_TAC
     >> HO_MATCH_MP_TAC sampled_integrable
     >> Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `N` >> rw [])
 >> DISCH_TAC
 >> Induct_on `j`
 >- (rw [EXTREAL_SUM_IMAGE_EMPTY, mul_rzero, add_rzero, crossUT_def]
     >> rw [Abbr `G`, le_refl])

 >> Know `EXTREAL_SUM_IMAGE MU (count (SUC j)) =
          EXTREAL_SUM_IMAGE MU (count j) + MU j`
 >- (HO_MATCH_MP_TAC EXTREAL_SUM_IMAGE_COUNT_SUC
     >> DISJ1_TAC >> rw [])
 >> Rewr'

 >> Know `integral m (\x. G (crossUT u b c N j x) x) <=
          integral m (\x. G (crossLT u b c N j x) x)`
 >- (HO_MATCH_MP_TAC optional_sampling_sub
     >> Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `N`
     >> rw [crossUT_le_crossLT, crossLT_le_cap]
     >> `!i. (\x. crossLT u b c N i x) = crossLT u b c N i`
          by rw [FUN_EQ_THM]
     >> `!i. (\x. crossUT u b c N i x) = crossUT u b c N i`
          by rw [FUN_EQ_THM]
     >> METIS_TAC [])
 >> DISCH_TAC
 >> Know `integral m (\x. G (crossLT u b c N j x) x) +
          Normal (c - b) * MU j <=
          integral m (\x. G (crossUT u b c N (SUC j) x) x)`
 >- (rw [Abbr `MU`, Abbr `G`]
     >> MP_TAC (Q.SPECL [`m`, `a`, `u`, `b`, `c`, `N`, `j`] upcross_episode)
     >> rw [])
 >> DISCH_TAC
 >> Know `!t. stopping_time a t /\ (!x. t x <= N) ==>
              integral m (\x. G (t x) x) <> PosInf /\
              integral m (\x. G (t x) x) <> NegInf`
 >- (GEN_TAC >> STRIP_TAC
     >> MATCH_MP_TAC integrable_finite_integral >> rw [])
 >> DISCH_TAC
 >> `integral m (\x. G (crossUT u b c N j x) x) <> PosInf /\
     integral m (\x. G (crossUT u b c N j x) x) <> NegInf`
      by (Q.PAT_ASSUM `!t. _ ==> integral m _ <> PosInf /\ _`
            (MP_TAC o Q.SPEC `\x. crossUT u b c N j (x :'a)`)
          >> rw [crossUT_le_cap])
 >> `integral m (\x. G (crossLT u b c N j x) x) <> PosInf /\
     integral m (\x. G (crossLT u b c N j x) x) <> NegInf`
      by (Q.PAT_ASSUM `!t. _ ==> integral m _ <> PosInf /\ _`
            (MP_TAC o Q.SPEC `\x. crossLT u b c N j (x :'a)`)
          >> rw [crossLT_le_cap])
 >> `integral m (\x. G (crossUT u b c N (SUC j) x) x) <> PosInf /\
     integral m (\x. G (crossUT u b c N (SUC j) x) x) <> NegInf`
      by (Q.PAT_ASSUM `!t. _ ==> integral m _ <> PosInf /\ _`
            (MP_TAC o Q.SPEC `\x. crossUT u b c N (SUC j) (x :'a)`)
          >> rw [crossUT_le_cap])
 >> Know `integral m (\x. G 0 x) <> PosInf /\
          integral m (\x. G 0 x) <> NegInf`
 >- (MATCH_MP_TAC integrable_finite_integral >> rw []
     >> `(\x. G 0 x) = G 0` by rw [FUN_EQ_THM] >> rw [])
 >> STRIP_TAC

 >> Know `integral m (\x. fn_plus (\y. u 0 y - Normal b) x) =
          integral m (\x. G 0 x)`
 >- rw [Abbr `G`]
 >> DISCH_TAC
 >> Know `integral m (\x. fn_plus (\y. u (crossUT u b c N j x) y - Normal b) x) =
          integral m (\x. G (crossUT u b c N j x) x)`
 >- rw [Abbr `G`]
 >> DISCH_TAC
 >> Know `integral m (\x. fn_plus (\y. u (crossUT u b c N (SUC j) x) y -
                                   Normal b) x) =
          integral m (\x. G (crossUT u b c N (SUC j) x) x)`
 >- rw [Abbr `G`]
 >> DISCH_TAC
 >> fs []

 >> Q.ABBREV_TAC `X0 = integral m (\x. G 0 x)`
 >> Q.ABBREV_TAC `EJ = integral m (\x. G (crossUT u b c N j x) x)`
 >> Q.ABBREV_TAC `LJ = integral m (\x. G (crossLT u b c N j x) x)`
 >> Q.ABBREV_TAC `ES = integral m (\x. G (crossUT u b c N (SUC j) x) x)`
 >> Q.ABBREV_TAC `SG = EXTREAL_SUM_IMAGE MU (count j)`
 >> `0 <= SG /\ SG <> PosInf /\ SG <> NegInf`
      by (rw [Abbr `SG`]
          >| [ MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> rw [],
               METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY, FINITE_COUNT],
               METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY, FINITE_COUNT] ])
 >> `?x0. X0 = Normal x0` by METIS_TAC [extreal_cases]
 >> `?ej. EJ = Normal ej` by METIS_TAC [extreal_cases]
 >> `?lj. LJ = Normal lj` by METIS_TAC [extreal_cases]
 >> `?es. ES = Normal es` by METIS_TAC [extreal_cases]
 >> `?sg. SG = Normal sg` by METIS_TAC [extreal_cases]
 >> `?mj. MU j = Normal mj` by METIS_TAC [extreal_cases]
 >> fs [extreal_add_def, extreal_mul_def, extreal_le_eq, extreal_11]
 >> REAL_ASM_ARITH_TAC
QED

Theorem upcrossing_inequality :
    !m a u b c N.
       sub_martingale m a u /\
       (!n. u n IN measurable (a n) Borel) /\
       measure m (m_space m) < PosInf /\
       (!n x. x IN m_space m ==> u n x <> PosInf /\ u n x <> NegInf) /\
       b < c ==>
       integral m (\x. fn_plus (\y. u 0 y - Normal b) x) +
       Normal (c - b) * pos_fn_integral m (\x. &(upcrossings u b c N x)) <=
       integral m (\x. fn_plus (\y. u N y - Normal b) x)
Proof
    rpt STRIP_TAC
 >> `filtered_measure_space m a`
      by fs [sub_martingale_def, sigma_finite_filtered_measure_space_def]
 >> `measure_space m` by fs [filtered_measure_space_def]
 >> Know `!k. {x | x IN m_space m /\ crossUT u b c N (SUC k) x < N}
              IN measurable_sets m`
 >- (GEN_TAC
     >> HO_MATCH_MP_TAC stopping_time_lt_measurable
     >> Q.EXISTS_TAC `a`
     >> rw []
     >> METIS_TAC [crossUT_stopping_time])
 >> DISCH_TAC

 >> Know `pos_fn_integral m (\x. &(upcrossings u b c N x)) =
          EXTREAL_SUM_IMAGE
            (\k. measure m {x | x IN m_space m /\ crossUT u b c N (SUC k) x < N})
            (count N)`
 >- (Know `pos_fn_integral m (\x. &(upcrossings u b c N x)) =
           pos_fn_integral m
             (\x. EXTREAL_SUM_IMAGE
                    (\k. indicator_fn
                           {y | y IN m_space m /\ crossUT u b c N (SUC k) y < N}
                           x)
                    (count N))`
     >- (MATCH_MP_TAC pos_fn_integral_cong >> rw []
         >> ((rw [extreal_of_num_def, extreal_le_eq, REAL_POS] >> NO_TAC)
             ORELSE (MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
                     >> rw [INDICATOR_FN_POS] >> NO_TAC)
             ORELSE (MATCH_MP_TAC upcrossings_sum >> rw [])))
     >> Rewr'
     >> Know `!k. indicator_fn
                    {y | y IN m_space m /\ crossUT u b c N (SUC k) y < N}
                    IN measurable (m_space m,measurable_sets m) Borel`
     >- (GEN_TAC
         >> MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR
         >> Q.EXISTS_TAC `{y | y IN m_space m /\ crossUT u b c N (SUC k) y < N}`
         >> rw []
         >> METIS_TAC [measure_space_def, subsets_def, space_def,
                       MEASURE_SPACE_SIGMA_ALGEBRA])
     >> DISCH_TAC
     >> Know `pos_fn_integral m
                (\x. EXTREAL_SUM_IMAGE
                       (\k. indicator_fn
                              {y | y IN m_space m /\
                                   crossUT u b c N (SUC k) y < N} x)
                       (count N)) =
              EXTREAL_SUM_IMAGE
                (\k. pos_fn_integral m
                       (indicator_fn
                          {y | y IN m_space m /\ crossUT u b c N (SUC k) y < N}))
                (count N)`
     >- (MP_TAC (Q.ISPECL
           [`m :'a m_space`,
            `\k. indicator_fn
                  {y | y IN m_space (m :'a m_space) /\
                       crossUT (u :num -> 'a -> extreal) b c N (SUC k) y < N}`,
            `count N`] pos_fn_integral_sum)
         >> rw [INDICATOR_FN_POS])
     >> Rewr'
     >> irule EXTREAL_SUM_IMAGE_EQ >> rw []
     >> ((DISJ1_TAC >> rw []
          >> MATCH_MP_TAC pos_not_neginf
          >> ((MATCH_MP_TAC pos_fn_integral_pos >> rw [INDICATOR_FN_POS])
              ORELSE METIS_TAC [MEASURE_SPACE_POSITIVE, positive_def])
          >> NO_TAC)
         ORELSE
         (MATCH_MP_TAC pos_fn_integral_indicator >> rw [])))
 >> Rewr'

 >> Know `integral m (\x. fn_plus (\y. u (crossUT u b c N N x) y - Normal b) x) =
          integral m (\x. fn_plus (\y. u N y - Normal b) x)`
 >- (MATCH_MP_TAC integral_cong >> rw []
     >> rw [crossUT_cap])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [`m`, `a`, `u`, `b`, `c`, `N`, `N`] upcross_partial)
 >> rw []
QED

Theorem hitting_cap_mono[local] :
    !P u n N x. hitting P u n N x < N ==>
                (hitting P u n (SUC N) x = hitting P u n N x)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC `h = hitting P u n N x`
 >> `n <= h /\ P (u h x)` by METIS_TAC [hitting_hit]
 >> `h <= N` by rw [Abbr `h`, hitting_le_cap]
 >> `hitting P u n (SUC N) x <= h`
      by (MATCH_MP_TAC hitting_least >> FULL_SIMP_TAC arith_ss [])
 >> Q.ABBREV_TAC `h' = hitting P u n (SUC N) x`
 >> `h' < SUC N` by FULL_SIMP_TAC arith_ss []
 >> `n <= h' /\ P (u h' x)` by METIS_TAC [hitting_hit]
 >> `h <= h'`
      by (Q.UNABBREV_TAC `h`
          >> MATCH_MP_TAC hitting_least >> FULL_SIMP_TAC arith_ss [])
 >> FULL_SIMP_TAC arith_ss []
QED

Theorem crossUT_horizon_suc[local] :
    !u b c N x k. crossUT u b c N k x < N ==>
                  (crossUT u b c (SUC N) k x = crossUT u b c N k x)
Proof
    NTAC 5 GEN_TAC
 >> Induct_on `k`
 >- rw [crossUT_def]
 >> STRIP_TAC
 >> `crossUT u b c N k x <= crossLT u b c N k x /\
     crossLT u b c N k x <= crossUT u b c N (SUC k) x`
      by rw [crossUT_le_crossLT, crossLT_le_crossUT_SUC]
 >> `crossUT u b c N k x < N /\ crossLT u b c N k x < N`
      by FULL_SIMP_TAC arith_ss []
 >> `crossUT u b c (SUC N) k x = crossUT u b c N k x` by METIS_TAC []
 >> Know `crossLT u b c (SUC N) k x = crossLT u b c N k x`
 >- (rw [crossLT_def]
     >> METIS_TAC [hitting_cap_mono, crossLT_def])
 >> DISCH_TAC
 >> rw [crossUT_def, GSYM crossLT_def]
 >> METIS_TAC [hitting_cap_mono, crossUT_def, GSYM crossLT_def]
QED

Theorem upcrossings_mono_suc[local] :
    !u b c N x. b < c ==>
                upcrossings u b c N x <= upcrossings u b c (SUC N) x
Proof
    rpt STRIP_TAC
 >> rw [upcrossings_def]
 >> Know `FINITE {k | 0 < k /\ crossUT u b c (SUC N) k x < SUC N}`
 >- (Know `{k | 0 < k /\ crossUT u b c (SUC N) k x < SUC N} SUBSET
           count (SUC N)`
     >- (rw [SUBSET_DEF, IN_COUNT]
         >> `x' <= crossUT u b c (SUC N) x' x` by METIS_TAC [crossUT_lower]
         >> FULL_SIMP_TAC arith_ss [])
     >> METIS_TAC [SUBSET_FINITE, FINITE_COUNT])
 >> DISCH_TAC
 >> Know `{k | 0 < k /\ crossUT u b c N k x < N} SUBSET
          {k | 0 < k /\ crossUT u b c (SUC N) k x < SUC N}`
 >- (rw [SUBSET_DEF]
     >> `crossUT u b c (SUC N) x' x = crossUT u b c N x' x`
          by METIS_TAC [crossUT_horizon_suc]
     >> FULL_SIMP_TAC arith_ss [])
 >> DISCH_TAC
 >> METIS_TAC [CARD_SUBSET]
QED

Theorem crossUT_horizon_le[local] :
    !u b c x k N M. N <= M /\ crossUT u b c N k x < N ==>
                    (crossUT u b c M k x = crossUT u b c N k x)
Proof
    NTAC 5 GEN_TAC
 >> Suff `!d N. crossUT u b c N k x < N ==>
                (crossUT u b c (N + d) k x = crossUT u b c N k x)`
 >- (rpt STRIP_TAC
     >> `M = N + (M - N)` by FULL_SIMP_TAC arith_ss []
     >> METIS_TAC [])
 >> Induct_on `d`
 >- rw []
 >> rpt STRIP_TAC
 >> `N + SUC d = SUC (N + d)` by FULL_SIMP_TAC arith_ss []
 >> POP_ORW
 >> `crossUT u b c (N + d) k x = crossUT u b c N k x` by METIS_TAC []
 >> `crossUT u b c (N + d) k x < N + d` by FULL_SIMP_TAC arith_ss []
 >> METIS_TAC [crossUT_horizon_suc]
QED

Theorem upcross_unbounded[local] :
    !u b c x. b < c /\
              (!mm. ?n. mm <= n /\ u n x < Normal b) /\
              (!mm. ?n. mm <= n /\ Normal c < u n x) ==>
              !kk. ?N. kk <= upcrossings u b c N x
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Induct_on `kk`
 >- (Q.EXISTS_TAC `0` >> rw [])
 >> POP_ASSUM STRIP_ASSUME_TAC

 >> Know `?H. crossUT u b c H kk x < H`
 >- (Cases_on `kk = 0`
     >- (Q.EXISTS_TAC `SUC 0` >> rw [crossUT_def])
     >> Q.EXISTS_TAC `N`
     >> `0 < kk` by FULL_SIMP_TAC arith_ss []
     >> METIS_TAC [upcrossings_iff])
 >> STRIP_TAC

 >> Q.PAT_X_ASSUM `!mm. ?n. mm <= n /\ u n x < Normal b`
      (MP_TAC o Q.SPEC `H + crossUT u b c H kk x + 1`)
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM `!mm. ?n. mm <= n /\ Normal c < u n x`
      (MP_TAC o Q.SPEC `n + 1`)
 >> STRIP_TAC
 >> Q.EXISTS_TAC `SUC n'`
 >> `0 < SUC kk` by rw []
 >> Suff `crossUT u b c (SUC n') (SUC kk) x < SUC n'`
 >- METIS_TAC [upcrossings_iff]
 >> `H <= SUC n'` by FULL_SIMP_TAC arith_ss []
 >> `crossUT u b c (SUC n') kk x = crossUT u b c H kk x`
      by METIS_TAC [crossUT_horizon_le]

 >> Know `crossLT u b c (SUC n') kk x <= n`
 >- (rw [crossLT_def]
     >> MATCH_MP_TAC hitting_least
     >> FULL_SIMP_TAC arith_ss []
     >> METIS_TAC [lt_imp_le])
 >> DISCH_TAC

 >> Know `crossUT u b c (SUC n') (SUC kk) x <= n'`
 >- (rw [crossUT_def, GSYM crossLT_def]
     >> MATCH_MP_TAC hitting_least
     >> FULL_SIMP_TAC arith_ss []
     >> METIS_TAC [lt_imp_le])
 >> DISCH_TAC
 >> FULL_SIMP_TAC arith_ss []
QED

Theorem upcrossings_measurable :
    !m a u b c N.
       filtered_measure_space m a /\
       (!n. u n IN measurable (a n) Borel) /\ b < c ==>
       (\x. &(upcrossings u b c N x)) IN
         measurable (m_space m, measurable_sets m) Borel
Proof
    rpt STRIP_TAC
 >> `measure_space m` by fs [filtered_measure_space_def]
 >> Know `!k. {x | x IN m_space m /\ crossUT u b c N (SUC k) x < N}
              IN measurable_sets m`
 >- (GEN_TAC
     >> HO_MATCH_MP_TAC stopping_time_lt_measurable
     >> Q.EXISTS_TAC `a`
     >> rw []
     >> METIS_TAC [crossUT_stopping_time])
 >> DISCH_TAC
 >> MATCH_MP_TAC (INST_TYPE [beta |-> ``:num``] IN_MEASURABLE_BOREL_SUM')
 >> Q.EXISTS_TAC `\k. indicator_fn
                        {y | y IN m_space m /\ crossUT u b c N (SUC k) y < N}`
 >> Q.EXISTS_TAC `count N`
 >> rw [space_def, subsets_def]
 >> ((fs [measure_space_def] >> NO_TAC)
     ORELSE
     (MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR
      >> Q.EXISTS_TAC `{y | y IN m_space m /\
                            crossUT u b c N (SUC i) y < N}`
      >> rw [space_def, subsets_def]
      >> fs [measure_space_def]
      >> NO_TAC)
     ORELSE
     (MATCH_MP_TAC upcrossings_sum >> rw []))
QED

val _ = export_theory ();
