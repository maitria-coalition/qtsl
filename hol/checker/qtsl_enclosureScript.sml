(*
  The remainder-bound (enclosure) rule: certified Maclaurin-tail
  bounds for exp/sin/cos, checked over exact rationals — including the
  meaning theorem (encCheck_sound) against the distribution's
  transcendental functions, whose defining series coincide with the
  per-index coefficient series this rule consumes.
*)
Theory qtsl_enclosure
Ancestors
  arithmetic list rat integer real real_of_rat seq transc
Libs
  bossLib realLib RealField

Datatype:
  fnTag = FTExp | FTSin | FTCos
End

Definition ratPow_def:
  ratPow (q:rat) 0 = 1 ∧
  ratPow q (SUC n) = q * ratPow q n
End

Definition maclaurin_def:
  maclaurin t k =
    case t of
      FTExp => 1 / &FACT k
    | FTSin => if ¬EVEN k then ratPow (-1) ((k - 1) DIV 2) / &FACT k else 0
    | FTCos => if EVEN k then ratPow (-1) (k DIV 2) / &FACT k else 0 : rat
End

Datatype:
  encWitness = <| tag : fnTag; n : num; r : rat; R : rat; coeffs : rat list |>
End

Definition tailBound_def:
  tailBound n (r:rat) =
    ratPow r (n + 1) / &FACT (n + 1) * ((&n + 2) / (&n + 2 - r))
End

Definition encCheck_def:
  encCheck w ⇔
    LENGTH w.coeffs = w.n + 1 ∧
    w.coeffs = GENLIST (maclaurin w.tag) (w.n + 1) ∧
    0 ≤ w.r ∧ w.r < &w.n + 2 ∧
    tailBound w.n w.r ≤ w.R
End

Definition fnEval_def:
  fnEval FTExp x = exp x ∧
  fnEval FTSin x = sin x ∧
  fnEval FTCos x = cos x
End

Definition evalPolyR_def:
  evalPolyR cs (x:real) =
    sum (0, LENGTH cs) (λk. real_of_rat (EL k cs) * x pow k)
End

Definition coeffR_def:
  coeffR t k =
    case t of
      FTExp => inv (&FACT k)
    | FTSin => if EVEN k then 0 else -1 pow ((k - 1) DIV 2) / &FACT k
    | FTCos => if EVEN k then -1 pow (k DIV 2) / &FACT k else 0 : real
End

Theorem COEFFR_CONVERGES:
  ∀t x. (λk. coeffR t k * x pow k) sums fnEval t x
Proof
  Cases >> gen_tac >> rw[coeffR_def, fnEval_def]
  >- (‘(λk. (λn. inv (&FACT n)) k * x pow k) sums exp x’
        by ACCEPT_TAC (SPEC “x:real” EXP_CONVERGES) >> gvs[])
  >- (‘(λk. (λn. if EVEN n then 0 else -1 pow ((n - 1) DIV 2) / &FACT n) k * x pow k)
        sums sin x’ by ACCEPT_TAC (SPEC “x:real” SIN_CONVERGES) >> gvs[])
  >- (‘(λk. (λn. if EVEN n then -1 pow (n DIV 2) / &FACT n else 0) k * x pow k)
        sums cos x’ by ACCEPT_TAC (SPEC “x:real” COS_CONVERGES) >> gvs[])
QED

Theorem ROR_MUL[local]:
  real_of_rat (a * b) = real_of_rat a * real_of_rat b
Proof
  metis_tac[REAL_OF_RAT_MUL]
QED

Theorem ROR_ADD[local]:
  real_of_rat (a + b) = real_of_rat a + real_of_rat b
Proof
  metis_tac[REAL_OF_RAT_ADD]
QED

Theorem ROR_SUB[local]:
  real_of_rat (a - b) = real_of_rat a - real_of_rat b
Proof
  metis_tac[REAL_OF_RAT_SUB]
QED

Theorem ROR_NEG[local]:
  real_of_rat (-a) = -real_of_rat a
Proof
  metis_tac[REAL_OF_RAT_NEG]
QED

Theorem ROR_DIV[local]:
  b ≠ 0 ⇒ real_of_rat (a / b) = real_of_rat a / real_of_rat b
Proof
  metis_tac[REAL_OF_RAT_DIV]
QED

Theorem RAT_FACT_NZ[local]:
  &FACT k ≠ (0:rat)
Proof
  ‘0 < FACT k’ by rw[FACT_LESS] >> Cases_on ‘FACT k’ >> gvs[]
QED

Theorem REAL_OF_RAT_POW:
  ∀n q. real_of_rat (ratPow q n) = real_of_rat q pow n
Proof
  Induct >> rw[ratPow_def, pow, ROR_MUL]
QED

Theorem REAL_OF_RAT_FACT:
  real_of_rat (&FACT k) = &FACT k
Proof
  rw[REAL_OF_RAT_OF_NUM]
QED

Theorem REAL_OF_RAT_M1_POW:
  real_of_rat (ratPow (-1) m) = -1 pow m
Proof
  rw[REAL_OF_RAT_POW, ROR_NEG, REAL_OF_RAT_1]
QED

Theorem MACLAURIN_COEFFR:
  ∀t k. real_of_rat (maclaurin t k) = coeffR t k
Proof
  Cases >> gen_tac >>
  rw[maclaurin_def, coeffR_def, ROR_DIV, RAT_FACT_NZ, REAL_OF_RAT_FACT,
     REAL_OF_RAT_M1_POW, REAL_OF_RAT_0, REAL_OF_RAT_1] >>
  gvs[REAL_INV_1OVER]
QED

Theorem ABS_M1_POW:
  ∀m. abs (((-1) : real) pow m) = 1
Proof
  Induct >> rw[pow, ABS_MUL, ABS_NEG, ABS_1]
QED

Theorem ABS_COEFFR_LE:
  ∀t k. abs (coeffR t k) ≤ inv (&FACT k)
Proof
  Cases >> gen_tac >> rw[coeffR_def, real_div, ABS_MUL, ABS_M1_POW] >>
  rw[abs] >> gvs[REAL_LE_INV_EQ, REAL_POS]
QED

Theorem FACT_MUL_EXP_LE:
  ∀j N. FACT N * (N + 1) EXP j ≤ FACT (N + j)
Proof
  Induct >- rw[EXP] >>
  gen_tac >>
  ‘N + SUC j = SUC (N + j)’ by decide_tac >>
  rw[EXP, FACT] >>
  ‘FACT N * (N + 1) * (N + 1) EXP j = (FACT N * (N + 1) EXP j) * (N + 1)’
    by metis_tac[MULT_ASSOC, MULT_COMM] >>
  pop_assum SUBST1_TAC >>
  irule LESS_MONO_MULT2 >> conj_tac >- metis_tac[] >> decide_tac
QED

Theorem INV_MONO_RMUL[local]:
  ∀z y c m. 0 < (z:real) ∧ z ≤ y ∧ 0 ≤ (c:real) ⇒
            inv y * c pow m ≤ inv z * c pow m
Proof
  rpt strip_tac >>
  metis_tac[REAL_LE_MUL2, REAL_LE_INV2, REAL_LE_INV_EQ, POW_POS,
            REAL_LE_REFL, REAL_LT_IMP_LE, REAL_LE_TRANS]
QED

Theorem TERM_LE:
  ∀t x rr N j.
    abs x ≤ rr ⇒
    abs (coeffR t (j + N) * x pow (j + N)) ≤
      rr pow N / &FACT N * (rr / (&N + 1)) pow j
Proof
  rpt strip_tac >>
  ‘0 ≤ rr’ by (irule REAL_LE_TRANS >> qexists_tac ‘abs x’ >> rw[ABS_POS]) >>
  ‘abs (x pow (j + N)) ≤ rr pow (j + N)’
    by metis_tac[POW_ABS, POW_LE, ABS_POS] >>
  ‘abs (coeffR t (j + N) * x pow (j + N)) ≤ inv (&FACT (j + N)) * rr pow (j + N)’
    by metis_tac[ABS_MUL, REAL_LE_MUL2, ABS_POS, ABS_COEFFR_LE] >>
  irule REAL_LE_TRANS >> qexists_tac ‘inv (&FACT (j + N)) * rr pow (j + N)’ >>
  simp[] >>
  ‘(0:real) < &(FACT N * (N + 1) EXP j)’ by (rw[REAL_LT] >> simp[FACT_LESS, EXP_EQ_0]) >>
  ‘&(FACT N * (N + 1) EXP j) ≤ (&FACT (j + N) : real)’
    by (rw[REAL_LE] >> metis_tac[FACT_MUL_EXP_LE, ADD_COMM]) >>
  ‘inv (&FACT (j + N)) * rr pow (j + N) ≤
     inv (&(FACT N * (N + 1) EXP j)) * rr pow (j + N)’
    by (irule INV_MONO_RMUL >> simp[]) >>
  irule REAL_LE_TRANS >>
  qexists_tac ‘inv (&(FACT N * (N + 1) EXP j)) * rr pow (j + N)’ >> simp[] >>
  ‘(&(FACT N * (N + 1) EXP j) : real) = (&FACT N) * (&N + 1) pow j’
    by (rw[GSYM REAL_MUL, GSYM REAL_OF_NUM_POW] >> simp[GSYM REAL_ADD]) >>
  pop_assum SUBST1_TAC >>
  rw[POW_ADD, REAL_POW_DIV, REAL_INV_MUL', GSYM REAL_POW_INV, real_div] >>
  RealField.REAL_FIELD_TAC
QED

Theorem MAJORANT_SUMS:
  ∀rr N.
    0 ≤ rr ∧ rr < &N + 1 ⇒
    (λj. rr pow N / &FACT N * (rr / (&N + 1)) pow j) sums
      (rr pow N / &FACT N * ((&N + 1) / (&N + 1 - rr)))
Proof
  rpt strip_tac >>
  ‘0 < (&N + 1):real’ by (irule REAL_LET_TRANS >> qexists_tac ‘rr’ >> simp[]) >>
  ‘(&N + 1):real ≠ 0’ by simp[REAL_LT_IMP_NE] >>
  ‘(&N + 1) - rr ≠ (0:real)’ by RealField.REAL_ASM_ARITH_TAC >>
  ‘0 ≤ rr / (&N + 1)’
    by metis_tac[real_div, REAL_LE_MUL, REAL_LE_INV_EQ, REAL_LT_IMP_LE] >>
  ‘abs (rr / (&N + 1)) < 1’
    by metis_tac[ABS_REFL, REAL_LT_LDIV_EQ, REAL_MUL_LID] >>
  drule GP >> strip_tac >>
  drule_then (qspec_then ‘rr pow N / &FACT N’ assume_tac) SER_CMUL >>
  ‘((&N + 1) ≠ (0:real) ∧ (&N + 1) - rr ≠ (0:real)) ⇒
   (1 - rr / (&N + 1)) * ((&N + 1) / (&N + 1 - rr)) = 1’
    by RealField.REAL_FIELD_TAC >>
  ‘(1 - rr / (&N + 1)) * ((&N + 1) / (&N + 1 - rr)) = 1’ by gvs[] >>
  ‘(&N + 1) / (&N + 1 - rr) = inv (1 - rr / (&N + 1))’
    by metis_tac[REAL_RINV_UNIQ] >>
  gvs[]
QED

Theorem TAIL_MAIN:
  ∀t x rr N.
    abs x ≤ rr ∧ rr < &N + 1 ⇒
    abs (fnEval t x - sum (0, N) (λk. coeffR t k * x pow k)) ≤
      rr pow N / &FACT N * ((&N + 1) / (&N + 1 - rr))
Proof
  rpt strip_tac >>
  ‘0 ≤ rr’ by (irule REAL_LE_TRANS >> qexists_tac ‘abs x’ >> rw[ABS_POS]) >>
  qabbrev_tac ‘f = λk. coeffR t k * x pow k’ >>
  ‘f sums fnEval t x’ by metis_tac[COEFFR_CONVERGES] >>
  ‘summable f’ by metis_tac[SUM_SUMMABLE] >>
  ‘fnEval t x = suminf f’ by metis_tac[SUM_UNIQ] >>
  ‘(λj. f (j + N)) sums (suminf f - sum (0, N) f)’ by metis_tac[SER_OFFSET] >>
  qabbrev_tac ‘m = λj. rr pow N / &FACT N * (rr / (&N + 1)) pow j’ >>
  ‘m sums (rr pow N / &FACT N * ((&N + 1) / (&N + 1 - rr)))’
    by metis_tac[MAJORANT_SUMS] >>
  ‘summable m’ by metis_tac[SUM_SUMMABLE] >>
  ‘∀j. abs (f (j + N)) ≤ m j’
    by (rw[Abbr‘f’, Abbr‘m’] >> metis_tac[TERM_LE]) >>
  ‘summable (λj. f (j + N))’
    by metis_tac[SER_COMPAR, GREATER_EQ, ZERO_LESS_EQ] >>
  ‘summable (λj. abs (f (j + N)))’
    by metis_tac[SER_COMPAR, GREATER_EQ, ZERO_LESS_EQ, ABS_ABS] >>
  ‘abs (suminf (λj. f (j + N))) ≤ suminf (λj. abs (f (j + N)))’
    by metis_tac[SER_ABS] >>
  ‘suminf (λj. abs (f (j + N))) ≤ suminf m’
    by (irule SER_LE >> simp[]) >>
  ‘suminf m = rr pow N / &FACT N * ((&N + 1) / (&N + 1 - rr))’
    by metis_tac[SUM_UNIQ] >>
  ‘suminf (λj. f (j + N)) = suminf f - sum (0, N) f’ by metis_tac[SUM_UNIQ] >>
  gvs[]
QED

Theorem RAT_CAST_NZ[local]:
  real_of_rat d ≠ 0 ⇒ d ≠ 0
Proof
  metis_tac[REAL_OF_RAT_0]
QED

Theorem ENCCHECK_TAILBOUND_REAL:
  ∀n r. r < &n + 2 ⇒
    real_of_rat (tailBound n r) =
    real_of_rat r pow (n + 1) / &FACT (n + 1) *
      ((&n + 2) / (&n + 2 - real_of_rat r))
Proof
  rpt strip_tac >>
  ‘real_of_rat r < real_of_rat (&n + 2)’ by metis_tac[REAL_OF_RAT_LT] >>
  ‘real_of_rat (&n + 2) = &n + 2’
    by rw[ROR_ADD, REAL_OF_RAT_OF_NUM] >>
  ‘(&n + 2 - r) ≠ (0:rat)’
    by (irule RAT_CAST_NZ >> rw[ROR_SUB] >> gvs[] >> REAL_ARITH_TAC) >>
  rw[tailBound_def, ROR_MUL, ROR_DIV, RAT_FACT_NZ, REAL_OF_RAT_POW,
     REAL_OF_RAT_FACT, ROR_ADD, ROR_SUB, REAL_OF_RAT_OF_NUM]
QED

Theorem encCheck_sound:
  ∀w x.
    encCheck w ∧ abs x ≤ real_of_rat w.r ⇒
    abs (fnEval w.tag x - evalPolyR w.coeffs x) ≤ real_of_rat w.R
Proof
  rpt strip_tac >> gvs[encCheck_def] >>
  ‘evalPolyR (GENLIST (maclaurin w.tag) (w.n + 1)) x =
   sum (0, w.n + 1) (λk. coeffR w.tag k * x pow k)’
    by (rw[evalPolyR_def, LENGTH_GENLIST] >> irule SUM_EQ >>
        rw[EL_GENLIST, MACLAURIN_COEFFR]) >>
  ‘(&(w.n + 1) + 1 : real) = &w.n + 2’
    by (rw[GSYM REAL_ADD] >> REAL_ARITH_TAC) >>
  ‘real_of_rat (&w.n + 2) = &w.n + 2’ by rw[ROR_ADD, REAL_OF_RAT_OF_NUM] >>
  ‘real_of_rat w.r < &w.n + 2’
    by (‘real_of_rat w.r < real_of_rat (&w.n + 2)’ by metis_tac[REAL_OF_RAT_LT] >>
        gvs[]) >>
  ‘abs (fnEval w.tag x - sum (0, w.n + 1) (λk. coeffR w.tag k * x pow k)) ≤
     real_of_rat w.r pow (w.n + 1) / &FACT (w.n + 1) *
       ((&w.n + 2) / (&w.n + 2 - real_of_rat w.r))’
    by (‘abs (fnEval w.tag x - sum (0, w.n + 1) (λk. coeffR w.tag k * x pow k)) ≤
           real_of_rat w.r pow (w.n + 1) / &FACT (w.n + 1) *
             ((&(w.n + 1) + 1) / (&(w.n + 1) + 1 - real_of_rat w.r))’
         by (irule TAIL_MAIN >> gvs[]) >>
        gvs[]) >>
  ‘real_of_rat (tailBound w.n w.r) ≤ real_of_rat w.R’ by rw[REAL_OF_RAT_LE] >>
  ‘real_of_rat (tailBound w.n w.r) =
     real_of_rat w.r pow (w.n + 1) / &FACT (w.n + 1) *
       ((&w.n + 2) / (&w.n + 2 - real_of_rat w.r))’
    by rw[ENCCHECK_TAILBOUND_REAL] >>
  gvs[] >> irule REAL_LE_TRANS >>
  qexists_tac ‘real_of_rat w.r pow (w.n + 1) / &FACT (w.n + 1) *
       ((&w.n + 2) / (&w.n + 2 - real_of_rat w.r))’ >>
  rw[]
QED

Theorem encCheck_sound_bracket:
  ∀w x.
    encCheck w ∧ abs x ≤ real_of_rat w.r ⇒
    evalPolyR w.coeffs x - real_of_rat w.R ≤ fnEval w.tag x ∧
    fnEval w.tag x ≤ evalPolyR w.coeffs x + real_of_rat w.R
Proof
  rpt gen_tac >> strip_tac >>
  drule_all encCheck_sound >> rw[ABS_BOUNDS] >>
  RealField.REAL_ASM_ARITH_TAC
QED

Theorem LINEAR_INTERP_LE:
  ∀A C l h w : real.
    l ≤ w ∧ w ≤ h ∧ A + C * l ≤ 0 ∧ A + C * h ≤ 0 ⇒ A + C * w ≤ 0
Proof
  rpt strip_tac >>
  Cases_on ‘0 ≤ C’
  >- (‘C * w ≤ C * h’ by metis_tac[REAL_LE_LMUL_IMP] >>
      RealField.REAL_ASM_ARITH_TAC)
  >- (‘0 ≤ -C’ by RealField.REAL_ASM_ARITH_TAC >>
      ‘-C * l ≤ -C * w’ by metis_tac[REAL_LE_LMUL_IMP] >>
      RealField.REAL_ASM_ARITH_TAC)
QED

Definition encReceipts_def:
  encReceipts =
    [encCheck <| tag := FTSin; n := 7; r := 1; R := 1/35840;
                 coeffs := [0; 1; 0; -1/6; 0; 1/120; 0; -1/5040] |>;
     encCheck <| tag := FTExp; n := 4; r := 1/2; R := 1/3520;
                 coeffs := [1; 1; 1/2; 1/6; 1/24] |>;
     encCheck <| tag := FTCos; n := 6; r := 1; R := 1/4410;
                 coeffs := [1; 0; -1/2; 0; 1/24; 0; -1/720] |>;
     encCheck <| tag := FTSin; n := 7; r := 1; R := 1/35840;
                 coeffs := [0; 1; 0; 1/6; 0; 1/120; 0; -1/5040] |>;
     encCheck <| tag := FTSin; n := 7; r := 1; R := 1/40000;
                 coeffs := [0; 1; 0; -1/6; 0; 1/120; 0; -1/5040] |>;
     encCheck <| tag := FTSin; n := 7; r := 9; R := 1;
                 coeffs := [0; 1; 0; -1/6; 0; 1/120; 0; -1/5040] |>;
     encCheck <| tag := FTSin; n := 7; r := 1; R := 1/35840;
                 coeffs := [0; 1; 0; -1/6; 0; 1/120; 0] |>]
End

Definition encReceiptNames_def:
  encReceiptNames =
    [strlit "encCheck sin-7 [-1,1] R=1/35840 (accept)";
     strlit "encCheck exp-4 [-1/2,1/2] R=1/3520 (accept)";
     strlit "encCheck cos-6 [-1,1] R=1/4410 exact-boundary (accept)";
     strlit "encCheck sin-7 sign-flip mutant (reject)";
     strlit "encCheck sin-7 R-below-tail mutant (reject)";
     strlit "encCheck sin-7 radius-out-of-range mutant (reject)";
     strlit "encCheck sin-7 short-list mutant (reject)"]
End

Definition encExpected_def:
  encExpected = [T; T; T; F; F; F; F]
End

Definition encReceiptRows_def:
  encReceiptRows =
    ZIP (encReceiptNames,
         MAP (λ(e, b). e ⇔ b) (ZIP (encExpected, encReceipts)))
End

Definition encReceipts_string_def:
  encReceipts_string =
    concat (MAP receipt_line encReceiptRows ++
            [if EVERY SND encReceiptRows
             then strlit "== ALL ENCLOSURE CHECKS PASS ==\n"
             else strlit "== ENCLOSURE FAILURES PRESENT ==\n"])
End

Definition full_output_def:
  full_output = concat [receipts_string; qreceipts_string; creceipts_string;
                        encReceipts_string]
End
