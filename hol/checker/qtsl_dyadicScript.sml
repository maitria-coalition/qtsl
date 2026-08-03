(*
  Numeric primitives for the Bernstein Logic certificate checker:
  binomial/logarithm helpers, a dyadic floating-point model with
  round-to-nearest/up/down/toward-zero modes over explicit formats, and
  exact extended rationals (erat) with partial arithmetic. Ported
  side-by-side from the Lean development's Core/Prim, Core/Dyadic and
  Core/ERat modules; ground-fact receipts at the bottom mirror the Lean
  side's kernel-reduction checks as boolean computations.
*)
Theory qtsl_dyadic
Ancestors
  rat integer mlstring
Libs
  preamble

Definition nchoose_def:
  nchoose n 0 = 1n ∧
  nchoose 0 (SUC k) = 0 ∧
  nchoose (SUC n) (SUC k) = nchoose n k + nchoose n (SUC k)
End

Definition log2f_def:
  log2f n = if 2 ≤ n then log2f (n DIV 2) + 1 else 0n
Termination
  WF_REL_TAC ‘measure I’ >> rw[] >> irule DIV_LESS >> simp[]
End

Definition clog2_def:
  clog2 n = if 1 < n then clog2 ((n + 1) DIV 2) + 1 else 0n
Termination
  WF_REL_TAC ‘measure I’ >> rw[DIV_LT_X]
End

Definition ratFloor_def:
  ratFloor (q:rat) = RATN q / &RATD q
End

Definition ratCeil_def:
  ratCeil (q:rat) = let i = ratFloor q in if rat_of_int i = q then i else i + 1
End

Definition ratAbs_def:
  ratAbs (q:rat) = if q < 0 then -q else q
End

Definition ceilInvPos_def:
  ceilInvPos (q:rat) =
    if RATN q ≤ 0 then 0n
    else (RATD q + Num (RATN q) - 1) DIV Num (RATN q)
End

Definition intLog2_def:
  intLog2 (q:rat) =
    if 1 ≤ q then (&(log2f (Num (RATN q) DIV RATD q)) : int)
    else -&(clog2 (ceilInvPos q))
End

Definition roundNQ_def:
  roundNQ (q:rat) = ratFloor (q + 1/2)
End

Definition pow2i_def:
  pow2i (e:int) : rat =
    if 0 ≤ e then &(2 ** Num e) else 1 / &(2 ** Num (-e))
End

Theorem pow2i_nonzero:
  ∀e. pow2i e ≠ 0
Proof
  rw[pow2i_def] \\ simp[RAT_DIV_EQ0, RAT_EQ_NUM_CALCULATE]
QED

Datatype:
  floatfmt = <| prec : num ; eMin : int ; eMax : int |>
End

Definition maxFin_def:
  maxFin fmt = (&(2 ** fmt.prec) - 1) * pow2i fmt.eMax
End

Definition intMax_def:
  intMax (a:int) b = if a ≤ b then b else a
End

Definition gridExp_def:
  gridExp fmt (q:rat) = intMax fmt.eMin (intLog2 (ratAbs q) + 1 - &fmt.prec)
End

Definition rdnRaw_def:
  rdnRaw fmt (q:rat) =
    rat_of_int (ratFloor (q / pow2i (gridExp fmt q))) * pow2i (gridExp fmt q)
End

Definition rdn_def:
  rdn fmt (q:rat) =
    if maxFin fmt ≤ q then maxFin fmt
    else if q < -maxFin fmt then -maxFin fmt
    else rdnRaw fmt q
End

Definition rup_def:
  rup fmt (q:rat) = -(rdn fmt (-q))
End

Definition rtz_def:
  rtz fmt (q:rat) = if 0 ≤ q then rdn fmt q else rup fmt q
End

Definition rne_def:
  rne fmt (q:rat) =
    if q - rdn fmt q < rup fmt q - q then rdn fmt q
    else if rup fmt q - q < q - rdn fmt q then rup fmt q
    else if ratFloor (q / pow2i (gridExp fmt q)) % 2 = 0 then rdn fmt q
    else rup fmt q
End

Definition f16_def:
  f16 = <| prec := 11; eMin := -24; eMax := 5 |>
End
Definition bf16_def:
  bf16 = <| prec := 8; eMin := -133; eMax := 120 |>
End
Definition f32_def:
  f32 = <| prec := 24; eMin := -149; eMax := 104 |>
End
Definition f64_def:
  f64 = <| prec := 53; eMin := -1074; eMax := 971 |>
End

Theorem fmt_bounds_ok:
  (0 < f16.prec ∧ f16.eMin ≤ f16.eMax) ∧
  (0 < bf16.prec ∧ bf16.eMin ≤ bf16.eMax) ∧
  (0 < f32.prec ∧ f32.eMin ≤ f32.eMax) ∧
  (0 < f64.prec ∧ f64.eMin ≤ f64.eMax)
Proof
  EVAL_TAC
QED

Datatype:
  erat = NegInf | Fin rat | PosInf
End

Definition eratLe_def:
  (eratLe NegInf _ = T) ∧
  (eratLe _ PosInf = T) ∧
  (eratLe (Fin a) (Fin b) = (a ≤ b)) ∧
  (eratLe PosInf _ = F) ∧
  (eratLe _ NegInf = F)
End

Definition eratAdd_def:
  (eratAdd PosInf NegInf = NONE) ∧
  (eratAdd NegInf PosInf = NONE) ∧
  (eratAdd NegInf _ = SOME NegInf) ∧
  (eratAdd _ NegInf = SOME NegInf) ∧
  (eratAdd PosInf _ = SOME PosInf) ∧
  (eratAdd _ PosInf = SOME PosInf) ∧
  (eratAdd (Fin a) (Fin b) = SOME (Fin (a + b)))
End

Definition eratMul_def:
  (eratMul (Fin a) (Fin b) = SOME (Fin (a * b))) ∧
  (eratMul (Fin a) PosInf =
     if 0 < a then SOME PosInf else if a < 0 then SOME NegInf else NONE) ∧
  (eratMul PosInf (Fin a) =
     if 0 < a then SOME PosInf else if a < 0 then SOME NegInf else NONE) ∧
  (eratMul (Fin a) NegInf =
     if 0 < a then SOME NegInf else if a < 0 then SOME PosInf else NONE) ∧
  (eratMul NegInf (Fin a) =
     if 0 < a then SOME NegInf else if a < 0 then SOME PosInf else NONE) ∧
  (eratMul PosInf PosInf = SOME PosInf) ∧
  (eratMul NegInf NegInf = SOME PosInf) ∧
  (eratMul PosInf NegInf = SOME NegInf) ∧
  (eratMul NegInf PosInf = SOME NegInf)
End

Definition eratSum_def:
  eratSum l =
    FOLDL (λacc e. case acc of NONE => NONE | SOME a => eratAdd a e)
          (SOME (Fin 0)) l
End

Definition eratProd_def:
  eratProd l =
    FOLDL (λacc e. case acc of NONE => NONE | SOME a => eratMul a e)
          (SOME (Fin 1)) l
End

Definition ratEq_def:
  ratEq (a:rat) b ⇔ a ≤ b ∧ b ≤ a
End

Definition eratEq_def:
  (eratEq NegInf NegInf = T) ∧
  (eratEq PosInf PosInf = T) ∧
  (eratEq (Fin a) (Fin b) = ratEq a b) ∧
  (eratEq _ _ = F)
End

Definition oeratEq_def:
  (oeratEq NONE NONE = T) ∧
  (oeratEq (SOME a) (SOME b) = eratEq a b) ∧
  (oeratEq _ _ = F)
End

Definition receipts_def:
  receipts =
    [ (strlit "nchoose 5 2 = 10", nchoose 5 2 = 10) ;
      (strlit "clog2 100 = 7", clog2 100 = 7) ;
      (strlit "log2f 100 = 6", log2f 100 = 6) ;
      (strlit "intLog2 (1/3) = -2", intLog2 (1/3) = -2) ;
      (strlit "roundNQ (7/2) = 4 (half up)", roundNQ (7/2) = 4) ;
      (strlit "f64.rdn(1/3) = 6004799503160661/2^54",
         ratEq (rdn f64 (1/3)) (&6004799503160661 / &(2 ** 54))) ;
      (strlit "f64.rne(1/10) = 7205759403792794/2^56",
         ratEq (rne f64 (1/10)) (&7205759403792794 / &(2 ** 56))) ;
      (strlit "bf16.rdn(1/3) = 85/256",
         ratEq (rdn bf16 (1/3)) (&85 / &256)) ;
      (strlit "f64.rdn(2^2000) clamps to maxFin",
         ratEq (rdn f64 (&(2 ** 2000))) (maxFin f64)) ;
      (strlit "f64.rup(-1/3) = -f64.rdn(1/3)",
         ratEq (rup f64 (-(1/3))) (-(rdn f64 (1/3)))) ;
      (strlit "f64.rdn(2^-1080) = 0 (subnormal underflow)",
         ratEq (rdn f64 (1 / &(2 ** 1080))) 0) ;
      (strlit "f64.rup(2^-1080) = 2^-1074 (min subnormal)",
         ratEq (rup f64 (1 / &(2 ** 1080))) (pow2i (-1074))) ;
      (strlit "sum? [+inf; -inf] = none (NaN case)",
         oeratEq (eratSum [PosInf; NegInf]) NONE) ;
      (strlit "mul? 0 +inf = none (NaN case)",
         oeratEq (eratMul (Fin 0) PosInf) NONE) ;
      (strlit "sum? [1; 2; +inf] = +inf",
         oeratEq (eratSum [Fin 1; Fin 2; PosInf]) (SOME PosInf)) ;
      (strlit "le: -inf <= fin 5 <= +inf",
         eratLe NegInf (Fin 5) ∧ eratLe (Fin 5) PosInf)
    ]
End

Definition receipt_line_def:
  receipt_line (name, ok) =
    concat [if ok then strlit "PASS  " else strlit "FAIL  "; name;
            strlit "\n"]
End

Definition receipts_string_def:
  receipts_string =
    concat (MAP receipt_line receipts ++
            [if EVERY SND receipts then strlit "== ALL CHECKS PASS ==\n"
             else strlit "== FAILURES PRESENT ==\n"])
End
