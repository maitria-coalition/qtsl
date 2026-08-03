(*
  Exact-rational polynomial and Bernstein-coefficient machinery:
  multivariate polynomials over the rationals, composition/substitution,
  Bernstein-basis coefficient enumeration, and the combinatorial support
  (compositions, multinomials). Ported side-by-side from the Lean
  development's Core/QArith module; representation deltas (list-based
  in place of dependent functions) are value-preserving.
*)
Theory qtsl_qarith
Ancestors
  rat integer mlstring qtsl_dyadic
Libs
  preamble

Datatype:
  bcmp = BLt | BEq | BGt
End

Definition natCmp_def:
  natCmp (n:num) m = if n < m then BLt else if n = m then BEq else BGt
End

Definition ratPow_def:
  ratPow (q:rat) 0 = 1 ∧
  ratPow q (SUC n) = q * ratPow q n
End

Definition pfind_def:
  pfind p [] = NONE ∧
  pfind p (x::xs) = if p x then SOME x else pfind p xs
End

Definition nubL_def:
  nubL [] = [] ∧
  nubL (x::xs) = x :: nubL (FILTER (λy. y ≠ x) xs)
Termination
  WF_REL_TAC ‘measure LENGTH’ >> rw[]
  >> irule arithmeticTheory.LESS_EQ_IMP_LESS_SUC
  >> simp[LENGTH_FILTER_LEQ]
End

Definition rangeL_def:
  rangeL 0 = ([]:num list) ∧
  rangeL (SUC n) = rangeL n ++ [n]
End

Definition getD_def:
  getD [] (i:num) (d:'a) = d ∧
  getD (x::xs) 0 d = x ∧
  getD (x::xs) (SUC i) d = getD xs i d
End

Definition zipL_def:
  zipL [] _ = [] ∧
  zipL _ [] = [] ∧
  zipL (x::xs) (y::ys) = (x,y) :: zipL xs ys
End

Type mono = “:(num # num) list”
Type poly = “:((num # num) list # rat) list”

Definition monoCmp_def:
  monoCmp ([]:(num # num) list) ([]:(num # num) list) = BEq ∧
  monoCmp [] (_::_) = BLt ∧
  monoCmp (_::_) [] = BGt ∧
  monoCmp ((v1,e1)::r1) ((v2,e2)::r2) =
    (case natCmp v1 v2 of
     | BLt => BLt
     | BGt => BGt
     | BEq =>
       (case natCmp e1 e2 of
        | BLt => BLt
        | BGt => BGt
        | BEq => monoCmp r1 r2))
End

Definition insertVar_def:
  insertVar (p:num # num) [] = [p] ∧
  insertVar (v,e) ((v',e')::r) =
    if v < v' then (v,e) :: (v',e') :: r
    else if v = v' then (v, e + e') :: r
    else (v',e') :: insertVar (v,e) r
End

Definition monoCanon_def:
  monoCanon (m:mono) = FILTER (λp. SND p ≠ 0) (FOLDR insertVar [] m)
End

Definition monoMul_def:
  monoMul (a:mono) (b:mono) = monoCanon (a ++ b)
End

Definition monoDeg_def:
  monoDeg (m:mono) = FOLDR (λp acc. SND p + acc) 0 m
End

Definition insertTerm_def:
  insertTerm (t:(num # num) list # rat) [] = [t] ∧
  insertTerm (m,c) ((m',c')::r) =
    case monoCmp m m' of
    | BLt => (m,c) :: (m',c') :: r
    | BEq => (m, c + c') :: r
    | BGt => (m',c') :: insertTerm (m,c) r
End

Definition polyCanon_def:
  polyCanon (p:poly) = FILTER (λt. SND t ≠ (0:rat)) (FOLDR insertTerm [] p)
End

Definition polyAdd_def:
  polyAdd (p:poly) q = polyCanon (p ++ q)
End

Definition polyNeg_def:
  polyNeg (p:poly) = MAP (λ(m,c). (m, -c:rat)) p
End

Definition polySub_def:
  polySub p q = polyAdd p (polyNeg q)
End

Definition polyScale_def:
  polyScale (a:rat) (p:poly) = if a = 0 then [] else MAP (λ(m,c). (m, a * c)) p
End

Definition polyMul_def:
  polyMul (p:poly) (q:poly) =
    polyCanon (FLAT (MAP (λ(m,c). MAP (λ(m',c'). (monoMul m m', c * c':rat)) q) p))
End

Definition polyConst_def:
  polyConst (c:rat) = if c = 0 then [] else [([], c)]
End

Definition polyVar_def:
  polyVar (v:num) = [([(v,1:num)], 1:rat)]
End

Definition polyPow_def:
  polyPow (p:poly) 0 = polyConst 1 ∧
  polyPow p (SUC n) = polyMul p (polyPow p n)
End

Definition polyTotalDeg_def:
  polyTotalDeg (p:poly) = FOLDR (λt acc. MAX (monoDeg (FST t)) acc) 0 p
End

Definition polyCoeffOf_def:
  polyCoeffOf (p:poly) (m:mono) =
    case pfind (λt. FST t = m) p of
    | SOME t => SND t
    | NONE => (0:rat)
End

Definition polyVars_def:
  polyVars (p:poly) = nubL (FLAT (MAP (λt. MAP FST (FST t)) p))
End

Definition polyEval_def:
  polyEval (σ:num -> rat) (p:poly) =
    FOLDR (λ(m,c) acc.
      c * FOLDR (λ(v,e) a. ratPow (σ v) e * a) 1 m + acc) 0 p
End

Definition multinomial_def:
  multinomial [] = 1n ∧
  multinomial (a::rest) =
    nchoose (a + FOLDR $+ 0 rest) a * multinomial rest
End

Definition compositions_def:
  compositions 0 0 = [[]] ∧
  compositions 0 (SUC _) = [] ∧
  compositions (SUC parts) total =
    FLAT (MAP (λa. MAP (λv. a::v) (compositions parts (total - a)))
              (rangeL (total + 1)))
End

Definition compositionsUpTo_def:
  compositionsUpTo parts bound =
    FLAT (MAP (compositions parts) (rangeL (bound + 1)))
End

Definition subCompositions_def:
  subCompositions [] = [[]] ∧
  subCompositions (a::rest) =
    FLAT (MAP (λk. MAP (λv. k::v) (subCompositions rest))
              (rangeL (a + 1)))
End

Definition vecToMono_def:
  vecToMono v = FILTER (λp. SND p ≠ 0n) (zipL (rangeL (LENGTH v)) v)
End

Definition assembleVec_def:
  assembleVec [] k b = ([]:num list) ∧
  assembleVec (T::rest) (k0::ks) b = k0 :: assembleVec rest ks b ∧
  assembleVec (T::rest) [] b = 0 :: assembleVec rest [] b ∧
  assembleVec (F::rest) k (b0::bs) = b0 :: assembleVec rest k bs ∧
  assembleVec (F::rest) k [] = 0 :: assembleVec rest k []
End

Definition sumVars_def:
  sumVars m = polyCanon (MAP (λi. ([(i,1:num)], 1:rat)) (rangeL m))
End

Definition coordPoly_def:
  coordPoly (verts: rat list list) (j:num) =
    polyCanon (MAP (λi. ([(i,1:num)], getD (getD verts i []) j 0))
                   (rangeL (LENGTH verts)))
End

Definition polySubst_def:
  polySubst (σ:num -> poly) (p:poly) =
    FOLDR (λ(m,c) acc.
      polyAdd acc
        (polyScale c (FOLDR (λ(v,e) a. polyMul (polyPow (σ v) e) a)
                            (polyConst 1) m)))
      [] p
End

Definition homogenize_def:
  homogenize m d (p:poly) =
    FOLDR (λ(mo,c) acc.
      case acc of
      | NONE => NONE
      | SOME accp =>
        let e = monoDeg mo in
        if e ≤ d then
          SOME (polyAdd accp (polyMul [(mo,c)] (polyPow (sumVars m) (d - e))))
        else NONE)
      (SOME []) p
End

Definition bernCoeffRows_def:
  bernCoeffRows m d (hp:poly) =
    MAP (λα. (α, polyCoeffOf hp (vecToMono α) / &(multinomial α)))
        (compositions m d)
End

Datatype:
  fdtable = <| base : (num list # rat) list ;
               grid : (num list # (num list # rat) list) list |>
End

Definition fdBernstein_def:
  fdBernstein (verts: rat list list) (smask: bool list) (d:num) (p:poly) =
    let m = LENGTH verts in
    if LENGTH smask ≠ m then NONE else
    let mS = LENGTH (FILTER I smask) in
    let mB = m - mS in
    if mB = 0 then NONE else
    let pLam = polySubst (coordPoly verts) p in
    case homogenize m d pLam of
    | NONE => NONE
    | SOME hp =>
      let base = bernCoeffRows m d hp in
      let bAt = (λk β.
        let α = assembleVec smask k β in
        polyCoeffOf hp (vecToMono α) / &(multinomial α)) in
      let grid =
        MAP (λj.
          let pj =
            FOLDR (λk acc.
              let sgn = if (FOLDR $+ 0 k) MOD 2 = 0 then (1:rat) else -1 in
              let binomProd =
                FOLDR $* 1 (MAP (λ(ji,ki). nchoose ji ki) (zipL j k)) in
              let kSum = FOLDR $+ 0 k in

              let dk = if kSum ≤ d then d - kSum else 0 in
              let qk = polyCanon
                (MAP (λβ. (vecToMono β, bAt k β * &(multinomial β)))
                     (compositions mB dk)) in
              let hk = polyMul qk (polyPow (sumVars mB) kSum) in
              polyAdd acc (polyScale (sgn * &binomProd) hk))
              [] (subCompositions j) in
          (j, bernCoeffRows mB d pj))
        (compositionsUpTo mS d) in
      SOME <| base := base ; grid := grid |>
End

Definition gridAll_def:
  gridAll pred t = EVERY (λ(j,row). EVERY (λ(g,c). pred c) row) t.grid
End

Definition assembleVecQ_def:
  assembleVecQ [] k b = ([]:rat list) ∧
  assembleVecQ (T::rest) (k0::ks) b = k0 :: assembleVecQ rest ks b ∧
  assembleVecQ (T::rest) [] b = 0 :: assembleVecQ rest [] b ∧
  assembleVecQ (F::rest) k (b0::bs) = b0 :: assembleVecQ rest k bs ∧
  assembleVecQ (F::rest) k [] = 0 :: assembleVecQ rest k []
End

Definition starIdentityCheck_def:
  starIdentityCheck (verts: rat list list) (smask: bool list) (d:num) (p:poly)
                    (u: rat list) (yFace: rat list) =
    case fdBernstein verts smask d p of
    | NONE => NONE
    | SOME t =>
      let mB = LENGTH (FILTER (λx. ¬x) smask) in
      if LENGTH u ≠ LENGTH (FILTER I smask) then NONE
      else if LENGTH yFace ≠ mB then NONE else
      let bigU = FOLDR $+ (0:rat) u in
      let lamS = MAP (λui. -ui) u in
      let lamB = MAP (λyi. (1 + bigU) * yi) yFace in
      let lam = assembleVecQ smask lamS lamB in
      let lhs =
        FOLDR (λ(α,b) acc.
          acc + b * &(multinomial α) *
            FOLDR (λ(e,l) a. ratPow l e * a) 1 (zipL α lam))
          (0:rat) t.base in
      let rhs =
        FOLDR (λ(j,row) acc.
          let jSum = FOLDR $+ 0 j in
          let mult = &(nchoose d jSum) * &(multinomial j) in
          let uPow = FOLDR (λ(e,ui) a. ratPow ui e * a) 1 (zipL j u) in
          let pjAtY =
            FOLDR (λ(γ,c) a.
              a + c * &(multinomial γ) *
                FOLDR (λ(e,yi) b. ratPow yi e * b) 1 (zipL γ yFace))
              (0:rat) row in
          acc + mult * uPow * pjAtY)
          (0:rat) t.grid in
      SOME (lhs = rhs)
End

Theorem nchoose_pos:
  ∀n k. k ≤ n ⇒ 0 < nchoose n k
Proof
  Induct_on ‘n’ >> Cases_on ‘k’ >> rw[nchoose_def] >>
  ‘n' ≤ n’ by decide_tac >> res_tac >> simp[]
QED

Theorem multinomial_nz:
  ∀l. multinomial l ≠ 0
Proof
  Induct >> rw[multinomial_def] >>
  ‘0 < nchoose (h + FOLDR $+ 0 l) h’ by simp[nchoose_pos] >>
  simp[]
QED

Theorem rat_multinomial_nz:
  ∀l. &(multinomial l) ≠ (0:rat)
Proof
  simp[RAT_EQ_NUM_CALCULATE, multinomial_nz]
QED

Definition qreceipts_def:
  qreceipts =
    [ (strlit "poly: x + x = 2x (canonical)",
       polyAdd (polyVar 0) (polyVar 0) = [([(0,1)], &2)]) ;
      (strlit "poly: (x+1)(x-1) = x^2 - 1",
       polyMul (polyAdd (polyVar 0) (polyConst 1))
               (polySub (polyVar 0) (polyConst 1)) =
       [([], -&1); ([(0,2)], &1)]) ;
      (strlit "poly: eval (x^2+1) at x=2 gives 5",
       polyEval (λv. &2)
         (polyAdd (polyMul (polyVar 0) (polyVar 0)) (polyConst 1)) = &5) ;
      (strlit "compositions 2 2 = [[0,2],[1,1],[2,0]]",
       compositions 2 2 = [[0;2];[1;1];[2;0]]) ;
      (strlit "multinomial [2,1] = 3",
       multinomial [2;1] = 3) ;
      (strlit "homogenize catches the degree lie (x^2 at d=1)",
       homogenize 2 1 (polyMul (polyVar 0) (polyVar 0)) = NONE) ;
      (strlit "fdBernstein (1/2+2x on [1,2], d=1): coeffs 5/2, 9/2",
       fdBernstein [[&1];[&2]] [F;F] 1 [([], (&1:rat) / &2); ([(0,1)], &2)] =
       SOME <| base := [([0;1], (&9:rat) / &2); ([1;0], (&5:rat) / &2)] ;
               grid := [([], [([0;1], (&9:rat) / &2); ([1;0], (&5:rat) / &2)])] |>) ;
      (strlit "fdBernstein |S|=1 table exists (sign-direction witness)",
       IS_SOME (fdBernstein [[&1];[&2]] [T;F] 1 (polyVar 0))) ;
      (strlit "gridAll (0 <= c) on the demo table",
       (case fdBernstein [[&1];[&2]] [F;F] 1 [([], (&1:rat) / &2); ([(0,1)], &2)] of
        | SOME t => gridAll (λc. 0 ≤ c) t
        | NONE => F)) ;
      (strlit "gridAll (c <= 3) rejects (9/2 > 3)",
       (case fdBernstein [[&1];[&2]] [F;F] 1 [([], (&1:rat) / &2); ([(0,1)], &2)] of
        | SOME t => ¬ gridAll (λc. c ≤ &3) t
        | NONE => F)) ;
      (strlit "starIdentityCheck (3x^2 - x + 1/7, facet-extended, exact)",
       starIdentityCheck [[&1];[&2]] [T;F] 2
         (polyAdd (polyScale (&3) (polyMul (polyVar 0) (polyVar 0)))
            (polyAdd (polyScale (-&1) (polyVar 0)) (polyConst ((&1:rat) / &7))))
         [&3] [&1] = SOME T)
    ]
End

Definition qreceipts_string_def:
  qreceipts_string =
    concat (MAP receipt_line qreceipts ++
            [if EVERY SND qreceipts then strlit "== ALL QARITH CHECKS PASS ==\n"
             else strlit "== QARITH FAILURES PRESENT ==\n"])
End

Theorem MEM_rangeL:
  ∀n x. MEM x (rangeL n) ⇔ x < n
Proof
  Induct >> rw[rangeL_def]
QED

Theorem sum_compositions:
  ∀parts total v. MEM v (compositions parts total) ⇒ FOLDR $+ 0 v = total
Proof
  Induct
  >- (Cases >> rw[compositions_def])
  >> rw[compositions_def]
  >> gvs[MEM_FLAT, MEM_MAP, MEM_rangeL]
  >> first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem mem_compositionsUpTo_sum:
  ∀parts bound j. MEM j (compositionsUpTo parts bound) ⇒ FOLDR $+ 0 j ≤ bound
Proof
  rw[compositionsUpTo_def] >> gvs[MEM_FLAT, MEM_MAP, MEM_rangeL] >>
  imp_res_tac sum_compositions >> gvs[]
QED

Theorem sum_subCompositions:
  ∀j k. MEM k (subCompositions j) ⇒ FOLDR $+ 0 k ≤ FOLDR $+ 0 j
Proof
  Induct
  >- rw[subCompositions_def]
  >> rw[subCompositions_def]
  >> gvs[MEM_FLAT, MEM_MAP, MEM_rangeL]
  >> first_x_assum drule >> strip_tac >> gvs[]
QED
