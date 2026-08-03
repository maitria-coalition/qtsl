(*
  Interval-sharded checking for the fused certificate fold: a shard
  worker runs the same structural walk over a summary table, evaluating
  local rule obligations only for node ordinals its check-policy
  selects. Accepted shards over a tiling of the ordinals compose by
  policy-union to the all-ordinals run, which lifts to the fused fold.
  The composition statements never mention workers: every shard run is
  a value of one pure function of the same bytes.
*)
Theory qtsl_certShard
Ancestors
  rat integer mlstring mllist sptree[qualified] qtsl_dyadic qtsl_qarith
  qtsl_catalogue qtsl_cert qtsl_certPerf
Libs
  preamble

Definition lookNodeSI_def:
  lookNodeSI (t : (sequent # fwire) spt) (off:num) = sptree$lookup off t
End

Definition lookNodesSI_def:
  lookNodesSI (t : (sequent # fwire) spt) ([]:num list) =
    SOME ([] : (sequent # fwire) list) ∧
  lookNodesSI t (off::offs) =
    case lookNodeSI t off of NONE => NONE
    | SOME x =>
      case lookNodesSI t offs of NONE => NONE
      | SOME xs => SOME (x::xs)
End

Definition bproj_def:
  bproj (t' : (bool # sequent # fwire) spt) (t : (sequent # fwire) spt) ⇔
    ∀k. sptree$lookup k t =
        OPTION_MAP (λ(b,sq,pw). (sq,pw)) (sptree$lookup k t')
End

Definition allT_def:
  allT (t' : (bool # sequent # fwire) spt) ⇔
    ∀k b sq pw. sptree$lookup k t' = SOME (b,sq,pw) ⇒ b
End

Theorem MAP_FST_bdrop:
  MAP FST (MAP (λ(b,sq,pw). (sq,pw)) (l:(bool # sequent # fwire) list)) =
  MAP (λ(b,sq,pw). sq) l
Proof
  Induct_on ‘l’ >> rw[] >> PairCases_on ‘h’ >> simp[]
QED

Theorem lookNodesI_allT:
  ∀offs xs. allT t' ∧ lookNodesI t' offs = SOME xs ⇒
            EVERY (λ(b,sq,pw). b) xs
Proof
  Induct
  >- (rw[lookNodesI_def] >> gvs[])
  >> rw[lookNodesI_def] >> gvs[AllCaseEqs(), lookNodeI_def, allT_def]
  >> res_tac >> gvs[]
  >> TRY (PairCases_on ‘x’ >> gvs[] >> res_tac >> gvs[])
QED

Definition parseNodeSI_def:
  parseNodeSI (chk:bool) (ws:tensortype list) (pt : pobjI spt)
              (t : (sequent # fwire) spt)
              (s:mlstring) (lim:num) (i:num) =
    case rdU8I s lim i of NONE => NONE | SOME (tag, r0) =>
    case rdU8I s lim r0 of NONE => NONE | SOME (var, r1) =>
    case rdLEI s lim 2 r1 of NONE => NONE | SOME (resv, r2) =>
    if resv ≠ (0:num) then NONE else
    case rdLEI s lim 4 r2 of NONE => NONE | SOME (cj, r3) =>
    case lookJudgI pt cj of NONE => NONE | SOME (prew, postw, prex, postx) =>
    let sq = <| pre := prex ; post := postx |> in
    if tag = (0:num) then
      (if var ≠ (0:num) then NONE else
         SOME ((if chk then (sq.pre = sq.post) else T), sq, prew, r3))
    else if tag = 1 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLEI s lim 4 r4 of NONE => NONE | SOME (ex, r5) =>
       case lookNodeSI t pr of NONE => NONE | SOME (ps, ppw) =>
       case lookFormulaI pt ex of NONE => NONE | SOME (exw, exx, exn) =>
         SOME ((if chk then
                  (sq.pre = FAnd ps.pre exx ∧ sq.post = ps.post)
                else T),
               sq, prew, r5))
    else if tag = 2 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 4 r3 of NONE => NONE | SOME (cutf, r4) =>
       case rdLEI s lim 8 r4 of NONE => NONE | SOME (lo, r5) =>
       case rdLEI s lim 8 r5 of NONE => NONE | SOME (ro, r6) =>
       case lookFormulaI pt cutf of NONE => NONE | SOME (cfw, cfx, cfn) =>
       case lookNodeSI t lo of NONE => NONE | SOME (ls, lpw) =>
       case lookNodeSI t ro of NONE => NONE | SOME (rs, rpw) =>
         SOME ((if chk then
                  (sq.pre = ls.pre ∧ sq.post = rs.post ∧
                   ls.post = cfx ∧ rs.pre = FAnd ls.pre cfx)
                else T),
               sq, prew, r6))
    else if tag = 3 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (lo, r4) =>
       case rdLEI s lim 8 r4 of NONE => NONE | SOME (ro, r5) =>
       case lookNodeSI t lo of NONE => NONE | SOME (ls, lpw) =>
       case lookNodeSI t ro of NONE => NONE | SOME (rs, rpw) =>
         SOME ((if chk then
                  (ls.pre = rs.pre ∧ sq.pre = ls.pre ∧
                   sq.post = FAnd ls.post rs.post)
                else T),
               sq, prew, r5))
    else if tag = 4 ∨ tag = 5 then
      (if ¬(var = 0 ∨ var = 1) then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLEI s lim 4 r4 of NONE => NONE | SOME (ot, r5) =>
       case lookNodeSI t pr of NONE => NONE | SOME (ps, ppw) =>
       case lookFormulaI pt ot of NONE => NONE | SOME (otw, otx, otn) =>
         SOME ((if chk then
                  (if tag = 4 then
                     (if var = 0 then
                        sq.pre = ps.pre ∧ ps.post = FAnd sq.post otx
                      else
                        sq.pre = ps.pre ∧ ps.post = FAnd otx sq.post)
                   else
                     (if var = 0 then
                        sq.pre = ps.pre ∧ sq.post = FOr ps.post otx
                      else
                        sq.pre = ps.pre ∧ sq.post = FOr otx ps.post))
                else T),
               sq, prew, r5))
    else if tag = 6 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (lo, r4) =>
       case rdLEI s lim 8 r4 of NONE => NONE | SOME (ro, r5) =>
       case rdLEI s lim 4 r5 of NONE => NONE | SOME (plen, r6) =>
       case takeNI s lim plen r6 of NONE => NONE | SOME (stps, r7) =>
       if ¬ EVERY (λst. st ≤ (1:num)) stps then NONE else
       case lookNodeSI t lo of NONE => NONE | SOME (ls, lpw) =>
       case lookNodeSI t ro of NONE => NONE | SOME (rs, rpw) =>
         SOME ((if chk then
                  (case conjGet sq.pre (stepsToPath stps) of
                   | SOME (FOr d1 d2) =>
                       (conjReplace sq.pre (stepsToPath stps) d1 = SOME ls.pre ∧
                        conjReplace sq.pre (stepsToPath stps) d2 = SOME rs.pre ∧
                        ls.post = sq.post ∧ rs.post = sq.post)
                   | _ => F)
                else T),
               sq, prew, r7))
    else if tag = 7 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (eo, r4) =>
       case rdLEI s lim 8 r4 of NONE => NONE | SOME (bo, r5) =>
       case rdLEI s lim 4 r5 of NONE => NONE | SOME (w, r6) =>
       case rdLEI s lim 4 r6 of NONE => NONE | SOME (tt0, r7) =>
       case rdLEI s lim 4 r7 of NONE => NONE | SOME (tu, r8) =>
       case rdLEI s lim 4 r8 of NONE => NONE | SOME (bf, r9) =>
       case lookNodeSI t eo of NONE => NONE | SOME (es, epw) =>
       case lookNodeSI t bo of NONE => NONE | SOME (bs, bpw) =>
       case lookTermI pt tt0 of NONE => NONE | SOME tT =>
       case lookTermI pt tu of NONE => NONE | SOME tU =>
       case lookFormulaI pt bf of NONE => NONE | SOME (bfw, bfx, bfn) =>
         SOME ((if chk then
                  (sq.pre = es.pre ∧ es.pre = bs.pre ∧
                   es.post = FAtom BowEq tT tU ∧
                   termBshape ws tT = termBshape ws tU ∧
                   IS_SOME (termBshape ws tT) ∧
                   bs.post = formulaSubst w tT bfx ∧
                   sq.post = formulaSubst w tU bfx)
                else T),
               sq, prew, r9))
    else if tag = 8 ∨ tag = 9 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLEI s lim 4 r4 of NONE => NONE | SOME (tm, r5) =>
       case rdLEI s lim 4 r5 of NONE => NONE | SOME (so, r6) =>
       case rdLEI s lim 4 r6 of NONE => NONE | SOME (eo, r7) =>
       case lookNodeSI t pr of NONE => NONE | SOME (ps, ppw) =>
       case lookTermI pt tm of NONE => NONE | SOME tt =>
       case lookSimplexI pt so of NONE => NONE | SOME sx =>
       case lookExtSetI pt eo of NONE => NONE | SOME es =>
         SOME ((if chk then
                  (if tag = 8 then
                     sq.pre = ps.pre ∧
                     termBshape ws tt = SOME [sx.complex.ambDim] ∧
                     barycentricHalfspaceBuild tt sx es = SOME ps.post ∧
                     sq.post = FInRegion tt sx es
                   else
                     sq.pre = ps.pre ∧
                     ps.post = FInRegion tt sx es ∧
                     barycentricHalfspaceBuild tt sx es = SOME sq.post)
                else T),
               sq, prew, r7))
    else if tag = 10 then
      (if ¬(var = 0 ∨ var = 1) then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLEI s lim 4 r4 of NONE => NONE | SOME (l, r5) =>
       case rdLEI s lim 4 r5 of NONE => NONE | SOME (rr, r6) =>
       case rdU8I s lim r6 of NONE => NONE | SOME (bb, r7) =>
       if (4:num) < bb then NONE else
       case takeNI s lim 3 r7 of NONE => NONE | SOME (pad, r8) =>
       if ¬ EVERY (λb. b = (0:num)) pad then NONE else
       case bowtieOf bb of NONE => NONE | SOME b =>
       case lookNodeSI t pr of NONE => NONE | SOME (ps, ppw) =>
       case lookTermI pt l of NONE => NONE | SOME tl =>
       case lookTermI pt rr of NONE => NONE | SOME tr =>
         SOME ((if chk then
                  (if var = 0 then
                     b ≠ BowNe ∧ sq.pre = ps.pre ∧
                     ps.post = FAtom b (TmSub tl tr) (TmConst 0) ∧
                     sq.post = FAtom b tl tr
                   else
                     b ≠ BowNe ∧ sq.pre = ps.pre ∧
                     ps.post = FAtom b tl tr ∧
                     sq.post = FAtom b (TmSub tl tr) (TmConst 0))
                else T),
               sq, prew, r8))
    else if tag = 11 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLEI s lim 4 r4 of NONE => NONE | SOME (tx, r5) =>
       case rdLEI s lim 4 r5 of NONE => NONE | SOME (so, r6) =>
       case rdLEI s lim 4 r6 of NONE => NONE | SOME (eo, r7) =>
       case rdLEI s lim 4 r7 of NONE => NONE | SOME (deg, r8) =>
       case rdLEI s lim 4 r8 of NONE => NONE | SOME (po, r9) =>
       case rdLEI s lim 4 r9 of NONE => NONE | SOME (pd, r10) =>
       case lookNodeSI t pr of NONE => NONE | SOME (ps, ppw) =>
       case lookTermI pt tx of NONE => NONE | SOME tX =>
       case lookSimplexI pt so of NONE => NONE | SOME sx =>
       case lookExtSetI pt eo of NONE => NONE | SOME es =>
       case lookTermI pt po of NONE => NONE | SOME poly =>
       case lookFormulaI pt pd of NONE => NONE | SOME (pdw, pdx, pdn) =>
         SOME ((if chk then
                  (sq.pre = ps.pre ∧
                   ps.post = FInRegion tX sx es ∧
                   polyTieB tX poly ∧
                   (if extIsEmptyB es then isConvexPredicateB pdx
                    else isConicPredicateB pdx) ∧
                   bernConeCoeffCheck sx es deg poly pdx ∧
                   sq.post = formulaSubst predicateHole poly pdx)
                else T),
               sq, prew, r10))
    else if tag = 12 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 4 r3 of NONE => NONE | SOME (l, r4) =>
       case rdLEI s lim 4 r4 of NONE => NONE | SOME (rr, r5) =>
       case lookTermI pt l of NONE => NONE | SOME tl =>
       case lookTermI pt rr of NONE => NONE | SOME tr =>
         SOME ((if chk then
                  (polynomialCanonicalEqB tl tr ∧
                   termBshape ws tl = termBshape ws tr ∧
                   IS_SOME (termBshape ws tl) ∧
                   finWiresB ws tl ∧ finWiresB ws tr ∧
                   sq.post = FAtom BowEq tl tr)
                else T),
               sq, prew, r5))
    else if tag = 14 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 4 r3 of NONE => NONE | SOME (cc, r4) =>
       case rdLEI s lim 4 r4 of NONE => NONE | SOME (co, r5) =>
       case rdLEI s lim 8 r5 of NONE => NONE | SOME (dbl, r6) =>
       case lookTermI pt cc of NONE => NONE | SOME ccT =>
       case lookTermI pt co of NONE => NONE | SOME coT =>
         SOME ((if chk then
                  (IS_SOME (termBshape ws coT) ∧
                   finWiresB ws coT ∧
                   wiresPosB ws (formulaFreeWires sq.pre ++ termFreeWires coT) ∧
                   farkasCheck ccT sq.pre coT ∧
                   sq.post = FAtom BowLe coT (TmConst 0))
                else T),
               sq, prew, r6))
    else if tag = 23 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 4 r3 of NONE => NONE | SOME (tm, r4) =>
       case lookTermI pt tm of NONE => NONE | SOME tt =>
         SOME ((if chk then
                  (IS_SOME (termBshape ws tt) ∧ finWiresB ws tt ∧
                   sq.post = FAtom BowEq tt tt)
                else T),
               sq, prew, r4))
    else if tag = 24 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLEI s lim 4 r4 of NONE => NONE | SOME (tt0, r5) =>
       case rdLEI s lim 4 r5 of NONE => NONE | SOME (tu, r6) =>
       case lookNodeSI t pr of NONE => NONE | SOME (ps, ppw) =>
       case lookTermI pt tt0 of NONE => NONE | SOME tT =>
       case lookTermI pt tu of NONE => NONE | SOME tU =>
         SOME ((if chk then
                  (sq.pre = ps.pre ∧
                   ps.post = FAtom BowEq tT tU ∧
                   sq.post = FAtom BowEq tU tT)
                else T),
               sq, prew, r6))
    else if tag = 25 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (so, r4) =>
       case rdLEI s lim 8 r4 of NONE => NONE | SOME (co, r5) =>
       case rdLEI s lim 4 r5 of NONE => NONE | SOME (ct, r6) =>
       case rdLEI s lim 4 r6 of NONE => NONE | SOME (plen, r7) =>
       case takeNI s lim plen r7 of NONE => NONE | SOME (stps, r8) =>
       if ¬ EVERY (λst. st ≤ (1:num)) stps then NONE else
       case rdLEI s lim 4 r8 of NONE => NONE | SOME (ilen, r9) =>
       case rdLEsNI s lim 4 ilen r9 of NONE => NONE | SOME (iface, r10) =>
       case lookNodeSI t so of NONE => NONE | SOME (ss, spw) =>
       case lookNodeSI t co of NONE => NONE | SOME (cs, cpw) =>
       case lookFormulaI pt ct of NONE => NONE | SOME (ctw, ctx, ctn) =>
         SOME ((if chk then
                  (ss.post = ctx ∧
                   conjGet cs.pre (stepsToPath stps) = SOME ctx ∧
                   conjReplace cs.pre (stepsToPath stps) ss.pre = SOME sq.pre ∧
                   sq.post = cs.post ∧
                   (case conjReplace cs.pre (stepsToPath stps) FTt of
                    | SOME ctx0 =>
                        (EVERY (λw. MEM w iface) (formulaFreeWires ctx) ∧
                         EVERY (λw. (MEM w (formulaFreeWires ctx0) ∨
                                     MEM w (formulaFreeWires sq.post)) ⇒
                                    MEM w iface)
                               (formulaFreeWires ss.pre))
                    | NONE => F))
                else T),
               sq, prew, r10))
    else if tag = 26 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 4 r3 of NONE => NONE | SOME (ncomp, r4) =>
       case rdLEsNI s lim 8 ncomp r4 of NONE => NONE | SOME (coffs, r5) =>
       case rdLEI s lim 4 r5 of NONE => NONE | SOME (cc, r6) =>
       case rdLEI s lim 4 r6 of NONE => NONE | SOME (co, r7) =>
       case rdLEI s lim 8 r7 of NONE => NONE | SOME (dbl, r8) =>
       case rdLEI s lim 4 r8 of NONE => NONE | SOME (th, r9) =>
       case lookNodesSI t coffs of NONE => NONE | SOME comps =>
       case lookTermI pt cc of NONE => NONE | SOME ccT =>
       case lookTermI pt co of NONE => NONE | SOME coT =>
       (let bsum =
          (if chk then
             (let cseqs = MAP FST comps in
                EVERY (λc. premiseContainsB sq.pre c.pre) cseqs ∧
                IS_SOME (termBshape ws coT) ∧
                finWiresB ws coT ∧
                wiresPosB ws (formulaFreeWires sq.pre ++ termFreeWires coT) ∧
                EVERY (λc. wiresPosB ws (formulaFreeWires c.post)) cseqs ∧
                syzygyCheck ccT cseqs sq.pre coT ∧
                sq.post = FAtom BowLe coT (TmConst 0))
           else T) in
        if th = (4294967295:num) then
          SOME (bsum, sq, prew, r9)
        else
          (case lookTermI pt th of
           | SOME (TmConst q) => SOME (bsum, sq, prew, r9)
           | _ => NONE)))
    else NONE
End

Theorem parseNodeSI_chk:
  parseNodeSI chk ws pt t s lim i =
  case parseNodeSI T ws pt t s lim i of
  | NONE => NONE
  | SOME (ok, sq, prew, j) => SOME ((chk ⇒ ok), sq, prew, j)
Proof
  Cases_on ‘chk’
  >- (namedCases_on ‘parseNodeSI T ws pt t s lim i’ ["", "r"]
      >> simp[] >> TRY (PairCases_on ‘r’ >> simp[]))
  >> simp[parseNodeSI_def]
  >> rpt (TOP_CASE_TAC >> simp[])
QED

Theorem lookNodeSI_bproj:
  bproj t' t ⇒
  lookNodeSI t off = OPTION_MAP (λ(b,sq,pw). (sq,pw)) (lookNodeI t' off)
Proof
  rw[bproj_def, lookNodeSI_def, lookNodeI_def]
QED

Theorem lookNodesSI_bproj:
  ∀offs t' t. bproj t' t ⇒
  lookNodesSI t offs =
  OPTION_MAP (MAP (λ(b,sq,pw). (sq,pw))) (lookNodesI t' offs)
Proof
  Induct
  >- rw[lookNodesSI_def, lookNodesI_def]
  >> rpt gen_tac >> strip_tac
  >> res_tac
  >> ‘∀off. lookNodeSI t off =
        OPTION_MAP (λ(b,sq,pw). (sq,pw)) (lookNodeI t' off)’
       by metis_tac[lookNodeSI_bproj]
  >> simp[lookNodesSI_def, lookNodesI_def]
  >> Cases_on ‘lookNodeI t' h’ >> simp[]
  >> TRY (PairCases_on ‘x’ >> simp[])
  >> TRY (Cases_on ‘lookNodesI t' offs’ >> gvs[])
QED

Theorem parseNodeSI_rel:
  ∀ws pt t' t s lim i. bproj t' t ⇒
  (case parseNodeI ws pt t' s lim i of
   | NONE => parseNodeSI T ws pt t s lim i = NONE
   | SOME (b, sq, prew, j) =>
       ∃ok. parseNodeSI T ws pt t s lim i = SOME (ok, sq, prew, j) ∧
            (b ⇒ ok) ∧ (allT t' ⇒ ok ⇒ b))
Proof
  rpt gen_tac >> strip_tac
  >> ‘∀off. lookNodeSI t off =
        OPTION_MAP (λ(b,sq,pw). (sq,pw)) (lookNodeI t' off)’
       by metis_tac[lookNodeSI_bproj]
  >> ‘∀offs. lookNodesSI t offs =
        OPTION_MAP (MAP (λ(b,sq,pw). (sq,pw))) (lookNodesI t' offs)’
       by metis_tac[lookNodesSI_bproj]
  >> simp[parseNodeI_def, parseNodeSI_def]
  >> namedCases_on ‘rdU8I s lim i’ ["", "p"] >> simp[]
  >> PairCases_on ‘p’ >> simp[]
  >> namedCases_on ‘rdU8I s lim p1’ ["", "v"] >> simp[]
  >> PairCases_on ‘v’ >> simp[]
  >> namedCases_on ‘rdLEI s lim 2 v1’ ["", "rz"] >> simp[]
  >> PairCases_on ‘rz’ >> simp[]
  >> rw[]
  >> namedCases_on ‘rdLEI s lim 4 rz1’ ["", "cj"] >> simp[]
  >> PairCases_on ‘cj’ >> simp[]
  >> namedCases_on ‘lookJudgI pt cj0’ ["", "lj"] >> simp[]
  >> PairCases_on ‘lj’ >> simp[]
  >> Cases_on ‘p0 = 0’ >> simp[]
  >- (rw[]
      >> simp[] >> rw[]
      >> gvs[allT_def, lookNodeI_def] >> TRY res_tac >> gvs[])
  >> Cases_on ‘p0 = 1’ >> simp[]
  >- (rw[]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘lookNodeI t' q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookFormulaI pt q20’ ["", "f1"] >> simp[]
      >> PairCases_on ‘f1’ >> simp[]
      >> simp[] >> rw[]
      >> gvs[allT_def, lookNodeI_def] >> TRY res_tac >> gvs[])
  >> Cases_on ‘p0 = 2’ >> simp[]
  >- (rw[]
      >> namedCases_on ‘rdLEI s lim 4 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 8 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 8 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘lookFormulaI pt q10’ ["", "f1"] >> simp[]
      >> PairCases_on ‘f1’ >> simp[]
      >> namedCases_on ‘lookNodeI t' q20’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookNodeI t' q30’ ["", "e2"] >> simp[]
      >> PairCases_on ‘e2’ >> simp[]
      >> simp[] >> rw[]
      >> gvs[allT_def, lookNodeI_def] >> TRY res_tac >> gvs[])
  >> Cases_on ‘p0 = 3’ >> simp[]
  >- (rw[]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 8 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘lookNodeI t' q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookNodeI t' q20’ ["", "e2"] >> simp[]
      >> PairCases_on ‘e2’ >> simp[]
      >> simp[] >> rw[]
      >> gvs[allT_def, lookNodeI_def] >> TRY res_tac >> gvs[])
  >> Cases_on ‘p0 = 4 ∨ p0 = 5’ >> simp[]
  >- (rw[]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘lookNodeI t' q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookFormulaI pt q20’ ["", "f1"] >> simp[]
      >> PairCases_on ‘f1’ >> simp[]
      >> simp[] >> rw[]
      >> gvs[allT_def, lookNodeI_def] >> TRY res_tac >> gvs[])
  >> Cases_on ‘p0 = 6’ >> simp[]
  >- (rw[]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 8 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘takeNI s lim q30 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> rw[]
      >> namedCases_on ‘lookNodeI t' q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookNodeI t' q20’ ["", "e2"] >> simp[]
      >> PairCases_on ‘e2’ >> simp[]
      >> simp[] >> rw[]
      >> gvs[allT_def, lookNodeI_def] >> TRY res_tac >> gvs[])
  >> Cases_on ‘p0 = 7’ >> simp[]
  >- (rw[]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 8 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q41’ ["", "q5"] >> simp[]
      >> PairCases_on ‘q5’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q51’ ["", "q6"] >> simp[]
      >> PairCases_on ‘q6’ >> simp[]
      >> namedCases_on ‘lookNodeI t' q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookNodeI t' q20’ ["", "e2"] >> simp[]
      >> PairCases_on ‘e2’ >> simp[]
      >> namedCases_on ‘lookTermI pt q40’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q50’ ["", "tB"] >> simp[]
      >> namedCases_on ‘lookFormulaI pt q60’ ["", "f1"] >> simp[]
      >> PairCases_on ‘f1’ >> simp[]
      >> simp[] >> rw[]
      >> gvs[allT_def, lookNodeI_def] >> TRY res_tac >> gvs[])
  >> Cases_on ‘p0 = 8 ∨ p0 = 9’ >> simp[]
  >- (rw[]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> namedCases_on ‘lookNodeI t' q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookSimplexI pt q30’ ["", "sA"] >> simp[]
      >> namedCases_on ‘lookExtSetI pt q40’ ["", "eA"] >> simp[]
      >> simp[] >> rw[]
      >> gvs[allT_def, lookNodeI_def] >> TRY res_tac >> gvs[])
  >> Cases_on ‘p0 = 10’ >> simp[]
  >- (rw[]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘rdU8I s lim q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> rw[]
      >> namedCases_on ‘takeNI s lim 3 q41’ ["", "q5"] >> simp[]
      >> PairCases_on ‘q5’ >> simp[]
      >> rw[]
      >> namedCases_on ‘bowtieOf q40’ ["", "bw"] >> simp[]
      >> namedCases_on ‘lookNodeI t' q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q30’ ["", "tB"] >> simp[]
      >> simp[] >> rw[]
      >> gvs[allT_def, lookNodeI_def] >> TRY res_tac >> gvs[])
  >> Cases_on ‘p0 = 11’ >> simp[]
  >- (rw[]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q41’ ["", "q5"] >> simp[]
      >> PairCases_on ‘q5’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q51’ ["", "q6"] >> simp[]
      >> PairCases_on ‘q6’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q61’ ["", "q7"] >> simp[]
      >> PairCases_on ‘q7’ >> simp[]
      >> namedCases_on ‘lookNodeI t' q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookSimplexI pt q30’ ["", "sA"] >> simp[]
      >> namedCases_on ‘lookExtSetI pt q40’ ["", "eA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q60’ ["", "tB"] >> simp[]
      >> namedCases_on ‘lookFormulaI pt q70’ ["", "f1"] >> simp[]
      >> PairCases_on ‘f1’ >> simp[]
      >> simp[] >> rw[]
      >> gvs[allT_def, lookNodeI_def] >> TRY res_tac >> gvs[])
  >> Cases_on ‘p0 = 12’ >> simp[]
  >- (rw[]
      >> namedCases_on ‘rdLEI s lim 4 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘lookTermI pt q10’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tB"] >> simp[]
      >> simp[] >> rw[]
      >> gvs[allT_def, lookNodeI_def] >> TRY res_tac >> gvs[])
  >> Cases_on ‘p0 = 14’ >> simp[]
  >- (rw[]
      >> namedCases_on ‘rdLEI s lim 4 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 8 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘lookTermI pt q10’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tB"] >> simp[]
      >> simp[] >> rw[]
      >> gvs[allT_def, lookNodeI_def] >> TRY res_tac >> gvs[])
  >> Cases_on ‘p0 = 23’ >> simp[]
  >- (rw[]
      >> namedCases_on ‘rdLEI s lim 4 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘lookTermI pt q10’ ["", "tA"] >> simp[]
      >> simp[] >> rw[]
      >> gvs[allT_def, lookNodeI_def] >> TRY res_tac >> gvs[])
  >> Cases_on ‘p0 = 24’ >> simp[]
  >- (rw[]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘lookNodeI t' q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q30’ ["", "tB"] >> simp[]
      >> simp[] >> rw[]
      >> gvs[allT_def, lookNodeI_def] >> TRY res_tac >> gvs[])
  >> Cases_on ‘p0 = 25’ >> simp[]
  >- (rw[]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 8 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> namedCases_on ‘takeNI s lim q40 q41’ ["", "q5"] >> simp[]
      >> PairCases_on ‘q5’ >> simp[]
      >> rw[]
      >> namedCases_on ‘rdLEI s lim 4 q51’ ["", "q6"] >> simp[]
      >> PairCases_on ‘q6’ >> simp[]
      >> namedCases_on ‘rdLEsNI s lim 4 q60 q61’ ["", "q7"] >> simp[]
      >> PairCases_on ‘q7’ >> simp[]
      >> namedCases_on ‘lookNodeI t' q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookNodeI t' q20’ ["", "e2"] >> simp[]
      >> PairCases_on ‘e2’ >> simp[]
      >> namedCases_on ‘lookFormulaI pt q30’ ["", "f1"] >> simp[]
      >> PairCases_on ‘f1’ >> simp[]
      >> simp[] >> rw[]
      >> gvs[allT_def, lookNodeI_def] >> TRY res_tac >> gvs[])
  >> Cases_on ‘p0 = 26’ >> simp[]
  >- (rw[]
      >> namedCases_on ‘rdLEI s lim 4 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEsNI s lim 8 q10 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 8 q41’ ["", "q5"] >> simp[]
      >> PairCases_on ‘q5’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q51’ ["", "q6"] >> simp[]
      >> PairCases_on ‘q6’ >> simp[]
      >> namedCases_on ‘lookNodesI t' q20’ ["", "cm"] >> simp[]
      >> namedCases_on ‘lookTermI pt q30’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q40’ ["", "tB"] >> simp[]
      >> simp[MAP_FST_bdrop]
      >> rw[]
      >> TRY (namedCases_on ‘lookTermI pt q60’ ["", "tv"] >> simp[] >> Cases_on ‘tv’ >> simp[])
      >> rw[] >> imp_res_tac lookNodesI_allT
      >> gvs[allT_def, lookNodeI_def] >> TRY res_tac >> gvs[])
  >> simp[]
QED

Theorem parseNodeSI_project:
  ∀ws pt t' t s lim i. bproj t' t ⇒
  (case parseNodeI ws pt t' s lim i of
   | NONE => parseNodeSI T ws pt t s lim i = NONE
   | SOME (b, sq, prew, j) =>
       ∃ok. parseNodeSI T ws pt t s lim i = SOME (ok, sq, prew, j) ∧
            (b ⇒ ok))
Proof
  rpt gen_tac >> strip_tac
  >> drule_then (qspecl_then [‘ws’, ‘pt’, ‘s’, ‘lim’, ‘i’] mp_tac)
       parseNodeSI_rel
  >> Cases_on ‘parseNodeI ws pt t' s lim i’ >> simp[]
  >> TRY (PairCases_on ‘x’ >> simp[])
  >> rpt strip_tac >> simp[] >> metis_tac[]
QED

Theorem parseNodeSI_lift:
  ∀ws pt t' t s lim i sq prew j. bproj t' t ∧ allT t' ∧
  parseNodeSI T ws pt t s lim i = SOME (T, sq, prew, j) ⇒
  parseNodeI ws pt t' s lim i = SOME (T, sq, prew, j)
Proof
  rpt gen_tac >> strip_tac
  >> drule_then (qspecl_then [‘ws’, ‘pt’, ‘s’, ‘lim’, ‘i’] mp_tac)
       parseNodeSI_rel
  >> Cases_on ‘parseNodeI ws pt t' s lim i’ >> simp[]
  >> TRY (PairCases_on ‘x’ >> simp[])
  >> rpt strip_tac >> gvs[]
QED

Theorem parseNodeSI_pair:
  parseNodeSI c1 ws pt t s lim i = SOME (ok1, sq, prew, j) ∧
  parseNodeSI c2 ws pt t s lim i = SOME (ok2, sq2, prew2, j2) ⇒
  sq2 = sq ∧ prew2 = prew ∧ j2 = j ∧
  parseNodeSI (c1 ∨ c2) ws pt t s lim i = SOME (ok1 ∧ ok2, sq, prew, j)
Proof
  once_rewrite_tac[parseNodeSI_chk]
  >> Cases_on ‘parseNodeSI T ws pt t s lim i’ >> simp[]
  >> TRY (PairCases_on ‘x’ >> simp[])
  >> rpt strip_tac >> gvs[]
  >> Cases_on ‘c1’ >> Cases_on ‘c2’ >> gvs[]
QED

Definition shardPassI_def:
  shardPassI (0:num) (chkf:num -> bool) (ws:tensortype list)
             (pt : pobjI spt) (s:mlstring) (lim:num) (pos:num) (i:num)
             (t : (sequent # fwire) spt) (cnt:num) (acc:bool) =
    (if i = lim ∨ strlen s ≤ i then SOME (t, cnt, acc) else NONE) ∧
  shardPassI (SUC f) chkf ws pt s lim pos i t cnt acc =
    if i = lim ∨ strlen s ≤ i then SOME (t, cnt, acc) else
    case parseNodeSI (chkf cnt) ws pt t s lim i of NONE => NONE
    | SOME (ok, sq, prew, i') =>
        if i' < i then NONE else
        shardPassI f chkf ws pt s lim (pos + (i' − i)) i'
                   (sptree$insert pos (sq, prew) t) (cnt + 1) (ok ∧ acc)
End

Theorem shardPassI_cnt_mono:
  ∀f chkf pos i t cnt acc t1 cnt1 acc1.
    shardPassI f chkf ws pt s lim pos i t cnt acc = SOME (t1, cnt1, acc1) ⇒
    cnt ≤ cnt1
Proof
  Induct
  >- (rw[shardPassI_def] >> gvs[])
  >> rw[shardPassI_def] >> gvs[AllCaseEqs()]
  >> res_tac >> DECIDE_TAC
QED

Theorem shardPassI_accT:
  ∀f chkf pos i t cnt acc t1 cnt1.
    shardPassI f chkf ws pt s lim pos i t cnt acc = SOME (t1, cnt1, T) ⇒
    acc = T
Proof
  Induct
  >- (rw[shardPassI_def] >> gvs[])
  >> rw[shardPassI_def] >> gvs[AllCaseEqs()]
  >> res_tac >> gvs[]
QED

Theorem shardPassI_project:
  ∀f pos i t' t cnt acc.
    bproj t' t ⇒
    (case nodePassI f ws pt s lim pos i t' cnt of
     | NONE => shardPassI f chkf ws pt s lim pos i t cnt acc = NONE
     | SOME (t1', cnt1) =>
         ∃t1 acc1. shardPassI f chkf ws pt s lim pos i t cnt acc =
                   SOME (t1, cnt1, acc1) ∧ bproj t1' t1)
Proof
  Induct
  >- (rw[nodePassI_def, shardPassI_def] >> gvs[])
  >> rw[nodePassI_def, shardPassI_def]
  >> TRY (gvs[] >> NO_TAC)
  >> drule_then (mp_tac o SPEC_ALL) parseNodeSI_project
  >> qabbrev_tac ‘pn = parseNodeI ws pt t' s lim i’
  >> Cases_on ‘pn’ >> simp[]
  >- (strip_tac >> simp[Once parseNodeSI_chk])
  >> PairCases_on ‘x’ >> simp[] >> strip_tac
  >> ‘parseNodeSI (chkf cnt) ws pt t s lim i =
        SOME ((chkf cnt ⇒ ok), x1, x2, x3)’
       by simp[Once parseNodeSI_chk]
  >> simp[]
  >> IF_CASES_TAC >> gvs[]
  >> first_x_assum irule
  >> gvs[bproj_def, sptreeTheory.lookup_insert] >> rw[] >> rw[]
QED

Theorem shardPassI_union:
  ∀ws pt s lim f c1f c2f pos i t cnt t1 n1 t2 n2.
    shardPassI f c1f ws pt s lim pos i t cnt T = SOME (t1, n1, T) ∧
    shardPassI f c2f ws pt s lim pos i t cnt T = SOME (t2, n2, T) ⇒
    t2 = t1 ∧ n2 = n1 ∧
    shardPassI f (λm. c1f m ∨ c2f m) ws pt s lim pos i t cnt T =
    SOME (t1, n1, T)
Proof
  ntac 4 gen_tac
  >> Induct
  >- (rw[shardPassI_def] >> gvs[])
  >> rpt gen_tac >> strip_tac
  >> qpat_x_assum ‘shardPassI (SUC f) c1f _ _ _ _ _ _ _ _ _ = _’
       (strip_assume_tac o SIMP_RULE (srw_ss()) [shardPassI_def, AllCaseEqs()])
  >> qpat_x_assum ‘shardPassI (SUC f) c2f _ _ _ _ _ _ _ _ _ = _’
       (strip_assume_tac o SIMP_RULE (srw_ss()) [shardPassI_def, AllCaseEqs()])
  >> gvs[]
  >> TRY (simp[shardPassI_def] >> NO_TAC)
  >> imp_res_tac shardPassI_accT >> gvs[]
  >> qpat_x_assum ‘parseNodeSI (c1f cnt) _ _ _ _ _ _ = _’ (fn th1 =>
       qpat_x_assum ‘parseNodeSI (c2f cnt) _ _ _ _ _ _ = _’ (fn th2 =>
         mp_tac (MATCH_MP parseNodeSI_pair (CONJ th1 th2))))
  >> strip_tac >> gvs[]
  >> qpat_x_assum ‘shardPassI f c1f _ _ _ _ _ _ _ _ _ = _’ (fn r1 =>
       qpat_x_assum ‘shardPassI f c2f _ _ _ _ _ _ _ _ _ = _’ (fn r2 =>
         first_x_assum (fn ih => mp_tac (MATCH_MP ih (CONJ r1 r2)))))
  >> strip_tac
  >> gvs[shardPassI_def]
QED

Theorem shardPassI_policy_local:
  ∀ws pt s lim f c1f c2f pos i t cnt acc t1 cnt1 acc1.
    shardPassI f c1f ws pt s lim pos i t cnt acc = SOME (t1, cnt1, acc1) ∧
    (∀m. cnt ≤ m ∧ m < cnt1 ⇒ (c1f m ⇔ c2f m)) ⇒
    shardPassI f c2f ws pt s lim pos i t cnt acc = SOME (t1, cnt1, acc1)
Proof
  ntac 4 gen_tac
  >> Induct
  >- (rw[shardPassI_def] >> gvs[])
  >> rpt gen_tac >> strip_tac
  >> Cases_on ‘i = lim ∨ strlen s ≤ i’
  >- (qpat_x_assum ‘shardPassI (SUC f) c1f _ _ _ _ _ _ _ _ _ = _’ mp_tac
      >> simp[shardPassI_def])
  >> qpat_x_assum ‘shardPassI (SUC f) c1f _ _ _ _ _ _ _ _ _ = _’ mp_tac
  >> simp[shardPassI_def]
  >> Cases_on ‘parseNodeSI (c1f cnt) ws pt t s lim i’ >> simp[]
  >> TRY (PairCases_on ‘x’ >> simp[])
  >> TRY (IF_CASES_TAC >> simp[]) >> strip_tac
  >> imp_res_tac shardPassI_cnt_mono
  >> ‘c2f cnt = c1f cnt’
       by (qpat_x_assum ‘∀m. _ ⇒ _’ (qspec_then ‘cnt’ mp_tac) >> simp[])

  >> pop_assum (fn th => rewrite_tac[th])
  >> qpat_x_assum ‘parseNodeSI _ _ _ _ _ _ _ = _’ (fn th => simp[th])
  >> first_x_assum irule >> simp[]
  >> TRY (qexists_tac ‘c1f’ >> simp[])
  >> rw[]
  >> qpat_x_assum ‘∀m. _ ⇒ _’ (qspec_then ‘m’ mp_tac) >> simp[]
QED

Theorem shardPassI_allT_lift:
  ∀f pos i t' t cnt t1 cnt1.
    bproj t' t ∧ allT t' ∧
    shardPassI f (K T) ws pt s lim pos i t cnt T = SOME (t1, cnt1, T) ⇒
    ∃t1'. nodePassI f ws pt s lim pos i t' cnt = SOME (t1', cnt1) ∧
          bproj t1' t1 ∧ allT t1'
Proof
  Induct
  >- (rw[nodePassI_def, shardPassI_def] >> gvs[])
  >> rpt gen_tac >> strip_tac
  >> qpat_x_assum ‘shardPassI _ _ _ _ _ _ _ _ _ _ _ = _’ mp_tac
  >> simp[nodePassI_def, shardPassI_def]
  >> IF_CASES_TAC >> simp[]
  >- (rpt strip_tac >> gvs[])
  >> TOP_CASE_TAC >> simp[]
  >> TOP_CASE_TAC >> TOP_CASE_TAC >> TOP_CASE_TAC
  >> IF_CASES_TAC >> simp[]
  >> strip_tac
  >> imp_res_tac shardPassI_accT >> gvs[]
  >> drule_all_then strip_assume_tac parseNodeSI_lift
  >> simp[]
  >> first_x_assum irule >> simp[]
  >> gvs[bproj_def, allT_def, sptreeTheory.lookup_insert]
  >> rw[] >> rw[] >> TRY (res_tac >> gvs[] >> NO_TAC)
  >> TRY (qexists_tac ‘insert pos (q',q'') t’
          >> simp[sptreeTheory.lookup_insert]
          >> rw[] >> gvs[])
QED

Definition shardProofSectionI_def:
  shardProofSectionI (chkf:num -> bool) (ws:tensortype list) (s:mlstring)
                     (base:num) (seclen:num) (cxs:simpc list)
                     (hnn:num) (rootOff:num) (thetaRef:num) =
    let lim = base + seclen in
    case rdLEI s lim 8 base of NONE => NONE | SOME (plen, i1) =>
    if ¬(i1 + plen ≤ lim ∧ i1 + plen ≤ strlen s) then NONE else
    (let poolLim = i1 + plen in
     case poolPassI (SUC plen) cxs s poolLim 0 i1 sptree$LN of
     | NONE => NONE
     | SOME pt =>
     if ¬(thetaRef = (4294967295:num) ∨
          (case lookTermI pt thetaRef of
           | SOME (TmConst q) => T
           | _ => F)) then NONE else
     case shardPassI (SUC (lim − (i1 + plen))) chkf ws pt s lim (8 + plen)
                     poolLim sptree$LN 0 T of
     | NONE => NONE
     | SOME (nt, cnt, acc) =>
     if cnt ≠ hnn then NONE else
     case lookNodeSI nt rootOff of
     | NONE => NONE
     | SOME (sq, prew) =>
         if rootShapeOK prew then SOME acc else NONE)
End

Definition checkShardI_def:
  checkShardI (s:mlstring) (lo:num) (hi:num) =
    case parseHeaderI s of NONE => NONE | SOME h =>
    case parseSymtabI s h.symOff h.symLen h.nWires h.payOff h.payLen of
    | NONE => NONE
    | SOME ws =>
    case parseDiagramI s h.diaOff h.diaLen h.nCxs h.nApps of
    | NONE => NONE
    | SOME cxs =>
    case shardProofSectionI (λm. lo ≤ m ∧ m < hi) ws s h.prfOff h.prfLen
                            cxs h.nNodes h.rootOff h.thetaRef of
    | NONE => NONE
    | SOME acc => if acc then SOME h.nNodes else NONE
End

Definition shardTranscriptI_def:
  shardTranscriptI (s:mlstring) (lo:num) (hi:num) =
    (lo, hi, checkShardI s lo hi)
End

Definition ivLo_def:
  ivLo (deltas:num list) (j:num) = SUM (TAKE j deltas)
End
Definition ivHi_def:
  ivHi (deltas:num list) (j:num) = SUM (TAKE (SUC j) deltas)
End

Theorem SUM_TAKE_mono:
  ∀ds j. SUM (TAKE j ds) ≤ SUM (TAKE (SUC j) ds)
Proof
  Induct >> rw[] >> Cases_on ‘j’ >> simp[]
QED

Theorem bproj_LN:
  bproj LN LN
Proof
  rw[bproj_def, sptreeTheory.lookup_def]
QED

Theorem allT_LN:
  allT LN
Proof
  rw[allT_def, sptreeTheory.lookup_def]
QED

Theorem shardPassI_prefix:
  ∀ws pt s lim ds f pos i t0 N.
    (∀j. j < LENGTH ds ⇒
         ∃tj. shardPassI f (λm. ivLo ds j ≤ m ∧ m < ivHi ds j)
                ws pt s lim pos i t0 0 T = SOME (tj, N, T)) ∧ ds ≠ [] ⇒
    ∃nt. shardPassI f (λm. m < SUM ds) ws pt s lim pos i t0 0 T =
         SOME (nt, N, T)
Proof
  simp[ivLo_def, ivHi_def]
  >> rpt gen_tac >> strip_tac
  >> ‘0 < LENGTH ds’ by (Cases_on ‘ds’ >> gvs[])
  >> ‘∀n. 0 < n ∧ n ≤ LENGTH ds ⇒
        ∃nt. shardPassI f (λm. m < SUM (TAKE n ds)) ws pt s lim pos i t0 0 T =
             SOME (nt, N, T)’
     suffices_by (disch_then (qspec_then ‘LENGTH ds’ mp_tac)
                  >> simp[TAKE_LENGTH_ID])
  >> Induct_on ‘n’ >- simp[]
  >> strip_tac
  >> Cases_on ‘n = 0’
  >- (gvs[]
      >> last_x_assum (qspec_then ‘0’ mp_tac) >> simp[]
      >> strip_tac
      >> qexists_tac ‘tj’
      >> irule shardPassI_policy_local
      >> qexists_tac ‘λm. SUM (TAKE 0 ds) ≤ m ∧ m < SUM (TAKE (SUC 0) ds)’
      >> simp[])
  >> ‘0 < n ∧ n ≤ LENGTH ds ∧ n < LENGTH ds’ by (Cases_on ‘n’ >> gvs[])
  >> qpat_x_assum
       ‘_ ⇒ ∃nt. shardPassI _ (λm. m < SUM (TAKE n ds)) _ _ _ _ _ _ _ _ _ = _’
       mp_tac
  >> simp[] >> strip_tac
  >> last_x_assum (qspec_then ‘n’ mp_tac) >> simp[] >> strip_tac
  >> qspecl_then [‘ws’, ‘pt’, ‘s’, ‘lim’, ‘f’, ‘λm. m < SUM (TAKE n ds)’,
                  ‘λm. SUM (TAKE n ds) ≤ m ∧ m < SUM (TAKE (SUC n) ds)’,
                  ‘pos’, ‘i’, ‘t0’, ‘0’, ‘nt’, ‘N’, ‘tj’, ‘N’]
       mp_tac shardPassI_union
  >> simp[] >> strip_tac
  >> qexists_tac ‘nt’
  >> irule shardPassI_policy_local
  >> qexists_tac ‘λm. m < SUM (TAKE n ds) ∨
                      (SUM (TAKE n ds) ≤ m ∧ m < SUM (TAKE (SUC n) ds))’
  >> simp[]
  >> ‘SUM (TAKE n ds) ≤ SUM (TAKE (SUC n) ds)’ by simp[SUM_TAKE_mono]
  >> rw[] >> DECIDE_TAC
QED

Theorem shardProofSection_coverage:
  ∀ws s base seclen cxs hnn rootOff thetaRef deltas.
    deltas ≠ [] ∧ SUM deltas = hnn ∧
    (∀j. j < LENGTH deltas ⇒
         shardProofSectionI (λm. ivLo deltas j ≤ m ∧ m < ivHi deltas j)
           ws s base seclen cxs hnn rootOff thetaRef = SOME T) ⇒
    parseProofSectionI ws s base seclen cxs hnn rootOff thetaRef = SOME T
Proof
  rpt gen_tac >> strip_tac
  >> ‘0 < LENGTH deltas’ by (Cases_on ‘deltas’ >> gvs[])
  >> first_assum (qspec_then ‘0’ mp_tac)
  >> impl_tac >- simp[]
  >> disch_then (mp_tac o SIMP_RULE (srw_ss()) [shardProofSectionI_def,
                                                LET_THM])
  >> namedCases_on ‘rdLEI s (base + seclen) 8 base’ ["", "pl"] >> simp[]
  >> PairCases_on ‘pl’ >> simp[]
  >> TRY (IF_CASES_TAC >> simp[])
  >> namedCases_on ‘poolPassI (SUC pl0) cxs s (pl0 + pl1) 0 pl1 LN’
       ["", "ptb"] >> simp[]
  >> TRY (IF_CASES_TAC >> simp[])
  >> namedCases_on
       ‘shardPassI (SUC (base + seclen − (pl0 + pl1)))
          (λm. ivLo deltas 0 ≤ m ∧ m < ivHi deltas 0) ws ptb s
          (base + seclen) (pl0 + 8) (pl0 + pl1) LN 0 T’ ["", "r0"] >> simp[]
  >> TRY (PairCases_on ‘r0’ >> simp[])
  >> TRY (IF_CASES_TAC >> simp[])
  >> namedCases_on ‘lookNodeSI r00 rootOff’ ["", "rt"] >> simp[]
  >> TRY (PairCases_on ‘rt’ >> simp[])
  >> TRY (IF_CASES_TAC >> simp[])
  >> strip_tac >> gvs[]

  >| [(
      ‘∀j. j < LENGTH deltas ⇒
         ∃tj. shardPassI (SUC (base + seclen − (pl0 + pl1)))
                (λm. ivLo deltas j ≤ m ∧ m < ivHi deltas j)
                ws ptb s (base + seclen) (pl0 + 8) (pl0 + pl1) LN 0 T =
              SOME (tj, SUM deltas, T)’
        by (rw[] >> first_x_assum drule
            >> simp[shardProofSectionI_def, LET_THM]
            >> gvs[AllCaseEqs()] >> rw[] >> gvs[] >> metis_tac[])
      >> qspecl_then [‘ws’, ‘ptb’, ‘s’, ‘base + seclen’, ‘deltas’,
                      ‘SUC (base + seclen − (pl0 + pl1))’,
                      ‘pl0 + 8’, ‘pl0 + pl1’, ‘LN’, ‘SUM deltas’]
           mp_tac shardPassI_prefix
      >> impl_tac >- simp[]
      >> strip_tac
      >> ‘shardPassI (SUC (base + seclen − (pl0 + pl1))) (K T) ws ptb s
            (base + seclen) (pl0 + 8) (pl0 + pl1) LN 0 T =
          SOME (nt, SUM deltas, T)’
         by (irule shardPassI_policy_local
             >> qexists_tac ‘λm. m < SUM deltas’
             >> gvs[combinTheory.K_DEF])
      >> assume_tac bproj_LN >> assume_tac allT_LN
      >> drule_all_then strip_assume_tac shardPassI_allT_lift
      >> TRY (qspecl_then [‘ws’, ‘ptb’, ‘s’, ‘base + seclen’,
                           ‘SUC (base + seclen − (pl0 + pl1))’,
                           ‘λm. ivLo deltas 0 ≤ m ∧ m < ivHi deltas 0’,
                           ‘K T’, ‘pl0 + 8’, ‘pl0 + pl1’, ‘LN’, ‘0’,
                           ‘r00’, ‘SUM deltas’, ‘nt’, ‘SUM deltas’]
                mp_tac shardPassI_union
              >> simp[] >> strip_tac >> gvs[])
      >> qpat_assum ‘bproj t1' nt’ (fn b => assume_tac
           (MP (Q.INST [‘t'’ |-> ‘t1'’, ‘t’ |-> ‘nt’, ‘off’ |-> ‘rootOff’]
                  (SPEC_ALL lookNodeSI_bproj)) b))
      >> Cases_on ‘lookNodeI t1' rootOff’ >> gvs[]
      >> TRY (PairCases_on ‘x’ >> gvs[])
      >> TRY (‘x0’ by (qpat_x_assum ‘lookNodeI t1' rootOff = _’ mp_tac
                       >> qpat_x_assum ‘allT t1'’ mp_tac
                       >> simp[allT_def, lookNodeI_def]
                       >> rpt strip_tac >> res_tac >> gvs[])
              >> gvs[])
      >> simp[parseProofSectionI_def, LET_THM, lookNodeI_def]
      >> TRY (gvs[lookNodeI_def])),
      (
      ‘∀j. j < LENGTH deltas ⇒
         ∃tj. shardPassI (SUC (base + seclen − (pl0 + pl1)))
                (λm. ivLo deltas j ≤ m ∧ m < ivHi deltas j)
                ws ptb s (base + seclen) (pl0 + 8) (pl0 + pl1) LN 0 T =
              SOME (tj, SUM deltas, T)’
        by (rw[] >> first_x_assum drule
            >> simp[shardProofSectionI_def, LET_THM]
            >> gvs[AllCaseEqs()] >> rw[] >> gvs[] >> metis_tac[])
      >> qspecl_then [‘ws’, ‘ptb’, ‘s’, ‘base + seclen’, ‘deltas’,
                      ‘SUC (base + seclen − (pl0 + pl1))’,
                      ‘pl0 + 8’, ‘pl0 + pl1’, ‘LN’, ‘SUM deltas’]
           mp_tac shardPassI_prefix
      >> impl_tac >- simp[]
      >> strip_tac
      >> ‘shardPassI (SUC (base + seclen − (pl0 + pl1))) (K T) ws ptb s
            (base + seclen) (pl0 + 8) (pl0 + pl1) LN 0 T =
          SOME (nt, SUM deltas, T)’
         by (irule shardPassI_policy_local
             >> qexists_tac ‘λm. m < SUM deltas’
             >> gvs[combinTheory.K_DEF])
      >> assume_tac bproj_LN >> assume_tac allT_LN
      >> drule_all_then strip_assume_tac shardPassI_allT_lift
      >> TRY (qspecl_then [‘ws’, ‘ptb’, ‘s’, ‘base + seclen’,
                           ‘SUC (base + seclen − (pl0 + pl1))’,
                           ‘λm. ivLo deltas 0 ≤ m ∧ m < ivHi deltas 0’,
                           ‘K T’, ‘pl0 + 8’, ‘pl0 + pl1’, ‘LN’, ‘0’,
                           ‘r00’, ‘SUM deltas’, ‘nt’, ‘SUM deltas’]
                mp_tac shardPassI_union
              >> simp[] >> strip_tac >> gvs[])
      >> qpat_assum ‘bproj t1' nt’ (fn b => assume_tac
           (MP (Q.INST [‘t'’ |-> ‘t1'’, ‘t’ |-> ‘nt’, ‘off’ |-> ‘rootOff’]
                  (SPEC_ALL lookNodeSI_bproj)) b))
      >> Cases_on ‘lookNodeI t1' rootOff’ >> gvs[]
      >> TRY (PairCases_on ‘x’ >> gvs[])
      >> TRY (‘x0’ by (qpat_x_assum ‘lookNodeI t1' rootOff = _’ mp_tac
                       >> qpat_x_assum ‘allT t1'’ mp_tac
                       >> simp[allT_def, lookNodeI_def]
                       >> rpt strip_tac >> res_tac >> gvs[])
              >> gvs[])
      >> simp[parseProofSectionI_def, LET_THM, lookNodeI_def]
      >> TRY (gvs[lookNodeI_def]))]
QED

Theorem shard_coverage:
  ∀s deltas N.
    deltas ≠ [] ∧ SUM deltas = N ∧
    (∀j. j < LENGTH deltas ⇒
         checkShardI s (ivLo deltas j) (ivHi deltas j) = SOME N) ⇒
    checkTopI s
Proof
  rpt gen_tac >> strip_tac
  >> ‘0 < LENGTH deltas’ by (Cases_on ‘deltas’ >> gvs[])
  >> first_assum (qspec_then ‘0’ mp_tac)
  >> impl_tac >- simp[]
  >> disch_then (mp_tac o SIMP_RULE (srw_ss()) [checkShardI_def])
  >> namedCases_on ‘parseHeaderI s’ ["", "h"] >> simp[]
  >> namedCases_on
       ‘parseSymtabI s h.symOff h.symLen h.nWires h.payOff h.payLen’
       ["", "ws1"] >> simp[]
  >> namedCases_on ‘parseDiagramI s h.diaOff h.diaLen h.nCxs h.nApps’
       ["", "cxs1"] >> simp[]
  >> namedCases_on
       ‘shardProofSectionI (λm. ivLo deltas 0 ≤ m ∧ m < ivHi deltas 0) ws1 s
          h.prfOff h.prfLen cxs1 h.nNodes h.rootOff h.thetaRef’
       ["", "acc0"] >> simp[]
  >> rw[] >> gvs[]
  >> ‘∀j. j < LENGTH deltas ⇒
        shardProofSectionI (λm. ivLo deltas j ≤ m ∧ m < ivHi deltas j) ws1 s
          h.prfOff h.prfLen cxs1 (SUM deltas) h.rootOff h.thetaRef = SOME T’
     by (rw[] >> first_x_assum drule
         >> simp[checkShardI_def]
         >> gvs[AllCaseEqs()] >> rw[] >> gvs[])
  >> ‘parseProofSectionI ws1 s h.prfOff h.prfLen cxs1 (SUM deltas) h.rootOff
        h.thetaRef = SOME T’
     by (irule shardProofSection_coverage >> simp[]
         >> qexists_tac ‘deltas’ >> simp[])
  >> simp[checkTopI_def]
QED
