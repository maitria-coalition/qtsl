(*
  The relational well-formedness layer over the succinct columns:
  mkCtx (the fail-closed directory builder), wfColumns (the
  well-formedness predicate, each item naming its parser counterpart),
  and nodeCorr (the per-node refinement relation, realized as the graph
  of a fuel-indexed reconstruction function so uniqueness is
  definitional and existence is a totality lemma). Includes a
  computational demo instance and a mutant battery.
*)
Theory qtsl_wf
Ancestors
  rat integer mlstring mllist qtsl_dyadic qtsl_qarith qtsl_catalogue
  qtsl_cert qtsl_cols
Libs
  preamble

Definition peekPrfLen_def:
  peekPrfLen (img:num list) : num = leN (TAKE 8 (DROP 72 img))
End

Datatype:
  pstate = <|
    poff  : num ;
    poffs : num list ;
    pidx  : (num # num) list ;
    jidx  : ((num # num) # num) list ;
    refb  : num list ;
    refn  : num ;
    elemb : num list ;
    elemn : num ;
    miscn : num ;
    vtx   : (num # num) list
  |>
End

Definition pInit_def:
  pInit = <| poff := 0 ; poffs := [] ; pidx := [] ; jidx := [] ;
             refb := [0] ; refn := 0 ; elemb := [0] ; elemn := 0 ;
             miscn := 0 ; vtx := [] |>
End

Definition poolRecLen_def:
  poolRecLen (cols:columns) (cxs:simpc list) (st:pstate) (t:num)
             : (num # num) option =

    if t = (1:num) then SOME (5, 1)
    else if t = 2 then
      (case oEL st.elemn cols.poolNumLen of NONE => NONE | SOME nl =>
       case oEL st.elemn cols.poolDenId of NONE => NONE | SOME did =>
       case oEL did cols.poolDenDict of NONE => NONE | SOME db =>
         SOME (9 + nl + LENGTH db, 0))
    else if t = 3 ∨ t = 4 ∨ t = 5 then SOME (9, 0)
    else if t = 6 then SOME (5, 0)
    else if t = 7 then SOME (9, 1)
    else if t = 16 then
      (case oEL st.miscn cols.poolMisc of NONE => NONE | SOME ci =>
       case oEL ci cxs of NONE => NONE | SOME cx =>
         SOME (5 + (cx.nVertices + 7) DIV 8, 1 + (cx.nVertices + 7) DIV 8))
    else if t = 17 then
      (case oEL st.refn cols.poolRef of NONE => NONE | SOME so =>
       case ALOOKUP st.vtx so of NONE => NONE | SOME nv =>
         SOME (5 + (nv + 7) DIV 8, (nv + 7) DIV 8))
    else if t = 32 then SOME (10, 1)
    else if t = 33 then SOME (13, 0)
    else if t = 34 ∨ t = 35 then SOME (9, 0)
    else if t = 36 ∨ t = 37 ∨ t = 38 then SOME (1, 0)
    else if t = 48 then SOME (9, 0)
    else NONE
End

Definition poolStep_def:
  poolStep (cols:columns) (cxs:simpc list)
           (acc:pstate option) (j:num) : pstate option =
    case acc of
    | NONE => NONE
    | SOME st =>
      case oEL j cols.poolTag of
      | NONE => NONE
      | SOME t =>
        case poolRecLen cols cxs st t of
        | NONE => NONE
        | SOME (len, mc) =>
          let vtx' = (if t = (16:num) then
                        (case oEL st.miscn cols.poolMisc of
                         | NONE => st.vtx
                         | SOME ci =>
                           (case oEL ci cxs of
                            | NONE => st.vtx
                            | SOME cx => (st.poff, cx.nVertices) :: st.vtx))
                      else st.vtx) in
          let jidx' = (if t = (48:num) then
                         (case oEL st.refn cols.poolRef of
                          | NONE => st.jidx
                          | SOME preR =>
                            (case oEL (st.refn + 1) cols.poolRef of
                             | NONE => st.jidx
                             | SOME postR =>
                               if ALOOKUP st.jidx (preR, postR) = NONE
                               then ((preR, postR), st.poff) :: st.jidx
                               else st.jidx))
                       else st.jidx) in

          if t = (48:num) ∧ LENGTH cols.poolRef < st.refn + 2 then NONE else
            SOME (st with
                  <| poff  := st.poff + len ;
                     poffs := st.poffs ++ [st.poff] ;
                     pidx  := (st.poff, j) :: st.pidx ;
                     jidx  := jidx' ;
                     refb  := st.refb ++ [st.refn + poolRefCnt t] ;
                     refn  := st.refn + poolRefCnt t ;
                     elemb := st.elemb ++ [st.elemn + poolElemCnt t] ;
                     elemn := st.elemn + poolElemCnt t ;
                     miscn := st.miscn + mc ;
                     vtx   := vtx' |>)
End

Definition poolFold_def:
  poolFold (cols:columns) (cxs:simpc list) : pstate option =
    FOLDL (poolStep cols cxs) (SOME pInit) (rangeL cols.nPool)
End

Datatype:
  nstate = <|
    noff   : num ;
    noffs  : num list ;
    nidx   : (num # num) list ;
    scalb  : num list ;
    scaln  : num ;
    pathn  : num ;
    arityn : num
  |>
End

Definition nInit_def:
  nInit (start:num) =
    <| noff := start ; noffs := [] ; nidx := [] ;
       scalb := [0] ; scaln := 0 ; pathn := 0 ; arityn := 0 |>
End

Definition nodeStep_def:
  nodeStep (cols:columns) (acc:nstate option) (i:num) : nstate option =
    case acc of
    | NONE => NONE
    | SOME st =>
      case oEL i cols.nodeTag of
      | NONE => NONE
      | SOME s =>
        case tagDec s of
        | NONE => NONE
        | SOME (r, v) =>
          let lenO =
            (if hasPathR r then
               (case oEL st.pathn cols.nodePath of
                | NONE => NONE
                | SOME (stps, ifc) => SOME (nodeLenR r stps ifc 0))
             else if hasArityR r then
               (case oEL st.arityn cols.nodeArity of
                | NONE => NONE
                | SOME nc => SOME (nodeLenR r [] [] nc))
             else SOME (nodeLenR r [] [] 0)) in
          case lenO of
          | NONE => NONE
          | SOME len =>
              SOME (st with
                    <| noff   := st.noff + len ;
                       noffs  := st.noffs ++ [st.noff] ;
                       nidx   := (st.noff, i) :: st.nidx ;
                       scalb  := st.scalb ++ [st.scaln + scalCntR r] ;
                       scaln  := st.scaln + scalCntR r ;
                       pathn  := st.pathn + (if hasPathR r then 1 else 0) ;
                       arityn := st.arityn + (if hasArityR r then 1 else 0) |>)
End

Definition nodeFold_def:
  nodeFold (cols:columns) (start:num) : nstate option =
    FOLDL (nodeStep cols) (SOME (nInit start)) (rangeL cols.nNodes)
End

Definition rpnStep_def:
  rpnStep (cols:columns)
          (acc:((num list) list # num list) option) (i:num)
          : ((num list) list # num list) option =
    case acc of
    | NONE => NONE
    | SOME (rows, stk) =>
      let a = nodeArityAt cols i in
        if LENGTH stk < a then NONE
        else SOME (rows ++ [REVERSE (TAKE a stk)], i :: DROP a stk)
End

Definition rpnReplay_def:
  rpnReplay (cols:columns) : ((num list) list # num list) option =
    FOLDL (rpnStep cols) (SOME ([], [])) (rangeL cols.nNodes)
End

Definition explChildren_def:
  explChildren (cols:columns) (nidx:(num # num) list) (myoff:num)
               (base:num) (0:num) = SOME ([]:num list) ∧
  explChildren cols nidx myoff base (SUC k) =
    case explChildren cols nidx myoff base k of
    | NONE => NONE
    | SOME acc =>
      case oEL (base + k) cols.nodeTopo of
      | NONE => NONE
      | SOME d =>
        case ALOOKUP nidx (myoff − d) of
        | NONE => NONE
        | SOME c => SOME (acc ++ [c])
End

Definition explStep_def:
  explStep (cols:columns) (noffs:num list) (nidx:(num # num) list)
           (acc:((num list) list # num) option) (i:num)
           : ((num list) list # num) option =
    case acc of
    | NONE => NONE
    | SOME (rows, tb) =>
      let a = nodeArityAt cols i in
        case explChildren cols nidx (getD noffs i 0) tb a of
        | NONE => NONE
        | SOME cs => SOME (rows ++ [cs], tb + a)
End

Definition explRows_def:
  explRows (cols:columns) (noffs:num list) (nidx:(num # num) list)
           : ((num list) list) option =
    case FOLDL (explStep cols noffs nidx) (SOME ([], 0))
               (rangeL cols.nNodes) of
    | NONE => NONE
    | SOME (rows, tb) =>
        if tb = LENGTH cols.nodeTopo then SOME rows else NONE
End

Definition prefExplCnt_def:
  prefExplCnt (cols:columns) (ct:ctx) (cdir:(bool # num) list) (i:num)
              : num =
    let r = ruleOfD cols i in
      if r = (4:num) then
        (case childConcl ct cdir i of
         | NONE => 1
         | SOME cref =>
           case andeOther cols ct (varOfD cols i) cref of
           | NONE => 1
           | SOME _ => if escContains cols.nodeEsc2 i then 1 else 0)
      else if r = 9 then
        (case childConcl ct cdir i of
         | NONE => 3
         | SOME cref =>
           case convTriple cols ct cref of
           | NONE => 3
           | SOME _ => if escContains cols.nodeEsc2 i then 3 else 0)
      else prefCntR r
End

Definition prefBaseOf_def:
  prefBaseOf (cols:columns) (ct:ctx) (cdir:(bool # num) list) : num list =
    GENLIST (λi. SUM (GENLIST (prefExplCnt cols ct cdir) i))
            (cols.nNodes + 1)
End

Definition mkCtx_def:
  mkCtx (cols:columns) : ctx option =
    let img = cols.hdrImage in
    case parseHeader (img ++ REPLICATE (peekPrfLen img) 0) of
    | NONE => NONE
    | SOME h =>
    case parseSymtab (TAKE h.symLen (DROP h.symOff img)) h.symLen
                     h.nWires h.payOff h.payLen of
    | NONE => NONE
    | SOME ws =>
    case parseDiagram (TAKE h.diaLen (DROP h.diaOff img)) h.nCxs h.nApps of
    | NONE => NONE
    | SOME cxs =>
    if ¬(cols.topoMode = 0 ∨ cols.topoMode = 1) then NONE else
    if LENGTH cols.poolTag ≠ cols.nPool then NONE else
    if LENGTH cols.nodeTag ≠ cols.nNodes then NONE else
    case poolFold cols cxs of
    | NONE => NONE
    | SOME pst =>
    case nodeFold cols (8 + pst.poff) of
    | NONE => NONE
    | SOME nst =>
    case (if cols.topoMode = 0 then
            (case rpnReplay cols of
             | NONE => NONE
             | SOME (rows, stk) => SOME rows)
          else explRows cols nst.noffs nst.nidx) of
    | NONE => NONE
    | SOME rows =>
    let ctx0 = <| hdr := h ; ws := ws ; cxs := cxs ;
                  poolOffs := pst.poffs ++ [pst.poff] ;
                  nodeOffs := nst.noffs ++ [nst.noff] ;
                  poolIdx := pst.pidx ; nodeIdx := nst.nidx ;
                  judgIdx := pst.jidx ; childTbl := rows ;
                  prefBase := [] ; scalBase := nst.scalb ;
                  refBase := pst.refb ; elemBase := pst.elemb |> in
    case conclDir cols ctx0 of
    | NONE => NONE
    | SOME cdir =>
      if prefDir cols ctx0 = NONE then NONE
      else SOME (ctx0 with prefBase := prefBaseOf cols ctx0 cdir)
End

Definition isTermAt_def:
  isTermAt (cols:columns) (ct:ctx) (r:num) =
    case poolTagAt cols ct r of SOME t => isTermTag t | NONE => F
End

Definition isFormulaAt_def:
  isFormulaAt (cols:columns) (ct:ctx) (r:num) =
    case poolTagAt cols ct r of SOME t => isFormulaTag t | NONE => F
End

Definition isSimplexAt_def:
  isSimplexAt (cols:columns) (ct:ctx) (r:num) =
    (poolTagAt cols ct r = SOME 16)
End

Definition isExtSetAt_def:
  isExtSetAt (cols:columns) (ct:ctx) (r:num) =
    (poolTagAt cols ct r = SOME 17)
End

Definition isJudgAt_def:
  isJudgAt (cols:columns) (ct:ctx) (r:num) =
    (poolTagAt cols ct r = SOME 48)
End

Definition isConstAt_def:
  isConstAt (cols:columns) (ct:ctx) (r:num) =
    (poolTagAt cols ct r = SOME 2)
End

Definition fwNoSphRef_def:
  fwNoSphRef (cols:columns) (ct:ctx) (0:num) (off:num) = F ∧
  fwNoSphRef cols ct (SUC f) off =
    case poolTagAt cols ct off of
    | NONE => F
    | SOME t =>
        if t = (38:num) then F
        else if t = 34 ∨ t = 35 then
          (case ALOOKUP ct.poolIdx off of
           | NONE => F
           | SOME j =>
             case refAt cols ct j 0 of
             | NONE => F
             | SOME l =>
               case refAt cols ct j 1 of
               | NONE => F
               | SOME rr => fwNoSphRef cols ct f l ∧ fwNoSphRef cols ct f rr)
        else isFormulaTag t
End

Definition wf1_def:
  wf1 (cols:columns) (ct:ctx) ⇔
    EVERY (λb. b < (256:num)) cols.hdrImage ∧
    LENGTH cols.hdrImage = ct.hdr.prfOff ∧
    ct.hdr.symOff + ct.hdr.symLen ≤ ct.hdr.prfOff ∧
    ct.hdr.payOff + ct.hdr.payLen ≤ ct.hdr.prfOff ∧
    ct.hdr.diaOff + ct.hdr.diaLen ≤ ct.hdr.prfOff ∧
    ct.hdr.prfLen = getD ct.nodeOffs cols.nNodes 0 ∧
    ct.hdr.nNodes = cols.nNodes ∧
    0 < cols.nNodes ∧
    ct.hdr.rootOff = getD ct.nodeOffs (cols.nNodes − 1) 0
End

Definition wf2_def:
  wf2 (cols:columns) (ct:ctx) ⇔
    parseSymtab (TAKE ct.hdr.symLen (DROP ct.hdr.symOff cols.hdrImage))
                ct.hdr.symLen ct.hdr.nWires ct.hdr.payOff ct.hdr.payLen
      = SOME ct.ws
End

Definition wf3_def:
  wf3 (cols:columns) (ct:ctx) ⇔
    parseDiagram (TAKE ct.hdr.diaLen (DROP ct.hdr.diaOff cols.hdrImage))
                 ct.hdr.nCxs ct.hdr.nApps
      = SOME ct.cxs
End

Definition wf4_def:
  wf4 (cols:columns) (ct:ctx) ⇔
    LENGTH cols.nodeTag = cols.nNodes ∧
    LENGTH cols.poolTag = cols.nPool ∧
    (cols.topoMode = 0 ⇒ cols.nodeTopo = []) ∧
    (cols.topoMode = 1 ⇒
       LENGTH cols.nodeTopo =
       SUM (GENLIST (nodeArityAt cols) cols.nNodes)) ∧
    LENGTH cols.nodeArity = arityRankN cols cols.nNodes ∧
    LENGTH cols.nodePath = pathRankN cols cols.nNodes ∧
    LENGTH cols.nodeScal =
      SUM (GENLIST (λi. scalCntR (ruleOfD cols i)) cols.nNodes) ∧
    cols.nodeRat = [] ∧

    IS_SOME (conclDir cols ct) ∧
    IS_SOME (prefDir cols ct) ∧
    LENGTH cols.poolRef =
      SUM (GENLIST (λj. poolRefCnt (getD cols.poolTag j 0)) cols.nPool) ∧
    LENGTH cols.poolNumLen =
      SUM (GENLIST (λj. poolElemCnt (getD cols.poolTag j 0)) cols.nPool) ∧
    LENGTH cols.poolDenId = LENGTH cols.poolNumLen ∧
    LENGTH cols.poolNum = SUM cols.poolNumLen ∧
    LENGTH cols.poolMisc =
      SUM (GENLIST (λj. poolMiscCnt (getD cols.poolTag j 0) (recLenP ct j))
                   cols.nPool) ∧

    EVERY (λx. x < 4294967296) cols.nodeConcl ∧
    EVERY (λx. x < 4294967296) cols.nodePref ∧
    EVERY (λx. x < 4294967296) cols.nodeScal ∧
    EVERY (λx. x < 4294967296) cols.poolRef ∧
    EVERY (λx. x < 4294967296) cols.poolNumLen ∧
    EVERY (λp. FST p < cols.nNodes ∧ SND p < 18446744073709551616)
          cols.nodeDen ∧
    cols.denDefault < 18446744073709551616
End

Definition wf5_def:
  wf5 (cols:columns) (ct:ctx) ⇔
    0 < cols.nNodes ∧
    (if cols.topoMode = 0 then
       (case rpnReplay cols of
        | NONE => F
        | SOME (rows, stk) => LENGTH stk = 1)
     else

       EVERY (λi. EVERY (λc. c < i) (getD ct.childTbl i []))
             (rangeL cols.nNodes) ∧
       (let allc = FLAT ct.childTbl in
          EVERY (λj. LENGTH (FILTER (λx. x = j) allc) = 1)
                (rangeL (cols.nNodes − 1))))
End

Definition wf6rec_def:
  wf6rec (cols:columns) (ct:ctx) (j:num) ⇔
    case oEL j cols.poolTag of
    | NONE => F
    | SOME t =>
      poolTagOK t ∧

      EVERY (λk. case refAt cols ct j k of
                 | NONE => F
                 | SOME r => r < getD ct.poolOffs j 0)
            (rangeL (poolRefCnt t)) ∧

      (if t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 then
         EVERY (λk. case refAt cols ct j k of
                    | NONE => F
                    | SOME r => isTermAt cols ct r)
               (rangeL (poolRefCnt t))
       else if t = 17 then
         (case refAt cols ct j 0 of
          | NONE => F
          | SOME r => isSimplexAt cols ct r)
       else if t = 32 then
         (EVERY (λk. case refAt cols ct j k of
                     | NONE => F
                     | SOME r => isTermAt cols ct r) (rangeL 2) ∧
          (case poolField cols ct (getD ct.poolOffs j 0) 2 of
           | NONE => F
           | SOME bb => bb ≤ 5))
       else if t = 33 then
         ((case refAt cols ct j 0 of
           | NONE => F | SOME r => isTermAt cols ct r) ∧
          (case refAt cols ct j 1 of
           | NONE => F | SOME r => isSimplexAt cols ct r) ∧
          (case refAt cols ct j 2 of
           | NONE => F | SOME r => isExtSetAt cols ct r))
       else if t = 34 ∨ t = 35 then
         EVERY (λk. case refAt cols ct j k of
                    | NONE => F
                    | SOME r => isFormulaAt cols ct r)
               (rangeL 2)
       else if t = 48 then
         ((case refAt cols ct j 0 of
           | NONE => F | SOME r => isFormulaAt cols ct r) ∧
          (case refAt cols ct j 1 of
           | NONE => F
           | SOME r => isFormulaAt cols ct r ∧
                       fwNoSphRef cols ct (SUC j) r))
       else T) ∧

      (if t = 16 then
         (case poolField cols ct (getD ct.poolOffs j 0) 0 of
          | NONE => F
          | SOME ci =>
            case oEL ci ct.cxs of
            | NONE => F
            | SOME cx =>
              let nb = (cx.nVertices + 7) DIV 8 in
              let mb = miscBaseP cols ct j in
                ¬(LENGTH cols.poolMisc < mb + 1 + nb) ∧
                EVERY (λb. b < (256:num))
                      (TAKE nb (DROP (mb + 1) cols.poolMisc)) ∧
                padOK (TAKE nb (DROP (mb + 1) cols.poolMisc)) cx.nVertices)
       else if t = 17 then
         (case refAt cols ct j 0 of
          | NONE => F
          | SOME so =>
            case pv cols ct so of
            | SOME (PSimplex sx) =>
              (let nb = (sx.complex.nVertices + 7) DIV 8 in
               let mb = miscBaseP cols ct j in
                 ¬(LENGTH cols.poolMisc < mb + nb) ∧
                 EVERY (λb. b < (256:num))
                       (TAKE nb (DROP mb cols.poolMisc)) ∧
                 padOK (TAKE nb (DROP mb cols.poolMisc))
                       sx.complex.nVertices)
            | _ => F)
       else T)
End

Definition wf6_def:
  wf6 (cols:columns) (ct:ctx) ⇔
    EVERY (wf6rec cols ct) (rangeL cols.nPool)
End

Definition wf7elem_def:
  wf7elem (cols:columns) (e:num) ⇔
    case oEL e cols.poolNumLen of
    | NONE => F
    | SOME nl =>
      case oEL e cols.poolDenId of
      | NONE => F
      | SOME did =>
        case oEL did cols.poolDenDict of
        | NONE => F
        | SOME db =>
          let base = elemNumBase cols e in
            ¬(LENGTH cols.poolNum < base + nl) ∧
            (let nb = TAKE nl (DROP base cols.poolNum) in
             let d = leN db in
             let v = leN nb in
             let m = (256:num) ** nl in
             let neg = ¬(2 * v < m) in
             let mag = if neg then m − v else v in
               EVERY (λb. b < (256:num)) nb ∧
               EVERY (λb. b < (256:num)) db ∧
               numMinimal nb ∧ denMinimal db ∧
               LENGTH db < 4294967296 ∧
               d ≠ 0 ∧
               (mag = 0 ⇒ d = 1) ∧
               (mag ≠ 0 ⇒ egcd mag d = 1))
End

Definition fuStep_def:
  fuStep (acc:bool # num) (id:num) : bool # num =
    if id < SND acc then acc
    else if id = SND acc then (FST acc, SND acc + 1)
    else (F, SND acc)
End

Definition wf7_def:
  wf7 (cols:columns) (ct:ctx) ⇔
    EVERY (wf7elem cols) (rangeL (LENGTH cols.poolNumLen)) ∧
    ALL_DISTINCT cols.poolDenDict ∧

    (let a = FOLDL fuStep (T, 0) cols.poolDenId in
       FST a ∧ SND a = LENGTH cols.poolDenDict)
End

Definition pfIs_def:
  pfIs (cols:columns) (ct:ctx) (i:num) (k:num) (p:num -> bool) ⇔
    case prefField cols ct i k of
    | NONE => F
    | SOME r => p r
End

Definition wf8node_def:
  wf8node (cols:columns) (ct:ctx) (i:num) ⇔
    case tagOf cols i of
    | NONE => F
    | SOME (r, v) =>

      (case conclRef cols ct i of
       | NONE => F
       | SOME cr => isJudgAt cols ct cr) ∧

      EVERY (λk. case childOrd ct i k of
                 | NONE => F
                 | SOME c => c < i)
            (rangeL (nodeArityAt cols i)) ∧

      (if r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 5 ∨ r = 25 then
         pfIs cols ct i 0 (isFormulaAt cols ct)
       else if r = 7 then
         (pfIs cols ct i 0 (isTermAt cols ct) ∧
          pfIs cols ct i 1 (isTermAt cols ct) ∧
          pfIs cols ct i 2 (isFormulaAt cols ct))
       else if r = 8 ∨ r = 9 then
         (pfIs cols ct i 0 (isTermAt cols ct) ∧
          pfIs cols ct i 1 (isSimplexAt cols ct) ∧
          pfIs cols ct i 2 (isExtSetAt cols ct))
       else if r = 10 ∨ r = 12 ∨ r = 14 ∨ r = 24 ∨ r = 26 then
         (pfIs cols ct i 0 (isTermAt cols ct) ∧
          pfIs cols ct i 1 (isTermAt cols ct))
       else if r = 11 then
         (pfIs cols ct i 0 (isTermAt cols ct) ∧
          pfIs cols ct i 1 (isSimplexAt cols ct) ∧
          pfIs cols ct i 2 (isExtSetAt cols ct) ∧
          pfIs cols ct i 3 (isTermAt cols ct) ∧
          pfIs cols ct i 4 (isFormulaAt cols ct))
       else if r = 23 then
         pfIs cols ct i 0 (isTermAt cols ct)
       else T) ∧

      (r = 10 ⇒ (case scalField cols ct i 0 of
                 | NONE => F
                 | SOME bb => bb ≤ 4)) ∧
      (r = 7 ⇒ IS_SOME (scalField cols ct i 0)) ∧
      (r = 11 ⇒ IS_SOME (scalField cols ct i 0)) ∧
      (r = 26 ⇒ (case scalField cols ct i 0 of
                 | NONE => F
                 | SOME th =>
                     th = 4294967295 ∨ isConstAt cols ct th)) ∧

      (hasPathR r ⇒
         (case pathOf cols ct i of
          | NONE => F
          | SOME (stps, ifc) =>
              EVERY (λs. s ≤ (1:num)) stps ∧
              LENGTH stps < 4294967296 ∧
              (r = 6 ⇒ ifc = []) ∧
              (r = 25 ⇒ EVERY (λw. w < 4294967296) ifc ∧
                        LENGTH ifc < 4294967296)))
End

Definition wf8_def:
  wf8 (cols:columns) (ct:ctx) ⇔
    EVERY (wf8node cols ct) (rangeL cols.nNodes)
End

Definition wf9_def:
  wf9 (cols:columns) (ct:ctx) ⇔
    0 < cols.nNodes ∧

    (case conclRef cols ct (cols.nNodes − 1) of
     | NONE => F
     | SOME cr =>
       case ALOOKUP ct.poolIdx cr of
       | NONE => F
       | SOME j0 =>
         getD cols.poolTag j0 0 = (48:num) ∧
         (case refAt cols ct j0 0 of
          | NONE => F
          | SOME preR =>
            case ALOOKUP ct.poolIdx preR of
            | NONE => F
            | SOME j1 =>
              getD cols.poolTag j1 0 = (34:num) ∧
              (case refAt cols ct j1 1 of
               | NONE => F
               | SOME rr => poolTagAt cols ct rr = SOME 38))) ∧
    (ct.hdr.thetaRef = 4294967295 ∨
     isConstAt cols ct ct.hdr.thetaRef)
End

Definition escPre_def:
  escPre (cols:columns) (ct:ctx) (cdir:(bool # num) list) (i:num) ⇔
    ruleOfD cols i = (4:num) ∧
    (case childConcl ct cdir i of
     | NONE => F
     | SOME cref => IS_SOME (andeDerive cols ct (varOfD cols i) cref))
End

Definition escPre2_def:
  escPre2 (cols:columns) (ct:ctx) (cdir:(bool # num) list) (i:num) ⇔
    (ruleOfD cols i = (4:num) ∧
     (case childConcl ct cdir i of
      | NONE => F
      | SOME cref => IS_SOME (andeOther cols ct (varOfD cols i) cref))) ∨
    (ruleOfD cols i = (9:num) ∧
     (case childConcl ct cdir i of
      | NONE => F
      | SOME cref => IS_SOME (convTriple cols ct cref)))
End

Definition wf10_def:
  wf10 (cols:columns) (ct:ctx) ⇔
    sortedLt cols.nodeEsc ∧
    sortedLt cols.nodeEsc2 ∧
    EVERY (λi. i < cols.nNodes) cols.nodeEsc ∧
    EVERY (λi. i < cols.nNodes) cols.nodeEsc2 ∧
    (case conclDir cols ct of
     | NONE => F
     | SOME cdir =>
         EVERY (escPre cols ct cdir) cols.nodeEsc ∧
         EVERY (escPre2 cols ct cdir) cols.nodeEsc2)
End

Definition wf11_def:
  wf11 (cols:columns) (ct:ctx) ⇔
    sortedLt (MAP FST cols.nodeDen) ∧
    EVERY (λp. ruleOfD cols (FST p) = 14 ∨ ruleOfD cols (FST p) = 26)
          cols.nodeDen
End

Definition wf12_def:
  wf12 (cols:columns) (ct:ctx) ⇔
    cols.blockSize = 0 ∨ cols.blockSize = 65536
End

Definition wfColumns_def:
  wfColumns (cols:columns) (ct:ctx) ⇔
    wf1 cols ct ∧ wf2 cols ct ∧ wf3 cols ct ∧ wf4 cols ct ∧
    wf5 cols ct ∧ wf6 cols ct ∧ wf7 cols ct ∧ wf8 cols ct ∧
    wf9 cols ct ∧ wf10 cols ct ∧ wf11 cols ct ∧ wf12 cols ct
End

Definition nodeReconF_def:
  nodeReconF (cols:columns) (ct:ctx) (0:num) (i:num) =
    (NONE : certpf option) ∧
  nodeReconF cols ct (SUC f) i =
    case tagOf cols i of
    | NONE => NONE
    | SOME (r, v) =>
    case conclRef cols ct i of
    | NONE => NONE
    | SOME cj =>
    case pv cols ct cj of
    | SOME (PJudg prew postw) =>
      (let sq = judgSeq FTt prew postw in
       if r = (0:num) then SOME (CertPf sq CnAx)
       else if r = 1 then
         (case childOrd ct i 0 of NONE => NONE | SOME k =>
          case nodeReconF cols ct f k of NONE => NONE | SOME p =>
          case prefField cols ct i 0 of NONE => NONE | SOME ex =>
          case pv cols ct ex of
          | SOME (PFormula exw) =>
              SOME (CertPf sq (CnWeaken p (expandSph FTt exw)))
          | _ => NONE)
       else if r = 2 then
         (case childOrd ct i 0 of NONE => NONE | SOME kl =>
          case childOrd ct i 1 of NONE => NONE | SOME kr =>
          case nodeReconF cols ct f kl of NONE => NONE | SOME lp =>
          case nodeReconF cols ct f kr of NONE => NONE | SOME rp =>
          case prefField cols ct i 0 of NONE => NONE | SOME cf0 =>
          case pv cols ct cf0 of
          | SOME (PFormula cfw) =>
              SOME (CertPf sq (CnCut (expandSph FTt cfw) lp rp))
          | _ => NONE)
       else if r = 3 then
         (case childOrd ct i 0 of NONE => NONE | SOME kl =>
          case childOrd ct i 1 of NONE => NONE | SOME kr =>
          case nodeReconF cols ct f kl of NONE => NONE | SOME lp =>
          case nodeReconF cols ct f kr of NONE => NONE | SOME rp =>
            SOME (CertPf sq (CnAndI lp rp)))
       else if r = 4 ∨ r = 5 then
         (case childOrd ct i 0 of NONE => NONE | SOME k =>
          case nodeReconF cols ct f k of NONE => NONE | SOME p =>
          case prefField cols ct i 0 of NONE => NONE | SOME ot =>
          case pv cols ct ot of
          | SOME (PFormula otw) =>
            (let ow = expandSph FTt otw in
               SOME (CertPf sq
                       (if r = 4 then
                          (if v = 0 then CnAndEL p ow else CnAndER p ow)
                        else
                          (if v = 0 then CnOrIL p ow else CnOrIR p ow))))
          | _ => NONE)
       else if r = 6 then
         (case childOrd ct i 0 of NONE => NONE | SOME kl =>
          case childOrd ct i 1 of NONE => NONE | SOME kr =>
          case nodeReconF cols ct f kl of NONE => NONE | SOME lp =>
          case nodeReconF cols ct f kr of NONE => NONE | SOME rp =>
          case pathOf cols ct i of
          | NONE => NONE
          | SOME (stps, ifc) =>
              SOME (CertPf sq (CnOrE lp rp (stepsToPath stps))))
       else if r = 7 then
         (case childOrd ct i 0 of NONE => NONE | SOME ke =>
          case childOrd ct i 1 of NONE => NONE | SOME kb =>
          case nodeReconF cols ct f ke of NONE => NONE | SOME ep =>
          case nodeReconF cols ct f kb of NONE => NONE | SOME bp =>
          case scalField cols ct i 0 of NONE => NONE | SOME w =>
          case prefField cols ct i 0 of NONE => NONE | SOME rt =>
          case prefField cols ct i 1 of NONE => NONE | SOME ru =>
          case prefField cols ct i 2 of NONE => NONE | SOME rb =>
          case pv cols ct rt of
          | SOME (PTerm tT) =>
            (case pv cols ct ru of
             | SOME (PTerm tU) =>
               (case pv cols ct rb of
                | SOME (PFormula bfw) =>
                    SOME (CertPf sq
                            (CnEqElim ep bp w tT tU (expandSph FTt bfw)))
                | _ => NONE)
             | _ => NONE)
          | _ => NONE)
       else if r = 8 ∨ r = 9 then
         (case childOrd ct i 0 of NONE => NONE | SOME k =>
          case nodeReconF cols ct f k of NONE => NONE | SOME p =>
          case prefField cols ct i 0 of NONE => NONE | SOME rt =>
          case prefField cols ct i 1 of NONE => NONE | SOME rs =>
          case prefField cols ct i 2 of NONE => NONE | SOME re =>
          case pv cols ct rt of
          | SOME (PTerm tt) =>
            (case pv cols ct rs of
             | SOME (PSimplex sx) =>
               (case pv cols ct re of
                | SOME (PExtSet es) =>
                    SOME (CertPf sq
                            (if r = 8 then CnConvIntro p tt sx es
                             else CnConvElim p tt sx es))
                | _ => NONE)
             | _ => NONE)
          | _ => NONE)
       else if r = 10 then
         (case childOrd ct i 0 of NONE => NONE | SOME k =>
          case nodeReconF cols ct f k of NONE => NONE | SOME p =>
          case prefField cols ct i 0 of NONE => NONE | SOME rl =>
          case prefField cols ct i 1 of NONE => NONE | SOME rr =>
          case scalField cols ct i 0 of NONE => NONE | SOME bb =>
          case bowtieOf bb of NONE => NONE | SOME b =>
          case pv cols ct rl of
          | SOME (PTerm tl) =>
            (case pv cols ct rr of
             | SOME (PTerm tr) =>
                 SOME (CertPf sq
                         (if v = 0 then CnArithFold p tl tr b
                          else CnArithUnfold p tl tr b))
             | _ => NONE)
          | _ => NONE)
       else if r = 11 then
         (case childOrd ct i 0 of NONE => NONE | SOME k =>
          case nodeReconF cols ct f k of NONE => NONE | SOME p =>
          case prefField cols ct i 0 of NONE => NONE | SOME rx =>
          case prefField cols ct i 1 of NONE => NONE | SOME rs =>
          case prefField cols ct i 2 of NONE => NONE | SOME re =>
          case prefField cols ct i 3 of NONE => NONE | SOME rp0 =>
          case prefField cols ct i 4 of NONE => NONE | SOME rd =>
          case scalField cols ct i 0 of NONE => NONE | SOME deg =>
          case pv cols ct rx of
          | SOME (PTerm tX) =>
            (case pv cols ct rs of
             | SOME (PSimplex sx) =>
               (case pv cols ct re of
                | SOME (PExtSet es) =>
                  (case pv cols ct rp0 of
                   | SOME (PTerm poly) =>
                     (case pv cols ct rd of
                      | SOME (PFormula pdw) =>
                          SOME (CertPf sq
                                  (CnBernCone p tX sx es deg poly
                                              (expandSph FTt pdw)))
                      | _ => NONE)
                   | _ => NONE)
                | _ => NONE)
             | _ => NONE)
          | _ => NONE)
       else if r = 12 then
         (case prefField cols ct i 0 of NONE => NONE | SOME rl =>
          case prefField cols ct i 1 of NONE => NONE | SOME rr =>
          case pv cols ct rl of
          | SOME (PTerm tl) =>
            (case pv cols ct rr of
             | SOME (PTerm tr) => SOME (CertPf sq (CnNorm tl tr))
             | _ => NONE)
          | _ => NONE)
       else if r = 14 then
         (case prefField cols ct i 0 of NONE => NONE | SOME rc =>
          case prefField cols ct i 1 of NONE => NONE | SOME ro =>
          case pv cols ct rc of
          | SOME (PTerm ccT) =>
            (case pv cols ct ro of
             | SOME (PTerm coT) =>
                 SOME (CertPf sq (CnFarkas ccT coT (denOf cols i)))
             | _ => NONE)
          | _ => NONE)
       else if r = 23 then
         (case prefField cols ct i 0 of NONE => NONE | SOME rt =>
          case pv cols ct rt of
          | SOME (PTerm tt) => SOME (CertPf sq (CnEqRefl tt))
          | _ => NONE)
       else if r = 24 then
         (case childOrd ct i 0 of NONE => NONE | SOME k =>
          case nodeReconF cols ct f k of NONE => NONE | SOME p =>
          case prefField cols ct i 0 of NONE => NONE | SOME rt =>
          case prefField cols ct i 1 of NONE => NONE | SOME ru =>
          case pv cols ct rt of
          | SOME (PTerm tT) =>
            (case pv cols ct ru of
             | SOME (PTerm tU) => SOME (CertPf sq (CnEqSym p tT tU))
             | _ => NONE)
          | _ => NONE)
       else if r = 25 then
         (case childOrd ct i 0 of NONE => NONE | SOME ks =>
          case childOrd ct i 1 of NONE => NONE | SOME kc =>
          case nodeReconF cols ct f ks of NONE => NONE | SOME sp =>
          case nodeReconF cols ct f kc of NONE => NONE | SOME cp =>
          case prefField cols ct i 0 of NONE => NONE | SOME rc =>
          case pathOf cols ct i of
          | NONE => NONE
          | SOME (stps, ifc) =>
            (case pv cols ct rc of
             | SOME (PFormula ctw) =>
                 SOME (CertPf sq
                         (CnPromise sp cp (expandSph FTt ctw)
                                    (stepsToPath stps) ifc))
             | _ => NONE)
          )
       else if r = 26 then
         (case arityOf cols ct i of
          | NONE => NONE
          | SOME nc =>
            case optSeq
                   (MAP (λk. case childOrd ct i k of
                             | NONE => NONE
                             | SOME c => nodeReconF cols ct f c)
                        (rangeL nc)) of
            | NONE => NONE
            | SOME comps =>
              case prefField cols ct i 0 of NONE => NONE | SOME rc =>
              case prefField cols ct i 1 of NONE => NONE | SOME ro =>
              case scalField cols ct i 0 of NONE => NONE | SOME th =>
              case pv cols ct rc of
              | SOME (PTerm ccT) =>
                (case pv cols ct ro of
                 | SOME (PTerm coT) =>
                   (if th = (4294967295:num) then
                      SOME (CertPf sq
                              (CnSyzygy comps ccT coT (denOf cols i) NONE))
                    else
                      case pv cols ct th of
                      | SOME (PTerm (TmConst q)) =>
                          SOME (CertPf sq
                                  (CnSyzygy comps ccT coT (denOf cols i)
                                            (SOME q)))
                      | _ => NONE)
                 | _ => NONE)
              | _ => NONE)
       else NONE)
    | _ => NONE
Termination
  WF_REL_TAC ‘measure (λ(cols, ct, fuel, i). fuel)’ >> rw[]
End

Definition nodeCorr_def:
  nodeCorr (cols:columns) (ct:ctx) (i:num) (pf:certpf) ⇔
    nodeReconF cols ct (SUC i) i = SOME pf
End

Theorem nodeCorr_unique:
  nodeCorr cols ct i pf1 ∧ nodeCorr cols ct i pf2 ⇒ pf1 = pf2
Proof
  rw[nodeCorr_def] >> gvs[]
QED

Theorem nodeCorr_exists_iff:
  (∃pf. nodeCorr cols ct i pf) ⇔ IS_SOME (nodeReconF cols ct (SUC i) i)
Proof
  rw[nodeCorr_def, optionTheory.IS_SOME_EXISTS]
QED

Theorem poolFold_offs_length:
  ∀n cols cxs st.
    FOLDL (poolStep cols cxs) (SOME pInit) (rangeL n) = SOME st ⇒
    LENGTH st.poffs = n ∧ LENGTH st.refb = n + 1 ∧ LENGTH st.elemb = n + 1
Proof
  Induct >> rw[rangeL_def, GSYM listTheory.SNOC_APPEND, listTheory.FOLDL_SNOC]
  >> gvs[pInit_def]
  >> Cases_on ‘FOLDL (poolStep cols cxs) (SOME pInit) (rangeL n)’
  >> gvs[poolStep_def]
  >> gvs[AllCaseEqs()]
  >> res_tac >> simp[]
QED

Theorem nodeFold_offs_length:
  ∀n cols start st.
    FOLDL (nodeStep cols) (SOME (nInit start)) (rangeL n) = SOME st ⇒
    LENGTH st.noffs = n ∧ LENGTH st.scalb = n + 1
Proof
  Induct >> rw[rangeL_def, GSYM listTheory.SNOC_APPEND, listTheory.FOLDL_SNOC]
  >> gvs[nInit_def]
  >> Cases_on ‘FOLDL (nodeStep cols) (SOME (nInit start)) (rangeL n)’
  >> gvs[nodeStep_def]
  >> gvs[AllCaseEqs()]
  >> res_tac >> simp[]
QED

Theorem mkCtx_poolOffs_length:
  mkCtx cols = SOME ct ⇒ LENGTH ct.poolOffs = cols.nPool + 1
Proof
  rw[mkCtx_def] >> gvs[AllCaseEqs(), poolFold_def]
  >> imp_res_tac poolFold_offs_length >> simp[]
QED

Theorem mkCtx_nodeOffs_length:
  mkCtx cols = SOME ct ⇒ LENGTH ct.nodeOffs = cols.nNodes + 1
Proof
  rw[mkCtx_def] >> gvs[AllCaseEqs(), nodeFold_def]
  >> imp_res_tac nodeFold_offs_length >> simp[]
QED

Theorem mkCtx_prefBase_length:
  mkCtx cols = SOME ct ⇒ LENGTH ct.prefBase = cols.nNodes + 1
Proof
  rw[mkCtx_def] >> gvs[AllCaseEqs(), prefBaseOf_def]
QED

Definition u32le_def:
  u32le (n:num) : num list =
    [n MOD 256; (n DIV 256) MOD 256; (n DIV 65536) MOD 256;
     (n DIV 16777216) MOD 256]
End

Definition u64le_def:
  u64le (n:num) : num list =
    u32le (n MOD 4294967296) ++ u32le (n DIV 4294967296)
End

Definition demoImg_def:
  demoImg : num list =
    bernMagic ++ u32le 1 ++ u32le 0 ++
    u64le 128 ++ u64le 0 ++
    u64le 128 ++ u64le 0 ++
    u64le 128 ++ u64le 8 ++
    u64le 136 ++ u64le 36 ++
    u32le 0 ++ u32le 0 ++
    u32le 1 ++ u32le 0 ++
    u64le 28 ++
    u32le 4294967295 ++
    REPLICATE 20 0 ++
    u32le 0 ++ u32le 0
End

Definition demoCols_def:
  demoCols : columns =
    <| hdrImage := demoImg ; topoMode := 0 ; denDefault := 731 ;
       nNodes := 1 ; nPool := 4 ; blockSize := 0 ;
       nodeTag := [0] ; nodeArity := [] ; nodeTopo := [] ;
       nodeConcl := [11] ; nodePref := [] ; nodeScal := [] ;
       nodeDen := [] ; nodePath := [] ; nodeRat := [] ;
       nodeEsc := [] ; nodeEsc2 := [] ;
       poolTag := [36; 38; 34; 48] ;
       poolRef := [0; 1; 2; 0] ;
       poolNumLen := [] ; poolDenId := [] ; poolDenDict := [] ;
       poolNum := [] ; poolMisc := [] |>
End

Theorem demo_mkCtx:
  IS_SOME (mkCtx demoCols)
Proof
  EVAL_TAC
QED

Theorem demo_wfColumns:
  wfColumns demoCols (THE (mkCtx demoCols))
Proof
  EVAL_TAC
QED

Theorem demo_nodeCorr:
  nodeCorr demoCols (THE (mkCtx demoCols)) 0
    (CertPf <| pre := FAnd FTt FTt ; post := FTt |> CnAx)
Proof
  EVAL_TAC
QED

Theorem demo_mut_concl:
  mkCtx (demoCols with nodeConcl := [12]) ≠ NONE ∧
  ¬ wfColumns (demoCols with nodeConcl := [12])
              (THE (mkCtx (demoCols with nodeConcl := [12])))
Proof
  EVAL_TAC
QED

Theorem demo_mut_sph:
  mkCtx (demoCols with poolRef := [0; 1; 2; 1]) ≠ NONE ∧
  ¬ wfColumns (demoCols with poolRef := [0; 1; 2; 1])
              (THE (mkCtx (demoCols with poolRef := [0; 1; 2; 1])))
Proof
  EVAL_TAC
QED

Theorem demo_mut_root:
  mkCtx (demoCols with poolRef := [0; 1; 0; 0]) ≠ NONE ∧
  ¬ wfColumns (demoCols with poolRef := [0; 1; 0; 0])
              (THE (mkCtx (demoCols with poolRef := [0; 1; 0; 0])))
Proof
  EVAL_TAC
QED

Theorem demo_mut_esc:
  mkCtx (demoCols with nodeEsc := [0]) ≠ NONE ∧
  ¬ wfColumns (demoCols with nodeEsc := [0])
              (THE (mkCtx (demoCols with nodeEsc := [0])))
Proof
  EVAL_TAC
QED

Theorem demo_mut_block:
  mkCtx (demoCols with blockSize := 7) ≠ NONE ∧
  ¬ wfColumns (demoCols with blockSize := 7)
              (THE (mkCtx (demoCols with blockSize := 7)))
Proof
  EVAL_TAC
QED

Theorem optSeq_MAP_mono:
  ∀l (f:'a -> 'b option) g ys.
    optSeq (MAP f l) = SOME ys ∧
    (∀x y. MEM x l ∧ f x = SOME y ⇒ g x = SOME y) ⇒
    optSeq (MAP g l) = SOME ys
Proof
  Induct >- rw[optSeq_def]
  >> rpt gen_tac >> strip_tac >> gvs[]
  >> Cases_on ‘f h’ >> gvs[optSeq_def, AllCaseEqs()]
  >> ‘g h = SOME x’ by simp[]
  >> rename [‘optSeq (MAP f l) = SOME vs’]
  >> ‘optSeq (MAP g l) = SOME vs’
       by (first_x_assum irule >> simp[] >> metis_tac[])
  >> simp[optSeq_def]
QED

Theorem nodeReconF_fuel_mono:
  ∀f cols ct i pf f2.
    nodeReconF cols ct f i = SOME pf ∧ f ≤ f2 ⇒
    nodeReconF cols ct f2 i = SOME pf
Proof
  Induct >- simp[nodeReconF_def]
  >> rpt gen_tac >> strip_tac
  >> Cases_on ‘f2’ >- gvs[]
  >> rename [‘nodeReconF _ _ (SUC f) _ = _’, ‘SUC f ≤ SUC f2’]
  >> ‘f ≤ f2’ by decide_tac
  >> qpat_x_assum ‘nodeReconF _ _ (SUC f) _ = _’ mp_tac
  >> simp[nodeReconF_def]
  >> simp[AllCaseEqs(), PULL_EXISTS]
  >> rpt strip_tac >> gvs[]
  >> res_tac >> gvs[]
  >> TRY (drule_at (Pos (el 1)) optSeq_MAP_mono
          >> disch_then (qspec_then
               ‘(λk. case childOrd ct i k of
                     | NONE => NONE
                     | SOME c => nodeReconF cols ct f2 c)’ mp_tac)
          >> impl_tac
          >- (rw[AllCaseEqs()] >> res_tac >> simp[])
          >> strip_tac >> simp[])
  >> metis_tac[]
QED
