(*
  The succinct-profile column relations and the frozen accessor kit:
  prefix-sum offset tables, per-node field accessors, and the elision
  partition engines (conclStep/prefStep) that decide which
  concludes/pref fields are derivable and therefore elided on the
  wire. The reader and the accessors share these engines, so they
  cannot disagree on the partition's inputs.
*)
Theory qtsl_cols
Ancestors
  rat integer mlstring mllist qtsl_dyadic qtsl_qarith qtsl_catalogue
  qtsl_cert
Libs
  preamble

Datatype:
  columns = <|

    hdrImage    : num list ;
    topoMode    : num ;
    denDefault  : num ;
    nNodes      : num ;
    nPool       : num ;
    blockSize   : num ;

    nodeTag     : num list ;
    nodeArity   : num list ;
    nodeTopo    : num list ;
    nodeConcl   : num list ;
    nodePref    : num list ;
    nodeScal    : num list ;
    nodeDen     : (num # num) list ;
    nodePath    : (num list # num list) list ;
    nodeRat     : num list ;
    nodeEsc     : num list ;
    nodeEsc2    : num list ;

    poolTag     : num list ;
    poolRef     : num list ;
    poolNumLen  : num list ;
    poolDenId   : num list ;
    poolDenDict : (num list) list ;
    poolNum     : num list ;
    poolMisc    : num list
  |>
End

Datatype:
  ctx = <|
    hdr       : bhdr ;
    ws        : tensortype list ;
    cxs       : simpc list ;
    poolOffs  : num list ;
    nodeOffs  : num list ;
    poolIdx   : (num # num) list ;
    nodeIdx   : (num # num) list ;
    judgIdx   : ((num # num) # num) list ;

    childTbl  : (num list) list ;
    prefBase  : num list ;
    scalBase  : num list ;
    refBase   : num list ;
    elemBase  : num list
  |>
End

Definition sortedLt_def:
  sortedLt ([]:num list) = T ∧
  sortedLt [x] = T ∧
  sortedLt (x::y::xs) = (x < y ∧ sortedLt (y::xs))
End

Definition escContains_def:
  escContains (es:num list) (i:num) = MEM i es
End

Definition escRank_def:
  escRank (es:num list) (i:num) = LENGTH (FILTER (λe. e < i) es)
End

Theorem sortedLt_every_lt:
  ∀x xs. sortedLt (x::xs) ⇒ EVERY (λe. x < e) xs
Proof
  Induct_on ‘xs’ >> rw[sortedLt_def]
  >> Cases_on ‘xs’ >> gvs[sortedLt_def]
  >> irule listTheory.EVERY_MONOTONIC
  >> first_x_assum (irule_at Any) >> simp[]
QED

Theorem sortedLt_all_distinct:
  ∀es. sortedLt es ⇒ ALL_DISTINCT es
Proof
  Induct >> rw[sortedLt_def]
  >> Cases_on ‘es’ >> gvs[sortedLt_def]
  >> drule sortedLt_every_lt >> rw[]
  >> gvs[listTheory.EVERY_MEM] >> strip_tac
  >- (first_x_assum drule >> simp[])
  >> res_tac >> simp[]
QED

Theorem sortedLt_tail:
  ∀x xs. sortedLt (x::xs) ⇒ sortedLt xs
Proof
  Cases_on ‘xs’ >> rw[sortedLt_def]
QED

Theorem escRank_select:
  ∀es i. sortedLt es ∧ escContains es i ⇒
         escRank es i < LENGTH es ∧ EL (escRank es i) es = i
Proof
  Induct >- rw[escContains_def]
  >> rpt gen_tac >> strip_tac
  >> rename [‘sortedLt (h::es)’]
  >> ‘sortedLt es’ by metis_tac[sortedLt_tail]
  >> drule sortedLt_every_lt >> strip_tac
  >> gvs[escContains_def]
  >- (‘FILTER (λe. e < h) (h::es) = []’
        by (simp[listTheory.FILTER_EQ_NIL] >> gvs[listTheory.EVERY_MEM]
            >> rpt strip_tac >> res_tac >> decide_tac)
      >> simp[escRank_def])
  >> ‘h < i’ by gvs[listTheory.EVERY_MEM]
  >> ‘escRank (h::es) i = SUC (escRank es i)’ by simp[escRank_def]
  >> first_x_assum (qspec_then ‘i’ mp_tac)
  >> simp[escContains_def]
QED

Definition tagDec_def:
  tagDec (s:num) : (num # num) option =
    if s ≤ 12 ∨ s = 14 ∨ (23 ≤ s ∧ s ≤ 26) then SOME (s, 0)
    else if s = 27 then SOME (4, 1)
    else if s = 28 then SOME (5, 1)
    else if s = 29 then SOME (10, 1)
    else NONE
End

Definition tagOf_def:
  tagOf (cols:columns) (i:num) : (num # num) option =
    case oEL i cols.nodeTag of
    | NONE => NONE
    | SOME s => tagDec s
End

Definition tagDecD_def:
  tagDecD (s:num) : num # num =
    case tagDec s of NONE => (999, 0) | SOME p => p
End

Definition ruleOfD_def:
  ruleOfD (cols:columns) (i:num) : num = FST (tagDecD (getD cols.nodeTag i 999))
End

Definition varOfD_def:
  varOfD (cols:columns) (i:num) : num = SND (tagDecD (getD cols.nodeTag i 999))
End

Definition isTermTag_def:
  isTermTag (t:num) = (1 ≤ t ∧ t ≤ 7)
End

Definition isFormulaTag_def:
  isFormulaTag (t:num) = (32 ≤ t ∧ t ≤ 38)
End

Definition poolTagOK_def:
  poolTagOK (t:num) =
    (isTermTag t ∨ t = 16 ∨ t = 17 ∨ isFormulaTag t ∨ t = 48)
End

Definition poolRefCnt_def:
  poolRefCnt (t:num) : num =
    if t = 3 ∨ t = 4 ∨ t = 5 then 2
    else if t = 6 ∨ t = 7 ∨ t = 17 then 1
    else if t = 32 then 2
    else if t = 33 then 3
    else if t = 34 ∨ t = 35 then 2
    else if t = 48 then 2
    else 0
End

Definition poolElemCnt_def:
  poolElemCnt (t:num) : num = if t = 2 then 1 else 0
End

Definition poolMiscCnt_def:
  poolMiscCnt (t:num) (len:num) : num =
    if t = 1 ∨ t = 7 ∨ t = 32 then 1
    else if t = 16 then 1 + (len − 5)
    else if t = 17 then len − 5
    else 0
End

Definition ruleArity_def:
  ruleArity (r:num) : num =
    if r = 0 ∨ r = 12 ∨ r = 14 ∨ r = 23 then 0
    else if r = 1 ∨ r = 4 ∨ r = 5 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 24
      then 1
    else if r = 2 ∨ r = 3 ∨ r = 6 ∨ r = 7 ∨ r = 25 then 2
    else 0
End

Definition prefCntR_def:
  prefCntR (r:num) : num =
    if r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 5 ∨ r = 23 ∨ r = 25 then 1
    else if r = 10 ∨ r = 12 ∨ r = 14 ∨ r = 24 ∨ r = 26 then 2
    else if r = 7 ∨ r = 8 ∨ r = 9 then 3
    else if r = 11 then 5
    else 0
End

Definition scalCntR_def:
  scalCntR (r:num) : num =
    if r = 7 ∨ r = 10 ∨ r = 11 ∨ r = 26 then 1 else 0
End

Definition hasPathR_def:
  hasPathR (r:num) = (r = 6 ∨ r = 25)
End

Definition hasArityR_def:
  hasArityR (r:num) = (r = 15 ∨ r = 26)
End

Definition nodeLenR_def:
  nodeLenR (r:num) (stps:num list) (ifc:num list) (ncomp:num) : num =
    if r = 0 then 8
    else if r = 1 then 20
    else if r = 2 then 28
    else if r = 3 then 24
    else if r = 4 ∨ r = 5 then 20
    else if r = 6 then 28 + LENGTH stps
    else if r = 7 then 40
    else if r = 8 ∨ r = 9 then 28
    else if r = 10 then 28
    else if r = 11 then 40
    else if r = 12 then 16
    else if r = 14 then 24
    else if r = 23 then 12
    else if r = 24 then 24
    else if r = 25 then 36 + LENGTH stps + 4 * LENGTH ifc
    else if r = 26 then 32 + 8 * ncomp
    else 0
End

Definition pathRankN_def:
  pathRankN (cols:columns) (i:num) : num =
    LENGTH (FILTER (λj. hasPathR (ruleOfD cols j)) (rangeL i))
End

Definition arityRankN_def:
  arityRankN (cols:columns) (i:num) : num =
    LENGTH (FILTER (λj. hasArityR (ruleOfD cols j)) (rangeL i))
End

Definition recLenP_def:
  recLenP (ct:ctx) (j:num) : num =
    getD ct.poolOffs (j + 1) 0 − getD ct.poolOffs j 0
End

Definition miscBaseP_def:
  miscBaseP (cols:columns) (ct:ctx) (j:num) : num =
    SUM (GENLIST (λk. poolMiscCnt (getD cols.poolTag k 0) (recLenP ct k)) j)
End

Definition elemNumBase_def:
  elemNumBase (cols:columns) (e:num) : num =
    SUM (GENLIST (λx. getD cols.poolNumLen x 0) e)
End

Definition childOrd_def:
  childOrd (ct:ctx) (i:num) (k:num) : num option =
    case oEL i ct.childTbl of
    | NONE => NONE
    | SOME l => oEL k l
End

Definition arityOf_def:
  arityOf (cols:columns) (ct:ctx) (i:num) : num option =
    case tagOf cols i of
    | NONE => NONE
    | SOME (r, v) =>
        if hasArityR r then oEL (arityRankN cols i) cols.nodeArity else NONE
End

Definition nodeArityAt_def:
  nodeArityAt (cols:columns) (i:num) : num =
    let r = ruleOfD cols i in
      if hasArityR r then getD cols.nodeArity (arityRankN cols i) 0
      else ruleArity r
End

Definition scalField_def:
  scalField (cols:columns) (ct:ctx) (i:num) (k:num) : num option =
    case tagOf cols i of
    | NONE => NONE
    | SOME (r, v) =>
        if k < scalCntR r then oEL (getD ct.scalBase i 0 + k) cols.nodeScal
        else NONE
End

Definition pathOf_def:
  pathOf (cols:columns) (ct:ctx) (i:num) : (num list # num list) option =
    case tagOf cols i of
    | NONE => NONE
    | SOME (r, v) =>
        if hasPathR r then oEL (pathRankN cols i) cols.nodePath else NONE
End

Definition denOf_def:
  denOf (cols:columns) (i:num) : num =
    case ALOOKUP cols.nodeDen i of
    | SOME v => v
    | NONE => cols.denDefault
End

Definition poolTagAt_def:
  poolTagAt (cols:columns) (ct:ctx) (off:num) : num option =
    case ALOOKUP ct.poolIdx off of
    | NONE => NONE
    | SOME j => oEL j cols.poolTag
End

Definition refAt_def:
  refAt (cols:columns) (ct:ctx) (j:num) (k:num) : num option =
    oEL (getD ct.refBase j 0 + k) cols.poolRef
End

Definition poolField_def:
  poolField (cols:columns) (ct:ctx) (off:num) (k:num) : num option =
    case ALOOKUP ct.poolIdx off of
    | NONE => NONE
    | SOME j =>
      case oEL j cols.poolTag of
      | NONE => NONE
      | SOME t =>
          if k < poolRefCnt t then refAt cols ct j k
          else if k < poolRefCnt t + poolMiscCnt t (recLenP ct j)
          then oEL (miscBaseP cols ct j + (k − poolRefCnt t)) cols.poolMisc
          else NONE
End

Definition ratOfElem_def:
  ratOfElem (cols:columns) (e:num) : rat option =
    case oEL e cols.poolNumLen of NONE => NONE | SOME nl =>
    case oEL e cols.poolDenId of NONE => NONE | SOME did =>
    case oEL did cols.poolDenDict of NONE => NONE | SOME db =>
    let base = elemNumBase cols e in
    if LENGTH cols.poolNum < base + nl then NONE else
    let nb = TAKE nl (DROP base cols.poolNum) in
    if ¬ EVERY (λb. b < (256:num)) nb then NONE else
    let d = leN db in
    let v = leN nb in
    let m = (256:num) ** nl in
    let neg = ¬(2 * v < m) in
    let mag = if neg then m − v else v in
      if d = 0 then NONE
      else SOME ((if neg then -(&mag / &d) else (&mag / &d)) : rat)
End

Definition ratAt_def:
  ratAt (cols:columns) (ct:ctx) (off:num) (k:num) : rat option =
    case ALOOKUP ct.poolIdx off of
    | NONE => NONE
    | SOME j =>
      case oEL j cols.poolTag of
      | NONE => NONE
      | SOME t =>
          if k < poolElemCnt t then ratOfElem cols (getD ct.elemBase j 0 + k)
          else NONE
End

Definition pvF_def:
  pvF (cols:columns) (ct:ctx) (0:num) (off:num) = (NONE : poolobj option) ∧
  pvF cols ct (SUC f) off =
    case ALOOKUP ct.poolIdx off of
    | NONE => NONE
    | SOME j =>
      case oEL j cols.poolTag of
      | NONE => NONE
      | SOME t =>
        if t = (1:num) then
          (case poolField cols ct off 0 of
           | NONE => NONE
           | SOME w => SOME (PTerm (TmVar w)))
        else if t = 2 then
          (case ratAt cols ct off 0 of
           | NONE => NONE
           | SOME q => SOME (PTerm (TmConst q)))
        else if t = 3 ∨ t = 4 ∨ t = 5 then
          (case refAt cols ct j 0 of NONE => NONE | SOME l =>
           case refAt cols ct j 1 of NONE => NONE | SOME rr =>
           case pvF cols ct f l of SOME (PTerm tl) =>
             (case pvF cols ct f rr of SOME (PTerm tr) =>
                SOME (PTerm (if t = 3 then TmAdd tl tr
                             else if t = 4 then TmMul tl tr
                             else TmSub tl tr))
              | _ => NONE)
           | _ => NONE)
        else if t = 6 then
          (case refAt cols ct j 0 of NONE => NONE | SOME l =>
           case pvF cols ct f l of
           | SOME (PTerm tl) => SOME (PTerm (TmNeg tl))
           | _ => NONE)
        else if t = 7 then
          (case refAt cols ct j 0 of NONE => NONE | SOME l =>
           case poolField cols ct off 1 of NONE => NONE | SOME ix =>
           case pvF cols ct f l of
           | SOME (PTerm tl) => SOME (PTerm (TmIdx tl ix))
           | _ => NONE)
        else if t = 16 then
          (case poolField cols ct off 0 of NONE => NONE | SOME ci =>
           case oEL ci ct.cxs of NONE => NONE | SOME cx =>
           let nb = (cx.nVertices + 7) DIV 8 in
           let mb = miscBaseP cols ct j in
           if LENGTH cols.poolMisc < mb + 1 + nb then NONE else
           let bs = TAKE nb (DROP (mb + 1) cols.poolMisc) in
           if ¬ EVERY (λb. b < (256:num)) bs then NONE else
           if ¬ padOK bs cx.nVertices then NONE else
             SOME (PSimplex <| complex := cx ;
                               vmask := bitsOf bs cx.nVertices |>))
        else if t = 17 then
          (case refAt cols ct j 0 of NONE => NONE | SOME so =>
           case pvF cols ct f so of
           | SOME (PSimplex sx) =>
             (let nb = (sx.complex.nVertices + 7) DIV 8 in
              let mb = miscBaseP cols ct j in
              if LENGTH cols.poolMisc < mb + nb then NONE else
              let bs = TAKE nb (DROP mb cols.poolMisc) in
              if ¬ EVERY (λb. b < (256:num)) bs then NONE else
              if ¬ padOK bs sx.complex.nVertices then NONE else
                SOME (PExtSet <| simplex := sx ;
                                 emask := bitsOf bs sx.complex.nVertices |>))
           | _ => NONE)
        else if t = 32 then
          (case poolField cols ct off 2 of NONE => NONE | SOME bb =>
           case bowtieOf bb of NONE => NONE | SOME b =>
           case refAt cols ct j 0 of NONE => NONE | SOME l =>
           case refAt cols ct j 1 of NONE => NONE | SOME rr =>
           case pvF cols ct f l of SOME (PTerm tl) =>
             (case pvF cols ct f rr of SOME (PTerm tr) =>
                SOME (PFormula (FwAtom b tl tr))
              | _ => NONE)
           | _ => NONE)
        else if t = 33 then
          (case refAt cols ct j 0 of NONE => NONE | SOME tr0 =>
           case refAt cols ct j 1 of NONE => NONE | SOME so =>
           case refAt cols ct j 2 of NONE => NONE | SOME eo =>
           case pvF cols ct f tr0 of SOME (PTerm tt) =>
             (case pvF cols ct f so of SOME (PSimplex sx) =>
                (case pvF cols ct f eo of SOME (PExtSet es) =>
                   SOME (PFormula (FwInRegion tt sx es))
                 | _ => NONE)
              | _ => NONE)
           | _ => NONE)
        else if t = 34 ∨ t = 35 then
          (case refAt cols ct j 0 of NONE => NONE | SOME l =>
           case refAt cols ct j 1 of NONE => NONE | SOME rr =>
           case pvF cols ct f l of SOME (PFormula fl) =>
             (case pvF cols ct f rr of SOME (PFormula fr) =>
                SOME (PFormula (if t = 34 then FwAnd fl fr else FwOr fl fr))
              | _ => NONE)
           | _ => NONE)
        else if t = 36 then SOME (PFormula FwTt)
        else if t = 37 then SOME (PFormula FwFf)
        else if t = 38 then SOME (PFormula FwSpH)
        else if t = 48 then
          (case refAt cols ct j 0 of NONE => NONE | SOME pre =>
           case refAt cols ct j 1 of NONE => NONE | SOME post =>
           case pvF cols ct f pre of SOME (PFormula prew) =>
             (case pvF cols ct f post of SOME (PFormula postw) =>
                (if fwNoSph postw then SOME (PJudg prew postw) else NONE)
              | _ => NONE)
           | _ => NONE)
        else NONE
End

Definition pv_def:
  pv (cols:columns) (ct:ctx) (off:num) : poolobj option =
    case ALOOKUP ct.poolIdx off of
    | NONE => NONE
    | SOME j => pvF cols ct (SUC j) off
End

Definition pvEq_def:
  pvEq (cols:columns) (ct:ctx) (r1:num) (r2:num) : bool option =
    case pv cols ct r1 of
    | NONE => NONE
    | SOME a =>
      case pv cols ct r2 of
      | NONE => NONE
      | SOME b => SOME (a = b)
End

Definition andeDerive_def:
  andeDerive (cols:columns) (ct:ctx) (v:num) (cref:num) : num option =
    case ALOOKUP ct.poolIdx cref of
    | NONE => NONE
    | SOME j0 =>
      if getD cols.poolTag j0 0 ≠ (48:num) then NONE else
      case refAt cols ct j0 0 of NONE => NONE | SOME preR =>
      case refAt cols ct j0 1 of NONE => NONE | SOME postR =>
      case ALOOKUP ct.poolIdx postR of
      | NONE => NONE
      | SOME j1 =>
        if getD cols.poolTag j1 0 ≠ (34:num) then NONE else
        case refAt cols ct j1 0 of NONE => NONE | SOME l =>
        case refAt cols ct j1 1 of NONE => NONE | SOME rr =>
        let taken = if v = (1:num) then rr else l in
          ALOOKUP ct.judgIdx (preR, taken)
End

Definition andeOther_def:
  andeOther (cols:columns) (ct:ctx) (v:num) (cref:num) : num option =
    case ALOOKUP ct.poolIdx cref of
    | NONE => NONE
    | SOME j0 =>
      if getD cols.poolTag j0 0 ≠ (48:num) then NONE else
      case refAt cols ct j0 1 of NONE => NONE | SOME postR =>
      case ALOOKUP ct.poolIdx postR of
      | NONE => NONE
      | SOME j1 =>
        if getD cols.poolTag j1 0 ≠ (34:num) then NONE else
        case refAt cols ct j1 0 of NONE => NONE | SOME l =>
        case refAt cols ct j1 1 of NONE => NONE | SOME rr =>
          SOME (if v = (1:num) then l else rr)
End

Definition convTriple_def:
  convTriple (cols:columns) (ct:ctx) (cref:num) : (num # num # num) option =
    case ALOOKUP ct.poolIdx cref of
    | NONE => NONE
    | SOME j0 =>
      if getD cols.poolTag j0 0 ≠ (48:num) then NONE else
      case refAt cols ct j0 1 of NONE => NONE | SOME postR =>
      case ALOOKUP ct.poolIdx postR of
      | NONE => NONE
      | SOME j1 =>
        if getD cols.poolTag j1 0 ≠ (33:num) then NONE else
        case refAt cols ct j1 0 of NONE => NONE | SOME t0 =>
        case refAt cols ct j1 1 of NONE => NONE | SOME so =>
        case refAt cols ct j1 2 of NONE => NONE | SOME eo =>
          SOME (t0, so, eo)
End

Definition childConcl_def:
  childConcl (ct:ctx) (dir:(bool # num) list) (i:num) : num option =
    case childOrd ct i 0 of
    | NONE => NONE
    | SOME k => if k < i then SOME (SND (getD dir k (F, 0))) else NONE
End

Definition conclStep_def:
  conclStep (cols:columns) (ct:ctx)
            (acc:((bool # num) list # num) option) (i:num)
            : ((bool # num) list # num) option =
    case acc of
    | NONE => NONE
    | SOME (dir, u) =>
      let explicit =
        (case oEL u cols.nodeConcl of
         | NONE => NONE
         | SOME r => SOME (dir ++ [(F, r)], u + 1)) in
        if ruleOfD cols i ≠ (4:num) then explicit
        else
          case childConcl ct dir i of
          | NONE => explicit
          | SOME cref =>
            case andeDerive cols ct (varOfD cols i) cref of
            | NONE => explicit
            | SOME d =>
                if escContains cols.nodeEsc i then explicit
                else SOME (dir ++ [(T, d)], u)
End

Definition conclDir_def:
  conclDir (cols:columns) (ct:ctx) : (bool # num) list option =
    case FOLDL (conclStep cols ct) (SOME ([], 0)) (rangeL cols.nNodes) of
    | NONE => NONE
    | SOME (dir, u) => if u = LENGTH cols.nodeConcl then SOME dir else NONE
End

Definition conclRef_def:
  conclRef (cols:columns) (ct:ctx) (i:num) : num option =

    case conclDir cols ct of
    | NONE => NONE
    | SOME dir => if i < LENGTH dir then SOME (SND (getD dir i (F, 0)))
                  else NONE
End

Definition readPrefs_def:
  readPrefs (cols:columns) (u:num) (0:num) = SOME ([]:num list, u) ∧
  readPrefs cols u (SUC k) =
    case oEL u cols.nodePref of
    | NONE => NONE
    | SOME x =>
      case readPrefs cols (u + 1) k of
      | NONE => NONE
      | SOME (xs, u') => SOME (x::xs, u')
End

Definition prefStep_def:
  prefStep (cols:columns) (ct:ctx) (cdir:(bool # num) list)
           (acc:((num list) list # num) option) (i:num)
           : ((num list) list # num) option =
    case acc of
    | NONE => NONE
    | SOME (rows, u) =>
      let r = ruleOfD cols i in
      let explicit =
        (case readPrefs cols u (prefCntR r) of
         | NONE => NONE
         | SOME (fs, u') => SOME (rows ++ [fs], u')) in
        if r = (4:num) then
          (case childConcl ct cdir i of
           | NONE => explicit
           | SOME cref =>
             case andeOther cols ct (varOfD cols i) cref of
             | NONE => explicit
             | SOME ot =>
                 if escContains cols.nodeEsc2 i then explicit
                 else SOME (rows ++ [[ot]], u))
        else if r = 9 then
          (case childConcl ct cdir i of
           | NONE => explicit
           | SOME cref =>
             case convTriple cols ct cref of
             | NONE => explicit
             | SOME (t0, so, eo) =>
                 if escContains cols.nodeEsc2 i then explicit
                 else SOME (rows ++ [[t0; so; eo]], u))
        else explicit
End

Definition prefDir_def:
  prefDir (cols:columns) (ct:ctx) : (num list) list option =
    case conclDir cols ct of
    | NONE => NONE
    | SOME cdir =>
      case FOLDL (prefStep cols ct cdir) (SOME ([], 0))
                 (rangeL cols.nNodes) of
      | NONE => NONE
      | SOME (rows, u) =>
          if u = LENGTH cols.nodePref then SOME rows else NONE
End

Definition prefField_def:
  prefField (cols:columns) (ct:ctx) (i:num) (k:num) : num option =
    case prefDir cols ct of
    | NONE => NONE
    | SOME rows =>
      case oEL i rows of
      | NONE => NONE
      | SOME fs => oEL k fs
End

Theorem conclStep_dir_length:
  ∀cols ct i dir u dir' u'.
    conclStep cols ct (SOME (dir, u)) i = SOME (dir', u') ⇒
    LENGTH dir' = LENGTH dir + 1
Proof
  rw[conclStep_def] >> gvs[AllCaseEqs()]
QED

Theorem conclFold_length:
  ∀n cols ct dir u.
    FOLDL (conclStep cols ct) (SOME ([], 0)) (rangeL n) = SOME (dir, u) ⇒
    LENGTH dir = n
Proof
  Induct
  >- (rw[rangeL_def] >> gvs[])
  >> rw[rangeL_def, GSYM listTheory.SNOC_APPEND, listTheory.FOLDL_SNOC]
  >> Cases_on ‘FOLDL (conclStep cols ct) (SOME ([], 0)) (rangeL n)’
  >- gvs[conclStep_def]
  >> PairCases_on ‘x’
  >> res_tac
  >> qpat_x_assum ‘conclStep _ _ _ _ = _’ mp_tac
  >> rw[conclStep_def] >> gvs[AllCaseEqs()]
QED

Theorem conclDir_length:
  conclDir cols ct = SOME dir ⇒ LENGTH dir = cols.nNodes
Proof
  rw[conclDir_def] >> gvs[AllCaseEqs()]
  >> metis_tac[conclFold_length]
QED

Theorem prefStep_rows_length:
  ∀cols ct cdir i rows u rows' u'.
    prefStep cols ct cdir (SOME (rows, u)) i = SOME (rows', u') ⇒
    LENGTH rows' = LENGTH rows + 1
Proof
  rw[prefStep_def] >> gvs[AllCaseEqs()]
QED

Theorem prefFold_length:
  ∀n cols ct cdir rows u.
    FOLDL (prefStep cols ct cdir) (SOME ([], 0)) (rangeL n) =
    SOME (rows, u) ⇒ LENGTH rows = n
Proof
  Induct
  >- (rw[rangeL_def] >> gvs[])
  >> rw[rangeL_def, GSYM listTheory.SNOC_APPEND, listTheory.FOLDL_SNOC]
  >> Cases_on ‘FOLDL (prefStep cols ct cdir) (SOME ([], 0)) (rangeL n)’
  >- gvs[prefStep_def]
  >> PairCases_on ‘x’
  >> res_tac
  >> qpat_x_assum ‘prefStep _ _ _ _ _ = _’ mp_tac
  >> rw[prefStep_def] >> gvs[AllCaseEqs()]
QED

Theorem prefDir_length:
  prefDir cols ct = SOME rows ⇒ LENGTH rows = cols.nNodes
Proof
  rw[prefDir_def] >> gvs[AllCaseEqs()]
  >> metis_tac[prefFold_length]
QED
