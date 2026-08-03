(*
  readColumns — the succinct (bsgc v1) wire reader, and the relational
  verdict function the compiled binary runs (VERIFIED / REJECT /
  UNREADABLE, with the unreadable arm printed distinctly). The reader
  carries no correctness theorem and needs none: in the machine-code
  verdict theorem it appears as its own specification, exactly as the
  flat parser does in the flat chain.
*)
Theory qtsl_colread
Ancestors
  mlstring qtsl_cert qtsl_cols qtsl_wf qtsl_rc qtsl_joins
Libs
  preamble

Definition rdU32At_def:
  rdU32At (bs:num list) (off:num) : num option =
    if LENGTH bs < off + 4 then NONE
    else SOME (leN (TAKE 4 (DROP off bs)))
End

Definition rdU64At_def:
  rdU64At (bs:num list) (off:num) : num option =
    if LENGTH bs < off + 8 then NONE
    else SOME (leN (TAKE 8 (DROP off bs)))
End

Definition rdDirEnts_def:
  rdDirEnts (bs:num list) (base:num) (0:num)
            : ((num # num # num # num # num) list) option = SOME [] ∧
  rdDirEnts bs base (SUC k) =
    if LENGTH bs < base + 32 then NONE
    else
      case rdU32At bs (base + 8) of
      | NONE => NONE
      | SOME _ =>
        (let id = leN (TAKE 2 (DROP base bs)) in
         let codec = leN (TAKE 1 (DROP (base + 2) bs)) in
         let blocked = leN (TAKE 1 (DROP (base + 3) bs)) in
           case rdU64At bs (base + 8) of
           | NONE => NONE
           | SOME off =>
             case rdU64At bs (base + 16) of
             | NONE => NONE
             | SOME len =>
               case rdDirEnts bs (base + 32) k of
               | NONE => NONE
               | SOME es => SOME ((id, codec, blocked, off, len)::es))
End

Definition dirFind_def:
  dirFind ([]:(num # num # num # num # num) list) (i:num)
          : (num # num # num # num) option = NONE ∧
  dirFind ((id, codec, blocked, off, len)::es) i =
    if id = i then SOME (codec, blocked, off, len) else dirFind es i
End

Definition streamDec_def:
  streamDec (bs:num list) (ents:(num # num # num # num # num) list)
            (i:num) : num list option =
    case dirFind ents i of
    | NONE => SOME []
    | SOME (codec, blocked, off, len) =>
        if LENGTH bs < off + len then NONE
        else
          let raw = TAKE len (DROP off bs) in
            if blocked = 0 then
              (if codec = 0 then SOME raw
               else if codec = 1 ∨ codec = 2 then decompressO01 raw
               else NONE)
            else
              (if codec = 0 then blockedRaw raw
               else if codec = 1 ∨ codec = 2 then decompressBlocks raw
               else NONE)
End

Definition rdDeltasF_def:
  rdDeltasF (bs:num list) (pos:num) (prev:num) (0:num) (acc:num list)
            : num list option =
    (if LENGTH bs ≤ pos then SOME (REVERSE acc) else NONE) ∧
  rdDeltasF bs pos prev (SUC f) acc =
    if LENGTH bs ≤ pos then SOME (REVERSE acc)
    else
      case rdVar bs pos of
      | NONE => NONE
      | SOME (d, p') => rdDeltasF bs p' (prev + d) f ((prev + d)::acc)
End

Definition rdDeltas_def:
  rdDeltas (bs:num list) : num list option =
    rdDeltasF bs 0 0 (LENGTH bs) []
End

Definition rdDenPairsF_def:
  rdDenPairsF (bs:num list) (pos:num) (prev:num) (0:num)
              (acc:(num # num) list) : ((num # num) list) option =
    (if LENGTH bs ≤ pos then SOME (REVERSE acc) else NONE) ∧
  rdDenPairsF bs pos prev (SUC f) acc =
    if LENGTH bs ≤ pos then SOME (REVERSE acc)
    else
      case rdVar bs pos of
      | NONE => NONE
      | SOME (d, p1) =>
        case rdVar bs p1 of
        | NONE => NONE
        | SOME (v, p2) =>
            rdDenPairsF bs p2 (prev + d) f ((prev + d, v)::acc)
End

Definition rdDenPairs_def:
  rdDenPairs (bs:num list) : ((num # num) list) option =
    rdDenPairsF bs 0 0 (LENGTH bs) []
End

Definition rdDictF_def:
  rdDictF (bs:num list) (pos:num) (0:num) (acc:(num list) list)
          : ((num list) list) option =
    (if LENGTH bs ≤ pos then SOME (REVERSE acc) else NONE) ∧
  rdDictF bs pos (SUC f) acc =
    if LENGTH bs ≤ pos then SOME (REVERSE acc)
    else
      case rdVar bs pos of
      | NONE => NONE
      | SOME (l, p') =>
          if LENGTH bs < p' + l then NONE
          else rdDictF bs (p' + l) f (TAKE l (DROP p' bs)::acc)
End

Definition rdDict_def:
  rdDict (bs:num list) : ((num list) list) option =
    rdDictF bs 0 (LENGTH bs) []
End

Definition rdVarsK_def:
  rdVarsK (bs:num list) (pos:num) (0:num) : (num list # num) option =
    SOME ([], pos) ∧
  rdVarsK bs pos (SUC k) =
    case rdVar bs pos of
    | NONE => NONE
    | SOME (v, p') =>
      case rdVarsK bs p' k of
      | NONE => NONE
      | SOME (vs, p'') => SOME (v::vs, p'')
End

Datatype:
  prst = <|
    rpos : num ; lpos : num ; dpos : num ; mpos : num ;
    prevR : (num # num) list ;
    prevD : num ;
    poff : num ;
    pidx : (num # num) list ;
    refbR : num list ;
    refn : num ;
    vtx : (num # num) list ;
    jmap : ((num # num) # num) list ;
    refA : num list ;
    lenA : num list ;
    didA : num list ;
    miscA : num list
  |>
End

Definition pInitR_def:
  pInitR = <| rpos := 0 ; lpos := 0 ; dpos := 0 ; mpos := 0 ;
              prevR := [] ; prevD := 0 ; poff := 0 ;
              pidx := [] ; refbR := [0] ; refn := 0 ;
              vtx := [] ; jmap := [] ;
              refA := [] ; lenA := [] ; didA := [] ; miscA := [] |>
End

Definition rdRef1_def:
  rdRef1 (refS:num list) (t:num) (field:num) (st:prst)
         : (num # prst) option =
    case rdVar refS st.rpos of
    | NONE => NONE
    | SOME (w, p') =>
        let role = t * 4 + MIN field 3 in
        let prev = (case ALOOKUP st.prevR role of NONE => 0 | SOME x => x) in
          case dApp prev w 4294967296 of
          | NONE => NONE
          | SOME v =>
              SOME (v, st with <| rpos := p' ;
                                  prevR := (role, v)::st.prevR ;
                                  refA := v::st.refA |>)
End

Definition rdRefsK_def:
  rdRefsK (refS:num list) (t:num) (field:num) (0:num) (st:prst)
          : (num list # prst) option = SOME ([], st) ∧
  rdRefsK refS t field (SUC k) st =
    case rdRef1 refS t field st of
    | NONE => NONE
    | SOME (v, st') =>
      case rdRefsK refS t (field + 1) k st' of
      | NONE => NONE
      | SOME (vs, st'') => SOME (v::vs, st'')
End

Definition rdElem1_def:
  rdElem1 (lenS:num list) (didS:num list) (st:prst)
          : (num # num # prst) option =
    case rdVar lenS st.lpos of
    | NONE => NONE
    | SOME (nl, lp') =>
      case rdVar didS st.dpos of
      | NONE => NONE
      | SOME (w, dp') =>
        case dApp st.prevD w 18446744073709551616 of
        | NONE => NONE
        | SOME did =>
            SOME (nl, did,
                  st with <| lpos := lp' ; dpos := dp' ; prevD := did ;
                             lenA := nl::st.lenA ; didA := did::st.didA |>)
End

Definition rdMiscV_def:
  rdMiscV (miscS:num list) (st:prst) : (num # prst) option =
    case rdVar miscS st.mpos of
    | NONE => NONE
    | SOME (v, p') =>
        SOME (v, st with <| mpos := p' ; miscA := v::st.miscA |>)
End

Definition rdMiscBytes_def:
  rdMiscBytes (miscS:num list) (n:num) (st:prst) : prst option =
    if LENGTH miscS < st.mpos + n then NONE
    else SOME (st with <| mpos := st.mpos + n ;
                          miscA := REVERSE (TAKE n (DROP st.mpos miscS))
                                   ++ st.miscA |>)
End

Definition poolRdStep_def:
  poolRdStep (cxs:simpc list) (ptags:num list) (refS:num list)
             (lenS:num list) (didS:num list) (miscS:num list)
             (dict:(num list) list) (bsz:num)
             (acc:prst option) (j:num) : prst option =
    case acc of
    | NONE => NONE
    | SOME st0 =>
      case oEL j ptags of
      | NONE => NONE
      | SOME t =>

        let st = (if 0 < bsz ∧ 0 < j ∧ j MOD bsz = 0
                  then st0 with <| prevR := [] ; prevD := 0 |>
                  else st0) in

        case rdRefsK refS t 0 (poolRefCnt t) st of
        | NONE => NONE
        | SOME (refs, st1) =>

          case (if poolElemCnt t = 1 then
                  (case rdElem1 lenS didS st1 of
                   | NONE => NONE
                   | SOME (nl, did, st2) =>
                     (case oEL did dict of
                      | NONE => NONE
                      | SOME db => SOME (nl, LENGTH db, st2)))
                else SOME (0, 0, st1)) of
          | NONE => NONE
          | SOME (nl, dl, st2) =>

            case
              (if t = 1 ∨ t = 7 then
                 (case rdMiscV miscS st2 of
                  | NONE => NONE
                  | SOME (_, st3) => SOME (5 + (if t = 7 then 4 else 0), st3))
               else if t = 2 then SOME (9 + nl + dl, st2)
               else if t = 3 ∨ t = 4 ∨ t = 5 then SOME (9, st2)
               else if t = 6 then SOME (5, st2)
               else if t = 16 then
                 (case rdMiscV miscS st2 of
                  | NONE => NONE
                  | SOME (ci, st3) =>
                    (case oEL ci cxs of
                     | NONE => NONE
                     | SOME cx =>
                       (let nb = (cx.nVertices + 7) DIV 8 in
                          case rdMiscBytes miscS nb st3 of
                          | NONE => NONE
                          | SOME st4 =>
                              SOME (5 + nb,
                                    st4 with vtx := (st.poff, cx.nVertices)
                                                    ::st4.vtx))))
               else if t = 17 then
                 (case refs of
                  | [so] =>
                    (case ALOOKUP st2.vtx so of
                     | NONE => NONE
                     | SOME nv =>
                       (let nb = (nv + 7) DIV 8 in
                          case rdMiscBytes miscS nb st2 of
                          | NONE => NONE
                          | SOME st3 => SOME (5 + nb, st3)))
                  | _ => NONE)
               else if t = 32 then

                 (case oEL st2.mpos miscS of
                  | NONE => NONE
                  | SOME b =>
                      SOME (10, st2 with <| mpos := st2.mpos + 1 ;
                                            miscA := b::st2.miscA |>))
               else if t = 33 then SOME (13, st2)
               else if t = 34 ∨ t = 35 then SOME (9, st2)
               else if t = 36 ∨ t = 37 ∨ t = 38 then SOME (1, st2)
               else if t = 48 then SOME (9, st2)
               else NONE) of
            | NONE => NONE
            | SOME (len, st5) =>

                let jmap' =
                  (if t = 48 then
                     (case refs of
                      | [preR; postR] =>
                          (if ALOOKUP st5.jmap (preR, postR) = NONE
                           then ((preR, postR), st.poff)::st5.jmap
                           else st5.jmap)
                      | _ => st5.jmap)
                   else st5.jmap) in
                  SOME (st5 with
                        <| poff := st.poff + len ;
                           pidx := (st.poff, j)::st5.pidx ;
                           refbR := (st.refn + poolRefCnt t)::st5.refbR ;
                           refn := st.refn + poolRefCnt t ;
                           jmap := jmap' |>)
End

Definition poolRdFold_def:
  poolRdFold (cxs:simpc list) (ptags:num list) (refS:num list)
             (lenS:num list) (didS:num list) (miscS:num list)
             (dict:(num list) list) (bsz:num) : prst option =
    FOLDL (poolRdStep cxs ptags refS lenS didS miscS dict bsz)
          (SOME pInitR) (rangeL (LENGTH ptags))
End

Datatype:
  nrst = <|
    cpos : num ; prevC : num ;
    fpos : num ; prevP : num ;
    spos : num ;
    papos : num ;
    apos : num ;
    tpos : num ;
    noff : num ;
    nidx : (num # num) list ;
    stk : num list ;
    cdir : (num # num) list ;
    conclA : num list ;
    prefA : num list ;
    scalA : num list ;
    arityA : num list ;
    topoA : num list ;
    pathA : (num list # num list) list
  |>
End

Definition nInitR_def:
  nInitR (start:num) =
    <| cpos := 0 ; prevC := 0 ; fpos := 0 ; prevP := 0 ;
       spos := 0 ; papos := 0 ; apos := 0 ; tpos := 0 ;
       noff := start ; nidx := [] ; stk := [] ; cdir := [] ;
       conclA := [] ; prefA := [] ; scalA := [] ; arityA := [] ;
       topoA := [] ; pathA := [] |>
End

Definition rdConclE_def:
  rdConclE (conclS:num list) (i:num) (st:nrst) : nrst option =
    case rdVar conclS st.cpos of
    | NONE => NONE
    | SOME (w, p') =>
      case dApp st.prevC w 4294967296 of
      | NONE => NONE
      | SOME v =>
          SOME (st with <| cpos := p' ; prevC := v ;
                           conclA := v::st.conclA ;
                           cdir := (i, v)::st.cdir |>)
End

Definition rdPrefsE_def:
  rdPrefsE (prefS:num list) (0:num) (st:nrst) : nrst option = SOME st ∧
  rdPrefsE prefS (SUC k) st =
    case rdVar prefS st.fpos of
    | NONE => NONE
    | SOME (w, p') =>
      case dApp st.prevP w 4294967296 of
      | NONE => NONE
      | SOME v =>
          rdPrefsE prefS k
            (st with <| fpos := p' ; prevP := v ; prefA := v::st.prefA |>)
End

Definition rdChildConcl_def:
  rdChildConcl (st:nrst) (childs:num list) (i:num) : num option =
    case childs of
    | [] => NONE
    | (k::_) => if k < i then ALOOKUP st.cdir k else NONE
End

Definition nodeRdStep_def:
  nodeRdStep (cols0:columns) (ct0:ctx) (ntags:num list)
             (conclS:num list) (prefS:num list) (scalS:num list)
             (pathS:num list) (arityS:num list) (topoS:num list)
             (esc:num list) (esc2:num list) (bsz:num) (tmode:num)
             (acc:nrst option) (i:num) : nrst option =
    case acc of
    | NONE => NONE
    | SOME st0 =>
      case oEL i ntags of
      | NONE => NONE
      | SOME s =>
        case tagDec s of
        | NONE => NONE
        | SOME (r, v) =>

          let stA = (if 0 < bsz ∧ 0 < i ∧ i MOD bsz = 0
                     then st0 with <| prevC := 0 ; prevP := 0 |>
                     else st0) in

          case (if hasArityR r then
                  (case rdVar arityS stA.apos of
                   | NONE => NONE
                   | SOME (a, ap') =>
                       SOME (a, stA with <| apos := ap' ;
                                            arityA := a::stA.arityA |>))
                else SOME (0, stA)) of
          | NONE => NONE
          | SOME (extra, stB) =>
            let nc = (if r = 26 then extra else ruleArity r) in

            case (if hasPathR r then
                    (case rdVar pathS stB.papos of
                     | NONE => NONE
                     | SOME (n, pp1) =>
                       (let nb = (n + 7) DIV 8 in
                          if LENGTH pathS < pp1 + nb then NONE
                          else
                            let bits = TAKE nb (DROP pp1 pathS) in
                            let stps = GENLIST
                              (λb. (getD bits (b DIV 8) 0 DIV 2 ** (b MOD 8))
                                   MOD 2) n in
                              if r = 25 then
                                (case rdVar pathS (pp1 + nb) of
                                 | NONE => NONE
                                 | SOME (ni, pp2) =>
                                   (case rdVarsK pathS pp2 ni of
                                    | NONE => NONE
                                    | SOME (ifc, pp3) =>
                                        SOME (stps, ifc,
                                              stB with
                                              <| papos := pp3 ;
                                                 pathA := (stps, ifc)
                                                          ::stB.pathA |>)))
                              else
                                SOME (stps, [],
                                      stB with
                                      <| papos := pp1 + nb ;
                                         pathA := (stps, [])::stB.pathA |>)))
                  else SOME ([], [], stB)) of
            | NONE => NONE
            | SOME (stps, ifc, stC) =>

              case (if tmode = 0 then
                      (if LENGTH stC.stk < nc then NONE
                       else SOME (REVERSE (TAKE nc stC.stk),
                                  stC with stk := i::DROP nc stC.stk))
                    else
                      (case rdVarsK topoS stC.tpos nc of
                       | NONE => NONE
                       | SOME (ds, tp') =>
                         (let stC' = stC with
                                     <| tpos := tp' ;
                                        topoA := REVERSE ds ++ stC.topoA |> in
                            case optSeq (MAP (λd. if d ≤ stC.noff
                                                  then ALOOKUP stC.nidx
                                                         (stC.noff − d)
                                                  else NONE) ds) of
                            | NONE => NONE
                            | SOME cs => SOME (cs, stC')))) of
              | NONE => NONE
              | SOME (childs, stD) =>

                case
                  (if r = 4 then
                     (case rdChildConcl stD childs i of
                      | NONE => rdConclE conclS i stD
                      | SOME cref =>
                        (case andeDerive cols0 ct0 v cref of
                         | NONE => rdConclE conclS i stD
                         | SOME d =>
                             if escContains esc i then rdConclE conclS i stD
                             else SOME (stD with cdir := (i, d)::stD.cdir)))
                   else rdConclE conclS i stD) of
                | NONE => NONE
                | SOME stE =>

                  case
                    (if r = 4 then
                       (case rdChildConcl stE childs i of
                        | NONE => rdPrefsE prefS 1 stE
                        | SOME cref =>
                          (case andeOther cols0 ct0 v cref of
                           | NONE => rdPrefsE prefS 1 stE
                           | SOME _ =>
                               if escContains esc2 i
                               then rdPrefsE prefS 1 stE
                               else SOME stE))
                     else if r = 9 then
                       (case rdChildConcl stE childs i of
                        | NONE => rdPrefsE prefS 3 stE
                        | SOME cref =>
                          (case convTriple cols0 ct0 cref of
                           | NONE => rdPrefsE prefS 3 stE
                           | SOME _ =>
                               if escContains esc2 i
                               then rdPrefsE prefS 3 stE
                               else SOME stE))
                     else rdPrefsE prefS (prefCntR r) stE) of
                  | NONE => NONE
                  | SOME stF =>

                    case rdVarsK scalS stF.spos (scalCntR r) of
                    | NONE => NONE
                    | SOME (svs, sp') =>
                        let stG = stF with
                                  <| spos := sp' ;
                                     scalA := REVERSE svs ++ stF.scalA |> in
                        let len = nodeLenR r stps ifc extra in
                          SOME (stG with
                                <| noff := stG.noff + len ;
                                   nidx := (stG.noff, i)::stG.nidx |>)
End

Definition nodeRdFold_def:
  nodeRdFold cols0 ct0 (ntags:num list) conclS prefS scalS pathS arityS
             topoS esc esc2 (bsz:num) (tmode:num) (start:num)
             : nrst option =
    FOLDL (nodeRdStep cols0 ct0 ntags conclS prefS scalS pathS arityS
                      topoS esc esc2 bsz tmode)
          (SOME (nInitR start)) (rangeL (LENGTH ntags))
End

Definition emptyCols_def:
  emptyCols = <|
    hdrImage := [] ; topoMode := 0 ; denDefault := 0 ;
    nNodes := 0 ; nPool := 0 ; blockSize := 0 ;
    nodeTag := [] ; nodeArity := [] ; nodeTopo := [] ; nodeConcl := [] ;
    nodePref := [] ; nodeScal := [] ; nodeDen := [] ; nodePath := [] ;
    nodeRat := [] ; nodeEsc := [] ; nodeEsc2 := [] ;
    poolTag := [] ; poolRef := [] ; poolNumLen := [] ; poolDenId := [] ;
    poolDenDict := [] ; poolNum := [] ; poolMisc := []
  |> : columns
End

Definition sgcMagic_def:
  sgcMagic : num list = [66; 69; 82; 78; 83; 71; 67; 1]
End

Definition readColumns_def:
  readColumns (bs:num list) : columns option =
    if TAKE 8 bs ≠ sgcMagic then NONE else
    case rdU32At bs 8 of NONE => NONE | SOME ver =>
    if ver ≠ 1 then NONE else
    if LENGTH bs < 180 then NONE else
    let tmode = getD bs 140 0 in
    case rdU32At bs 144 of NONE => NONE | SOME bsz =>
    case rdU64At bs 148 of NONE => NONE | SOME denDef =>
    case rdU64At bs 156 of NONE => NONE | SOME nn =>
    case rdU64At bs 164 of NONE => NONE | SOME np =>
    case rdU32At bs 172 of NONE => NONE | SOME nstreams =>
    case rdU32At bs 176 of NONE => NONE | SOME dirOff =>
    case rdDirEnts bs dirOff nstreams of NONE => NONE | SOME ents =>

    if dirFind ents 19 ≠ NONE then NONE else
    case streamDec bs ents 0 of NONE => NONE | SOME img =>
    case streamDec bs ents 1 of NONE => NONE | SOME ntags =>
    case streamDec bs ents 2 of NONE => NONE | SOME esc2W =>
    case streamDec bs ents 3 of NONE => NONE | SOME conclS =>
    case streamDec bs ents 4 of NONE => NONE | SOME prefS =>
    case streamDec bs ents 5 of NONE => NONE | SOME scalS =>
    case streamDec bs ents 6 of NONE => NONE | SOME denS =>
    case streamDec bs ents 7 of NONE => NONE | SOME pathS =>
    case streamDec bs ents 8 of NONE => NONE | SOME arityS =>
    case streamDec bs ents 9 of NONE => NONE | SOME ratS =>
    case streamDec bs ents 10 of NONE => NONE | SOME escW =>
    case streamDec bs ents 11 of NONE => NONE | SOME topoS =>
    case streamDec bs ents 12 of NONE => NONE | SOME ptags =>
    case streamDec bs ents 13 of NONE => NONE | SOME refS =>
    case streamDec bs ents 14 of NONE => NONE | SOME lenS =>
    case streamDec bs ents 15 of NONE => NONE | SOME didS =>
    case streamDec bs ents 16 of NONE => NONE | SOME dictS =>
    case streamDec bs ents 17 of NONE => NONE | SOME numS =>
    case streamDec bs ents 18 of NONE => NONE | SOME miscS =>

    case parseHeader (img ++ REPLICATE (peekPrfLen img) 0) of
    | NONE => NONE
    | SOME h =>
    case parseDiagram (TAKE h.diaLen (DROP h.diaOff img)) h.nCxs h.nApps of
    | NONE => NONE
    | SOME cxs =>
    case rdDict dictS of NONE => NONE | SOME dict =>
    case rdDeltas escW of NONE => NONE | SOME esc =>
    case rdDeltas esc2W of NONE => NONE | SOME esc2 =>
    case rdDenPairs denS of NONE => NONE | SOME denPairs =>
    case poolRdFold cxs ptags refS lenS didS miscS dict bsz of
    | NONE => NONE
    | SOME pst =>

    let poolRefCol = REVERSE pst.refA in
    let cols0 = emptyCols with <| poolTag := ptags ;
                                  poolRef := poolRefCol |> in
    let ct0 = <| hdr := h ; ws := [] ; cxs := cxs ;
                 poolOffs := [] ; nodeOffs := [] ;
                 poolIdx := pst.pidx ; nodeIdx := [] ;
                 judgIdx := pst.jmap ; childTbl := [] ;
                 prefBase := [] ; scalBase := [] ;
                 refBase := REVERSE pst.refbR ; elemBase := [] |> in
    case nodeRdFold cols0 ct0 ntags conclS prefS scalS pathS arityS
                    topoS esc esc2 bsz tmode (8 + pst.poff) of
    | NONE => NONE
    | SOME nst =>
      SOME (emptyCols with <|
              hdrImage := img ; topoMode := tmode ; denDefault := denDef ;
              nNodes := nn ; nPool := np ; blockSize := bsz ;
              nodeTag := ntags ;
              nodeArity := REVERSE nst.arityA ;
              nodeTopo := REVERSE nst.topoA ;
              nodeConcl := REVERSE nst.conclA ;
              nodePref := REVERSE nst.prefA ;
              nodeScal := REVERSE nst.scalA ;
              nodeDen := denPairs ;
              nodePath := REVERSE nst.pathA ;
              nodeRat := ratS ;
              nodeEsc := esc ; nodeEsc2 := esc2 ;
              poolTag := ptags ;
              poolRef := poolRefCol ;
              poolNumLen := REVERSE pst.lenA ;
              poolDenId := REVERSE pst.didA ;
              poolDenDict := dict ;
              poolNum := numS ;
              poolMisc := REVERSE pst.miscA |>)
End

Definition unreadable_string_def:
  unreadable_string = strlit "s BERNLGC UNREADABLE\n"
End

Definition qtsl_rel_result_def:
  qtsl_rel_result (bs:num list) : bool option =
    case readColumns bs of
    | NONE => NONE
    | SOME cols => checkJoins cols
End

Definition qtsl_rel_verdict_def:
  qtsl_rel_verdict (cs:string) : mlstring =
    case qtsl_rel_result (MAP ORD cs) of
    | NONE => unreadable_string
    | SOME F => reject_string
    | SOME T => verified_string
End

Definition qtsl_rel_verdict_strI_def:
  qtsl_rel_verdict_strI (s:mlstring) : mlstring =
    case qtsl_rel_result (MAP ORD (explode s)) of
    | NONE => unreadable_string
    | SOME F => reject_string
    | SOME T => verified_string
End

Theorem qtsl_rel_verdict_strI_correct:
  qtsl_rel_verdict_strI (implode cs) = qtsl_rel_verdict cs
Proof
  rw[qtsl_rel_verdict_strI_def, qtsl_rel_verdict_def,
     mlstringTheory.explode_implode]
QED

Theorem rel_strings_distinct[simp]:
  verified_string ≠ reject_string ∧
  verified_string ≠ unreadable_string ∧
  reject_string ≠ unreadable_string
Proof
  EVAL_TAC
QED

Theorem qtsl_rel_verdict_verified:
  qtsl_rel_verdict cs = verified_string ⇔
  qtsl_rel_result (MAP ORD cs) = SOME T
Proof
  rw[qtsl_rel_verdict_def]
  >> Cases_on ‘qtsl_rel_result (MAP ORD cs)’ >> simp[]
  >> Cases_on ‘x’ >> simp[]
QED

Theorem qtsl_rel_verdict_cases:
  (qtsl_rel_verdict cs = verified_string ⇔
     qtsl_rel_result (MAP ORD cs) = SOME T) ∧
  (qtsl_rel_verdict cs = reject_string ⇔
     qtsl_rel_result (MAP ORD cs) = SOME F) ∧
  (qtsl_rel_verdict cs = unreadable_string ⇔
     qtsl_rel_result (MAP ORD cs) = NONE)
Proof
  rw[qtsl_rel_verdict_def]
  >> Cases_on ‘qtsl_rel_result (MAP ORD cs)’ >> simp[]
  >> Cases_on ‘x’ >> simp[]
QED
