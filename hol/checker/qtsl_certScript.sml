(*
  The first-order certificate datatype, the binary (v0) wire parser,
  and the reference checker (checkPf/checkPf1) that re-checks every
  v0-fragment rule side condition — the analogue of cake_lpr's check_lpr
  for Bernstein Logic certificates. The parser is the format's
  specification: it appears in the machine-code theorems as its own
  spec, and the checker's per-rule obligations mirror the Lean
  development's proof-object side conditions constructor by
  constructor.
*)
Theory qtsl_cert
Ancestors
  rat integer mlstring mllist qtsl_dyadic qtsl_qarith qtsl_catalogue
Libs
  preamble

Definition takeN_def:
  takeN (n:num) (xs:num list) =
    if n ≤ LENGTH xs then SOME (TAKE n xs, DROP n xs) else NONE
End

Definition leN_def:
  leN ([]:num list) = (0:num) ∧
  leN (b::bs) = b + 256 * leN bs
End

Definition rdU8_def:
  rdU8 ([]:num list) = (NONE : (num # num list) option) ∧
  rdU8 (b::bs) = SOME (b, bs)
End

Theorem leN_lt:
  ∀bs. EVERY (λb. b < 256) bs ⇒ leN bs < 256 ** LENGTH bs
Proof
  Induct >> rw[leN_def] >> gvs[arithmeticTheory.EXP] >> DECIDE_TAC
QED

Definition rdLE_def:
  rdLE (k:num) (xs:num list) =
    case takeN k xs of
    | NONE => NONE
    | SOME (bs, r) => SOME (leN bs, r)
End

Definition denMinimal_def:
  denMinimal (bs:num list) =
    case REVERSE bs of
    | [] => F
    | [b] => T
    | (b::b'::rest) => b ≠ 0
End

Definition numMinimal_def:
  numMinimal (bs:num list) =
    case REVERSE bs of
    | [] => F
    | [b] => T
    | (b::b'::rest) => ¬((b = 0 ∧ b' < 128) ∨ (b = 255 ∧ 128 ≤ b'))
End

Definition egcd_def:
  egcd (a:num) (b:num) = if b = 0 then a else egcd b (a MOD b)
Termination
  WF_REL_TAC ‘measure SND’ >> rw[] >> irule arithmeticTheory.MOD_LESS >> simp[]
End

Definition rdRat_def:
  rdRat (xs:num list) =
    case rdLE 4 xs of NONE => NONE | SOME (nl, xs1) =>
    case rdLE 4 xs1 of NONE => NONE | SOME (dl, xs2) =>
    case takeN nl xs2 of NONE => NONE | SOME (nb, xs3) =>
    case takeN dl xs3 of NONE => NONE | SOME (db, xs4) =>
    if ¬(numMinimal nb ∧ denMinimal db) then NONE else

    if ¬ EVERY (λb. b < (256:num)) nb then NONE else
    (let d = leN db in
     let v = leN nb in
     let m = 256 ** LENGTH nb in
     let neg = ¬(2 * v < m) in
     let mag = if neg then m − v else v in
       if d = 0 then NONE else
       if mag = 0 ∧ d ≠ 1 then NONE else
       if mag ≠ 0 ∧ egcd mag d ≠ 1 then NONE else
       if (&d):rat = 0 then NONE else
         SOME ((if neg then -(&mag / &d) else (&mag / &d)):rat, xs4))
End

Definition byteBit_def:
  byteBit (b:num) (i:num) = ((b DIV 2 ** i) MOD 2 = 1)
End

Definition bitsOf_def:
  bitsOf (bs:num list) (n:num) =
    MAP (λi. byteBit (getD bs (i DIV 8) 0) (i MOD 8)) (rangeL n)
End

Definition padOK_def:
  padOK (bs:num list) (n:num) =
    EVERY (λk. k < n ∨ ¬ byteBit (getD bs (k DIV 8) 0) (k MOD 8))
          (rangeL (8 * LENGTH bs))
End

Definition rdBitset_def:
  rdBitset (n:num) (xs:num list) =
    case takeN ((n + 7) DIV 8) xs of
    | NONE => NONE
    | SOME (bs, r) => if padOK bs n then SOME (bitsOf bs n, r) else NONE
End

Definition rdRatsN_def:
  rdRatsN (0:num) (xs:num list) = SOME ([]:rat list, xs) ∧
  rdRatsN (SUC k) xs =
    case rdRat xs of NONE => NONE
    | SOME (q, xs1) =>
      case rdRatsN k xs1 of NONE => NONE
      | SOME (qs, xs2) => SOME (q::qs, xs2)
End

Definition rdBitsetsN_def:
  rdBitsetsN (nv:num) (0:num) (xs:num list) = SOME ([]:bool list list, xs) ∧
  rdBitsetsN nv (SUC k) xs =
    case rdBitset nv xs of NONE => NONE
    | SOME (b, xs1) =>
      case rdBitsetsN nv k xs1 of NONE => NONE
      | SOME (bs, xs2) => SOME (b::bs, xs2)
End

Definition rdCellsN_def:
  rdCellsN (nv:num) (0:num) (xs:num list) =
    SOME ([]:(bool list # bool list) list, xs) ∧
  rdCellsN nv (SUC k) xs =
    case rdBitset nv xs of NONE => NONE
    | SOME (sm, xs1) =>
      case rdBitset nv xs1 of NONE => NONE
      | SOME (em, xs2) =>
        case rdCellsN nv k xs2 of NONE => NONE
        | SOME (cs, xs3) => SOME ((sm, em)::cs, xs3)
End

Definition rdLEsN_def:
  rdLEsN (w:num) (0:num) (xs:num list) = SOME ([]:num list, xs) ∧
  rdLEsN w (SUC k) xs =
    case rdLE w xs of NONE => NONE
    | SOME (v, xs1) =>
      case rdLEsN w k xs1 of NONE => NONE
      | SOME (vs, xs2) => SOME (v::vs, xs2)
End

Definition optSeq_def:
  optSeq ([]:'a option list) = SOME ([]:'a list) ∧
  optSeq (NONE::xs) = NONE ∧
  optSeq (SOME x::xs) =
    case optSeq xs of NONE => NONE | SOME ys => SOME (x::ys)
End

Definition chunksOf_def:
  chunksOf (k:num) (xs:rat list) =
    if k = 0 ∨ NULL xs then [] else TAKE k xs :: chunksOf k (DROP k xs)
Termination
  WF_REL_TAC ‘measure (LENGTH o SND)’ >> rw[] >> Cases_on ‘xs’ >> gvs[]
End

Definition kindOf_def:
  kindOf (k:num) =
    if k = 0 then SOME KBool else if k = 1 then SOME KInt else
    if k = 2 then SOME KRat else if k = 3 then SOME KF16 else
    if k = 4 then SOME KBF16 else if k = 5 then SOME KF32 else
    if k = 6 then SOME KF64 else NONE
End

Definition signOf_def:
  signOf (s:num) =
    if s = 0 then SOME Nn else if s = 1 then SOME Signed else NONE
End

Definition extOf_def:
  extOf (e:num) =
    if e = 0 then SOME ExtFin else if e = 1 then SOME ExtExt else NONE
End

Definition bowtieOf_def:
  bowtieOf (b:num) =
    if b = 0 then SOME BowLt else if b = 1 then SOME BowLe else
    if b = 2 then SOME BowEq else if b = 3 then SOME BowGe else
    if b = 4 then SOME BowGt else if b = 5 then SOME BowNe else NONE
End

Datatype:
  bhdr = <| symOff : num ; symLen : num ; payOff : num ; payLen : num ;
            diaOff : num ; diaLen : num ; prfOff : num ; prfLen : num ;
            nWires : num ; nApps : num ; nNodes : num ; nCxs : num ;
            rootOff : num ; thetaRef : num |>
End

Definition bernMagic_def:
  bernMagic = [66;69;82;78;76;71;67;1] : num list
End

Definition sectionOK_def:
  sectionOK (flen:num) (off:num) (len:num) = (128 ≤ off ∧ off + len ≤ flen)
End

Definition parseHeader_def:
  parseHeader (bytes:num list) =
    case takeN 8 bytes of NONE => NONE | SOME (magic, r0) =>
    if magic ≠ bernMagic then NONE else
    case rdLE 4 r0 of NONE => NONE | SOME (ver, r1) =>
    if ver ≠ (1:num) then NONE else
    case rdLE 4 r1 of NONE => NONE | SOME (flg, r2) =>
    if flg ≠ (0:num) then NONE else
    case rdLE 8 r2 of NONE => NONE | SOME (syo, r3) =>
    case rdLE 8 r3 of NONE => NONE | SOME (syl, r4) =>
    case rdLE 8 r4 of NONE => NONE | SOME (po, r5) =>
    case rdLE 8 r5 of NONE => NONE | SOME (pl, r6) =>
    case rdLE 8 r6 of NONE => NONE | SOME (dio, r7) =>
    case rdLE 8 r7 of NONE => NONE | SOME (dil, r8) =>
    case rdLE 8 r8 of NONE => NONE | SOME (pro, r9) =>
    case rdLE 8 r9 of NONE => NONE | SOME (prl, r10) =>
    case rdLE 4 r10 of NONE => NONE | SOME (nw, r11) =>
    case rdLE 4 r11 of NONE => NONE | SOME (na, r12) =>
    case rdLE 4 r12 of NONE => NONE | SOME (nn, r13) =>
    case rdLE 4 r13 of NONE => NONE | SOME (nc, r14) =>
    case rdLE 8 r14 of NONE => NONE | SOME (ro, r15) =>
    case rdLE 4 r15 of NONE => NONE | SOME (th, r16) =>
    case takeN 20 r16 of NONE => NONE | SOME (resv, r17) =>
    if ¬ EVERY (λb. b = (0:num)) resv then NONE else
    (let flen = LENGTH bytes in
       if ¬(sectionOK flen syo syl ∧ sectionOK flen po pl ∧
            sectionOK flen dio dil ∧ sectionOK flen pro prl) then NONE else
       if nw = (4294967295:num) then NONE else
       if po MOD 64 ≠ (0:num) then NONE else
         SOME <| symOff := syo ; symLen := syl ; payOff := po ; payLen := pl ;
                 diaOff := dio ; diaLen := dil ; prfOff := pro ; prfLen := prl ;
                 nWires := nw ; nApps := na ; nNodes := nn ; nCxs := nc ;
                 rootOff := ro ; thetaRef := th |>)
End

Definition parseSymRec_def:
  parseSymRec (sec:num list) (seclen:num) (recslen:num)
              (payOff:num) (payLen:num) (i:num) =
    let xs = DROP (32 * i) sec in
    case rdU8 xs of NONE => NONE | SOME (k, r0) =>
    case rdU8 r0 of NONE => NONE | SOME (sg, r1) =>
    case rdU8 r1 of NONE => NONE | SOME (ex, r2) =>
    case rdU8 r2 of NONE => NONE | SOME (resv, r3) =>
    if resv ≠ (0:num) then NONE else
    case kindOf k of NONE => NONE | SOME kd =>
    case signOf sg of NONE => NONE | SOME sn =>
    case extOf ex of NONE => NONE | SOME et =>
    case rdLE 4 r3 of NONE => NONE | SOME (rank, r4) =>
    case rdLE 8 r4 of NONE => NONE | SOME (shOff, r5) =>
    case rdLE 8 r5 of NONE => NONE | SOME (pOff, r6) =>
    case rdLE 8 r6 of NONE => NONE | SOME (pLen, r7) =>
    if shOff < recslen ∨ seclen < shOff + 8 * rank then NONE else
    case rdLEsN 8 rank (DROP shOff sec) of NONE => NONE | SOME (shape, r8) =>
    if pOff = (18446744073709551615:num) then
      (if pLen ≠ (0:num) then NONE
       else SOME <| shape := shape ;
                    dtype := <| kind := kd ; sign := sn ; ext := et |> |>)
    else
      (if pOff MOD 64 ≠ (0:num) ∨ pOff < payOff ∨ payOff + payLen < pOff + pLen
       then NONE
       else SOME <| shape := shape ;
                    dtype := <| kind := kd ; sign := sn ; ext := et |> |>)
End

Definition parseSymtab_def:
  parseSymtab (sec:num list) (seclen:num) (nw:num)
              (payOff:num) (payLen:num) =
    if seclen < 32 * nw ∨ LENGTH sec < seclen then NONE else
      optSeq (MAP (parseSymRec sec seclen (32 * nw) payOff payLen)
                  (rangeL nw))
End

Definition parseComplex_def:
  parseComplex (xs:num list) =
    case rdLE 4 xs of NONE => NONE | SOME (nv, xs1) =>
    case rdLE 4 xs1 of NONE => NONE | SOME (amb, xs2) =>
    case rdRatsN (nv * amb) xs2 of NONE => NONE | SOME (qs, xs3) =>
    case rdLE 4 xs3 of NONE => NONE | SOME (nsimp, xs4) =>
    case rdBitsetsN nv nsimp xs4 of NONE => NONE | SOME (simps, xs5) =>
    case rdLE 4 xs5 of NONE => NONE | SOME (ncell, xs6) =>
    case rdCellsN nv ncell xs6 of NONE => NONE | SOME (cells, xs7) =>
      SOME (<| nVertices := nv ; ambDim := amb ;
               coord := chunksOf amb qs ;
               simplices := simps ; cells := cells |>, xs7)
End

Definition parseComplexesN_def:
  parseComplexesN (0:num) (xs:num list) = SOME ([]:simpc list, xs) ∧
  parseComplexesN (SUC k) xs =
    case parseComplex xs of NONE => NONE
    | SOME (cx, xs1) =>
      case parseComplexesN k xs1 of NONE => NONE
      | SOME (cxs, xs2) => SOME (cx::cxs, xs2)
End

Definition parseDiagram_def:
  parseDiagram (sec:num list) (hnc:num) (hna:num) =
    case rdLE 4 sec of NONE => NONE | SOME (nc, xs1) =>
    if nc ≠ hnc then NONE else
    case parseComplexesN nc xs1 of NONE => NONE | SOME (cxs, xs2) =>
    case rdLE 4 xs2 of NONE => NONE | SOME (na, xs3) =>
    if na ≠ hna ∨ na ≠ (0:num) then NONE else
      SOME cxs
End

Datatype:
  fwire = FwAtom bowtie term term
        | FwInRegion term simplex extensionset
        | FwAnd fwire fwire
        | FwOr fwire fwire
        | FwTt
        | FwFf
        | FwSpH
End

Definition expandSph_def:
  expandSph (sp:formula) (FwAtom b l r) = FAtom b l r ∧
  expandSph sp (FwInRegion t sx es) = FInRegion t sx es ∧
  expandSph sp (FwAnd l r) = FAnd (expandSph sp l) (expandSph sp r) ∧
  expandSph sp (FwOr l r) = FOr (expandSph sp l) (expandSph sp r) ∧
  expandSph sp FwTt = FTt ∧
  expandSph sp FwFf = FFf ∧
  expandSph sp FwSpH = sp
End

Definition fwNoSph_def:
  fwNoSph (FwAnd l r) = (fwNoSph l ∧ fwNoSph r) ∧
  fwNoSph (FwOr l r) = (fwNoSph l ∧ fwNoSph r) ∧
  fwNoSph FwSpH = F ∧
  fwNoSph (fw:fwire) = T
End

Datatype:
  poolobj = PTerm term
          | PSimplex simplex
          | PExtSet extensionset
          | PFormula fwire
          | PJudg fwire fwire
End

Definition lookTerm_def:
  lookTerm (tbl:(num # poolobj) list) (r:num) =
    case ALOOKUP tbl r of SOME (PTerm t) => SOME t | _ => NONE
End

Definition lookSimplex_def:
  lookSimplex (tbl:(num # poolobj) list) (r:num) =
    case ALOOKUP tbl r of SOME (PSimplex s) => SOME s | _ => NONE
End

Definition lookExtSet_def:
  lookExtSet (tbl:(num # poolobj) list) (r:num) =
    case ALOOKUP tbl r of SOME (PExtSet e) => SOME e | _ => NONE
End

Definition lookFormula_def:
  lookFormula (tbl:(num # poolobj) list) (r:num) =
    case ALOOKUP tbl r of SOME (PFormula f) => SOME f | _ => NONE
End

Definition lookJudg_def:
  lookJudg (tbl:(num # poolobj) list) (r:num) =
    case ALOOKUP tbl r of SOME (PJudg pre post) => SOME (pre, post) | _ => NONE
End

Definition parsePoolRec_def:
  parsePoolRec (cxs:simpc list) (tbl:(num # poolobj) list) (xs:num list) =
    case rdU8 xs of NONE => NONE | SOME (tag, r0) =>
    if tag = (1:num) then
      (case rdLE 4 r0 of NONE => NONE
       | SOME (w, r1) => SOME (PTerm (TmVar w), r1))
    else if tag = 2 then
      (case rdRat r0 of NONE => NONE
       | SOME (q, r1) => SOME (PTerm (TmConst q), r1))
    else if tag = 3 ∨ tag = 4 ∨ tag = 5 then
      (case rdLE 4 r0 of NONE => NONE | SOME (l, r1) =>
       case rdLE 4 r1 of NONE => NONE | SOME (rr, r2) =>
       case lookTerm tbl l of NONE => NONE | SOME tl =>
       case lookTerm tbl rr of NONE => NONE | SOME tr =>
         SOME (PTerm (if tag = 3 then TmAdd tl tr
                      else if tag = 4 then TmMul tl tr
                      else TmSub tl tr), r2))
    else if tag = 6 then
      (case rdLE 4 r0 of NONE => NONE | SOME (t, r1) =>
       case lookTerm tbl t of NONE => NONE | SOME tt =>
         SOME (PTerm (TmNeg tt), r1))
    else if tag = 7 then
      (case rdLE 4 r0 of NONE => NONE | SOME (t, r1) =>
       case rdLE 4 r1 of NONE => NONE | SOME (i, r2) =>
       case lookTerm tbl t of NONE => NONE | SOME tt =>
         SOME (PTerm (TmIdx tt i), r2))
    else if tag = 16 then
      (case rdLE 4 r0 of NONE => NONE | SOME (cxi, r1) =>
       case oEL cxi cxs of NONE => NONE | SOME cx =>
       case rdBitset cx.nVertices r1 of NONE => NONE | SOME (bits, r2) =>
         SOME (PSimplex <| complex := cx ; vmask := bits |>, r2))
    else if tag = 17 then
      (case rdLE 4 r0 of NONE => NONE | SOME (so, r1) =>
       case lookSimplex tbl so of NONE => NONE | SOME sx =>
       case rdBitset sx.complex.nVertices r1 of NONE => NONE
       | SOME (bits, r2) =>
         SOME (PExtSet <| simplex := sx ; emask := bits |>, r2))
    else if tag = 32 then
      (case rdU8 r0 of NONE => NONE | SOME (bb, r1) =>
       case bowtieOf bb of NONE => NONE | SOME b =>
       case rdLE 4 r1 of NONE => NONE | SOME (l, r2) =>
       case rdLE 4 r2 of NONE => NONE | SOME (rr, r3) =>
       case lookTerm tbl l of NONE => NONE | SOME tl =>
       case lookTerm tbl rr of NONE => NONE | SOME tr =>
         SOME (PFormula (FwAtom b tl tr), r3))
    else if tag = 33 then
      (case rdLE 4 r0 of NONE => NONE | SOME (t, r1) =>
       case rdLE 4 r1 of NONE => NONE | SOME (so, r2) =>
       case rdLE 4 r2 of NONE => NONE | SOME (eo, r3) =>
       case lookTerm tbl t of NONE => NONE | SOME tt =>
       case lookSimplex tbl so of NONE => NONE | SOME sx =>
       case lookExtSet tbl eo of NONE => NONE | SOME es =>
         SOME (PFormula (FwInRegion tt sx es), r3))
    else if tag = 34 ∨ tag = 35 then
      (case rdLE 4 r0 of NONE => NONE | SOME (l, r1) =>
       case rdLE 4 r1 of NONE => NONE | SOME (rr, r2) =>
       case lookFormula tbl l of NONE => NONE | SOME fl =>
       case lookFormula tbl rr of NONE => NONE | SOME fr =>
         SOME (PFormula (if tag = 34 then FwAnd fl fr else FwOr fl fr), r2))
    else if tag = 36 then SOME (PFormula FwTt, r0)
    else if tag = 37 then SOME (PFormula FwFf, r0)
    else if tag = 38 then SOME (PFormula FwSpH, r0)
    else if tag = 48 then
      (case rdLE 4 r0 of NONE => NONE | SOME (pre, r1) =>
       case rdLE 4 r1 of NONE => NONE | SOME (post, r2) =>
       case lookFormula tbl pre of NONE => NONE | SOME prew =>
       case lookFormula tbl post of NONE => NONE | SOME postw =>
       if fwNoSph postw then SOME (PJudg prew postw, r2) else NONE)
    else NONE
End

Definition poolPass_def:
  poolPass (0:num) (cxs:simpc list) (pos:num) (xs:num list)
           (tbl:(num # poolobj) list) =
    (if NULL xs then SOME tbl else NONE) ∧
  poolPass (SUC f) cxs pos xs tbl =
    if NULL xs then SOME tbl else
    case parsePoolRec cxs tbl xs of NONE => NONE
    | SOME (ob, xs') =>

        if LENGTH xs < LENGTH xs' then NONE else
        poolPass f cxs (pos + (LENGTH xs − LENGTH xs')) xs'
                 ((pos, ob)::tbl)
End

Datatype:
  cnode = CnAx
        | CnWeaken certpf formula
        | CnCut formula certpf certpf
        | CnAndI certpf certpf
        | CnAndEL certpf formula
        | CnAndER certpf formula
        | CnOrIL certpf formula
        | CnOrIR certpf formula
        | CnOrE certpf certpf conjpath
        | CnEqElim certpf certpf num term term formula
        | CnConvIntro certpf term simplex extensionset
        | CnConvElim certpf term simplex extensionset
        | CnArithFold certpf term term bowtie
        | CnArithUnfold certpf term term bowtie
        | CnBernCone certpf term simplex extensionset num term formula
        | CnNorm term term
        | CnFarkas term term num
        | CnEqRefl term
        | CnEqSym certpf term term
        | CnPromise certpf certpf formula conjpath (num list)
        | CnSyzygy (certpf list) term term num (rat option) ;
  certpf = CertPf sequent cnode
End

Definition certConcl_def:
  certConcl (CertPf s n) = s
End

Definition stepsToPath_def:
  stepsToPath ([]:num list) = CPHere ∧
  stepsToPath (s::ss) =
    if s = (0:num) then CPLeft (stepsToPath ss) else CPRight (stepsToPath ss)
End

Definition judgSeq_def:
  judgSeq (sp:formula) (prew:fwire) (postw:fwire) =
    <| pre := expandSph sp prew ; post := expandSph sp postw |>
End

Definition lookNodePf_def:
  lookNodePf (tbl:(num # (certpf # fwire)) list) (off:num) =
    case ALOOKUP tbl off of SOME (pf, prew) => SOME pf | _ => NONE
End

Definition parseNode_def:
  parseNode (ptbl:(num # poolobj) list)
            (tbl:(num # (certpf # fwire)) list) (xs:num list) =
    case rdU8 xs of NONE => NONE | SOME (tag, r0) =>
    case rdU8 r0 of NONE => NONE | SOME (var, r1) =>
    case rdLE 2 r1 of NONE => NONE | SOME (resv, r2) =>
    if resv ≠ (0:num) then NONE else
    case rdLE 4 r2 of NONE => NONE | SOME (cj, r3) =>
    case lookJudg ptbl cj of NONE => NONE | SOME (prew, postw) =>
    let sq = judgSeq FTt prew postw in
    if tag = (0:num) then
      (if var ≠ (0:num) then NONE else SOME (CertPf sq CnAx, prew, r3))
    else if tag = 1 then
      (if var ≠ 0 then NONE else
       case rdLE 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLE 4 r4 of NONE => NONE | SOME (ex, r5) =>
       case lookNodePf tbl pr of NONE => NONE | SOME p =>
       case lookFormula ptbl ex of NONE => NONE | SOME exw =>
         SOME (CertPf sq (CnWeaken p (expandSph FTt exw)), prew, r5))
    else if tag = 2 then
      (if var ≠ 0 then NONE else
       case rdLE 4 r3 of NONE => NONE | SOME (cutf, r4) =>
       case rdLE 8 r4 of NONE => NONE | SOME (lo, r5) =>
       case rdLE 8 r5 of NONE => NONE | SOME (ro, r6) =>
       case lookFormula ptbl cutf of NONE => NONE | SOME cfw =>
       case lookNodePf tbl lo of NONE => NONE | SOME lp =>
       case lookNodePf tbl ro of NONE => NONE | SOME rp =>
         SOME (CertPf sq (CnCut (expandSph FTt cfw) lp rp), prew, r6))
    else if tag = 3 then
      (if var ≠ 0 then NONE else
       case rdLE 8 r3 of NONE => NONE | SOME (lo, r4) =>
       case rdLE 8 r4 of NONE => NONE | SOME (ro, r5) =>
       case lookNodePf tbl lo of NONE => NONE | SOME lp =>
       case lookNodePf tbl ro of NONE => NONE | SOME rp =>
         SOME (CertPf sq (CnAndI lp rp), prew, r5))
    else if tag = 4 ∨ tag = 5 then
      (if ¬(var = 0 ∨ var = 1) then NONE else
       case rdLE 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLE 4 r4 of NONE => NONE | SOME (ot, r5) =>
       case lookNodePf tbl pr of NONE => NONE | SOME p =>
       case lookFormula ptbl ot of NONE => NONE | SOME otw =>
       (let ow = expandSph FTt otw in
          SOME (CertPf sq
                  (if tag = 4 then
                     (if var = 0 then CnAndEL p ow else CnAndER p ow)
                   else
                     (if var = 0 then CnOrIL p ow else CnOrIR p ow)),
                prew, r5)))
    else if tag = 6 then
      (if var ≠ 0 then NONE else
       case rdLE 8 r3 of NONE => NONE | SOME (lo, r4) =>
       case rdLE 8 r4 of NONE => NONE | SOME (ro, r5) =>
       case rdLE 4 r5 of NONE => NONE | SOME (plen, r6) =>
       case takeN plen r6 of NONE => NONE | SOME (stps, r7) =>
       if ¬ EVERY (λs. s ≤ (1:num)) stps then NONE else
       case lookNodePf tbl lo of NONE => NONE | SOME lp =>
       case lookNodePf tbl ro of NONE => NONE | SOME rp =>
         SOME (CertPf sq (CnOrE lp rp (stepsToPath stps)), prew, r7))
    else if tag = 7 then
      (if var ≠ 0 then NONE else
       case rdLE 8 r3 of NONE => NONE | SOME (eo, r4) =>
       case rdLE 8 r4 of NONE => NONE | SOME (bo, r5) =>
       case rdLE 4 r5 of NONE => NONE | SOME (w, r6) =>
       case rdLE 4 r6 of NONE => NONE | SOME (tt0, r7) =>
       case rdLE 4 r7 of NONE => NONE | SOME (tu, r8) =>
       case rdLE 4 r8 of NONE => NONE | SOME (bf, r9) =>
       case lookNodePf tbl eo of NONE => NONE | SOME ep =>
       case lookNodePf tbl bo of NONE => NONE | SOME bp =>
       case lookTerm ptbl tt0 of NONE => NONE | SOME tT =>
       case lookTerm ptbl tu of NONE => NONE | SOME tU =>
       case lookFormula ptbl bf of NONE => NONE | SOME bfw =>
         SOME (CertPf sq (CnEqElim ep bp w tT tU (expandSph FTt bfw)),
               prew, r9))
    else if tag = 8 ∨ tag = 9 then
      (if var ≠ 0 then NONE else
       case rdLE 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLE 4 r4 of NONE => NONE | SOME (t, r5) =>
       case rdLE 4 r5 of NONE => NONE | SOME (so, r6) =>
       case rdLE 4 r6 of NONE => NONE | SOME (eo, r7) =>
       case lookNodePf tbl pr of NONE => NONE | SOME p =>
       case lookTerm ptbl t of NONE => NONE | SOME tt =>
       case lookSimplex ptbl so of NONE => NONE | SOME sx =>
       case lookExtSet ptbl eo of NONE => NONE | SOME es =>
         SOME (CertPf sq
                 (if tag = 8 then CnConvIntro p tt sx es
                  else CnConvElim p tt sx es), prew, r7))
    else if tag = 10 then
      (if ¬(var = 0 ∨ var = 1) then NONE else
       case rdLE 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLE 4 r4 of NONE => NONE | SOME (l, r5) =>
       case rdLE 4 r5 of NONE => NONE | SOME (rr, r6) =>
       case rdU8 r6 of NONE => NONE | SOME (bb, r7) =>
       if (4:num) < bb then NONE else
       case takeN 3 r7 of NONE => NONE | SOME (pad, r8) =>
       if ¬ EVERY (λb. b = (0:num)) pad then NONE else
       case bowtieOf bb of NONE => NONE | SOME b =>
       case lookNodePf tbl pr of NONE => NONE | SOME p =>
       case lookTerm ptbl l of NONE => NONE | SOME tl =>
       case lookTerm ptbl rr of NONE => NONE | SOME tr =>
         SOME (CertPf sq
                 (if var = 0 then CnArithFold p tl tr b
                  else CnArithUnfold p tl tr b), prew, r8))
    else if tag = 11 then
      (if var ≠ 0 then NONE else
       case rdLE 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLE 4 r4 of NONE => NONE | SOME (tx, r5) =>
       case rdLE 4 r5 of NONE => NONE | SOME (so, r6) =>
       case rdLE 4 r6 of NONE => NONE | SOME (eo, r7) =>
       case rdLE 4 r7 of NONE => NONE | SOME (deg, r8) =>
       case rdLE 4 r8 of NONE => NONE | SOME (po, r9) =>
       case rdLE 4 r9 of NONE => NONE | SOME (pd, r10) =>
       case lookNodePf tbl pr of NONE => NONE | SOME p =>
       case lookTerm ptbl tx of NONE => NONE | SOME tX =>
       case lookSimplex ptbl so of NONE => NONE | SOME sx =>
       case lookExtSet ptbl eo of NONE => NONE | SOME es =>
       case lookTerm ptbl po of NONE => NONE | SOME poly =>
       case lookFormula ptbl pd of NONE => NONE | SOME pdw =>
         SOME (CertPf sq
                 (CnBernCone p tX sx es deg poly (expandSph FTt pdw)),
               prew, r10))
    else if tag = 12 then
      (if var ≠ 0 then NONE else
       case rdLE 4 r3 of NONE => NONE | SOME (l, r4) =>
       case rdLE 4 r4 of NONE => NONE | SOME (rr, r5) =>
       case lookTerm ptbl l of NONE => NONE | SOME tl =>
       case lookTerm ptbl rr of NONE => NONE | SOME tr =>
         SOME (CertPf sq (CnNorm tl tr), prew, r5))
    else if tag = 14 then
      (if var ≠ 0 then NONE else
       case rdLE 4 r3 of NONE => NONE | SOME (cc, r4) =>
       case rdLE 4 r4 of NONE => NONE | SOME (co, r5) =>
       case rdLE 8 r5 of NONE => NONE | SOME (dbl, r6) =>
       case lookTerm ptbl cc of NONE => NONE | SOME ccT =>
       case lookTerm ptbl co of NONE => NONE | SOME coT =>
         SOME (CertPf sq (CnFarkas ccT coT dbl), prew, r6))
    else if tag = 23 then
      (if var ≠ 0 then NONE else
       case rdLE 4 r3 of NONE => NONE | SOME (t, r4) =>
       case lookTerm ptbl t of NONE => NONE | SOME tt =>
         SOME (CertPf sq (CnEqRefl tt), prew, r4))
    else if tag = 24 then
      (if var ≠ 0 then NONE else
       case rdLE 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLE 4 r4 of NONE => NONE | SOME (tt0, r5) =>
       case rdLE 4 r5 of NONE => NONE | SOME (tu, r6) =>
       case lookNodePf tbl pr of NONE => NONE | SOME p =>
       case lookTerm ptbl tt0 of NONE => NONE | SOME tT =>
       case lookTerm ptbl tu of NONE => NONE | SOME tU =>
         SOME (CertPf sq (CnEqSym p tT tU), prew, r6))
    else if tag = 25 then
      (if var ≠ 0 then NONE else
       case rdLE 8 r3 of NONE => NONE | SOME (so, r4) =>
       case rdLE 8 r4 of NONE => NONE | SOME (co, r5) =>
       case rdLE 4 r5 of NONE => NONE | SOME (ct, r6) =>
       case rdLE 4 r6 of NONE => NONE | SOME (plen, r7) =>
       case takeN plen r7 of NONE => NONE | SOME (stps, r8) =>
       if ¬ EVERY (λs. s ≤ (1:num)) stps then NONE else
       case rdLE 4 r8 of NONE => NONE | SOME (ilen, r9) =>
       case rdLEsN 4 ilen r9 of NONE => NONE | SOME (iface, r10) =>
       case lookNodePf tbl so of NONE => NONE | SOME sp =>
       case lookNodePf tbl co of NONE => NONE | SOME cp =>
       case lookFormula ptbl ct of NONE => NONE | SOME ctw =>
         SOME (CertPf sq
                 (CnPromise sp cp (expandSph FTt ctw)
                            (stepsToPath stps) iface), prew, r10))
    else if tag = 26 then
      (if var ≠ 0 then NONE else
       case rdLE 4 r3 of NONE => NONE | SOME (ncomp, r4) =>
       case rdLEsN 8 ncomp r4 of NONE => NONE | SOME (coffs, r5) =>
       case rdLE 4 r5 of NONE => NONE | SOME (cc, r6) =>
       case rdLE 4 r6 of NONE => NONE | SOME (co, r7) =>
       case rdLE 8 r7 of NONE => NONE | SOME (dbl, r8) =>
       case rdLE 4 r8 of NONE => NONE | SOME (th, r9) =>
       case optSeq (MAP (lookNodePf tbl) coffs) of NONE => NONE
       | SOME comps =>
       case lookTerm ptbl cc of NONE => NONE | SOME ccT =>
       case lookTerm ptbl co of NONE => NONE | SOME coT =>
       if th = (4294967295:num) then
         SOME (CertPf sq (CnSyzygy comps ccT coT dbl NONE), prew, r9)
       else
         (case lookTerm ptbl th of
          | SOME (TmConst q) =>
              SOME (CertPf sq (CnSyzygy comps ccT coT dbl (SOME q)),
                    prew, r9)
          | _ => NONE))
    else NONE
End

Definition nodePass_def:
  nodePass (0:num) (ptbl:(num # poolobj) list) (pos:num) (xs:num list)
           (tbl:(num # (certpf # fwire)) list) (cnt:num) =
    (if NULL xs then SOME (tbl, cnt) else NONE) ∧
  nodePass (SUC f) ptbl pos xs tbl cnt =
    if NULL xs then SOME (tbl, cnt) else
    case parseNode ptbl tbl xs of NONE => NONE
    | SOME (pf, prew, xs') =>

        if LENGTH xs < LENGTH xs' then NONE else
        nodePass f ptbl (pos + (LENGTH xs − LENGTH xs')) xs'
                 ((pos, (pf, prew))::tbl) (cnt + 1)
End

Definition rootShapeOK_def:
  rootShapeOK (FwAnd phi FwSpH) = T ∧
  rootShapeOK (fw:fwire) = F
End

Definition parseProofSection_def:
  parseProofSection (sec:num list) (cxs:simpc list) (hnn:num)
                    (rootOff:num) (thetaRef:num) =
    case rdLE 8 sec of NONE => NONE | SOME (plen, xs1) =>
    case takeN plen xs1 of NONE => NONE | SOME (poolbytes, nodebytes) =>
    case poolPass (SUC (LENGTH poolbytes)) cxs 0 poolbytes [] of
    | NONE => NONE
    | SOME ptbl =>

    if ¬(thetaRef = (4294967295:num) ∨
         (case lookTerm ptbl thetaRef of
          | SOME (TmConst q) => T
          | _ => F)) then NONE else
    case nodePass (SUC (LENGTH nodebytes)) ptbl (8 + plen) nodebytes [] 0 of
    | NONE => NONE
    | SOME (ntbl, cnt) =>
    if cnt ≠ hnn then NONE else
    case ALOOKUP ntbl rootOff of
    | NONE => NONE
    | SOME (rootpf, rootprew) =>
        if rootShapeOK rootprew then SOME rootpf else NONE
End

Definition parseCert_def:
  parseCert (bytes:num list) =
    case parseHeader bytes of NONE => NONE | SOME h =>
    case parseSymtab (TAKE h.symLen (DROP h.symOff bytes)) h.symLen
                     h.nWires h.payOff h.payLen of
    | NONE => NONE
    | SOME ws =>
    case parseDiagram (TAKE h.diaLen (DROP h.diaOff bytes)) h.nCxs h.nApps of
    | NONE => NONE
    | SOME cxs =>
    case parseProofSection (TAKE h.prfLen (DROP h.prfOff bytes)) cxs
                           h.nNodes h.rootOff h.thetaRef of
    | NONE => NONE
    | SOME pf => SOME (ws, pf)
End

Definition wireTy_def:
  wireTy (ws:tensortype list) (w:num) = oEL w ws
End

Definition bshapeJoin_def:
  bshapeJoin (s1o:shape option) (s2o:shape option) =
    case s1o of NONE => NONE
    | SOME s1 =>
      case s2o of NONE => NONE
      | SOME s2 =>
        if s1 = s2 then SOME s1
        else if s1 = [] then SOME s2
        else if s2 = [] then SOME s1
        else NONE
End

Definition termBshape_def:
  termBshape (ws:tensortype list) (TmVar w) =
    (case wireTy ws w of NONE => NONE | SOME ty => SOME ty.shape) ∧
  termBshape ws (TmConst c) = SOME ([]:shape) ∧
  termBshape ws (TmAdd l r) =
    bshapeJoin (termBshape ws l) (termBshape ws r) ∧
  termBshape ws (TmMul l r) =
    bshapeJoin (termBshape ws l) (termBshape ws r) ∧
  termBshape ws (TmSub l r) =
    bshapeJoin (termBshape ws l) (termBshape ws r) ∧
  termBshape ws (TmNeg t) = termBshape ws t ∧
  termBshape ws (TmIdx t i) =
    (case termBshape ws t of
     | SOME [e] => if i < e then SOME ([]:shape) else NONE
     | _ => NONE)
End

Definition finWiresB_def:
  finWiresB (ws:tensortype list) (t:term) =
    EVERY (λw. case wireTy ws w of
               | SOME ty => ty.dtype.ext = ExtFin
               | NONE => F)
          (termFreeWires t)
End

Definition wirePosB_def:
  wirePosB (ws:tensortype list) (w:num) =
    case wireTy ws w of
    | SOME ty => 0 < shapeTotalSize ty.shape
    | NONE => F
End

Definition wiresPosB_def:
  wiresPosB (ws:tensortype list) (l:num list) = EVERY (wirePosB ws) l
End

Definition premiseContainsB_def:
  premiseContainsB (pre:formula) (sub:formula) =
    EVERY (λa. MEM a (conjunctList pre)) (conjunctList sub)
End

Definition polyTieB_def:
  polyTieB (tX:term) (poly:term) =
    (termFreeWires poly = [] ∨
     case termVarHead tX of
     | SOME w => EVERY (λx. x = w) (termFreeWires poly)
     | NONE => F)
End

Definition checkPf1_def:
  (checkPf1 (ws:tensortype list) (INL (CertPf sq nd) : certpf + certpf list) =
     case nd of
     | CnAx => (sq.pre = sq.post)
     | CnWeaken p extra =>
         (checkPf1 ws (INL p) ∧
          let ps = certConcl p in
            sq.pre = FAnd ps.pre extra ∧ sq.post = ps.post)
     | CnCut cutf lp rp =>
         (checkPf1 ws (INL lp) ∧ checkPf1 ws (INL rp) ∧
          let ls = certConcl lp in
          let rs = certConcl rp in
            sq.pre = ls.pre ∧ sq.post = rs.post ∧
            ls.post = cutf ∧ rs.pre = FAnd ls.pre cutf)
     | CnAndI lp rp =>
         (checkPf1 ws (INL lp) ∧ checkPf1 ws (INL rp) ∧
          let ls = certConcl lp in
          let rs = certConcl rp in
            ls.pre = rs.pre ∧ sq.pre = ls.pre ∧
            sq.post = FAnd ls.post rs.post)
     | CnAndEL p other =>
         (checkPf1 ws (INL p) ∧
          let ps = certConcl p in
            sq.pre = ps.pre ∧ ps.post = FAnd sq.post other)
     | CnAndER p other =>
         (checkPf1 ws (INL p) ∧
          let ps = certConcl p in
            sq.pre = ps.pre ∧ ps.post = FAnd other sq.post)
     | CnOrIL p other =>
         (checkPf1 ws (INL p) ∧
          let ps = certConcl p in
            sq.pre = ps.pre ∧ sq.post = FOr ps.post other)
     | CnOrIR p other =>
         (checkPf1 ws (INL p) ∧
          let ps = certConcl p in
            sq.pre = ps.pre ∧ sq.post = FOr other ps.post)
     | CnOrE lp rp path =>
         (checkPf1 ws (INL lp) ∧ checkPf1 ws (INL rp) ∧
          let ls = certConcl lp in
          let rs = certConcl rp in
            case conjGet sq.pre path of
            | SOME (FOr d1 d2) =>
                (conjReplace sq.pre path d1 = SOME ls.pre ∧
                 conjReplace sq.pre path d2 = SOME rs.pre ∧
                 ls.post = sq.post ∧ rs.post = sq.post)
            | _ => F)
     | CnEqElim ep bp w tT tU bodyForm =>
         (checkPf1 ws (INL ep) ∧ checkPf1 ws (INL bp) ∧
          let es = certConcl ep in
          let bs = certConcl bp in
            sq.pre = es.pre ∧ es.pre = bs.pre ∧
            es.post = FAtom BowEq tT tU ∧
            termBshape ws tT = termBshape ws tU ∧
            IS_SOME (termBshape ws tT) ∧
            bs.post = formulaSubst w tT bodyForm ∧
            sq.post = formulaSubst w tU bodyForm)
     | CnConvIntro p t sx es =>
         (checkPf1 ws (INL p) ∧
          let ps = certConcl p in
            sq.pre = ps.pre ∧
            termBshape ws t = SOME [sx.complex.ambDim] ∧
            barycentricHalfspaceBuild t sx es = SOME ps.post ∧
            sq.post = FInRegion t sx es)
     | CnConvElim p t sx es =>
         (checkPf1 ws (INL p) ∧
          let ps = certConcl p in
            sq.pre = ps.pre ∧
            ps.post = FInRegion t sx es ∧
            barycentricHalfspaceBuild t sx es = SOME sq.post)
     | CnArithFold p tl tr b =>
         (checkPf1 ws (INL p) ∧ b ≠ BowNe ∧
          let ps = certConcl p in
            sq.pre = ps.pre ∧
            ps.post = FAtom b (TmSub tl tr) (TmConst 0) ∧
            sq.post = FAtom b tl tr)
     | CnArithUnfold p tl tr b =>
         (checkPf1 ws (INL p) ∧ b ≠ BowNe ∧
          let ps = certConcl p in
            sq.pre = ps.pre ∧
            ps.post = FAtom b tl tr ∧
            sq.post = FAtom b (TmSub tl tr) (TmConst 0))
     | CnBernCone p tX sx es deg poly pred =>
         (checkPf1 ws (INL p) ∧
          let ps = certConcl p in
            sq.pre = ps.pre ∧
            ps.post = FInRegion tX sx es ∧
            polyTieB tX poly ∧
            (if extIsEmptyB es then isConvexPredicateB pred
             else isConicPredicateB pred) ∧
            bernConeCoeffCheck sx es deg poly pred ∧
            sq.post = formulaSubst predicateHole poly pred)
     | CnNorm tl tr =>
         (polynomialCanonicalEqB tl tr ∧
          termBshape ws tl = termBshape ws tr ∧
          IS_SOME (termBshape ws tl) ∧
          finWiresB ws tl ∧ finWiresB ws tr ∧
          sq.post = FAtom BowEq tl tr)
     | CnFarkas cc concl dbl =>
         (IS_SOME (termBshape ws concl) ∧
          finWiresB ws concl ∧
          wiresPosB ws (formulaFreeWires sq.pre ++ termFreeWires concl) ∧
          farkasCheck cc sq.pre concl ∧
          sq.post = FAtom BowLe concl (TmConst 0))
     | CnEqRefl t =>
         (IS_SOME (termBshape ws t) ∧ finWiresB ws t ∧
          sq.post = FAtom BowEq t t)
     | CnEqSym p tT tU =>
         (checkPf1 ws (INL p) ∧
          let ps = certConcl p in
            sq.pre = ps.pre ∧
            ps.post = FAtom BowEq tT tU ∧
            sq.post = FAtom BowEq tU tT)
     | CnPromise sp cp contract path iface =>
         (checkPf1 ws (INL sp) ∧ checkPf1 ws (INL cp) ∧
          let ss = certConcl sp in
          let cs = certConcl cp in
            ss.post = contract ∧
            conjGet cs.pre path = SOME contract ∧
            conjReplace cs.pre path ss.pre = SOME sq.pre ∧
            sq.post = cs.post ∧
            (case conjReplace cs.pre path FTt of
             | SOME ctx =>
                 (EVERY (λw. MEM w iface) (formulaFreeWires contract) ∧
                  EVERY (λw. (MEM w (formulaFreeWires ctx) ∨
                              MEM w (formulaFreeWires sq.post)) ⇒
                             MEM w iface)
                        (formulaFreeWires ss.pre))
             | NONE => F))
     | CnSyzygy comps cc concl dbl th =>
         (checkPf1 ws (INR comps) ∧
          let cseqs = MAP certConcl comps in
            EVERY (λc. premiseContainsB sq.pre c.pre) cseqs ∧
            IS_SOME (termBshape ws concl) ∧
            finWiresB ws concl ∧
            wiresPosB ws (formulaFreeWires sq.pre ++ termFreeWires concl) ∧
            EVERY (λc. wiresPosB ws (formulaFreeWires c.post)) cseqs ∧
            syzygyCheck cc cseqs sq.pre concl ∧
            sq.post = FAtom BowLe concl (TmConst 0))) ∧
  (checkPf1 ws (INR ([]:certpf list)) = T) ∧
  (checkPf1 ws (INR (p::ps)) = (checkPf1 ws (INL p) ∧ checkPf1 ws (INR ps)))
Termination
  WF_REL_TAC ‘measure (λx. case SND x of
                           | INL pf => certpf_size pf
                           | INR ps => list_size certpf_size ps)’
  >> rw[fetch "-" "cnode_size_def", listTheory.list_size_def]
  >> simp[]
End

Definition checkPf_def:
  checkPf (ws:tensortype list) (pf:certpf) = checkPf1 ws (INL pf)
End

Definition qtslCheckBytes_def:
  qtslCheckBytes (cs:char list) =
    case parseCert (MAP ORD cs) of
    | NONE => F
    | SOME (ws, pf) => checkPf ws pf
End

Definition verified_string_def:
  verified_string = strlit "s BERNLGC VERIFIED v0\n"
End

Definition reject_string_def:
  reject_string = strlit "s BERNLGC REJECT\n"
End

Definition qtsl_verdict_def:
  qtsl_verdict (cs:char list) =
    if qtslCheckBytes cs then verified_string else reject_string
End

Definition consStep_def:
  consStep (c:char) (acc:char list) = c :: acc
End

Definition qtsl_verdict_rev_def:
  qtsl_verdict_rev (rcs:char list) = qtsl_verdict (REVERSE rcs)
End

Theorem foldl_consStep:
  ∀cs acc. mllist$foldl consStep acc cs = REVERSE cs ++ acc
Proof
  Induct >> rw[mllistTheory.foldl_def, consStep_def]
QED

Theorem verified_neq_reject:
  verified_string ≠ reject_string
Proof
  EVAL_TAC
QED

Theorem qtslCheckBytes_eq_parse:
  qtslCheckBytes cs ⇔
  ∃ws pf. parseCert (MAP ORD cs) = SOME (ws, pf) ∧ checkPf ws pf
Proof
  rw[qtslCheckBytes_def]
  >> Cases_on ‘parseCert (MAP ORD cs)’ >> simp[]
  >> Cases_on ‘x’ >> simp[]
QED

Theorem qtsl_verdict_verified:
  qtsl_verdict cs = verified_string ⇔ qtslCheckBytes cs
Proof
  rw[qtsl_verdict_def, verified_neq_reject]
QED
