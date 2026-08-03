(*
  readGeolog — the native geolog container reader in the verified-HOL
  world: magic/version framing, the prereq table, and per-commit
  envelope/body parsing, mirroring the normative container grammar.
  Fail-closed at every tier; the bytes that hash are the bytes in the
  file (length framing stays outside the hashed strings).
*)
Theory geolog_read

Ancestors
  arithmetic list rich_list option pair sorting string ASCIInumbers gcd

Definition leN_def:
  leN ([]:num list) = (0:num) /\
  leN (b::bs) = b + 256 * leN bs
End

Definition bytesAt_def:
  bytesAt (bs:num list) (off:num) (len:num) : num list option =
    if off + len <= LENGTH bs then SOME (TAKE len (DROP off bs)) else NONE
End

Definition rdLeAt_def:
  rdLeAt (bs:num list) (off:num) (len:num) : num option =
    case bytesAt bs off len of
    | NONE => NONE
    | SOME chunk => SOME (leN chunk)
End

Definition lexLt_def:
  lexLt ([]:num list) (ys:num list) = (ys <> []) /\
  lexLt (x::xs) [] = F /\
  lexLt (x::xs) (y::ys) = (x < y \/ (x = y /\ lexLt xs ys))
End

Definition lexLe_def:
  lexLe xs ys <=> lexLt xs ys \/ xs = ys
End

Definition strictAsc_def:
  strictAsc ([]:(num list) list) = T /\
  strictAsc [x] = T /\
  strictAsc (x::y::rest) = (lexLt x y /\ strictAsc (y::rest))
End

Definition sortedLexLe_def:
  sortedLexLe ([]:(num list) list) = T /\
  sortedLexLe [x] = T /\
  sortedLexLe (x::y::rest) = (lexLe x y /\ sortedLexLe (y::rest))
End

Definition rdUlebLoop_def:
  rdUlebLoop (bs:num list) (pos:num) (shift:num) (acc:num) (fuel:num)
             : (num # num) option =
    case fuel of
    | 0 => NONE
    | SUC f =>
      (case oEL pos bs of
       | NONE => NONE
       | SOME b =>
         if b < 128 then
           (if b = 0 /\ 0 < shift then NONE
            else
              let v = acc + b * 2 ** shift in
                if v < 18446744073709551616 then SOME (v, pos + 1)
                else NONE)
         else rdUlebLoop bs (pos + 1) (shift + 7)
                         (acc + (b - 128) * 2 ** shift) f)
End

Definition rdUleb_def:
  rdUleb (bs:num list) (pos:num) : (num # num) option =
    rdUlebLoop bs pos 0 0 10
End

Definition encUlebF_def:
  encUlebF (fuel:num) (v:num) : num list =
    case fuel of
    | 0 => []
    | SUC f => if v < 128 then [v]
               else (v MOD 128 + 128) :: encUlebF f (v DIV 128)
End

Definition encUleb_def:
  encUleb (v:num) : num list = encUlebF 10 v
End

Definition rdSlebFin_def:
  rdSlebFin (b:num) (shift:num) (acc:num) (pos:num)
            : (bool # num # num) option =
    let raw = acc + b * 2 ** shift in
    let nbits = shift + 7 in
      if (b DIV 64) MOD 2 = 1 then
        (let mag = 2 ** nbits - raw in
           if mag <= 9223372036854775808 then SOME (T, mag, pos + 1)
           else NONE)
      else
        (if raw < 9223372036854775808 then SOME (F, raw, pos + 1)
         else NONE)
End

Definition rdSlebLoop_def:
  rdSlebLoop (bs:num list) (pos:num) (shift:num) (acc:num)
             (prev:num option) (fuel:num) : (bool # num # num) option =
    case fuel of
    | 0 => NONE
    | SUC f =>
      (case oEL pos bs of
       | NONE => NONE
       | SOME b =>
         if b < 128 then
           (case prev of
            | SOME pb =>
                if (b = 0 /\ (pb DIV 64) MOD 2 = 0) \/
                   (b = 127 /\ (pb DIV 64) MOD 2 = 1)
                then NONE
                else rdSlebFin b shift acc pos
            | NONE => rdSlebFin b shift acc pos)
         else rdSlebLoop bs (pos + 1) (shift + 7)
                         (acc + (b - 128) * 2 ** shift) (SOME b) f)
End

Definition rdSleb_def:
  rdSleb (bs:num list) (pos:num) : (bool # num # num) option =
    rdSlebLoop bs pos 0 0 NONE 10
End

Definition encSlebPosF_def:
  encSlebPosF (fuel:num) (v:num) : num list =
    case fuel of
    | 0 => []
    | SUC f =>
        let g = v MOD 128 in
        let rest = v DIV 128 in
          if rest = 0 /\ g < 64 then [g]
          else (g + 128) :: encSlebPosF f rest
End

Definition encSlebPos_def:
  encSlebPos (v:num) : num list = encSlebPosF 10 v
End

Definition encSlebNegF_def:
  encSlebNegF (fuel:num) (m:num) : num list =
    case fuel of
    | 0 => []
    | SUC f =>
        let g = (128 - m MOD 128) MOD 128 in
        let rest = (m + 127) DIV 128 in
          if rest = 1 /\ 64 <= g then [g]
          else if rest = 0 then [g]
          else (g + 128) :: encSlebNegF f rest
End

Definition encSlebNeg_def:
  encSlebNeg (m:num) : num list = encSlebNegF 10 m
End

Datatype:
  hexrun = HRep num 'a | HLit ('a list)
End

Definition runCount_def:
  runCount (HRep n (v:'a)) = n /\
  runCount (HLit vs) = LENGTH vs
End

Definition rdHexU64_def:
  rdHexU64 (bs:num list) (pos:num) : (num # num) option = rdUleb bs pos
End

Definition rdHexBytes_def:
  rdHexBytes (bs:num list) (pos:num) : (num list # num) option =
    case rdUleb bs pos of
    | NONE => NONE
    | SOME (len, p1) =>
        (case bytesAt bs p1 len of
         | NONE => NONE
         | SOME chunk => SOME (chunk, p1 + len))
End

Definition rdHexValsKA_def:
  rdHexValsKA (rd:num list -> num -> ('a # num) option)
              (bs:num list) (pos:num) (k:num) (acc:'a list)
              : ('a list # num) option =
    case k of
    | 0 => SOME (REVERSE acc, pos)
    | SUC k' =>
      (case rd bs pos of
       | NONE => NONE
       | SOME (v, p1) => rdHexValsKA rd bs p1 k' (v::acc))
End

Definition rdHexValsK_def:
  rdHexValsK (rd:num list -> num -> ('a # num) option)
             (bs:num list) (pos:num) (k:num)
             : ('a list # num) option =
    rdHexValsKA rd bs pos k []
End

Definition rdHexRunsF_def:
  rdHexRunsF (rd:num list -> num -> ('a # num) option)
             (bs:num list) (pos:num) (fuel:num) (acc:('a hexrun) list)
             : (('a hexrun) list) option =
    case fuel of
    | 0 => (if LENGTH bs <= pos then SOME (REVERSE acc) else NONE)
    | SUC f =>
      if LENGTH bs <= pos then SOME (REVERSE acc)
      else
        (case rdSleb bs pos of
         | NONE => NONE
         | SOME (neg, mag, p1) =>
             if neg then
               (if LENGTH bs < p1 + mag then NONE
                else
                  case rdHexValsK rd bs p1 mag of
                  | NONE => NONE
                  | SOME (vs, p2) => rdHexRunsF rd bs p2 f (HLit vs::acc))
             else
               if mag = 0 then NONE
               else
                 (case rd bs p1 of
                  | NONE => NONE
                  | SOME (v, p2) =>
                      rdHexRunsF rd bs p2 f (HRep mag v::acc)))
End

Definition rdHexRuns_def:
  rdHexRuns rd (bs:num list) : (('a hexrun) list) option =
    rdHexRunsF rd bs 0 (LENGTH bs) []
End

Definition hexClaim_def:
  hexClaim (runs:('a hexrun) list) : num = SUM (MAP runCount runs)
End

Definition hexExpand_def:
  hexExpand ([]:('a hexrun) list) : 'a list = [] /\
  hexExpand (r::rest) =
    (case r of
     | HRep n v => REPLICATE n v
     | HLit vs => vs) ++ hexExpand rest
End

Definition groupRunsA_def:
  groupRunsA (xs:'a list) (cur:'a) (cnt:num) (acc:('a # num) list)
             : ('a # num) list =
    case xs of
    | [] => REVERSE ((cur, cnt)::acc)
    | (v::vs) => if v = cur then groupRunsA vs cur (cnt + 1) acc
                 else groupRunsA vs v 1 ((cur, cnt)::acc)
End

Definition groupRuns_def:
  groupRuns ([]:'a list) : ('a # num) list = [] /\
  groupRuns (v::vs) = groupRunsA vs v 1 []
End

Definition flushLit_def:
  flushLit (enc:'a -> num list) (pend:'a list) : num list =
    if pend = [] then []
    else encSlebNeg (LENGTH pend) ++ FLAT (MAP enc pend)
End

Definition emitRuns_def:
  emitRuns (enc:'a -> num list) ([]:('a # num) list) (pend:'a list)
           : num list = flushLit enc pend /\
  emitRuns enc ((v, n)::rest) pend =
    if n = 1 then emitRuns enc rest (pend ++ [v])
    else flushLit enc pend ++ encSlebPos n ++ enc v ++ emitRuns enc rest []
End

Definition hexSave_def:
  hexSave (enc:'a -> num list) (vals:'a list) : num list =
    emitRuns enc (groupRuns vals) []
End

Definition encHexU64_def:
  encHexU64 (v:num) : num list = encUleb v
End

Definition encHexBytes_def:
  encHexBytes (b:num list) : num list = encUleb (LENGTH b) ++ b
End

Definition MAX_BODY_OPS_def:
  MAX_BODY_OPS = (1048576:num)
End

Definition readCol_def:
  readCol (rd:num list -> num -> ('a # num) option)
          (enc:'a -> num list) (bs:num list) : ('a list) option =
    case rdHexRuns rd bs of
    | NONE => NONE
    | SOME runs =>
        if MAX_BODY_OPS < hexClaim runs then NONE
        else
          let vals = hexExpand runs in
            if hexSave enc vals = bs then SOME vals else NONE
End

Definition readU64Col_def:
  readU64Col bs = readCol rdHexU64 encHexU64 bs
End

Definition readBytesCol_def:
  readBytesCol bs = readCol rdHexBytes encHexBytes bs
End

Definition contB_def:
  contB (b:num) <=> 128 <= b /\ b < 192
End

Definition utf8Ok_def:
  utf8Ok (bs:num list) =
    case bs of
    | [] => T
    | (b::rest) =>
      if b < 128 then utf8Ok rest
      else if b < 194 then F
      else if b < 224 then
        (case rest of
         | (b1::rest') => contB b1 /\ utf8Ok rest'
         | _ => F)
      else if b < 240 then
        (case rest of
         | (b1::b2::rest') =>
             contB b1 /\ contB b2 /\
             (b = 224 ==> 160 <= b1) /\
             (b = 237 ==> b1 < 160) /\
             utf8Ok rest'
         | _ => F)
      else if b < 245 then
        (case rest of
         | (b1::b2::b3::rest') =>
             contB b1 /\ contB b2 /\ contB b3 /\
             (b = 240 ==> 144 <= b1) /\
             (b = 244 ==> b1 < 144) /\
             utf8Ok rest'
         | _ => F)
      else F
Termination
  WF_REL_TAC `measure LENGTH` >> rw[]
End

Definition MAJ_UINT_def:
  MAJ_UINT = (0:num)
End

Definition MAJ_BYTES_def:
  MAJ_BYTES = (2:num)
End

Definition MAJ_TEXT_def:
  MAJ_TEXT = (3:num)
End

Definition MAJ_ARRAY_def:
  MAJ_ARRAY = (4:num)
End

Definition MAJ_MAP_def:
  MAJ_MAP = (5:num)
End

Definition peekMajor_def:
  peekMajor (bs:num list) (pos:num) : num option =
    case oEL pos bs of
    | NONE => NONE
    | SOME b => SOME (b DIV 32)
End

Definition rdHead_def:
  rdHead (bs:num list) (pos:num) (m:num) : (num # num) option =
    case oEL pos bs of
    | NONE => NONE
    | SOME ib =>
      if ib DIV 32 <> m then NONE
      else
        let ai = ib MOD 32 in
          if ai < 24 then SOME (ai, pos + 1)
          else if ai = 24 then
            (case oEL (pos + 1) bs of
             | NONE => NONE
             | SOME v => if v < 24 then NONE else SOME (v, pos + 2))
          else if ai = 25 then
            (case bytesAt bs (pos + 1) 2 of
             | SOME [b1; b0] =>
                 (let v = b1 * 256 + b0 in
                    if v <= 255 then NONE else SOME (v, pos + 3))
             | _ => NONE)
          else if ai = 26 then
            (case bytesAt bs (pos + 1) 4 of
             | SOME [b3; b2; b1; b0] =>
                 (let v = ((b3 * 256 + b2) * 256 + b1) * 256 + b0 in
                    if v <= 65535 then NONE else SOME (v, pos + 5))
             | _ => NONE)
          else if ai = 27 then
            (case bytesAt bs (pos + 1) 8 of
             | SOME [b7; b6; b5; b4; b3; b2; b1; b0] =>
                 (let v = ((((((b7 * 256 + b6) * 256 + b5) * 256 + b4) *
                             256 + b3) * 256 + b2) * 256 + b1) * 256
                          + b0 in
                    if v <= 4294967295 then NONE else SOME (v, pos + 9))
             | _ => NONE)
          else NONE
End

Definition rdUintC_def:
  rdUintC bs pos = rdHead bs pos MAJ_UINT
End

Definition rdBstrC_def:
  rdBstrC (bs:num list) (pos:num) : (num list # num) option =
    case rdHead bs pos MAJ_BYTES of
    | NONE => NONE
    | SOME (len, p1) =>
        (case bytesAt bs p1 len of
         | NONE => NONE
         | SOME chunk => SOME (chunk, p1 + len))
End

Definition rdArrC_def:
  rdArrC bs pos = rdHead bs pos MAJ_ARRAY
End

Definition rdMapC_def:
  rdMapC bs pos = rdHead bs pos MAJ_MAP
End

Definition minLeU_def:
  minLeU (b:num list) <=>
    b <> [] /\ (LENGTH b = 1 \/ LAST b <> 0)
End

Definition minLeS_def:
  minLeS (b:num list) <=>
    b <> [] /\
    (LENGTH b = 1 \/
     ~((LAST b = 0 /\ (EL (LENGTH b - 2) b) DIV 128 = 0) \/
       (LAST b = 255 /\ (EL (LENGTH b - 2) b) DIV 128 = 1)))
End

Definition sgnMagLe_def:
  sgnMagLe (b:num list) : num =
    let v = leN b in
    let n = LENGTH b in
      if b <> [] /\ (LAST b) DIV 128 = 1 then 2 ** (8 * n) - v else v
End

Definition GEOLOG_BLOB_INLINE_MAX_def:
  GEOLOG_BLOB_INLINE_MAX = (4096:num)
End

Definition qShape_def:
  qShape (p:num list) : (num list # num list) option =
    case rdUleb p 0 of
    | NONE => NONE
    | SOME (nlen, pos) =>
        if LENGTH p < pos + nlen then NONE
        else
          let num_ = TAKE nlen (DROP pos p) in
          let den_ = DROP (pos + nlen) p in
            if nlen = 0 \/ den_ = [] then NONE
            else SOME (num_, den_)
End

Definition litQOk_def:
  litQOk (p:num list) <=>
    case qShape p of
    | NONE => F
    | SOME (num_, den_) =>
        minLeS num_ /\ minLeU den_ /\ leN den_ <> 0 /\
        gcd (sgnMagLe num_) (leN den_) = 1
End

Definition litEnnRatOk_def:
  litEnnRatOk (p:num list) <=>
    case qShape p of
    | NONE => F
    | SOME (num_, den_) =>
        minLeU num_ /\ minLeU den_ /\
        (if leN den_ = 0 then leN num_ = 1
         else gcd (leN num_) (leN den_) = 1)
End

Definition litShapeOk_def:
  litShapeOk (p:num list) <=>
    case rdUleb p 0 of
    | NONE => F
    | SOME (cnt, pos0) =>
        if LENGTH p < pos0 + cnt then F
        else
          (case rdHexValsK (\bs pos. rdUleb bs pos) p pos0 cnt of
           | NONE => F
           | SOME (vs, pend) => pend = LENGTH p)
End

Definition litTensorOk_def:
  litTensorOk (p:num list) <=>
    LENGTH p = 34 /\ oEL 0 p = SOME 30 /\ oEL 1 p = SOME 32
End

Definition litBlobRefOk_def:
  litBlobRefOk (p:num list) <=>
    LENGTH p = 35 /\ (oEL 0 p = SOME 12 \/ oEL 0 p = SOME 4) /\
    oEL 1 p = SOME 30 /\ oEL 2 p = SOME 32
End

Definition litPeerIdOk_def:
  litPeerIdOk (p:num list) <=>
    LENGTH p <= 64 /\
    (case rdUleb p 0 of
     | NONE => F
     | SOME (code, p1) =>
       (case rdUleb p p1 of
        | NONE => F
        | SOME (len, p2) =>
            LENGTH p = p2 + len /\
            (if code = 0 then len <= 42
             else if code = 18 then len = 32
             else F)))
End

Definition litOk_def:
  litOk (code:num) (p:num list) <=>
    if code = 0 then litQOk p
    else if code = 1 then minLeS p /\ LENGTH p <= 8
    else if code = 2 then minLeU p /\ LENGTH p <= 8
    else if code = 3 then p = [0] \/ p = [1]
    else if code = 4 then LENGTH p <= GEOLOG_BLOB_INLINE_MAX /\ utf8Ok p
    else if code = 5 then litEnnRatOk p
    else if code = 6 then minLeS p
    else if code = 7 then minLeU p
    else if code = 8 then litShapeOk p
    else if code = 9 then minLeU p /\ LENGTH p <= 8
    else if code = 10 then litTensorOk p
    else if code = 11 then minLeS p /\ LENGTH p <= 8
    else if code = 12 then LENGTH p <= GEOLOG_BLOB_INLINE_MAX
    else if code = 13 then litBlobRefOk p
    else if code = 14 then litPeerIdOk p
    else F
End

Definition MAX_DEP_INDEX_def:
  MAX_DEP_INDEX = (65534:num)
End

Datatype:
  elemref = ERLocal num | ERExt num num
End

Datatype:
  gvalue = GVRef elemref
         | GVLit num (num list)
         | GVCommitId num
         | GVExt num (num list)
         | GVAbs num (num list)
End

Definition rdElemRef_def:
  rdElemRef (bs:num list) (pos:num) : (elemref # num) option =
    case peekMajor bs pos of
    | NONE => NONE
    | SOME m =>
      if m = MAJ_BYTES then
        (case rdBstrC bs pos of
         | NONE => NONE
         | SOME (b, p1) =>
             if LENGTH b = 36 then NONE
             else if LENGTH b < 2 \/ 7 < LENGTH b then NONE
             else
               (case rdUleb b 0 of
                | NONE => NONE
                | SOME (dep, dpos) =>
                    if MAX_DEP_INDEX < dep then NONE
                    else
                      let ctr = DROP dpos b in
                        if minLeU ctr /\ LENGTH ctr <= 8 /\
                           leN ctr <= 4294967295
                        then SOME (ERExt dep (leN ctr), p1)
                        else NONE))
      else if m = MAJ_UINT then
        (case rdUintC bs pos of
         | NONE => NONE
         | SOME (n, p1) =>
             if 4294967295 < n then NONE else SOME (ERLocal n, p1))
      else NONE
End

Definition rdValue_def:
  rdValue (bs:num list) (pos:num) : (gvalue # num) option =
    case peekMajor bs pos of
    | NONE => NONE
    | SOME m =>
      if m = MAJ_BYTES \/ m = MAJ_UINT then
        (case rdElemRef bs pos of
         | NONE => NONE
         | SOME (r, p1) => SOME (GVRef r, p1))
      else if m = MAJ_ARRAY then
        (case rdArrC bs pos of
         | NONE => NONE
         | SOME (arity, p1) =>
           if arity <> 2 then NONE
           else
             (case rdUintC bs p1 of
              | NONE => NONE
              | SOME (code, p2) =>
                (case rdBstrC bs p2 of
                 | NONE => NONE
                 | SOME (payload, p3) =>
                     if code = 15 then
                       (if payload = [] \/ 3 < LENGTH payload then NONE
                        else
                          case rdUleb payload 0 of
                          | NONE => NONE
                          | SOME (idx, ppos) =>
                              if ppos = LENGTH payload /\
                                 idx <= MAX_DEP_INDEX
                              then SOME (GVCommitId idx, p3)
                              else NONE)
                     else if code <= 14 then
                       (if litOk code payload
                        then SOME (GVLit code payload, p3)
                        else NONE)
                     else if 16 <= code /\ code <= 63 then
                       SOME (GVExt code payload, p3)
                     else if 64 <= code /\ code <= 79 then
                       SOME (GVAbs code payload, p3)
                     else NONE)))
      else NONE
End

Definition rdValuesKA_def:
  rdValuesKA (bs:num list) (pos:num) (k:num) (acc:gvalue list)
             : (gvalue list # num) option =
    case k of
    | 0 => SOME (REVERSE acc, pos)
    | SUC k' =>
      (case rdValue bs pos of
       | NONE => NONE
       | SOME (v, p1) => rdValuesKA bs p1 k' (v::acc))
End

Definition rdValuesK_def:
  rdValuesK (bs:num list) (pos:num) (k:num)
            : (gvalue list # num) option =
    rdValuesKA bs pos k []
End

Datatype:
  certmeta = <|
    goalJudgmentHash : (num list) option ;
    theoryRev        : (num list) option ;
    rootHash         : (num list) option ;
    denBoundLog2Max  : num option
  |>
End

Datatype:
  gop = GElta elemref
      | GRela elemref (gvalue list)
      | GFuna elemref (gvalue list) gvalue
      | GEltd elemref
      | GCert num certmeta (num list)
      | GUnknown num (num list)
End

Definition oneRefExact_def:
  oneRefExact (b:num list) : elemref option =
    case rdElemRef b 0 of
    | NONE => NONE
    | SOME (r, pos) => if pos = LENGTH b then SOME r else NONE
End

Definition isTextMajor_def:
  isTextMajor (b:num list) <=>
    case peekMajor b 0 of SOME m => m = MAJ_TEXT | NONE => F
End

Definition rdArgsRow_def:
  rdArgsRow (b:num list) : (gvalue list) option =
    case rdArrC b 0 of
    | NONE => NONE
    | SOME (n, p1) =>
        if LENGTH b < p1 + n then NONE
        else
          (case rdValuesK b p1 n of
           | NONE => NONE
           | SOME (vs, p2) => if p2 = LENGTH b then SOME vs else NONE)
End

Definition rdValueRowExact_def:
  rdValueRowExact (b:num list) : gvalue option =
    case rdValue b 0 of
    | NONE => NONE
    | SOME (v, pos) => if pos = LENGTH b then SOME v else NONE
End

Definition emptyCertMeta_def:
  emptyCertMeta = <| goalJudgmentHash := NONE ; theoryRev := NONE ;
                     rootHash := NONE ; denBoundLog2Max := NONE |>
End

Definition rdCertMetaEntries_def:
  rdCertMetaEntries (b:num list) (pos:num) (prev:num option) (k:num)
                    (m:certmeta) : (certmeta # num) option =
    case k of
    | 0 => SOME (m, pos)
    | SUC k' =>
      (case rdUintC b pos of
       | NONE => NONE
       | SOME (key, p1) =>
         if (case prev of SOME pk => key <= pk | NONE => F) then NONE
         else if key = 0 then
           (case rdBstrC b p1 of
            | SOME (h, p2) =>
                if LENGTH h = 32
                then rdCertMetaEntries b p2 (SOME key) k'
                       (m with goalJudgmentHash := SOME h)
                else NONE
            | NONE => NONE)
         else if key = 1 then
           (case rdBstrC b p1 of
            | SOME (h, p2) =>
                if LENGTH h = 32
                then rdCertMetaEntries b p2 (SOME key) k'
                       (m with theoryRev := SOME h)
                else NONE
            | NONE => NONE)
         else if key = 2 then
           (case rdBstrC b p1 of
            | SOME (h, p2) =>
                if LENGTH h = 32
                then rdCertMetaEntries b p2 (SOME key) k'
                       (m with rootHash := SOME h)
                else NONE
            | NONE => NONE)
         else if key = 3 then
           (case rdUintC b p1 of
            | SOME (v, p2) =>
                rdCertMetaEntries b p2 (SOME key) k'
                  (m with denBoundLog2Max := SOME v)
            | NONE => NONE)
         else NONE)
End

Definition rdCertPayload_def:
  rdCertPayload (b:num list) : (num # certmeta # num list) option =
    case rdUintC b 0 of
    | NONE => NONE
    | SOME (fmt, p1) =>
      if 65535 < fmt then NONE
      else
        (case rdMapC b p1 of
         | NONE => NONE
         | SOME (n, p2) =>
           if 4 < n then NONE
           else
             (case rdCertMetaEntries b p2 NONE n emptyCertMeta of
              | NONE => NONE
              | SOME (meta, p3) =>
                (case rdBstrC b p3 of
                 | NONE => NONE
                 | SOME (cert, p4) =>
                     if p4 = LENGTH b then SOME (fmt, meta, cert)
                     else NONE)))
End

Datatype:
  rclass = CUnread | CUnsupp
End

Datatype:
  skel = <|
    author      : num list ;
    deps        : (num list) list ;
    parentCount : num ;
    tsClaim     : num ;
    message     : (num list) option ;
    bodyHash    : num list
  |>
End

Definition vecRefOK_def:
  vecRefOK (bs:num list) (fp:num) (target:num) (count:num) <=>
    case rdLeAt bs fp 4 of
    | NONE => F
    | SOME off =>
      (case rdLeAt bs (fp + 4) 4 of
       | NONE => F
       | SOME cnt => (fp + off) MOD 4294967296 = target /\ cnt = count)
End

Definition noCrossDup_def:
  noCrossDup ([]:(num list) list) (ys:(num list) list) = T /\
  noCrossDup (x::xs) [] = T /\
  noCrossDup (x::xs) (y::ys) =
    if x = y then F
    else if lexLt x y then noCrossDup xs (y::ys)
    else noCrossDup (x::xs) ys
End

Definition rdSkelDepsA_def:
  rdSkelDepsA (sk:num list) (k:num) (base:num)
              (acc:(num list) list) : ((num list) list) option =
    case k of
    | 0 => SOME (REVERSE acc)
    | SUC k' =>
      (case bytesAt sk base 32 of
       | NONE => NONE
       | SOME c => rdSkelDepsA sk k' (base + 32) (c::acc))
End

Definition rdSkelDeps_def:
  rdSkelDeps (sk:num list) (k:num) (base:num)
             : ((num list) list) option =
    rdSkelDepsA sk k base []
End

Definition rdSkeleton_def:
  rdSkeleton (sk:num list) : skel option =
    if LENGTH sk < 92 then NONE
    else
      let root = LENGTH sk - 92 in
      case oEL root sk of
      | NONE => NONE
      | SOME ver =>
        if ver <> 1 then NONE else
        (case bytesAt sk (root + 1) 32 of
         | NONE => NONE
         | SOME author =>
           (case rdLeAt sk (root + 37) 4 of
            | NONE => NONE
            | SOME depCnt =>
              if 65535 < depCnt then NONE else
              if ~vecRefOK sk (root + 33) 0 depCnt then NONE else
              (case rdSkelDeps sk depCnt 0 of
               | NONE => NONE
               | SOME deps =>
                 (case rdLeAt sk (root + 41) 2 of
                  | NONE => NONE
                  | SOME pc =>
                    if depCnt < pc then NONE else
                    (case rdLeAt sk (root + 43) 8 of
                     | NONE => NONE
                     | SOME ts =>
                       (case oEL (root + 51) sk of
                        | NONE => NONE
                        | SOME tag =>
                          (case
                             (if tag = 0 then
                                (case bytesAt sk (root + 52) 8 of
                                 | SOME z =>
                                     if z = REPLICATE 8 0
                                     then SOME (NONE, 0)
                                     else NONE
                                 | NONE => NONE)
                              else if tag = 1 then
                                (case rdLeAt sk (root + 56) 4 of
                                 | NONE => NONE
                                 | SOME mlen =>
                                   if 4096 < mlen then NONE else
                                   if ~vecRefOK sk (root + 52)
                                        (32 * depCnt) mlen
                                   then NONE else
                                   (case bytesAt sk (32 * depCnt) mlen of
                                    | NONE => NONE
                                    | SOME mb =>
                                        if utf8Ok mb
                                        then SOME (SOME mb, mlen)
                                        else NONE))
                              else NONE) of
                           | NONE => NONE
                           | SOME (msg, mlen) =>
                             (case bytesAt sk (root + 60) 32 of
                              | NONE => NONE
                              | SOME bh =>
                                if LENGTH sk <> 32 * depCnt + mlen + 92
                                then NONE
                                else
                                  let ps = TAKE pc deps in
                                  let cs = DROP pc deps in
                                    if strictAsc ps /\ strictAsc cs /\
                                       noCrossDup ps cs
                                    then SOME
                                      <| author := author ;
                                         deps := deps ;
                                         parentCount := pc ;
                                         tsClaim := ts ;
                                         message := msg ;
                                         bodyHash := bh |>
                                    else NONE))))))))
End

Datatype:
  zonerun = <| zcount : num ; zindex : num |>
End

Datatype:
  gbody = <|
    ops      : gop list ;
    zoneRuns : zonerun list
  |>
End

Definition rdFrameChans_def:
  rdFrameChans (fr:num list) : ((num list) list) option =
    if LENGTH fr < 88 then NONE
    else
      let root = LENGTH fr - 88 in
      let rdc = \i. rdLeAt fr (root + 8 * i + 4) 4 in
      (case (rdc 0, rdc 1, rdc 2, rdc 3, rdc 4, rdc 5) of
       | (SOME c0, SOME c1, SOME c2, SOME c3, SOME c4, SOME c5) =>
         (case (rdc 6, rdc 7, rdc 8, rdc 9, rdc 10) of
          | (SOME c6, SOME c7, SOME c8, SOME c9, SOME c10) =>
            (let cnts = [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] in
               if LENGTH fr <> SUM cnts + 88 then NONE
               else
                 let chk = \i. vecRefOK fr (root + 8 * i)
                                        (SUM (TAKE i cnts))
                                        (EL i cnts) in
                   if ~(chk 0 /\ chk 1 /\ chk 2 /\ chk 3 /\ chk 4 /\
                        chk 5 /\ chk 6 /\ chk 7 /\ chk 8 /\ chk 9 /\
                        chk 10)
                   then NONE
                   else
                     let sl = \i. TAKE (EL i cnts)
                                       (DROP (SUM (TAKE i cnts)) fr) in
                       SOME [sl 0; sl 1; sl 2; sl 3; sl 4; sl 5;
                             sl 6; sl 7; sl 8; sl 9; sl 10])
          | _ => NONE)
       | _ => NONE)
End

Definition rdZoneRecsA_def:
  rdZoneRecsA (b:num list) (k:num) (pos:num) (acc:zonerun list)
              : (zonerun list) option =
    case k of
    | 0 => (if pos = LENGTH b then SOME (REVERSE acc) else NONE)
    | SUC k' =>
      (case (rdLeAt b pos 4, rdLeAt b (pos + 4) 2) of
       | (SOME c, SOME z) =>
           rdZoneRecsA b k' (pos + 6)
                       (<| zcount := c ; zindex := z |> :: acc)
       | _ => NONE)
End

Definition rdZoneRecs_def:
  rdZoneRecs (b:num list) (k:num) (pos:num) : (zonerun list) option =
    rdZoneRecsA b k pos []
End

Definition zAdjOk_def:
  zAdjOk ([]:zonerun list) = T /\
  zAdjOk [r] = T /\
  zAdjOk (r::s::rest) = (r.zindex <> s.zindex /\ zAdjOk (s::rest))
End

Definition zoneLawsOk_def:
  zoneLawsOk (runs:zonerun list) (tsCells:num) <=>
    EVERY (\r. r.zcount <> 0) runs /\
    zAdjOk runs /\
    ~(LENGTH runs = 1 /\ (HD runs).zindex = 65535) /\
    (runs <> [] ==> SUM (MAP (\r. r.zcount) runs) = tsCells)
End

Definition tsOfVal_def:
  tsOfVal (v:gvalue) : num =
    case v of
    | GVLit code p => if code = 11 then 1 else 0
    | _ => 0
End

Definition tsOfOp_def:
  tsOfOp (op:gop) : num =
    case op of
    | GRela r args => SUM (MAP tsOfVal args)
    | GFuna r args v => SUM (MAP tsOfVal args) + tsOfVal v
    | _ => 0
End

Definition tsCellCount_def:
  tsCellCount (ops:gop list) = SUM (MAP tsOfOp ops)
End

Definition childrenOf_def:
  childrenOf (sorts:elemref list) (p:num) : num list =
    FILTER (\i. case oEL i sorts of
                | SOME (ERLocal k) => k = p /\ k <> i
                | _ => F)
           (COUNT_LIST (LENGTH sorts))
End

Definition esBfs_def:
  esBfs (sorts:elemref list) (queue:num list) (emitted:num list)
        (fuel:num) : num list =
    case fuel of
    | 0 => emitted
    | SUC f =>
      (case queue of
       | [] => emitted
       | (p::rest) =>
           esBfs sorts (rest ++ childrenOf sorts p) (emitted ++ [p]) f)
End

Definition esLegalSort_def:
  esLegalSort (sorts:elemref list) (i:num) <=>
    case oEL i sorts of
    | SOME (ERLocal k) => (k = i ==> i = 0) /\ k < LENGTH sorts
    | SOME (ERExt d c) => T
    | NONE => F
End

Definition esEltaOrder_def:
  esEltaOrder (sorts:elemref list) (cells:(num list) list)
              : (num list) option =
    let e = LENGTH sorts in
      if ~EVERY (esLegalSort sorts) (COUNT_LIST e) then NONE
      else
        let selfRoots = FILTER (\i. case oEL i sorts of
                                    | SOME (ERLocal k) => k = i
                                    | _ => F) (COUNT_LIST e) in
        let extRoots0 = FILTER (\i. case oEL i sorts of
                                    | SOME (ERExt d c) => T
                                    | _ => F) (COUNT_LIST e) in
        let extRoots = QSORT (\i j.
              lexLt (EL i cells) (EL j cells) \/
              (EL i cells = EL j cells /\ i <= j)) extRoots0 in
        let order = esBfs sorts (selfRoots ++ extRoots) [] (e + 1) in
          if LENGTH order = e then SOME order else NONE
End

Definition isIdentityPerm_def:
  isIdentityPerm (order:num list) <=>
    order = COUNT_LIST (LENGTH order)
End

Definition symResolve_def:
  symResolve (symbols:(num list) list) (idx:num) : (num list) option =
    oEL idx symbols
End

Definition decEltasA_def:
  decEltasA (symbols:(num list) list) (idxs:num list)
            (accR:elemref list) (accC:(num list) list)
            : ((elemref list # (num list) list)) option =
    case idxs of
    | [] => SOME (REVERSE accR, REVERSE accC)
    | (idx::rest) =>
      (case symResolve symbols idx of
       | NONE => NONE
       | SOME cell =>
         if isTextMajor cell then NONE else
         (case oneRefExact cell of
          | NONE => NONE
          | SOME r => decEltasA symbols rest (r::accR) (cell::accC)))
End

Definition decEltas_def:
  decEltas (symbols:(num list) list) (idxs:num list)
           : ((elemref list # (num list) list)) option =
    decEltasA symbols idxs [] []
End

Definition decRelasA_def:
  decRelasA (symbols:(num list) list) (idxs:num list)
            (rows:(num list) list)
            (accO:gop list) (accK:(num list) list)
            : ((gop list # (num list) list)) option =
    case idxs of
    | [] => (if rows = [] then SOME (REVERSE accO, REVERSE accK)
             else NONE)
    | (idx::is_) =>
      (case rows of
       | [] => NONE
       | (arow::rows') =>
         (case symResolve symbols idx of
          | NONE => NONE
          | SOME cell =>
            if isTextMajor cell then NONE else
            (case oneRefExact cell of
             | NONE => NONE
             | SOME r =>
               (case rdArgsRow arow of
                | NONE => NONE
                | SOME args =>
                    decRelasA symbols is_ rows'
                              (GRela r args::accO)
                              ((cell ++ arow)::accK)))))
End

Definition decRelas_def:
  decRelas (symbols:(num list) list) (idxs:num list)
           (rows:(num list) list)
           : ((gop list # (num list) list)) option =
    decRelasA symbols idxs rows [] []
End

Definition decFunasA_def:
  decFunasA (symbols:(num list) list) (idxs:num list)
            (arows:(num list) list) (vrows:(num list) list)
            (accO:gop list) (accK:(num list) list)
            : ((gop list # (num list) list)) option =
    case idxs of
    | [] => (if arows = [] /\ vrows = []
             then SOME (REVERSE accO, REVERSE accK) else NONE)
    | (idx::is_) =>
      (case (arows, vrows) of
       | (arow::arows', vrow::vrows') =>
         (case symResolve symbols idx of
          | NONE => NONE
          | SOME cell =>
            if isTextMajor cell then NONE else
            (case oneRefExact cell of
             | NONE => NONE
             | SOME r =>
               (case rdArgsRow arow of
                | NONE => NONE
                | SOME args =>
                  (case rdValueRowExact vrow of
                   | NONE => NONE
                   | SOME v =>
                       decFunasA symbols is_ arows' vrows'
                                 (GFuna r args v::accO)
                                 ((cell ++ arow ++ vrow)::accK)))))
       | _ => NONE)
End

Definition decFunas_def:
  decFunas (symbols:(num list) list) (idxs:num list)
           (arows:(num list) list) (vrows:(num list) list)
           : ((gop list # (num list) list)) option =
    decFunasA symbols idxs arows vrows [] []
End

Definition decEltdsA_def:
  decEltdsA (rows:(num list) list) (accO:gop list)
            (accK:(num list) list)
            : ((gop list # (num list) list)) option =
    case rows of
    | [] => SOME (REVERSE accO, REVERSE accK)
    | (row::rest) =>
      if isTextMajor row then NONE else
      (case oneRefExact row of
       | NONE => NONE
       | SOME r => decEltdsA rest (GEltd r::accO) (row::accK))
End

Definition decEltds_def:
  decEltds (rows:(num list) list)
           : ((gop list # (num list) list)) option =
    decEltdsA rows [] []
End

Definition decResidualsA_def:
  decResidualsA (rows:(num list) list) (acc:gop list)
                : (gop list) option =
    case rows of
    | [] => SOME (REVERSE acc)
    | (row::rest) =>
      if LENGTH row < 2 then NONE
      else
        let kind = leN (TAKE 2 row) in
        let payload = DROP 2 row in
          if kind <= 3 then NONE
          else if kind = 4 \/ kind = 5 then NONE
          else if kind = 6 then
            (case rdCertPayload payload of
             | NONE => NONE
             | SOME (fmt, meta, cert) =>
                 decResidualsA rest (GCert fmt meta cert::acc))
          else decResidualsA rest (GUnknown kind payload::acc)
End

Definition decResiduals_def:
  decResiduals (rows:(num list) list) : (gop list) option =
    decResidualsA rows []
End

Definition dedupAdj_def:
  dedupAdj ([]:num list) = [] /\
  dedupAdj [x] = [x] /\
  dedupAdj (x::y::rest) =
    if x = y then dedupAdj (y::rest) else x :: dedupAdj (y::rest)
End

Definition allUsed_def:
  allUsed (nsym:num) (idxs:num list) <=>
    dedupAdj (QSORT $<= idxs) = COUNT_LIST nsym
End

Datatype:
  bres = BOk gbody | BErr rclass string num
End

(* FORMAT REGISTRY (measured against both Rust registries; behavior
   deliberately unchanged here). This reader speaks the WORKSHOP-ERA
   wire: its format 1 is the hexane-columns channel layout — the
   workshop engine's BODY_FORMAT_HEXANE_COLUMNS_V1 = 1, a legacy
   layout retained there for read-compatibility — and the committed
   fixtures are hexane bodies under that numbering. The PRODUCTION
   wire (geolog-alpha's geolog-envelope) carries the TEMPLATE frame
   under the same byte: BODY_FORMAT_HEXANE_TEMPLATES_V1 = 1, "the
   only format, and the default" — a grammar this reader does not yet
   implement. Consequence, measured against the real production unit:
   it refuses below at symbols_column; expect production containers
   to refuse in general (fail-closed), though note this walk has no
   re-encode fixed-point gate, so bytes parsing under BOTH grammars
   with different ops are not excluded by construction — the port
   below is what retires that question. The Lean reference reader
   (Reflection/Body.lean) was re-registered so that fmt 1 and 2 both
   route to the template grammar there; its hexane walk is deleted.
   Porting the template grammar here (decoder + canonical encoder +
   the frame fixed-point gate + rdBody_wf extension + fixture
   re-mint) is planned follow-up work; until it lands, HOL4-side
   acceptance covers the workshop-era hexane wire only. *)
Definition rdBody_def:
  rdBody (bb:num list) : bres =
    case rdLeAt bb 0 2 of
    | NONE => BErr CUnread "body_prefix_truncated" (LENGTH bb)
    | SOME fmt =>
      if fmt = 0 then BErr CUnsupp "body_format_0_legacy_lane" 0
      else if fmt <> 1 then BErr CUnsupp "body_format_unknown" fmt
      else
        let fr = DROP 2 bb in
        case rdFrameChans fr of
        | NONE => BErr CUnread "frame_layout" 0
        | SOME chans =>
          if EL 0 chans <> [] then
            BErr CUnread "interleave_not_empty" (LENGTH (EL 0 chans))
          else
          (case readBytesCol (EL 1 chans) of
           | NONE => BErr CUnread "symbols_column" 0
           | SOME symbols =>
           case readU64Col (EL 2 chans) of
           | NONE => BErr CUnread "elta_sort_column" 0
           | SOME eltaIdx =>
           case readU64Col (EL 3 chans) of
           | NONE => BErr CUnread "rela_rel_column" 0
           | SOME relaIdx =>
           case readBytesCol (EL 4 chans) of
           | NONE => BErr CUnread "rela_args_column" 0
           | SOME relaArgs =>
           case readU64Col (EL 5 chans) of
           | NONE => BErr CUnread "funa_fun_column" 0
           | SOME funaIdx =>
           case readBytesCol (EL 6 chans) of
           | NONE => BErr CUnread "funa_args_column" 0
           | SOME funaArgs =>
           case readBytesCol (EL 7 chans) of
           | NONE => BErr CUnread "funa_value_column" 0
           | SOME funaVals =>
           case readBytesCol (EL 8 chans) of
           | NONE => BErr CUnread "eltd_target_column" 0
           | SOME eltdRows =>
           case readBytesCol (EL 9 chans) of
           | NONE => BErr CUnread "seg_other_column" 0
           | SOME otherRows =>
           if LENGTH relaIdx <> LENGTH relaArgs then
             BErr CUnread "rela_lockstep" (LENGTH relaIdx)
           else if LENGTH funaIdx <> LENGTH funaArgs \/
                   LENGTH funaIdx <> LENGTH funaVals then
             BErr CUnread "funa_lockstep" (LENGTH funaIdx)
           else if MAX_BODY_OPS < LENGTH eltaIdx + LENGTH relaIdx +
                                  LENGTH funaIdx + LENGTH eltdRows +
                                  LENGTH otherRows then
             BErr CUnread "op_count_overflow"
                  (LENGTH eltaIdx + LENGTH relaIdx + LENGTH funaIdx +
                   LENGTH eltdRows + LENGTH otherRows)
           else if ~strictAsc symbols then
             BErr CUnread "symbols_not_canonical" 0
           else
           case decEltas symbols eltaIdx of
           | NONE => BErr CUnread "elta_rows" 0
           | SOME (eltaSorts, eltaCells) =>
           case decRelas symbols relaIdx relaArgs of
           | NONE => BErr CUnread "rela_rows" 0
           | SOME (relaOps, relaKeys) =>
           case decFunas symbols funaIdx funaArgs funaVals of
           | NONE => BErr CUnread "funa_rows" 0
           | SOME (funaOps, funaKeys) =>
           case decEltds eltdRows of
           | NONE => BErr CUnread "eltd_rows" 0
           | SOME (eltdOps, eltdKeys) =>
           case decResiduals otherRows of
           | NONE => BErr CUnread "residual_rows" 0
           | SOME otherOps =>
           if ~allUsed (LENGTH symbols) (eltaIdx ++ relaIdx ++ funaIdx)
           then BErr CUnread "symbol_orphan" 0
           else if ~sortedLexLe relaKeys then
             BErr CUnread "rela_order" 0
           else if ~sortedLexLe funaKeys then
             BErr CUnread "funa_order" 0
           else if ~sortedLexLe eltdKeys then
             BErr CUnread "eltd_order" 0
           else
           (case esEltaOrder eltaSorts eltaCells of
            | NONE => BErr CUnread "elta_es_order" 0
            | SOME order =>
              if ~isIdentityPerm order then
                BErr CUnread "elta_es_order" 0
              else
                let ops = MAP GElta eltaSorts ++ relaOps ++ funaOps ++
                          eltdOps ++ otherOps in
                  if LENGTH (EL 10 chans) MOD 6 <> 0 then
                    BErr CUnread "zone_runs_extent"
                         (LENGTH (EL 10 chans))
                  else
                    (case rdZoneRecs (EL 10 chans)
                                     (LENGTH (EL 10 chans) DIV 6) 0 of
                     | NONE => BErr CUnread "zone_runs_records" 0
                     | SOME runs =>
                       if ~zoneLawsOk runs (tsCellCount ops) then
                         BErr CUnread "zone_runs_laws" (LENGTH runs)
                       else
                         BOk <| ops := ops ; zoneRuns := runs |>)))
End

Datatype:
  prereq = <| pflag : num ; pchid : num list ; prosterId : num option |>
End

Datatype:
  gcommit = <|
    sigBytes  : num list ;
    skelBytes : num list ;
    cskel     : skel ;
    bodyBytes : num list ;
    cbody     : gbody
  |>
End

Datatype:
  geolog = <|
    prereqs : prereq list ;
    commits : gcommit list
  |>
End

Datatype:
  gres = ROk geolog | RErr rclass string num
End

Definition gMagic_def:
  gMagic : num list = [103; 101; 111; 108; 111; 103; 102; 108]
End

Datatype:
  prereqR = PROk (prereq list) num | PRErr rclass string num
End

Definition rdPrereqsA_def:
  rdPrereqsA (bs:num list) (k:num) (pos:num) (acc:prereq list)
             : prereqR =
    case k of
    | 0 => PROk (REVERSE acc) pos
    | SUC k' =>
      (case oEL pos bs of
       | NONE => PRErr CUnread "prereq_truncated" pos
       | SOME flag =>
         if flag = 3 then PRErr CUnsupp "prereq_flag_3_reserved" pos
         else if 3 < flag then PRErr CUnread "prereq_flag_unknown" flag
         else
           (case bytesAt bs (pos + 1) 32 of
            | NONE => PRErr CUnread "prereq_truncated" pos
            | SOME chid =>
              if flag = 1 then
                (case rdLeAt bs (pos + 33) 2 of
                 | NONE => PRErr CUnread "prereq_truncated" pos
                 | SOME r =>
                     rdPrereqsA bs k' (pos + 35)
                       (<| pflag := flag ; pchid := chid ;
                           prosterId := SOME r |> :: acc))
              else
                rdPrereqsA bs k' (pos + 33)
                  (<| pflag := flag ; pchid := chid ;
                      prosterId := NONE |> :: acc)))
End

Definition rdPrereqs_def:
  rdPrereqs (bs:num list) (k:num) (pos:num) : prereqR =
    rdPrereqsA bs k pos []
End

Datatype:
  commitR = CROk (gcommit list) num | CRErr rclass string num
End

Definition rdCommitsA_def:
  rdCommitsA (bs:num list) (k:num) (pos:num) (acc:gcommit list)
             : commitR =
    case k of
    | 0 => CROk (REVERSE acc) pos
    | SUC k' =>
      (case rdLeAt bs pos 4 of
       | NONE => CRErr CUnread "commit_env_len_truncated" pos
       | SOME envLen =>
         if envLen < 64 then
           CRErr CUnread "envelope_shorter_than_signature" envLen
         else
         (case bytesAt bs (pos + 4) envLen of
          | NONE => CRErr CUnread "envelope_truncated" pos
          | SOME env =>
            let sg = TAKE 64 env in
            let sk = DROP 64 env in
            (case rdSkeleton sk of
             | NONE => CRErr CUnread "skeleton" pos
             | SOME skv =>
               let bpos = pos + 4 + envLen in
               (case rdLeAt bs bpos 4 of
                | NONE => CRErr CUnread "commit_body_len_truncated" bpos
                | SOME bodyLen =>
                  (case bytesAt bs (bpos + 4) bodyLen of
                   | NONE => CRErr CUnread "body_truncated" bpos
                   | SOME bb =>
                     (case rdBody bb of
                      | BErr c t w => CRErr c t w
                      | BOk body =>
                          rdCommitsA bs k' (bpos + 4 + bodyLen)
                            (<| sigBytes := sg ;
                                skelBytes := sk ;
                                cskel := skv ;
                                bodyBytes := bb ;
                                cbody := body |> :: acc)))))))
End

Definition rdCommits_def:
  rdCommits (bs:num list) (k:num) (pos:num) : commitR =
    rdCommitsA bs k pos []
End

Definition prereqAsc_def:
  prereqAsc (ps:prereq list) = strictAsc (MAP (\p. p.pchid) ps)
End

Definition readGeolog_def:
  readGeolog (bs:num list) : gres =
    if TAKE 8 bs <> gMagic then RErr CUnread "magic" 0
    else
      case rdLeAt bs 8 4 of
      | NONE => RErr CUnread "version_truncated" 8
      | SOME ver =>
        if ver <> 1 then RErr CUnsupp "container_version" ver
        else
        (case rdLeAt bs 12 4 of
         | NONE => RErr CUnread "prereq_count_truncated" 12
         | SOME pcount =>
           if LENGTH bs < 16 + 33 * pcount then
             RErr CUnread "prereq_count_over_input" pcount
           else
           (case rdPrereqs bs pcount 16 of
            | PRErr c t w => RErr c t w
            | PROk prereqs ppos =>
              if ~prereqAsc prereqs then RErr CUnread "prereq_order" 0
              else
              (case rdLeAt bs ppos 4 of
               | NONE => RErr CUnread "commit_count_truncated" ppos
               | SOME ccount =>
                 if ccount = 0 then RErr CUnread "commit_count_zero" 0
                 else if LENGTH bs < ppos + 4 + 8 * ccount then
                   RErr CUnread "commit_count_over_input" ccount
                 else
                 (case rdCommits bs ccount (ppos + 4) of
                  | CRErr c t w => RErr c t w
                  | CROk commits cend =>
                      if cend <> LENGTH bs then
                        RErr CUnread "trailing_bytes" (LENGTH bs - cend)
                      else
                        ROk <| prereqs := prereqs ;
                               commits := commits |>))))
End

Definition opUnsuppTag_def:
  opUnsuppTag (op:gop) : (string # num) option =
    case op of
    | GEltd r => SOME ("eltd_in_sealed_artifact", 3)
    | GCert fmt m c => SOME ("op_kind_outside_fragment", 6)
    | GUnknown k p => SOME ("op_kind_outside_fragment", k)
    | _ => NONE
End

Definition firstUnsupp_def:
  firstUnsupp (ops:gop list) : (string # num) option =
    case ops of
    | [] => NONE
    | (op::rest) =>
      (case opUnsuppTag op of
       | SOME tw => SOME tw
       | NONE => firstUnsupp rest)
End

Definition sealedCheck_def:
  sealedCheck (g:geolog) : (string # num) option =
    case FLAT (MAP (\c. case firstUnsupp c.cbody.ops of
                        | SOME tw => [tw]
                        | NONE => []) g.commits) of
    | [] => NONE
    | (tw::rest) => SOME tw
End

Definition readGeologSealed_def:
  readGeologSealed (bs:num list) : gres =
    case readGeolog bs of
    | RErr c t w => RErr c t w
    | ROk g =>
      (case sealedCheck g of
       | SOME (t, w) => RErr CUnsupp t w
       | NONE => ROk g)
End

Definition hexDig_def:
  hexDig (n:num) : string =
    if n < 10 then STR (CHR (48 + n)) else STR (CHR (87 + n))
End

Definition hex2_def:
  hex2 (b:num) : string = hexDig (b DIV 16) ++ hexDig (b MOD 16)
End

Definition hexS_def:
  hexS (bs:num list) : string = CONCAT (MAP hex2 bs)
End

Definition numS_def:
  numS (n:num) : string = num_to_dec_string n
End

Definition renderRef_def:
  renderRef (r:elemref) : string =
    case r of
    | ERLocal n => "L(" ++ numS n ++ ")"
    | ERExt d c => "E(" ++ numS d ++ "," ++ numS c ++ ")"
End

Definition renderVal_def:
  renderVal (v:gvalue) : string =
    case v of
    | GVRef r => renderRef r
    | GVLit code p => "lit(" ++ numS code ++ ",0x" ++ hexS p ++ ")"
    | GVCommitId i => "cid(" ++ numS i ++ ")"
    | GVExt code p => "ext(" ++ numS code ++ ",0x" ++ hexS p ++ ")"
    | GVAbs code p => "abs(" ++ numS code ++ ",0x" ++ hexS p ++ ")"
End

Definition renderVals_def:
  renderVals (vs:gvalue list) : string =
    case vs of
    | [] => ""
    | [v] => renderVal v
    | (v::rest) => renderVal v ++ "," ++ renderVals rest
End

Definition renderMeta1_def:
  renderMeta1 (tag:string) (h:(num list) option) : string =
    case h of NONE => "" | SOME b => " " ++ tag ++ "=0x" ++ hexS b
End

Definition renderOp_def:
  renderOp (op:gop) : string =
    case op of
    | GElta r => "elta sort=" ++ renderRef r
    | GRela r args =>
        "rela rel=" ++ renderRef r ++ " args=[" ++ renderVals args ++ "]"
    | GFuna r args v =>
        "funa fun=" ++ renderRef r ++ " args=[" ++ renderVals args ++
        "] value=" ++ renderVal v
    | GEltd r => "eltd target=" ++ renderRef r
    | GCert fmt m cert =>
        "cert fmt=" ++ numS fmt ++
        renderMeta1 "goal" m.goalJudgmentHash ++
        renderMeta1 "rev" m.theoryRev ++
        renderMeta1 "root" m.rootHash ++
        (case m.denBoundLog2Max of
         | NONE => "" | SOME v => " den=" ++ numS v) ++
        " cert=0x" ++ hexS cert
    | GUnknown k p =>
        "unknown kind=" ++ numS k ++ " payload=0x" ++ hexS p
End

Definition renderOps_def:
  renderOps (ops:gop list) (i:num) : string =
    case ops of
    | [] => ""
    | (op::rest) =>
        "op " ++ numS i ++ ": " ++ renderOp op ++ "\n" ++
        renderOps rest (i + 1)
End

Definition renderZone_def:
  renderZone (r:zonerun) : string =
    "(" ++ numS r.zcount ++ "," ++ numS r.zindex ++ ")"
End

Definition renderZones_def:
  renderZones (rs:zonerun list) : string =
    case rs of
    | [] => ""
    | [r] => renderZone r
    | (r::rest) => renderZone r ++ "," ++ renderZones rest
End

Definition renderMsg_def:
  renderMsg (m:(num list) option) : string =
    case m of NONE => "none" | SOME b => "0x" ++ hexS b
End

Definition renderDeps_def:
  renderDeps (ds:(num list) list) : string =
    case ds of
    | [] => ""
    | [d] => hexS d
    | (d::rest) => hexS d ++ "," ++ renderDeps rest
End

Definition renderCommit_def:
  renderCommit (c:gcommit) (i:num) : string =
    "commit " ++ numS i ++ ": sig=0x" ++ hexS (TAKE 8 c.sigBytes) ++
    " author=0x" ++ hexS c.cskel.author ++
    " deps=[" ++ renderDeps c.cskel.deps ++ "]" ++
    " parents=" ++ numS c.cskel.parentCount ++
    " ts=" ++ numS c.cskel.tsClaim ++
    " msg=" ++ renderMsg c.cskel.message ++
    " bodyhash=0x" ++ hexS c.cskel.bodyHash ++
    " ops=" ++ numS (LENGTH c.cbody.ops) ++
    " zones=[" ++ renderZones c.cbody.zoneRuns ++ "]\n" ++
    renderOps c.cbody.ops 0
End

Definition renderCommits_def:
  renderCommits (cs:gcommit list) (i:num) : string =
    case cs of
    | [] => ""
    | (c::rest) => renderCommit c i ++ renderCommits rest (i + 1)
End

Definition renderPrereq_def:
  renderPrereq (p:prereq) : string =
    "prereq flag=" ++ numS p.pflag ++ " chid=0x" ++ hexS p.pchid ++
    (case p.prosterId of
     | NONE => "" | SOME r => " roster=" ++ numS r) ++ "\n"
End

Definition renderGeolog_def:
  renderGeolog (g:geolog) : string =
    "container version=1 prereqs=" ++ numS (LENGTH g.prereqs) ++
    " commits=" ++ numS (LENGTH g.commits) ++ "\n" ++
    CONCAT (MAP renderPrereq g.prereqs) ++
    renderCommits g.commits 0
End

Definition renderClass_def:
  renderClass (c:rclass) : string =
    case c of
    | CUnread => "UNREADABLE"
    | CUnsupp => "UNSUPPORTED"
End

Definition renderRes_def:
  renderRes (r:gres) : string =
    case r of
    | ROk g => "OK\n" ++ renderGeolog g
    | RErr c t w => renderClass c ++ " " ++ t ++ " " ++ numS w ++ "\n"
End
