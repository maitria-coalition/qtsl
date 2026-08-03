(*
  decodeSpec: the functional specification of "the v0 bytes the
  columns encode" (columns -> byte list option). A proof device for the
  acceptance and equivalence theorems and the byte-exact oracle target
  against the untrusted reference decoder; it is never part of the
  translated program. Total and fail-closed.
*)
open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory optionTheory pairTheory;

val _ = new_theory "qtsl_decodeSpec";

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

Definition allBytes_def:
  (allBytes [] = T) /\
  (allBytes ((b:num)::bs) = (b < 256 /\ allBytes bs))
End

Definition allBytesL_def:
  (allBytesL [] = T) /\
  (allBytesL (l::ls) = (allBytes l /\ allBytesL ls))
End

Definition le32t_def:
  le32t (v:num) =
    [v MOD 256; (v DIV 256) MOD 256; (v DIV 65536) MOD 256;
     (v DIV 16777216) MOD 256]
End

Definition le64t_def:
  le64t (v:num) = le32t (v MOD 4294967296) ++ le32t (v DIV 4294967296)
End

Definition emit8_def:
  emit8 (v:num) = if v < 256 then SOME [v] else NONE
End

Definition emit16_def:
  emit16 (v:num) = if v < 65536 then SOME [v MOD 256; v DIV 256] else NONE
End

Definition emit32_def:
  emit32 (v:num) = if v < 4294967296 then SOME (le32t v) else NONE
End

Definition emit64_def:
  emit64 (v:num) = if v < 18446744073709551616 then SOME (le64t v) else NONE
End

Definition idxN_def:
  (idxN ([]:num list) (n:num) = NONE) /\
  (idxN (x::xs) n = if n = 0 then SOME x else idxN xs (n - 1))
End

Definition idxL_def:
  (idxL ([]:(num list) list) (n:num) = NONE) /\
  (idxL (x::xs) n = if n = 0 then SOME x else idxL xs (n - 1))
End

Definition rdU32_def:
  rdU32 (bs:num list) (off:num) =
    case (idxN bs off, idxN bs (off+1), idxN bs (off+2), idxN bs (off+3)) of
      (SOME b0, SOME b1, SOME b2, SOME b3) =>
        SOME (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3)
    | _ => NONE
End

Definition rdU64_def:
  rdU64 (bs:num list) (off:num) =
    case (rdU32 bs off, rdU32 bs (off+4)) of
      (SOME lo, SOME hi) => SOME (lo + 4294967296 * hi)
    | _ => NONE
End

Definition takeFront_def:
  (takeFront (0:num) (xs:num list) = SOME ([]:num list, xs)) /\
  (takeFront (SUC k) [] = NONE) /\
  (takeFront (SUC k) (x::xs) =
     case takeFront k xs of
       NONE => NONE
     | SOME (t, r) => SOME (x::t, r))
End

Definition u32v_def:
  u32v (b0:num) (b1:num) (b2:num) (b3:num) =
    b0 + 256 * b1 + 65536 * b2 + 16777216 * b3
End

Definition jlook_def:
  (jlook ([]:((num # num) # num) list) (k:num # num) = NONE) /\
  (jlook ((p,v)::rest) k = if p = k then SOME v else jlook rest k)
End

Definition jins_def:
  jins judg (k:num # num) (off:num) =
    case jlook judg k of SOME _ => judg | NONE => (k, off)::judg
End

Definition escHit_def:
  (escHit (ord:num) ([]:num list) = (F, [])) /\
  (escHit ord (e::es) = if e = ord then (T, es) else (F, e::es))
End

Definition skipQ_def:
  (skipQ (bs:num list) (pos:num) (0:num) = SOME pos) /\
  (skipQ bs pos (SUC k) =
     case (rdU32 bs pos, rdU32 bs (pos+4)) of
       (SOME nl, SOME dl) =>
         if pos + 8 + nl + dl <= LENGTH bs
         then skipQ bs (pos + 8 + nl + dl) k
         else NONE
     | _ => NONE)
End

Definition cnvLoop_def:
  (cnvLoop (bs:num list) (pos:num) (0:num) acc = SOME (REVERSE acc)) /\
  (cnvLoop bs pos (SUC k) acc =
     case (rdU32 bs pos, rdU32 bs (pos+4)) of
       (SOME nv, SOME ad) =>
         (case skipQ bs (pos+8) (nv * ad) of
            NONE => NONE
          | SOME p1 =>
              let bsz = (nv + 7) DIV 8 in
              case rdU32 bs p1 of
                NONE => NONE
              | SOME ns =>
                  let p2 = p1 + 4 + ns * bsz in
                  case rdU32 bs p2 of
                    NONE => NONE
                  | SOME nc => cnvLoop bs (p2 + 4 + nc * 2 * bsz) k (nv::acc))
     | _ => NONE)
End

Definition complexNVerts_def:
  complexNVerts (bs:num list) (doff:num) =
    case rdU32 bs doff of
      NONE => NONE
    | SOME n => cnvLoop bs (doff + 4) n []
End

Definition emitQ_def:
  emitQ (dict:(num list) list) (nls:num list) (dis:num list) (nums:num list) =
    case (nls, dis) of
      (nl::nls1, di::dis1) =>
        (case idxL dict di of
           NONE => NONE
         | SOME den =>
             case takeFront nl nums of
               NONE => NONE
             | SOME (nb, nums1) =>
                 case (emit32 nl, emit32 (LENGTH den)) of
                   (SOME a, SOME b) => SOME (a ++ b ++ nb ++ den, nls1, dis1, nums1)
                 | _ => NONE)
    | _ => NONE
End

Definition mU32s_def:
  (mU32s (0:num) (miscs:num list) = SOME ([]:num list, miscs)) /\
  (mU32s (SUC k) miscs =
     case miscs of
       [] => NONE
     | v::ms =>
         case emit32 v of
           NONE => NONE
         | SOME b =>
             case mU32s k ms of
               NONE => NONE
             | SOME (bs, ms1) => SOME (b ++ bs, ms1))
End

Definition mU64s_def:
  (mU64s (0:num) (miscs:num list) = SOME ([]:num list, miscs)) /\
  (mU64s (SUC k) miscs =
     case miscs of
       [] => NONE
     | v::ms =>
         case emit64 v of
           NONE => NONE
         | SOME b =>
             case mU64s k ms of
               NONE => NONE
             | SOME (bs, ms1) => SOME (b ++ bs, ms1))
End

Definition mU16s_def:
  (mU16s (0:num) (miscs:num list) = SOME ([]:num list, miscs)) /\
  (mU16s (SUC k) miscs =
     case miscs of
       [] => NONE
     | v::ms =>
         case emit16 v of
           NONE => NONE
         | SOME b =>
             case mU16s k ms of
               NONE => NONE
             | SOME (bs, ms1) => SOME (b ++ bs, ms1))
End

Definition takeBits_def:
  takeBits (n:num) (miscs:num list) =
    case takeFront n miscs of
      NONE => NONE
    | SOME (bs, ms) => if allBytes bs then SOME (bs, ms) else NONE
End

Definition einsumIns_def:
  (einsumIns (0:num) (refs:num list) (miscs:num list) =
     SOME ([]:num list, refs, miscs)) /\
  (einsumIns (SUC k) refs miscs =
     case refs of
       [] => NONE
     | r::refs1 =>
         case emit32 r of
           NONE => NONE
         | SOME rb =>
             case miscs of
               [] => NONE
             | rk::ms1 =>
                 case emit32 rk of
                   NONE => NONE
                 | SOME rkb =>
                     case mU32s rk ms1 of
                       NONE => NONE
                     | SOME (binds, ms2) =>
                         case einsumIns k refs1 ms2 of
                           NONE => NONE
                         | SOME (bs, refs2, ms3) =>
                             SOME (rb ++ rkb ++ binds ++ bs, refs2, ms3))
End

Definition polySup_def:
  (polySup (0:num) (miscs:num list) = SOME ([]:num list, miscs)) /\
  (polySup (SUC k) miscs =
     case miscs of
       w::c::ms =>
         (case (emit32 w, emit32 c) of
            (SOME wb, SOME cb) =>
              (case polySup k ms of
                 NONE => NONE
               | SOME (bs, ms1) => SOME (wb ++ cb ++ bs, ms1))
          | _ => NONE)
     | _ => NONE)
End

Definition polyEnts_def:
  (polyEnts (dict:(num list) list) (ilen:num) (0:num) nls dis nums (miscs:num list) =
     SOME ([]:num list, nls, dis, nums, miscs)) /\
  (polyEnts dict ilen (SUC k) nls dis nums miscs =
     case mU16s ilen miscs of
       NONE => NONE
     | SOME (ib, ms1) =>
         case emitQ dict nls dis nums of
           NONE => NONE
         | SOME (qb, nls1, dis1, nums1) =>
             case polyEnts dict ilen k nls1 dis1 nums1 ms1 of
               NONE => NONE
             | SOME (bs, nls2, dis2, nums2, ms2) =>
                 SOME (ib ++ qb ++ bs, nls2, dis2, nums2, ms2))
End

Definition poolRec_def:
  poolRec (nv:num list) (dict:(num list) list) (tag:num)
          (pout:num list) (refs:num list) (nls:num list) (dis:num list)
          (nums:num list) (miscs:num list)
          (judg:((num # num) # num) list) =
    if tag = 0x01 then
      (case miscs of
         w::ms => (case emit32 w of NONE => NONE
                   | SOME b => SOME (pout ++ [tag] ++ b, refs, nls, dis, nums, ms, judg))
       | _ => NONE)
    else if tag = 0x02 then
      (case emitQ dict nls dis nums of
         NONE => NONE
       | SOME (qb, nls1, dis1, nums1) =>
           SOME (pout ++ [tag] ++ qb, refs, nls1, dis1, nums1, miscs, judg))
    else if (tag = 0x03) \/ (tag = 0x04) \/ (tag = 0x05) \/ (tag = 0x22) \/
            (tag = 0x23) then
      (case refs of
         a::b::refs1 =>
           (case (emit32 a, emit32 b) of
              (SOME ab, SOME bb) =>
                SOME (pout ++ [tag] ++ ab ++ bb, refs1, nls, dis, nums, miscs, judg)
            | _ => NONE)
       | _ => NONE)
    else if tag = 0x06 then
      (case refs of
         a::refs1 =>
           (case emit32 a of NONE => NONE
            | SOME ab => SOME (pout ++ [tag] ++ ab, refs1, nls, dis, nums, miscs, judg))
       | _ => NONE)
    else if tag = 0x07 then
      (case refs of
         a::refs1 =>
           (case miscs of
              i::ms =>
                (case (emit32 a, emit32 i) of
                   (SOME ab, SOME ib) =>
                     SOME (pout ++ [tag] ++ ab ++ ib, refs1, nls, dis, nums, ms, judg)
                 | _ => NONE)
            | _ => NONE)
       | _ => NONE)
    else if tag = 0x10 then
      (case miscs of
         ci::ms =>
           (case idxN nv ci of
              NONE => NONE
            | SOME nverts =>
                case takeBits ((nverts + 7) DIV 8) ms of
                  NONE => NONE
                | SOME (bits, ms1) =>
                    case emit32 ci of
                      NONE => NONE
                    | SOME cib =>
                        SOME (pout ++ [tag] ++ cib ++ bits, refs, nls, dis, nums, ms1, judg))
       | _ => NONE)
    else if tag = 0x11 then
      (case refs of
         sref::refs1 =>
           (case emit32 sref of
              NONE => NONE
            | SOME sb =>

                case rdU32 pout (sref + 1) of
                  NONE => NONE
                | SOME ci =>
                    case idxN nv ci of
                      NONE => NONE
                    | SOME nverts =>
                        case takeBits ((nverts + 7) DIV 8) miscs of
                          NONE => NONE
                        | SOME (bits, ms1) =>
                            SOME (pout ++ [tag] ++ sb ++ bits, refs1, nls, dis, nums, ms1, judg))
       | _ => NONE)
    else if tag = 0x20 then
      (case miscs of
         bow::ms =>
           (case emit8 bow of
              NONE => NONE
            | SOME bwb =>
                case refs of
                  a::b::refs1 =>
                    (case (emit32 a, emit32 b) of
                       (SOME ab, SOME bb) =>
                         SOME (pout ++ [tag] ++ bwb ++ ab ++ bb, refs1, nls, dis, nums, ms, judg)
                     | _ => NONE)
                | _ => NONE)
       | _ => NONE)
    else if tag = 0x21 then
      (case refs of
         a::b::c::refs1 =>
           (case (emit32 a, emit32 b, emit32 c) of
              (SOME ab, SOME bb, SOME cb) =>
                SOME (pout ++ [tag] ++ ab ++ bb ++ cb, refs1, nls, dis, nums, miscs, judg)
            | _ => NONE)
       | _ => NONE)
    else if (tag = 0x24) \/ (tag = 0x25) \/ (tag = 0x26) then
      SOME (pout ++ [tag], refs, nls, dis, nums, miscs, judg)
    else if tag = 0x30 then
      (case refs of
         pre::post::refs1 =>
           (case (emit32 pre, emit32 post) of
              (SOME ab, SOME bb) =>
                SOME (pout ++ [tag] ++ ab ++ bb, refs1, nls, dis, nums, miscs,
                      jins judg (pre, post) (LENGTH pout))
            | _ => NONE)
       | _ => NONE)
    else if tag = 0x08 then
      (case miscs of
         nIn::nIdx::ms1 =>
           (case (emit32 nIn, emit32 nIdx) of
              (SOME nib, SOME nxb) =>
                (case mU64s nIdx ms1 of
                   NONE => NONE
                 | SOME (extb, ms2) =>
                     case einsumIns nIn refs ms2 of
                       NONE => NONE
                     | SOME (inb, refs1, ms3) =>
                         case ms3 of
                           outR::ms4 =>
                             (case emit32 outR of
                                NONE => NONE
                              | SOME orb =>
                                  case mU32s outR ms4 of
                                    NONE => NONE
                                  | SOME (outb, ms5) =>
                                      SOME (pout ++ [tag] ++ nib ++ nxb ++ extb ++ inb ++
                                            orb ++ outb, refs1, nls, dis, nums, ms5, judg))
                         | _ => NONE)
            | _ => NONE)
       | _ => NONE)
    else if tag = 0x09 then
      (case miscs of
         bas::dmn::deg::nvars::ms1 =>
           (case (emit8 bas, emit32 dmn, emit32 deg, emit32 nvars) of
              (SOME bb, SOME db, SOME gb, SOME vb) =>
                (case polySup nvars ms1 of
                   NONE => NONE
                 | SOME (supb, ms2) =>
                     case ms2 of
                       nents::ms3 =>
                         (case emit32 nents of
                            NONE => NONE
                          | SOME eb =>
                              let ilen = nvars + (if bas = 1 then 1 else 0) in
                              case polyEnts dict ilen nents nls dis nums ms3 of
                                NONE => NONE
                              | SOME (entb, nls1, dis1, nums1, ms4) =>
                                  SOME (pout ++ [tag] ++ bb ++ [0; 0] ++ db ++ gb ++ vb ++
                                        supb ++ eb ++ entb,
                                        refs, nls1, dis1, nums1, ms4, judg))
                     | _ => NONE)
            | _ => NONE)
       | _ => NONE)
    else NONE
End

Definition poolLoop_def:
  (poolLoop (nv:num list) (dict:(num list) list) ([]:num list)
            pout refs nls dis nums miscs judg =
     SOME (pout, refs, nls, dis, nums, miscs, judg)) /\
  (poolLoop nv dict (t::ts) pout refs nls dis nums miscs judg =
     case poolRec nv dict t pout refs nls dis nums miscs judg of
       NONE => NONE
     | SOME (pout1, refs1, nls1, dis1, nums1, miscs1, judg1) =>
         poolLoop nv dict ts pout1 refs1 nls1 dis1 nums1 miscs1 judg1)
End

Definition symNode_def:
  symNode (s:num) =
    if s <= 26 then SOME (s, 0:num)
    else if s = 27 then SOME (4:num, 1:num)
    else if s = 28 then SOME (5:num, 1:num)
    else if s = 29 then SOME (10:num, 1:num)
    else NONE
End

Definition nChildren_def:
  nChildren (tag:num) (xa:num) =
    if (tag = 0) \/ (tag = 12) \/ (tag = 14) \/ (tag = 19) \/ (tag = 20) \/
       (tag = 23) then SOME (0:num)
    else if (tag = 1) \/ (tag = 4) \/ (tag = 5) \/ (tag = 8) \/ (tag = 9) \/
            (tag = 10) \/ (tag = 11) \/ (tag = 13) \/ (tag = 17) \/
            (tag = 18) \/ (tag = 21) \/ (tag = 22) \/ (tag = 24) then SOME 1
    else if (tag = 2) \/ (tag = 3) \/ (tag = 6) \/ (tag = 7) \/ (tag = 16) \/
            (tag = 25) then SOME 2
    else if tag = 15 then SOME (1 + xa)
    else if tag = 26 then SOME xa
    else NONE
End

Definition popK_def:
  (popK (0:num) (stk:num list) (acc:num list) = SOME (acc, stk)) /\
  (popK (SUC k) [] acc = NONE) /\
  (popK (SUC k) (x::xs) acc = popK k xs (x::acc))
End

Definition memN_def:
  (memN (x:num) ([]:num list) = F) /\
  (memN x (y::ys) = ((x = y) \/ memN x ys))
End

Definition topoK_def:
  (topoK (0:num) (strt:num) (strts:num list) (topos:num list) =
     SOME ([]:num list, topos)) /\
  (topoK (SUC k) strt strts topos =
     case topos of
       [] => NONE
     | d::ts =>
         if d <= strt /\ memN (strt - d) strts then
           (case topoK k strt strts ts of
              NONE => NONE
            | SOME (cs, ts1) => SOME ((strt - d)::cs, ts1))
         else NONE)
End

Definition getChildren_def:
  getChildren (tmode:num) (k:num) (strt:num) (stk:num list) (strts:num list)
              (topos:num list) =
    if tmode = 0 then
      case popK k stk [] of
        NONE => NONE
      | SOME (cs, stk1) => SOME (cs, strt::stk1, topos)
    else
      case topoK k strt strts topos of
        NONE => NONE
      | SOME (cs, ts1) => SOME (cs, strt::stk, ts1)
End

Definition derivAndE_def:
  derivAndE (pool:num list) (nout:num list) (base:num) (vr:num) (ch:num) =
    if ch < base then NONE else
    case rdU32 nout (ch - base + 4) of
      NONE => NONE
    | SOME cj =>
        case (rdU32 pool (cj + 1), rdU32 pool (cj + 5)) of
          (SOME cpre, SOME cpost) =>
            (case idxN pool cpost of
               NONE => SOME NONE
             | SOME ptag =>
                 if ptag = 0x22 then
                   case (rdU32 pool (cpost + 1), rdU32 pool (cpost + 5)) of
                     (SOME l, SOME r) =>
                       SOME (SOME (cpre,
                                   (if vr = 0 then l else r),
                                   (if vr = 0 then r else l)))
                   | _ => NONE
                 else SOME NONE)
        | _ => NONE
End

Definition derivConv_def:
  derivConv (pool:num list) (nout:num list) (base:num) (ch:num) =
    if ch < base then NONE else
    case rdU32 nout (ch - base + 4) of
      NONE => NONE
    | SOME cj =>
        case rdU32 pool (cj + 5) of
          NONE => NONE
        | SOME cpost =>
            (case idxN pool cpost of
               NONE => SOME NONE
             | SOME ptag =>
                 if ptag = 0x21 then
                   case (rdU32 pool (cpost + 1), rdU32 pool (cpost + 5),
                         rdU32 pool (cpost + 9)) of
                     (SOME t, SOME sx, SOME e) => SOME (SOME (t, sx, e))
                   | _ => NONE
                 else SOME NONE)
End

Definition stepBytes_def:
  (stepBytes ([]:num list) = SOME ([]:num list)) /\
  (stepBytes (s::ss) =
     if s < 256 then
       (case stepBytes ss of NONE => NONE | SOME r => SOME (s::r))
     else NONE)
End

Definition wiresU32_def:
  (wiresU32 ([]:num list) = SOME ([]:num list)) /\
  (wiresU32 (w::ws) =
     case emit32 w of
       NONE => NONE
     | SOME b => case wiresU32 ws of NONE => NONE | SOME r => SOME (b ++ r))
End

Definition kids64_def:
  (kids64 ([]:num list) = SOME ([]:num list)) /\
  (kids64 (c::cs) =
     case emit64 c of
       NONE => NONE
     | SOME b => case kids64 cs of NONE => NONE | SOME r => SOME (b ++ r))
End

Definition subBranches_def:
  (subBranches ([]:num list) (pfs:num list) = SOME ([]:num list, pfs)) /\
  (subBranches (c::cs) pfs =
     case pfs of
       s::e::pfs1 =>
         (case (emit32 s, emit32 e, emit64 c) of
            (SOME sb, SOME eb, SOME cb) =>
              (case subBranches cs pfs1 of
                 NONE => NONE
               | SOME (bs, pfs2) => SOME (sb ++ eb ++ cb ++ bs, pfs2))
          | _ => NONE)
     | _ => NONE)
End

Definition rat1_def:
  rat1 (rts:num list) =
    case rts of
      a0::a1::a2::a3::b0::b1::b2::b3::rest =>
        (case takeFront (u32v a0 a1 a2 a3 + u32v b0 b1 b2 b3) rest of
           NONE => NONE
         | SOME (body, rest1) =>
             SOME ([a0; a1; a2; a3; b0; b1; b2; b3] ++ body, rest1))
    | _ => NONE
End

Definition ratsN_def:
  (ratsN (0:num) (rts:num list) = SOME ([]:num list, rts)) /\
  (ratsN (SUC k) rts =
     case rat1 rts of
       NONE => NONE
     | SOME (b, rts1) =>
         case ratsN k rts1 of
           NONE => NONE
         | SOME (bs, rts2) => SOME (b ++ bs, rts2))
End

Definition denTake_def:
  denTake (dns:(num # num) list) (dflt:num) (ord:num) =
    case dns of
      [] => (dflt, []:(num # num) list)
    | (a,v)::rest => if a = ord then (v, rest) else (dflt, dns)
End

Definition nodeStep_def:
  nodeStep (pool:num list) (judg:((num # num) # num) list) (base:num)
           (tmode:num) (dflt:num) (sym:num)
           (nout:num list) (stk:num list) (strts:num list) (cls:num list)
           (pfs:num list)
           (scs:num list) (pth:(num list # num list) list) (ars:num list)
           (rts:num list) (tps:num list) (e1:num list) (e2:num list)
           (dns:(num # num) list) (ord:num) =
    case symNode sym of
      NONE => NONE
    | SOME (tag, vr) =>

        let arres = (if (tag = 15) \/ (tag = 26) then
                       (case ars of [] => NONE | a::ars1 => SOME (a, ars1))
                     else SOME (0, ars)) in
        case arres of
          NONE => NONE
        | SOME (xa, ars1) =>
            case nChildren tag xa of
              NONE => NONE
            | SOME nk =>
                let strt = base + LENGTH nout in

                let (dv, dns1) =
                  (if (tag = 14) \/ (tag = 15) \/ (tag = 16) \/ (tag = 26)
                   then denTake dns dflt ord else (dflt, dns)) in
                case getChildren tmode nk strt stk strts tps of
                  NONE => NONE
                | SOME (cs, stk1, tps1) =>

                    let common =

                      (case cls of [] => NONE | c::cls1 => SOME (c, cls1))
                    in
                    case
                      (if tag = 0 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                            SOME (cc, []:num list, cls1, pfs, scs, pth, rts, e1, e2))
                       else if tag = 1 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case cs of [ch] =>
                            (case pfs of [] => NONE | x::pfs1 =>
                             case (emit64 ch, emit32 x) of
                               (SOME cb, SOME xb) =>
                                 SOME (cc, cb ++ xb, cls1, pfs1, scs, pth, rts, e1, e2)
                             | _ => NONE)
                          | _ => NONE)
                       else if tag = 2 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case cs of [lc; rc] =>
                            (case pfs of [] => NONE | x::pfs1 =>
                             case (emit32 x, emit64 lc, emit64 rc) of
                               (SOME xb, SOME lb, SOME rb) =>
                                 SOME (cc, xb ++ lb ++ rb, cls1, pfs1, scs, pth, rts, e1, e2)
                             | _ => NONE)
                          | _ => NONE)
                       else if tag = 3 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case cs of [lc; rc] =>
                            (case (emit64 lc, emit64 rc) of
                               (SOME lb, SOME rb) =>
                                 SOME (cc, lb ++ rb, cls1, pfs, scs, pth, rts, e1, e2)
                             | _ => NONE)
                          | _ => NONE)
                       else if tag = 6 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case cs of [lc; rc] =>
                            (case pth of
                               (stps, ifc)::pth1 =>
                                 (if ifc = [] then
                                    case (emit64 lc, emit64 rc,
                                          emit32 (LENGTH stps), stepBytes stps) of
                                      (SOME lb, SOME rb, SOME nb, SOME sb) =>
                                        SOME (cc, lb ++ rb ++ nb ++ sb,
                                              cls1, pfs, scs, pth1, rts, e1, e2)
                                    | _ => NONE
                                  else NONE)
                             | _ => NONE)
                          | _ => NONE)
                       else if tag = 4 then
                         (case cs of [ch] =>
                            (case derivAndE pool nout base vr ch of
                               NONE => NONE
                             | SOME NONE =>

                                 (case (cls, pfs) of
                                    (cc::cls1, x::pfs1) =>
                                      (case (emit64 ch, emit32 x) of
                                         (SOME cb, SOME xb) =>
                                           SOME (cc, cb ++ xb, cls1, pfs1, scs, pth, rts, e1, e2)
                                       | _ => NONE)
                                  | _ => NONE)
                             | SOME (SOME (cpre, taken, untaken)) =>
                                 let (h1, e1a) = escHit ord e1 in
                                 let (h2, e2a) = escHit ord e2 in
                                 let ccres =
                                   (if h1 then
                                      (case cls of [] => NONE | c::cls1 => SOME (c, cls1))
                                    else
                                      (case jlook judg (cpre, taken) of
                                         NONE => NONE
                                       | SOME j => SOME (j, cls))) in
                                 let otres =
                                   (if h2 then
                                      (case pfs of [] => NONE | x::pfs1 => SOME (x, pfs1))
                                    else SOME (untaken, pfs)) in
                                 (case (ccres, otres) of
                                    (SOME (cc, cls1), SOME (ot, pfs1)) =>
                                      (case (emit64 ch, emit32 ot) of
                                         (SOME cb, SOME ob) =>
                                           SOME (cc, cb ++ ob, cls1, pfs1, scs, pth, rts, e1a, e2a)
                                       | _ => NONE)
                                  | _ => NONE))
                          | _ => NONE)
                       else if tag = 5 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case cs of [ch] =>
                            (case pfs of [] => NONE | x::pfs1 =>
                             case (emit64 ch, emit32 x) of
                               (SOME cb, SOME xb) =>
                                 SOME (cc, cb ++ xb, cls1, pfs1, scs, pth, rts, e1, e2)
                             | _ => NONE)
                          | _ => NONE)
                       else if tag = 7 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case cs of [lc; rc] =>
                            (case scs of [] => NONE | w::scs1 =>
                             case pfs of
                               t::u::bf::pfs1 =>
                                 (case (emit64 lc, emit64 rc, emit32 w) of
                                    (SOME lb, SOME rb, SOME wb) =>
                                      (case (emit32 t, emit32 u, emit32 bf) of
                                         (SOME tb, SOME ub, SOME bb) =>
                                           SOME (cc, lb ++ rb ++ wb ++ tb ++ ub ++ bb,
                                                 cls1, pfs1, scs1, pth, rts, e1, e2)
                                       | _ => NONE)
                                  | _ => NONE)
                             | _ => NONE)
                          | _ => NONE)
                       else if tag = 8 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case cs of [ch] =>
                            (case pfs of
                               t::sx::e::pfs1 =>
                                 (case (emit64 ch, emit32 t, emit32 sx, emit32 e) of
                                    (SOME cb, SOME tb, SOME sxb, SOME eb) =>
                                      SOME (cc, cb ++ tb ++ sxb ++ eb,
                                            cls1, pfs1, scs, pth, rts, e1, e2)
                                  | _ => NONE)
                             | _ => NONE)
                          | _ => NONE)
                       else if tag = 9 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case cs of [ch] =>
                            (case derivConv pool nout base ch of
                               NONE => NONE
                             | SOME NONE =>
                                 (case pfs of
                                    t::sx::e::pfs1 =>
                                      (case (emit64 ch, emit32 t, emit32 sx, emit32 e) of
                                         (SOME cb, SOME tb, SOME sxb, SOME eb) =>
                                           SOME (cc, cb ++ tb ++ sxb ++ eb,
                                                 cls1, pfs1, scs, pth, rts, e1, e2)
                                       | _ => NONE)
                                  | _ => NONE)
                             | SOME (SOME (t, sx, e)) =>
                                 let (h2, e2a) = escHit ord e2 in
                                 if h2 then
                                   (case pfs of
                                      t1::sx1::e1v::pfs1 =>
                                        (case (emit64 ch, emit32 t1, emit32 sx1, emit32 e1v) of
                                           (SOME cb, SOME tb, SOME sxb, SOME eb) =>
                                             SOME (cc, cb ++ tb ++ sxb ++ eb,
                                                   cls1, pfs1, scs, pth, rts, e1, e2a)
                                         | _ => NONE)
                                    | _ => NONE)
                                 else
                                   (case (emit64 ch, emit32 t, emit32 sx, emit32 e) of
                                      (SOME cb, SOME tb, SOME sxb, SOME eb) =>
                                        SOME (cc, cb ++ tb ++ sxb ++ eb,
                                              cls1, pfs, scs, pth, rts, e1, e2a)
                                    | _ => NONE))
                          | _ => NONE)
                       else if tag = 10 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case cs of [ch] =>
                            (case pfs of
                               tmL::tmR::pfs1 =>
                                 (case scs of [] => NONE | bow::scs1 =>
                                  case (emit64 ch, emit32 tmL, emit32 tmR, emit8 bow) of
                                    (SOME cb, SOME tlb, SOME trb, SOME bwb) =>
                                      SOME (cc, cb ++ tlb ++ trb ++ bwb ++ [0; 0; 0],
                                            cls1, pfs1, scs1, pth, rts, e1, e2)
                                  | _ => NONE)
                             | _ => NONE)
                          | _ => NONE)
                       else if (tag = 11) \/ (tag = 13) then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case cs of [ch] =>
                            (case pfs of
                               t::sx::e::pfs1 =>
                                 (case scs of [] => NONE | deg::scs1 =>
                                  case pfs1 of
                                    pl::pd::pfs2 =>
                                      (case (emit64 ch, emit32 t, emit32 sx, emit32 e) of
                                         (SOME cb, SOME tb, SOME sxb, SOME eb) =>
                                           (case (emit32 deg, emit32 pl, emit32 pd) of
                                              (SOME db, SOME plb, SOME pdb) =>
                                                (if tag = 13 then
                                                   (case scs1 of
                                                      [] => NONE
                                                    | dt::scs2 =>
                                                        (case emit32 dt of
                                                           NONE => NONE
                                                         | SOME dtb =>
                                                             SOME (cc, cb ++ tb ++ sxb ++ eb ++
                                                                   db ++ plb ++ pdb ++ dtb,
                                                                   cls1, pfs2, scs2, pth, rts, e1, e2)))
                                                 else
                                                   SOME (cc, cb ++ tb ++ sxb ++ eb ++
                                                         db ++ plb ++ pdb,
                                                         cls1, pfs2, scs1, pth, rts, e1, e2))
                                            | _ => NONE)
                                       | _ => NONE)
                                  | _ => NONE)
                             | _ => NONE)
                          | _ => NONE)
                       else if tag = 12 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case pfs of
                            tmL::tmR::pfs1 =>
                              (case (emit32 tmL, emit32 tmR) of
                                 (SOME tlb, SOME trb) =>
                                   SOME (cc, tlb ++ trb, cls1, pfs1, scs, pth, rts, e1, e2)
                               | _ => NONE)
                          | _ => NONE)
                       else if tag = 14 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case pfs of
                            cmb::cnc::pfs1 =>
                              (case (emit32 cmb, emit32 cnc,
                                     emit64 dv) of
                                 (SOME ab, SOME bb, SOME db) =>
                                   SOME (cc, ab ++ bb ++ db, cls1, pfs1, scs, pth, rts, e1, e2)
                               | _ => NONE)
                          | _ => NONE)
                       else if tag = 15 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case cs of
                            [] => NONE
                          | ch::branchKids =>
                              (case pfs of
                                 t::sx::e::pfs1 =>
                                   (case (emit64 ch, emit32 t, emit32 sx, emit32 e,
                                          emit32 xa) of
                                      (SOME cb, SOME tb, SOME sxb, SOME eb, SOME nbb) =>
                                        (case subBranches branchKids pfs1 of
                                           NONE => NONE
                                         | SOME (brb, pfs2) =>
                                             case pfs2 of
                                               [] => NONE
                                             | cov::pfs3 =>
                                                 (case (emit32 cov,
                                                        emit64 dv) of
                                                    (SOME cvb, SOME db) =>
                                                      SOME (cc, cb ++ tb ++ sxb ++ eb ++ nbb ++
                                                            brb ++ cvb ++ db,
                                                            cls1, pfs3, scs, pth, rts, e1, e2)
                                                  | _ => NONE))
                                    | _ => NONE)
                               | _ => NONE))
                       else if tag = 16 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case cs of [lc; rc] =>
                            (case scs of
                               pa::po::scs1 =>
                                 (case (emit64 lc, emit64 rc, emit32 pa, emit32 po) of
                                    (SOME lb, SOME rb, SOME pab, SOME pob) =>
                                      (case ratsN 6 rts of
                                         NONE => NONE
                                       | SOME (qb, rts1) =>
                                           (case emit64 dv of
                                              NONE => NONE
                                            | SOME db =>
                                                SOME (cc, lb ++ rb ++ pab ++ pob ++ qb ++ db,
                                                      cls1, pfs, scs1, pth, rts1, e1, e2)))
                                  | _ => NONE)
                             | _ => NONE)
                          | _ => NONE)
                       else if (tag = 17) \/ (tag = 18) \/ (tag = 21) then

                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case cs of [ch] =>
                            (case scs of
                               a::b::scs1 =>
                                 (case (emit64 ch, emit32 a, emit32 b) of
                                    (SOME cb, SOME ab, SOME bb) =>
                                      SOME (cc, cb ++ ab ++ bb, cls1, pfs, scs1, pth, rts, e1, e2)
                                  | _ => NONE)
                             | _ => NONE)
                          | _ => NONE)
                       else if (tag = 19) \/ (tag = 20) then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case scs of
                            a::b::scs1 =>
                              (case (emit32 a, emit32 b) of
                                 (SOME ab, SOME bb) =>
                                   SOME (cc, ab ++ bb, cls1, pfs, scs1, pth, rts, e1, e2)
                               | _ => NONE)
                          | _ => NONE)
                       else if tag = 22 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case cs of [ch] =>
                            (case scs of
                               a::b::c::scs1 =>
                                 (case (emit64 ch, emit32 a, emit32 b, emit32 c) of
                                    (SOME chb, SOME ab, SOME bb, SOME cb) =>
                                      SOME (cc, chb ++ ab ++ bb ++ cb,
                                            cls1, pfs, scs1, pth, rts, e1, e2)
                                  | _ => NONE)
                             | _ => NONE)
                          | _ => NONE)
                       else if tag = 23 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case pfs of
                            [] => NONE
                          | t::pfs1 =>
                              (case emit32 t of
                                 NONE => NONE
                               | SOME tb => SOME (cc, tb, cls1, pfs1, scs, pth, rts, e1, e2)))
                       else if tag = 24 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case cs of [ch] =>
                            (case pfs of
                               t::u::pfs1 =>
                                 (case (emit64 ch, emit32 t, emit32 u) of
                                    (SOME cb, SOME tb, SOME ub) =>
                                      SOME (cc, cb ++ tb ++ ub, cls1, pfs1, scs, pth, rts, e1, e2)
                                  | _ => NONE)
                             | _ => NONE)
                          | _ => NONE)
                       else if tag = 25 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case cs of [supN; con] =>
                            (case pfs of
                               [] => NONE
                             | ctr::pfs1 =>
                                 (case pth of
                                    (stps, ifc)::pth1 =>
                                      (case (emit64 supN, emit64 con, emit32 ctr,
                                             emit32 (LENGTH stps), stepBytes stps) of
                                         (SOME sb, SOME cb, SOME ctb, SOME nb, SOME stb) =>
                                           (case (emit32 (LENGTH ifc), wiresU32 ifc) of
                                              (SOME ib, SOME wb) =>
                                                SOME (cc, sb ++ cb ++ ctb ++ nb ++ stb ++
                                                      ib ++ wb,
                                                      cls1, pfs1, scs, pth1, rts, e1, e2)
                                            | _ => NONE)
                                       | _ => NONE)
                                  | _ => NONE))
                          | _ => NONE)
                       else if tag = 26 then
                         (case common of NONE => NONE | SOME (cc, cls1) =>
                          case (emit32 xa, kids64 cs) of
                            (SOME ncb, SOME kb) =>
                              (case pfs of
                                 cmb::cnc::pfs1 =>
                                   (case scs of
                                      [] => NONE
                                    | th::scs1 =>
                                        (case (emit32 cmb, emit32 cnc,
                                               emit64 dv, emit32 th) of
                                           (SOME ab, SOME bb, SOME db, SOME thb) =>
                                             SOME (cc, ncb ++ kb ++ ab ++ bb ++ db ++ thb,
                                                   cls1, pfs1, scs1, pth, rts, e1, e2)
                                         | _ => NONE)
                                    )
                               | _ => NONE)
                          | _ => NONE)
                       else NONE)
                    of
                      NONE => NONE
                    | SOME (cc, flds, cls1, pfs1, scs1, pth1, rts1, e1b, e2b) =>
                        case emit32 cc of
                          NONE => NONE
                        | SOME ccb =>
                            SOME (nout ++ [tag; vr; 0; 0] ++ ccb ++ flds,
                                  stk1, strt::strts, cls1, pfs1, scs1, pth1, ars1,
                                  rts1, tps1, e1b, e2b, dns1, ord + 1)
End

Definition nodeLoop_def:
  (nodeLoop pool judg (base:num) (tmode:num) (dflt:num) ([]:num list)
            nout stk (strts:num list) cls pfs scs pth ars rts tps e1 e2
            (dns:(num # num) list) (ord:num) =
     SOME (nout:num list, stk:num list, e1:num list, e2:num list, dns)) /\
  (nodeLoop pool judg base tmode dflt (s::ss)
            nout stk strts cls pfs scs pth ars rts tps e1 e2 dns ord =
     case nodeStep pool judg base tmode dflt s
                   nout stk strts cls pfs scs pth ars rts tps e1 e2 dns ord of
       NONE => NONE
     | SOME (nout1, stk1, strts1, cls1, pfs1, scs1, pth1, ars1, rts1, tps1,
             e1a, e2a, dns1, ord1) =>
         nodeLoop pool judg base tmode dflt ss
                  nout1 stk1 strts1 cls1 pfs1 scs1 pth1 ars1 rts1 tps1
                  e1a e2a dns1 ord1)
End

Definition hdrSectionsOK_def:
  hdrSectionsOK (hdr:num list) =
    case (rdU64 hdr 16, rdU64 hdr 24, rdU64 hdr 32, rdU64 hdr 40,
          rdU64 hdr 48, rdU64 hdr 56) of
      (SOME so, SOME sl, SOME po, SOME pl, SOME dof, SOME dl) =>
        if so + sl <= LENGTH hdr /\ po + pl <= LENGTH hdr /\
           dof + dl <= LENGTH hdr
        then SOME dof else NONE
    | _ => NONE
End

Definition decodeSpec_def:
  decodeSpec cols =
    if ~(allBytes cols.hdrImage /\ allBytes cols.nodeRat /\
         allBytes cols.poolNum /\ allBytesL cols.poolDenDict /\
         ((cols.topoMode = 0) \/ (cols.topoMode = 1))) then NONE
    else
      case hdrSectionsOK cols.hdrImage of
        NONE => NONE
      | SOME doff =>
          case complexNVerts cols.hdrImage doff of
            NONE => NONE
          | SOME nv =>
              case poolLoop nv cols.poolDenDict cols.poolTag
                            [] cols.poolRef cols.poolNumLen cols.poolDenId
                            cols.poolNum cols.poolMisc [] of
                NONE => NONE
              | SOME (pout, refs1, nls1, dis1, nums1, miscs1, judg) =>
                  if ~(LENGTH pout < 18446744073709551616) then NONE
                  else
                    case nodeLoop pout judg (8 + LENGTH pout) cols.topoMode
                                  cols.denDefault cols.nodeTag
                                  [] [] [] cols.nodeConcl cols.nodePref
                                  cols.nodeScal cols.nodePath cols.nodeArity
                                  cols.nodeRat cols.nodeTopo cols.nodeEsc
                                  cols.nodeEsc2 cols.nodeDen 0 of
                      NONE => NONE
                    | SOME (nout, stk, e1f, e2f, dnsf) =>

                        if ((cols.topoMode = 0) /\ ~(LENGTH stk = 1)) \/
                           ~(e1f = []) \/ ~(e2f = []) \/ ~(dnsf = [])
                        then NONE
                        else
                          SOME (cols.hdrImage ++ le64t (LENGTH pout) ++ pout ++ nout)
End

Theorem allBytes_APPEND:
  !xs ys. allBytes (xs ++ ys) <=> allBytes xs /\ allBytes ys
Proof
  Induct >> rw[allBytes_def] >> metis_tac[]
QED

Theorem le32t_length:
  !v. LENGTH (le32t v) = 4
Proof
  rw[le32t_def]
QED

Theorem le64t_length:
  !v. LENGTH (le64t v) = 8
Proof
  rw[le64t_def, le32t_def]
QED

Theorem le32t_bytes:
  !v. allBytes (le32t v)
Proof
  rw[le32t_def] >> simp[allBytes_def]
QED

Theorem emit8_thm:
  !v b. (emit8 v = SOME b) ==> (LENGTH b = 1) /\ allBytes b
Proof
  rw[emit8_def] >> rw[allBytes_def]
QED

Theorem emit16_thm:
  !v b. (emit16 v = SOME b) ==> (LENGTH b = 2) /\ allBytes b
Proof
  rw[emit16_def] >> simp[allBytes_def, DIV_LT_X]
QED

Theorem emit32_thm:
  !v b. (emit32 v = SOME b) ==> (LENGTH b = 4) /\ allBytes b
Proof
  rw[emit32_def] >> simp[le32t_length, le32t_bytes]
QED

Theorem emit64_thm:
  !v b. (emit64 v = SOME b) ==> (LENGTH b = 8) /\ allBytes b
Proof
  rw[emit64_def] >> simp[le64t_def, allBytes_APPEND, le32t_bytes, le32t_length]
QED

Theorem decodeSpec_hdrImage_prefix:
  !cols out. (decodeSpec cols = SOME out) ==>
             ?rest. out = cols.hdrImage ++ rest
Proof
  rw[decodeSpec_def] >> gvs[AllCaseEqs()] >> metis_tac[]
QED

val _ = export_theory ();
