(*
  certOfRows — the transcode from a sealed geolog proof-artefact's
  object rows to the relational checker's columns record: the arrow
  composing the native geolog reader tier with the banked relational
  checking tier (readGeolog -> bindChain -> certOfRows -> checkJoins).
  Mirrors the elision/escape law decision for decision and targets the
  exact predicates (wfColumns) the emitted value must satisfy.
*)
Theory geolog_cert

Ancestors
  arithmetic list rich_list option pair sorting string rat integer
  geolog_read geolog_bind geolog_o2
  qtsl_dyadic qtsl_qarith qtsl_catalogue qtsl_cert qtsl_cols

Definition u16le_def:
  u16le (n:num) : num list = [n MOD 256; (n DIV 256) MOD 256]
End

Definition u32leG_def:
  u32leG (n:num) : num list =
    [n MOD 256; (n DIV 256) MOD 256; (n DIV 65536) MOD 256;
     (n DIV 16777216) MOD 256]
End

Definition u64leG_def:
  u64leG (n:num) : num list =
    u32leG (n MOD 4294967296) ++ u32leG (n DIV 4294967296)
End

Definition leLimbs_def:
  leLimbs (v:num) : num list =
    if v = 0 then [] else v MOD 256 :: leLimbs (v DIV 256)
Termination
  WF_REL_TAC `measure I` >> rw[]
  >> irule arithmeticTheory.DIV_LESS >> simp[]
End

Definition encUMin_def:
  encUMin (v:num) : num list = if v = 0 then [0] else leLimbs v
End

Definition encSMin_def:
  encSMin (neg:bool) (mag:num) : num list =
    if mag = 0 then [0]
    else if ~neg then
      (let bs = leLimbs mag in
         if LAST bs < 128 then bs else bs ++ [0])
    else
      let bs = leLimbs mag in
      let n = if mag <= 2 ** (8 * LENGTH bs - 1)
              then LENGTH bs else LENGTH bs + 1 in
        leLimbs (2 ** (8 * n) - mag)
End

Definition encRatBytes_def:
  encRatBytes (q:rat) : num list # num list =
    (encSMin (RATN q < 0) (Num (ABS (RATN q))), encUMin (RATD q))
End

Definition encRatV0_def:
  encRatV0 (q:rat) : num list =
    let (nb, db) = encRatBytes q in
      u32leG (LENGTH nb) ++ u32leG (LENGTH db) ++ nb ++ db
End

Definition bitsByteA_def:
  bitsByteA (bs:bool list) (w:num) (acc:num) : num =
    case bs of
    | [] => acc
    | (b::rest) => bitsByteA rest (w * 2) (if b then acc + w else acc)
End

Definition encBits_def:
  encBits (bs:bool list) : num list =
    if NULL bs then []
    else bitsByteA (TAKE 8 bs) 1 0 :: encBits (DROP 8 bs)
Termination
  WF_REL_TAC `measure LENGTH` >> rw[] >> Cases_on `bs` >> gvs[]
End

Definition kindCode_def:
  kindCode k : num =
    case k of KBool => 0 | KInt => 1 | KRat => 2 | KF16 => 3
            | KBF16 => 4 | KF32 => 5 | KF64 => 6
End

Definition signCode_def:
  signCode s : num = case s of Nn => 0 | Signed => 1
End

Definition extCode_def:
  extCode e : num = case e of ExtFin => 0 | ExtExt => 1
End

Definition bowtieCode_def:
  bowtieCode b : num =
    case b of BowLt => 0 | BowLe => 1 | BowEq => 2
            | BowGe => 3 | BowGt => 4 | BowNe => 5
End

Datatype:
  vocab =

      VsProof | VsTerm | VsFormula | VsJudgment | VsCert | VsWire
    | VsSimpC | VsSimplex | VsExtSet | VsCtxPath | VsDtype | VsShape
    | VsTensorType | VsKind | VsSign | VsExt
    | VsRule num
    | VsOOF string

    | VfTVar | VfTConst | VfTAdd | VfTMul | VfTSub | VfTNeg | VfTIdx
    | VfTHole
    | VfFAtom num | VfFInRegion | VfFAnd | VfFOr | VfFTrue | VfFFalse
    | VfFSpH
    | VfPathHere | VfPathL | VfPathR
    | VfMkDtype | VfShapeEmpty | VfShapeCons | VfMkTensorType
    | VfKindC num | VfSignC num | VfExtC num

    | VfJudgPre | VfJudgPost | VfProofConcludes
    | VfCertRoot | VfCertTheta | VfCertNWires | VfCertNApps
    | VfCertNComplexes
    | VfWireIndex | VfWireType
    | VfSimpCIndex | VfSimpCNVert | VfSimpCAmbDim | VfSimpCNSimp
    | VfSimpCNCells
    | VfSimplexComplex | VfExtSetSimplex
    | VfRuleProof num
    | VfRF num num

    | VfSimpCCoord | VfCplxSimpAt
    | VrSimplexContains | VrExtSetContains
    | VrCellSimpHasV | VrCellExtHasV
    | VrPromIface | VrSyzComp
    | VfOOF string
End

Definition isSortV_def:
  isSortV v <=>
    case v of
    | VsProof => T | VsTerm => T | VsFormula => T | VsJudgment => T
    | VsCert => T | VsWire => T | VsSimpC => T | VsSimplex => T
    | VsExtSet => T | VsCtxPath => T | VsDtype => T | VsShape => T
    | VsTensorType => T | VsKind => T | VsSign => T | VsExt => T
    | VsRule r => T | VsOOF s => T
    | _ => F
End

Definition isCtorV_def:
  isCtorV v <=>
    case v of
    | VfTVar => T | VfTConst => T | VfTAdd => T | VfTMul => T
    | VfTSub => T | VfTNeg => T | VfTIdx => T | VfTHole => T
    | VfFAtom b => T | VfFInRegion => T | VfFAnd => T | VfFOr => T
    | VfFTrue => T | VfFFalse => T | VfFSpH => T
    | VfPathHere => T | VfPathL => T | VfPathR => T
    | VfMkDtype => T | VfShapeEmpty => T | VfShapeCons => T
    | VfMkTensorType => T
    | VfKindC k => T | VfSignC s => T | VfExtC e => T
    | _ => F
End

Definition isFieldV_def:
  isFieldV v <=>
    case v of
    | VfJudgPre => T | VfJudgPost => T | VfProofConcludes => T
    | VfCertRoot => T | VfCertTheta => T | VfCertNWires => T
    | VfCertNApps => T | VfCertNComplexes => T
    | VfWireIndex => T | VfWireType => T
    | VfSimpCIndex => T | VfSimpCNVert => T | VfSimpCAmbDim => T
    | VfSimpCNSimp => T | VfSimpCNCells => T
    | VfSimplexComplex => T | VfExtSetSimplex => T
    | VfRuleProof r => T | VfRF r k => T
    | _ => F
End

Definition isRecV_def:
  isRecV v <=>
    case v of
    | VfSimpCCoord => T | VfCplxSimpAt => T
    | VrPromIface => T | VrSyzComp => T
    | _ => F
End

Definition isRelV_def:
  isRelV v <=>
    case v of
    | VrSimplexContains => T | VrExtSetContains => T
    | VrCellSimpHasV => T | VrCellExtHasV => T
    | _ => F
End

Definition v0fragTag_def:
  v0fragTag (r:num) <=> r <= 12 \/ r = 14 \/ (23 <= r /\ r <= 26)
End

Type pins = ``:((num list # num) # vocab) list``

Definition resolveRef_def:
  resolveRef (pins:pins) (deps:(num list) list) (r:elemref)
             : vocab option =
    case r of
    | ERLocal n => NONE
    | ERExt d c =>
        (case oEL d deps of
         | NONE => NONE
         | SOME chid => ALOOKUP pins (chid, c))
End

Datatype:
  cres = COk columns | CErr rclass string num
End

Definition natOfVal_def:
  natOfVal (v:gvalue) : num option =
    case v of
    | GVLit code p => if code = 2 then SOME (leN p) else NONE
    | _ => NONE
End

Definition qOfVal_def:
  qOfVal (v:gvalue) : rat option =
    case v of
    | GVLit code p =>
        if code <> 0 then NONE else
        (case qShape p of
         | NONE => NONE
         | SOME (nb, db) =>
             let vv = leN nb in
             let m = 256 ** LENGTH nb in
             let neg = ~(2 * vv < m) in
             let mag = if neg then m - vv else vv in
             let d = leN db in
               if d = 0 then NONE
               else SOME ((if neg then -(&mag / &d) else (&mag / &d)):rat))
    | _ => NONE
End

Definition elemOfVal_def:
  elemOfVal (v:gvalue) : num option =
    case v of
    | GVRef (ERLocal n) => SOME n
    | _ => NONE
End

Datatype:
  rowtbls = <|
    tsorts : vocab list ;
    tctor  : (num # (vocab # gvalue list)) list ;
    tfld   : ((vocab # num) # gvalue) list ;
    trp    : (num # (num # num)) list ;
    trec   : (vocab # gvalue list # gvalue option) list
  |>
End

Datatype:
  scanres = ScOk rowtbls | ScErr rclass string num
End

Definition scanOp_def:
  scanOp (pins:pins) (deps:(num list) list)
         (st:(vocab list # (num # (vocab # gvalue list)) list #
              ((vocab # num) # gvalue) list # (num # (num # num)) list #
              (vocab # gvalue list # gvalue option) list # num))
         (op:gop)
         : (vocab list # (num # (vocab # gvalue list)) list #
            ((vocab # num) # gvalue) list # (num # (num # num)) list #
            (vocab # gvalue list # gvalue option) list # num) option
           # (rclass # string # num) option =
    let (sorts, ctor, fld, rp, rec, i) = st in
    case op of
    | GElta r =>
        (case r of
         | ERLocal n => (NONE, SOME (CUnread, "local_schema_sort_ref", i))
         | ERExt d c =>
           (case resolveRef pins deps r of
            | NONE => (NONE, SOME (CUnsupp, "schema_sort_unpinned", i))
            | SOME v =>
                if isSortV v
                then (SOME (v::sorts, ctor, fld, rp, rec, i + 1), NONE)
                else (NONE, SOME (CUnread, "sort_position_not_a_sort", i))))
    | GRela r args =>
        (case resolveRef pins deps r of
         | NONE => (NONE, SOME (CUnsupp, "schema_rel_unpinned", i))
         | SOME v =>
             if isRelV v
             then (SOME (sorts, ctor, fld, rp, (v, args, NONE)::rec, i + 1),
                   NONE)
             else (NONE, SOME (CUnsupp, "rel_outside_fragment", i)))
    | GFuna r args value =>
        (case resolveRef pins deps r of
         | NONE => (NONE, SOME (CUnsupp, "schema_fun_unpinned", i))
         | SOME v =>
             if isCtorV v then
               (case elemOfVal value of
                | NONE => (NONE, SOME (CUnread, "ctor_value_not_local_elem", i))
                | SOME e =>
                    if ALOOKUP ctor e = NONE
                    then (SOME (sorts, (e, (v, args))::ctor, fld, rp, rec,
                                i + 1), NONE)
                    else (NONE, SOME (CUnread, "ambiguous_constructor", i)))
             else if isFieldV v then
               (case args of
                | [av] =>
                  (case elemOfVal av of
                   | NONE => (NONE, SOME (CUnread, "field_subject_not_elem", i))
                   | SOME s =>
                     (case v of
                      | VfRuleProof rt =>
                          (case elemOfVal value of
                           | NONE => (NONE, SOME (CUnread,
                                                  "rule_proof_not_elem", i))
                           | SOME p =>
                               if ALOOKUP rp p = NONE
                               then (SOME (sorts, ctor, fld,
                                           (p, (s, rt))::rp, rec, i + 1),
                                     NONE)
                               else (NONE, SOME (CUnread,
                                                 "proof_claimed_twice", i)))
                      | _ =>
                          if ALOOKUP fld (v, s) = NONE
                          then (SOME (sorts, ctor,
                                      ((v, s), value)::fld, rp, rec, i + 1),
                                NONE)
                          else (NONE, SOME (CUnread, "duplicate_fun_row", i))))
                | _ => (NONE, SOME (CUnread, "field_arity", i)))
             else if isRecV v then
               (SOME (sorts, ctor, fld, rp, (v, args, SOME value)::rec,
                      i + 1), NONE)
             else
               (NONE, SOME (CUnsupp, "fun_outside_fragment", i)))
    | GEltd r => (NONE, SOME (CUnsupp, "eltd_in_cert_body", i))
    | GCert fmt m c => (NONE, SOME (CUnsupp, "certblob_in_cert_body", i))
    | GUnknown k p => (NONE, SOME (CUnsupp, "op_kind_in_cert_body", i))
End

Definition scanOpsA_def:
  scanOpsA pins deps st (ops:gop list) : scanres =
    case ops of
    | [] =>
        (let (sorts, ctor, fld, rp, rec, i) = st in
           ScOk <| tsorts := REVERSE sorts ; tctor := ctor ; tfld := fld ;
                   trp := rp ; trec := REVERSE rec |>)
    | (op::rest) =>
        (case scanOp pins deps st op of
         | (SOME st', NONE) => scanOpsA pins deps st' rest
         | (_, SOME (c, t, w)) => ScErr c t w
         | (NONE, NONE) => ScErr CUnread "scan_impossible" 0)
End

Definition scanOps_def:
  scanOps pins deps ops = scanOpsA pins deps ([], [], [], [], [], 0) ops
End

Definition sortAt_def:
  sortAt (tb:rowtbls) (e:num) : vocab option = oEL e tb.tsorts
End

Definition ctorAt_def:
  ctorAt (tb:rowtbls) (e:num) : (vocab # gvalue list) option =
    ALOOKUP tb.tctor e
End

Definition fldAt_def:
  fldAt (tb:rowtbls) (v:vocab) (e:num) : gvalue option =
    ALOOKUP tb.tfld (v, e)
End

Definition fldNat_def:
  fldNat (tb:rowtbls) (v:vocab) (e:num) : num option =
    case fldAt tb v e of
    | NONE => NONE
    | SOME x => natOfVal x
End

Definition fldElem_def:
  fldElem (tb:rowtbls) (v:vocab) (e:num) : num option =
    case fldAt tb v e of
    | NONE => NONE
    | SOME x => elemOfVal x
End

Definition rowsOfV_def:
  rowsOfV (tb:rowtbls) (v:vocab) : (gvalue list # gvalue option) list =
    MAP (\r. (FST (SND r), SND (SND r)))
        (FILTER (\r. FST r = v) tb.trec)
End

Definition idxOfA_def:
  idxOfA (x:'a) (l:'a list) (i:num) : num option =
    case l of
    | [] => NONE
    | (h::t) => if h = x then SOME i else idxOfA x t (i + 1)
End

Definition idxOf_def:
  idxOf (x:'a) (l:'a list) : num option = idxOfA x l 0
End

Definition idxPairs_def:
  idxPairs (tb:rowtbls) (v:vocab) : (num # num) list =
    FLAT (GENLIST (\e. case fldNat tb v e of
                       | NONE => []
                       | SOME k => [(k, e)])
                  (LENGTH tb.tsorts))
End

Definition denseIdx_def:
  denseIdx (tb:rowtbls) (v:vocab) (n:num) : (num list) option =
    let ps = idxPairs tb v in
      if LENGTH ps = n /\ ALL_DISTINCT (MAP FST ps) /\
         EVERY (\p. FST p < n) ps
      then SOME (MAP (\k. case ALOOKUP ps k of SOME e => e | NONE => 0)
                     (COUNT_LIST n))
      else NONE
End

Definition recPairsA_def:
  recPairsA (rows:(gvalue list # gvalue option) list) (anchor:num)
            (acc:(num # num) list) : ((num # num) list) option =
    case rows of
    | [] => SOME acc
    | ((args, value)::rest) =>
      (case args of
       | [kv; av] =>
         (case natOfVal kv of
          | NONE => NONE
          | SOME k =>
            case elemOfVal av of
            | NONE => NONE
            | SOME a =>
              if a <> anchor then recPairsA rest anchor acc
              else
                (case value of
                 | NONE => NONE
                 | SOME ve =>
                   (case elemOfVal ve of
                    | NONE => NONE
                    | SOME e => recPairsA rest anchor ((k, e)::acc))))
       | _ => NONE)
End

Definition denseRecFor_def:
  denseRecFor (tb:rowtbls) (v:vocab) (anchor:num) (n:num)
              : (num list) option =
    case recPairsA (rowsOfV tb v) anchor [] of
    | NONE => NONE
    | SOME ps =>
        if LENGTH ps = n /\ ALL_DISTINCT (MAP FST ps) /\
           EVERY (\p. FST p < n) ps
        then SOME (MAP (\k. case ALOOKUP ps k of SOME e => e | NONE => 0)
                       (COUNT_LIST n))
        else NONE
End

Definition maskVsA_def:
  maskVsA (rows:(gvalue list # gvalue option) list) (subj:num)
          (acc:num list) : (num list) option =
    case rows of
    | [] => SOME acc
    | ((args, value)::rest) =>
      (case args of
       | [sv; vv] =>
         (case elemOfVal sv of
          | NONE => NONE
          | SOME s =>
            if s <> subj then maskVsA rest subj acc
            else
              (case natOfVal vv of
               | NONE => NONE
               | SOME vtx => maskVsA rest subj (vtx::acc)))
       | _ => NONE)
End

Definition maskOf_def:
  maskOf (tb:rowtbls) (v:vocab) (subj:num) (nv:num) : (bool list) option =
    case maskVsA (rowsOfV tb v) subj [] of
    | NONE => NONE
    | SOME vs =>
        if EVERY (\x. x < nv) vs
        then SOME (GENLIST (\x. MEM x vs) nv)
        else NONE
End

Definition cellVsA_def:
  cellVsA (rows:(gvalue list # gvalue option) list) (cxe:num)
          (acc:(num # num) list) : ((num # num) list) option =
    case rows of
    | [] => SOME acc
    | ((args, value)::rest) =>
      (case args of
       | [cv; av; vv] =>
         (case elemOfVal av of
          | NONE => NONE
          | SOME a =>
            if a <> cxe then cellVsA rest cxe acc
            else
              (case natOfVal cv of
               | NONE => NONE
               | SOME cell =>
                 (case natOfVal vv of
                  | NONE => NONE
                  | SOME vtx => cellVsA rest cxe ((cell, vtx)::acc))))
       | _ => NONE)
End

Definition cellMasks_def:
  cellMasks (tb:rowtbls) (v:vocab) (cxe:num) (ncell:num) (nv:num)
            : ((bool list) list) option =
    case cellVsA (rowsOfV tb v) cxe [] of
    | NONE => NONE
    | SOME ps =>
        if EVERY (\p. FST p < ncell /\ SND p < nv) ps
        then SOME (GENLIST (\c. GENLIST (\x. MEM (c, x) ps) nv) ncell)
        else NONE
End

Definition coordAlA_def:
  coordAlA (rows:(gvalue list # gvalue option) list) (cxe:num)
           (nv:num) (amb:num) (acc:((num # num) # rat) list)
           : (((num # num) # rat) list) option =
    case rows of
    | [] => SOME acc
    | ((args, value)::rest) =>
      (case args of
       | [av; jv; vv] =>
         (case elemOfVal av of
          | NONE => NONE
          | SOME a =>
            if a <> cxe then coordAlA rest cxe nv amb acc
            else
              (case natOfVal jv of
               | NONE => NONE
               | SOME j =>
                 (case natOfVal vv of
                  | NONE => NONE
                  | SOME vtx =>
                    if ~(vtx < nv /\ j < amb) then NONE
                    else if ALOOKUP acc (vtx, j) <> NONE then NONE
                    else
                      (case value of
                       | NONE => NONE
                       | SOME qv =>
                         (case qOfVal qv of
                          | NONE => NONE
                          | SOME q =>
                              coordAlA rest cxe nv amb
                                       (((vtx, j), q)::acc))))))
       | _ => NONE)
End

Definition coordsFor_def:
  coordsFor (tb:rowtbls) (cxe:num) (nv:num) (amb:num)
            : (rat list list) option =
    case coordAlA (rowsOfV tb VfSimpCCoord) cxe nv amb [] of
    | NONE => NONE
    | SOME al =>
        if LENGTH al = nv * amb
        then SOME (GENLIST
                     (\vtx. GENLIST
                              (\j. case ALOOKUP al (vtx, j) of
                                   | SOME q => q
                                   | NONE => 0)
                              amb)
                     nv)
        else NONE
End

Definition gConstCode_def:
  gConstCode (tb:rowtbls) (e:num) : (vocab # num) option =
    case ctorAt tb e of
    | SOME (VfKindC n, []) => SOME (VfKindC n, n)
    | SOME (VfSignC n, []) => SOME (VfSignC n, n)
    | SOME (VfExtC n, []) => SOME (VfExtC n, n)
    | _ => NONE
End

Definition gShapeF_def:
  gShapeF (tb:rowtbls) (fuel:num) (e:num) : (num list) option =
    case fuel of
    | 0 => NONE
    | SUC f =>
      if sortAt tb e <> SOME VsShape then NONE else
      (case ctorAt tb e of
       | SOME (VfShapeEmpty, args) =>
           (if args = [] then SOME [] else NONE)
       | SOME (VfShapeCons, [h; t]) =>
           (case natOfVal h of
            | NONE => NONE
            | SOME hv =>
              (case elemOfVal t of
               | NONE => NONE
               | SOME te =>
                   let r = gShapeF tb f te in
                     case r of
                     | NONE => NONE
                     | SOME rest => SOME (hv::rest)))
       | _ => NONE)
End

Definition gDtypeV_def:
  gDtypeV (tb:rowtbls) (e:num) : dtype option =
    if sortAt tb e <> SOME VsDtype then NONE else
    case ctorAt tb e of
    | SOME (VfMkDtype, [ea; ka; sa]) =>

        (case elemOfVal ea of
         | NONE => NONE
         | SOME ee =>
           case elemOfVal ka of
           | NONE => NONE
           | SOME ke =>
           case elemOfVal sa of
           | NONE => NONE
           | SOME se =>
           case gConstCode tb ee of
           | SOME (VfExtC en, _) =>
             (case gConstCode tb ke of
              | SOME (VfKindC kn, _) =>
                (case gConstCode tb se of
                 | SOME (VfSignC sn, _) =>
                   (case kindOf kn of
                    | NONE => NONE
                    | SOME kd =>
                      case signOf sn of
                      | NONE => NONE
                      | SOME sg =>
                      case extOf en of
                      | NONE => NONE
                      | SOME et =>
                        SOME <| kind := kd ; sign := sg ; ext := et |>)
                 | _ => NONE)
              | _ => NONE)
           | _ => NONE)
    | _ => NONE
End

Definition gTTypeV_def:
  gTTypeV (tb:rowtbls) (e:num) : tensortype option =
    if sortAt tb e <> SOME VsTensorType then NONE else
    case ctorAt tb e of
    | SOME (VfMkTensorType, [dt; sh]) =>

        (case elemOfVal dt of
         | NONE => NONE
         | SOME de =>
           case elemOfVal sh of
           | NONE => NONE
           | SOME she =>
           case gDtypeV tb de of
           | NONE => NONE
           | SOME d =>
           case gShapeF tb (LENGTH tb.tsorts + 1) she of
           | NONE => NONE
           | SOME s => SOME <| shape := s ; dtype := d |>)
    | _ => NONE
End

Definition gWiresA_def:
  gWiresA (tb:rowtbls) (wes:num list) (i:num)
          (accW:(num # num) list) (accT:tensortype list)
          : ((num # num) list # tensortype list) option =
    case wes of
    | [] => SOME (accW, REVERSE accT)
    | (e::rest) =>
        if sortAt tb e <> SOME VsWire then NONE else
        (case fldElem tb VfWireType e of
         | NONE => NONE
         | SOME te =>
           (case gTTypeV tb te of
            | NONE => NONE
            | SOME ty => gWiresA tb rest (i + 1) ((e, i)::accW) (ty::accT)))
End

Definition gWires_def:
  gWires (tb:rowtbls) (nw:num)
         : ((num # num) list # tensortype list) option =
    case denseIdx tb VfWireIndex nw of
    | NONE => NONE
    | SOME wes => gWiresA tb wes 0 [] []
End

Definition simpMasks_def:
  simpMasks (tb:rowtbls) (cxe:num) (nv:num) (sxes:num list)
            : ((bool list) list) option =
    case sxes of
    | [] => SOME []
    | (e::rest) =>
        if sortAt tb e <> SOME VsSimplex then NONE else
        if fldElem tb VfSimplexComplex e <> SOME cxe then NONE else
        (case maskOf tb VrSimplexContains e nv of
         | NONE => NONE
         | SOME m =>
           (case simpMasks tb cxe nv rest of
            | NONE => NONE
            | SOME ms => SOME (m::ms)))
End

Definition gComplex1_def:
  gComplex1 (tb:rowtbls) (cxe:num) : simpc option =
    if sortAt tb cxe <> SOME VsSimpC then NONE else
    case fldNat tb VfSimpCNVert cxe of
    | NONE => NONE
    | SOME nv =>
    case fldNat tb VfSimpCAmbDim cxe of
    | NONE => NONE
    | SOME amb =>
    if 4294967295 < nv \/ 4294967295 < amb then NONE else
    case coordsFor tb cxe nv amb of
    | NONE => NONE
    | SOME coords =>
    case fldNat tb VfSimpCNSimp cxe of
    | NONE => NONE
    | SOME nsimp =>
    case denseRecFor tb VfCplxSimpAt cxe nsimp of
    | NONE => NONE
    | SOME sxes =>

    case simpMasks tb cxe nv sxes of
    | NONE => NONE
    | SOME simps =>
    case fldNat tb VfSimpCNCells cxe of
    | NONE => NONE
    | SOME ncell =>
    case cellMasks tb VrCellSimpHasV cxe ncell nv of
    | NONE => NONE
    | SOME sm =>
    case cellMasks tb VrCellExtHasV cxe ncell nv of
    | NONE => NONE
    | SOME em =>
      SOME <| nVertices := nv ; ambDim := amb ; coord := coords ;
              simplices := simps ; cells := ZIP (sm, em) |>
End

Definition gComplexesA_def:
  gComplexesA (tb:rowtbls) (es:num list) (acc:simpc list)
              : (simpc list) option =
    case es of
    | [] => SOME (REVERSE acc)
    | (e::rest) =>
      (case gComplex1 tb e of
       | NONE => NONE
       | SOME cx => gComplexesA tb rest (cx::acc))
End

Definition gComplexes_def:
  gComplexes (tb:rowtbls) (nc:num) : (num list # simpc list) option =
    case denseIdx tb VfSimpCIndex nc of
    | NONE => NONE
    | SOME cxE =>
      (case gComplexesA tb cxE [] of
       | NONE => NONE
       | SOME cxs => SOME (cxE, cxs))
End

Datatype:
  rctx = <| rtb : rowtbls ; rwid : (num # num) list ;
            rcxE : num list ; rcxs : simpc list |>
End

Definition gSimplexV_def:
  gSimplexV (rc:rctx) (e:num) : simplex option =
    if sortAt rc.rtb e <> SOME VsSimplex then NONE else
    case fldElem rc.rtb VfSimplexComplex e of
    | NONE => NONE
    | SOME ce =>
      case idxOf ce rc.rcxE of
      | NONE => NONE
      | SOME ci =>
        case oEL ci rc.rcxs of
        | NONE => NONE
        | SOME cx =>
          case maskOf rc.rtb VrSimplexContains e cx.nVertices of
          | NONE => NONE
          | SOME m => SOME <| complex := cx ; vmask := m |>
End

Definition gExtSetV_def:
  gExtSetV (rc:rctx) (e:num) : extensionset option =
    if sortAt rc.rtb e <> SOME VsExtSet then NONE else
    case fldElem rc.rtb VfExtSetSimplex e of
    | NONE => NONE
    | SOME se =>
      case gSimplexV rc se of
      | NONE => NONE
      | SOME sx =>
        case maskOf rc.rtb VrExtSetContains e sx.complex.nVertices of
        | NONE => NONE
        | SOME m => SOME <| simplex := sx ; emask := m |>
End

Definition gTermF_def:
  gTermF (rc:rctx) (fuel:num) (e:num) : term option =
    case fuel of
    | 0 => NONE
    | SUC f =>
      if sortAt rc.rtb e <> SOME VsTerm then NONE else
      (case ctorAt rc.rtb e of
       | SOME (VfTHole, args) =>
           (if args = [] then SOME (TmVar 4294967295) else NONE)
       | SOME (VfTVar, [wv]) =>
           (case elemOfVal wv of
            | NONE => NONE
            | SOME we =>
              (case ALOOKUP rc.rwid we of
               | NONE => NONE
               | SOME id => SOME (TmVar id)))
       | SOME (VfTConst, [qv]) =>
           (case qOfVal qv of
            | NONE => NONE
            | SOME q => SOME (TmConst q))
       | SOME (VfTAdd, [l; r]) =>
           (case elemOfVal l of
            | NONE => NONE
            | SOME le =>
              case elemOfVal r of
              | NONE => NONE
              | SOME re =>
                let a = gTermF rc f le in
                  case a of
                  | NONE => NONE
                  | SOME ta =>
                    let b = gTermF rc f re in
                      case b of
                      | NONE => NONE
                      | SOME tb => SOME (TmAdd ta tb))
       | SOME (VfTMul, [l; r]) =>
           (case elemOfVal l of
            | NONE => NONE
            | SOME le =>
              case elemOfVal r of
              | NONE => NONE
              | SOME re =>
                let a = gTermF rc f le in
                  case a of
                  | NONE => NONE
                  | SOME ta =>
                    let b = gTermF rc f re in
                      case b of
                      | NONE => NONE
                      | SOME tb => SOME (TmMul ta tb))
       | SOME (VfTSub, [l; r]) =>
           (case elemOfVal l of
            | NONE => NONE
            | SOME le =>
              case elemOfVal r of
              | NONE => NONE
              | SOME re =>
                let a = gTermF rc f le in
                  case a of
                  | NONE => NONE
                  | SOME ta =>
                    let b = gTermF rc f re in
                      case b of
                      | NONE => NONE
                      | SOME tb => SOME (TmSub ta tb))
       | SOME (VfTNeg, [t]) =>
           (case elemOfVal t of
            | NONE => NONE
            | SOME te =>
              let r = gTermF rc f te in
                case r of
                | NONE => NONE
                | SOME tt => SOME (TmNeg tt))
       | SOME (VfTIdx, [iv; t]) =>

           (case natOfVal iv of
            | NONE => NONE
            | SOME ix =>
              if 4294967295 < ix then NONE else
              (case elemOfVal t of
               | NONE => NONE
               | SOME te =>
                 let r = gTermF rc f te in
                   case r of
                   | NONE => NONE
                   | SOME tt => SOME (TmIdx tt ix)))
       | _ => NONE)
End

Definition gFwireF_def:
  gFwireF (rc:rctx) (fuel:num) (e:num) : fwire option =
    case fuel of
    | 0 => NONE
    | SUC f =>
      if sortAt rc.rtb e <> SOME VsFormula then NONE else
      (case ctorAt rc.rtb e of
       | SOME (VfFTrue, args) => (if args = [] then SOME FwTt else NONE)
       | SOME (VfFFalse, args) => (if args = [] then SOME FwFf else NONE)
       | SOME (VfFSpH, args) => (if args = [] then SOME FwSpH else NONE)
       | SOME (VfFAtom b, [l; r]) =>
           (case bowtieOf b of
            | NONE => NONE
            | SOME bt =>
              case elemOfVal l of
              | NONE => NONE
              | SOME le =>
              case elemOfVal r of
              | NONE => NONE
              | SOME re =>
              case gTermF rc (LENGTH rc.rtb.tsorts + 1) le of
              | NONE => NONE
              | SOME tl =>
              case gTermF rc (LENGTH rc.rtb.tsorts + 1) re of
              | NONE => NONE
              | SOME tr => SOME (FwAtom bt tl tr))
       | SOME (VfFInRegion, [sv; xv; tv]) =>

           (case elemOfVal sv of
            | NONE => NONE
            | SOME se =>
              case elemOfVal xv of
              | NONE => NONE
              | SOME xe =>
              case elemOfVal tv of
              | NONE => NONE
              | SOME te =>
              case gTermF rc (LENGTH rc.rtb.tsorts + 1) te of
              | NONE => NONE
              | SOME tt =>
              case gSimplexV rc xe of
              | NONE => NONE
              | SOME sx =>
              case gExtSetV rc se of
              | NONE => NONE
              | SOME es => SOME (FwInRegion tt sx es))
       | SOME (VfFAnd, [l; r]) =>
           (case elemOfVal l of
            | NONE => NONE
            | SOME le =>
              case elemOfVal r of
              | NONE => NONE
              | SOME re =>
                let a = gFwireF rc f le in
                  case a of
                  | NONE => NONE
                  | SOME fl =>
                    let b = gFwireF rc f re in
                      case b of
                      | NONE => NONE
                      | SOME fr => SOME (FwAnd fl fr))
       | SOME (VfFOr, [l; r]) =>
           (case elemOfVal l of
            | NONE => NONE
            | SOME le =>
              case elemOfVal r of
              | NONE => NONE
              | SOME re =>
                let a = gFwireF rc f le in
                  case a of
                  | NONE => NONE
                  | SOME fl =>
                    let b = gFwireF rc f re in
                      case b of
                      | NONE => NONE
                      | SOME fr => SOME (FwOr fl fr))
       | _ => NONE)
End

Definition gJudg_def:
  gJudg (rc:rctx) (e:num) : (fwire # fwire) option =
    if sortAt rc.rtb e <> SOME VsJudgment then NONE else
    case fldElem rc.rtb VfJudgPre e of
    | NONE => NONE
    | SOME pe =>
    case fldElem rc.rtb VfJudgPost e of
    | NONE => NONE
    | SOME qe =>
    case gFwireF rc (LENGTH rc.rtb.tsorts + 1) pe of
    | NONE => NONE
    | SOME prew =>
    case gFwireF rc (LENGTH rc.rtb.tsorts + 1) qe of
    | NONE => NONE
    | SOME postw =>
      if fwNoSph postw then SOME (prew, postw) else NONE
End

Definition gPathF_def:
  gPathF (rc:rctx) (fuel:num) (e:num) : (num list) option =
    case fuel of
    | 0 => NONE
    | SUC f =>
      if sortAt rc.rtb e <> SOME VsCtxPath then NONE else
      (case ctorAt rc.rtb e of
       | SOME (VfPathHere, args) => (if args = [] then SOME [] else NONE)
       | SOME (VfPathL, [iv]) =>
           (case elemOfVal iv of
            | NONE => NONE
            | SOME ie =>
              let r = gPathF rc f ie in
                case r of
                | NONE => NONE
                | SOME ss => SOME (0::ss))
       | SOME (VfPathR, [iv]) =>
           (case elemOfVal iv of
            | NONE => NONE
            | SOME ie =>
              let r = gPathF rc f ie in
                case r of
                | NONE => NONE
                | SOME ss => SOME (1::ss))
       | _ => NONE)
End

Datatype:
  vfld = VFT term | VFF fwire | VFS simplex | VFE extensionset ;
  vtree = VTree num num (fwire # fwire) (vfld list) (num option)
                (rat option) (num option) ((num list # num list) option)
                (vtree list)
End

Definition gIface_def:
  gIface (rc:rctx) (re:num) (n:num) : (num list) option =
    case denseRecFor rc.rtb VrPromIface re n of
    | NONE => NONE
    | SOME wes =>
        (let ids = MAP (\e. ALOOKUP rc.rwid e) wes in
           if EVERY IS_SOME ids then SOME (MAP THE ids) else NONE)
End

Definition gRuleData_def:
  gRuleData (rc:rctx) (r:num) (re:num)
            : (num # vfld list # num option # rat option # num option #
               (num list # num list) option # num list) option =
    let tb = rc.rtb in
    let fe = \k. fldElem tb (VfRF r k) re in
    let fn_ = \k. fldNat tb (VfRF r k) re in
    let gT = \e. gTermF rc (LENGTH tb.tsorts + 1) e in
    let gF = \e. gFwireF rc (LENGTH tb.tsorts + 1) e in
      if r = 0 then SOME (0, [], NONE, NONE, NONE, NONE, [])
      else if r = 1 then
        (case fe 0 of NONE => NONE | SOME pr =>
         case fe 1 of NONE => NONE | SOME xe =>
         case gF xe of NONE => NONE | SOME xw =>
           SOME (0, [VFF xw], NONE, NONE, NONE, NONE, [pr]))
      else if r = 2 then
        (case fe 0 of NONE => NONE | SOME lp =>
         case fe 1 of NONE => NONE | SOME rp =>
         case fe 2 of NONE => NONE | SOME ce =>
         case gF ce of NONE => NONE | SOME cw =>
           SOME (0, [VFF cw], NONE, NONE, NONE, NONE, [lp; rp]))
      else if r = 3 then
        (case fe 0 of NONE => NONE | SOME lp =>
         case fe 1 of NONE => NONE | SOME rp =>
           SOME (0, [], NONE, NONE, NONE, NONE, [lp; rp]))
      else if r = 4 \/ r = 5 then
        (case fe 0 of NONE => NONE | SOME pr =>
         case fn_ 1 of NONE => NONE | SOME wh =>
         if 1 < wh then NONE else
         case fe 2 of NONE => NONE | SOME oe =>
         case gF oe of NONE => NONE | SOME ow =>
           SOME (wh, [VFF ow], NONE, NONE, NONE, NONE, [pr]))
      else if r = 6 then
        (case fe 0 of NONE => NONE | SOME lp =>
         case fe 1 of NONE => NONE | SOME rp =>
         case fe 2 of NONE => NONE | SOME pe =>
         case gPathF rc (LENGTH tb.tsorts + 1) pe of
         | NONE => NONE
         | SOME stps =>
             if 4294967295 < LENGTH stps then NONE else
             SOME (0, [], NONE, NONE, NONE, SOME (stps, []), [lp; rp]))
      else if r = 7 then
        (case fe 0 of NONE => NONE | SOME ep =>
         case fe 1 of NONE => NONE | SOME bp =>
         case fe 2 of NONE => NONE | SOME we =>
         case ALOOKUP rc.rwid we of NONE => NONE | SOME wid =>
         case fe 3 of NONE => NONE | SOME t1 =>
         case fe 4 of NONE => NONE | SOME t2 =>
         case fe 5 of NONE => NONE | SOME bf =>
         case gT t1 of NONE => NONE | SOME tT =>
         case gT t2 of NONE => NONE | SOME tU =>
         case gF bf of NONE => NONE | SOME bw =>
           SOME (0, [VFT tT; VFT tU; VFF bw], SOME wid, NONE, NONE, NONE,
                 [ep; bp]))
      else if r = 8 \/ r = 9 then
        (case fe 0 of NONE => NONE | SOME pr =>
         case fe 1 of NONE => NONE | SOME te =>
         case fe 2 of NONE => NONE | SOME xe =>
         case fe 3 of NONE => NONE | SOME se =>
         case gT te of NONE => NONE | SOME tt =>
         case gSimplexV rc xe of NONE => NONE | SOME sx =>
         case gExtSetV rc se of NONE => NONE | SOME es =>
           SOME (0, [VFT tt; VFS sx; VFE es], NONE, NONE, NONE, NONE, [pr]))
      else if r = 10 then
        (case fe 0 of NONE => NONE | SOME pr =>
         case fn_ 1 of NONE => NONE | SOME dir =>
         if 1 < dir then NONE else
         case fe 2 of NONE => NONE | SOME l1 =>
         case fe 3 of NONE => NONE | SOME r1 =>
         case fn_ 4 of NONE => NONE | SOME bb =>
         if 4 < bb then NONE else
         case gT l1 of NONE => NONE | SOME tl =>
         case gT r1 of NONE => NONE | SOME tr =>
           SOME (dir, [VFT tl; VFT tr], SOME bb, NONE, NONE, NONE, [pr]))
      else if r = 11 then
        (case fe 0 of NONE => NONE | SOME pr =>
         case fe 1 of NONE => NONE | SOME te =>
         case fe 2 of NONE => NONE | SOME xe =>
         case fe 3 of NONE => NONE | SOME se =>
         case fn_ 4 of NONE => NONE | SOME deg =>
         if 4294967295 < deg then NONE else
         case fe 5 of NONE => NONE | SOME pe =>
         case fe 6 of NONE => NONE | SOME de =>
         case gT te of NONE => NONE | SOME tx =>
         case gSimplexV rc xe of NONE => NONE | SOME sx =>
         case gExtSetV rc se of NONE => NONE | SOME es =>
         case gT pe of NONE => NONE | SOME poly =>
         case gF de of NONE => NONE | SOME pd =>
           SOME (0, [VFT tx; VFS sx; VFE es; VFT poly; VFF pd],
                 SOME deg, NONE, NONE, NONE, [pr]))
      else if r = 12 then
        (case fe 0 of NONE => NONE | SOME l1 =>
         case fe 1 of NONE => NONE | SOME r1 =>
         case gT l1 of NONE => NONE | SOME tl =>
         case gT r1 of NONE => NONE | SOME tr =>
           SOME (0, [VFT tl; VFT tr], NONE, NONE, NONE, NONE, []))
      else if r = 14 then
        (case fe 0 of NONE => NONE | SOME ce =>
         case fe 1 of NONE => NONE | SOME oe =>
         case fn_ 2 of NONE => NONE | SOME dbl =>
         case gT ce of NONE => NONE | SOME cc =>
         case gT oe of NONE => NONE | SOME co =>
           SOME (0, [VFT cc; VFT co], NONE, NONE, SOME dbl, NONE, []))
      else if r = 23 then
        (case fe 0 of NONE => NONE | SOME te =>
         case gT te of NONE => NONE | SOME tt =>
           SOME (0, [VFT tt], NONE, NONE, NONE, NONE, []))
      else if r = 24 then
        (case fe 0 of NONE => NONE | SOME pr =>
         case fe 1 of NONE => NONE | SOME t1 =>
         case fe 2 of NONE => NONE | SOME t2 =>
         case gT t1 of NONE => NONE | SOME tT =>
         case gT t2 of NONE => NONE | SOME tU =>
           SOME (0, [VFT tT; VFT tU], NONE, NONE, NONE, NONE, [pr]))
      else if r = 25 then
        (case fe 0 of NONE => NONE | SOME sp =>
         case fe 1 of NONE => NONE | SOME cp =>
         case fe 2 of NONE => NONE | SOME ce =>
         case fe 3 of NONE => NONE | SOME pe =>
         case fn_ 4 of NONE => NONE | SOME ni =>
         if 4294967295 < ni then NONE else
         case gF ce of NONE => NONE | SOME cw =>
         case gPathF rc (LENGTH tb.tsorts + 1) pe of
         | NONE => NONE
         | SOME stps =>
             if 4294967295 < LENGTH stps then NONE else
             (case gIface rc re ni of
              | NONE => NONE
              | SOME ifc =>
                  SOME (0, [VFF cw], NONE, NONE, NONE, SOME (stps, ifc),
                        [sp; cp])))
      else if r = 26 then
        (case fn_ 0 of NONE => NONE | SOME ncomp =>
         case denseRecFor tb VrSyzComp re ncomp of
         | NONE => NONE
         | SOME comps =>
           case fe 1 of NONE => NONE | SOME ce =>
           case fe 2 of NONE => NONE | SOME oe =>
           case fn_ 3 of NONE => NONE | SOME dbl =>
           case gT ce of NONE => NONE | SOME cc =>
           case gT oe of NONE => NONE | SOME co =>
           (case fldAt tb (VfRF 26 4) re of
            | NONE => SOME (0, [VFT cc; VFT co], NONE, NONE, SOME dbl,
                            NONE, comps)
            | SOME thv =>
              (case qOfVal thv of
               | NONE => NONE
               | SOME q => SOME (0, [VFT cc; VFT co], NONE, SOME q,
                                 SOME dbl, NONE, comps))))
      else NONE
End

Definition gProofF_def:
  (gProofF (rc:rctx) (fuel:num) (p:num) : vtree option =
    case fuel of
    | 0 => NONE
    | SUC f =>
      if sortAt rc.rtb p <> SOME VsProof then NONE else
      (case fldElem rc.rtb VfProofConcludes p of
       | NONE => NONE
       | SOME je =>
         (case gJudg rc je of
          | NONE => NONE
          | SOME cj =>
            (case ALOOKUP rc.rtb.trp p of
             | NONE => NONE
             | SOME (re, r) =>
               if ~v0fragTag r then NONE else
               (case gRuleData rc r re of
                | NONE => NONE
                | SOME (var, flds, scal, th, den, pa, kidEs) =>
                  let ks = gProofsF rc f kidEs in
                    case ks of
                    | NONE => NONE
                    | SOME kids =>
                        SOME (VTree r var cj flds scal th den pa kids)))))) /\
  (gProofsF (rc:rctx) (fuel:num) (es:num list) : (vtree list) option =
    case es of
    | [] => SOME []
    | (e::rest) =>
        let t = gProofF rc fuel e in
          case t of
          | NONE => NONE
          | SOME v =>
            let ts = gProofsF rc fuel rest in
              case ts of
              | NONE => NONE
              | SOME vs => SOME (v::vs))
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (\x. case x of
         | INL (rc, f, p) => (f, 0:num)
         | INR (rc, f, es) => (f, LENGTH es + 1))`
  >> rw[]
End

Datatype:
  istate = <|
    itags  : num list ;
    irefs  : num list ;
    inlens : num list ;
    idids  : num list ;
    idict  : (num list) list ;
    inums  : num list ;
    imisc  : num list ;
    imemo  : (poolobj # num) list ;
    ijinfo : (num # (num # num # (num # num) option # bool)) list ;
    ijcont : ((num # num) # num) list ;
    ioff   : num
  |>
End

Definition iInit_def:
  iInit = <| itags := [] ; irefs := [] ; inlens := [] ; idids := [] ;
             idict := [] ; inums := [] ; imisc := [] ; imemo := [] ;
             ijinfo := [] ; ijcont := [] ; ioff := 0 |>
End

Definition pushRec_def:
  pushRec (st:istate) (tag:num) (len:num) (refs:num list)
          (misc:num list) (ob:poolobj) : num # istate =
    (st.ioff,
     st with <| itags := tag::st.itags ;
                irefs := REVERSE refs ++ st.irefs ;
                imisc := REVERSE misc ++ st.imisc ;
                imemo := (ob, st.ioff)::st.imemo ;
                ioff := st.ioff + len |>)
End

Definition dictId_def:
  dictId (dict:(num list) list) (db:num list) : num # (num list) list =
    case idxOf db dict of
    | SOME i => (i, dict)
    | NONE => (LENGTH dict, dict ++ [db])
End

Definition internTerm_def:
  internTerm (t:term) (st:istate) : num # istate =
    case ALOOKUP st.imemo (PTerm t) of
    | SOME off => (off, st)
    | NONE =>
      (case t of
       | TmVar w => pushRec st 1 5 [] [w] (PTerm t)
       | TmConst q =>
           (let (nb, db) = encRatBytes q in
            let (did, dict') = dictId st.idict db in
            let off = st.ioff in
              (off,
               st with <| itags := 2::st.itags ;
                          inlens := LENGTH nb::st.inlens ;
                          idids := did::st.idids ;
                          idict := dict' ;
                          inums := REVERSE nb ++ st.inums ;
                          imemo := (PTerm t, off)::st.imemo ;
                          ioff := st.ioff + (9 + LENGTH nb + LENGTH db) |>))
       | TmAdd a b =>
           (let (ra, st1) = internTerm a st in
            let (rb, st2) = internTerm b st1 in
              pushRec st2 3 9 [ra; rb] [] (PTerm t))
       | TmMul a b =>
           (let (ra, st1) = internTerm a st in
            let (rb, st2) = internTerm b st1 in
              pushRec st2 4 9 [ra; rb] [] (PTerm t))
       | TmSub a b =>
           (let (ra, st1) = internTerm a st in
            let (rb, st2) = internTerm b st1 in
              pushRec st2 5 9 [ra; rb] [] (PTerm t))
       | TmNeg a =>
           (let (ra, st1) = internTerm a st in
              pushRec st1 6 5 [ra] [] (PTerm t))
       | TmIdx a i =>
           (let (ra, st1) = internTerm a st in
              pushRec st1 7 9 [ra] [i] (PTerm t)))
End

Definition internSimplex_def:
  internSimplex (cxs:simpc list) (sx:simplex) (st:istate)
                : (num # istate) option =
    case ALOOKUP st.imemo (PSimplex sx) of
    | SOME off => SOME (off, st)
    | NONE =>
        (case idxOf sx.complex cxs of
         | NONE => NONE
         | SOME ci =>
             if LENGTH sx.vmask <> sx.complex.nVertices then NONE else
             let mb = encBits sx.vmask in
               SOME (pushRec st 16 (5 + LENGTH mb) [] (ci::mb)
                             (PSimplex sx)))
End

Definition internExtSet_def:
  internExtSet (cxs:simpc list) (es:extensionset) (st:istate)
               : (num # istate) option =
    case ALOOKUP st.imemo (PExtSet es) of
    | SOME off => SOME (off, st)
    | NONE =>
        (case internSimplex cxs es.simplex st of
         | NONE => NONE
         | SOME (so, st1) =>
             if LENGTH es.emask <> es.simplex.complex.nVertices then NONE
             else
               let mb = encBits es.emask in
                 SOME (pushRec st1 17 (5 + LENGTH mb) [so] mb (PExtSet es)))
End

Definition internFwire_def:
  internFwire (cxs:simpc list) (fw:fwire) (st:istate)
              : (num # istate) option =
    case ALOOKUP st.imemo (PFormula fw) of
    | SOME off => SOME (off, st)
    | NONE =>
      (case fw of
       | FwTt => SOME (pushRec st 36 1 [] [] (PFormula fw))
       | FwFf => SOME (pushRec st 37 1 [] [] (PFormula fw))
       | FwSpH => SOME (pushRec st 38 1 [] [] (PFormula fw))
       | FwAtom b l r =>
           (let (rl, st1) = internTerm l st in
            let (rr, st2) = internTerm r st1 in
              SOME (pushRec st2 32 10 [rl; rr] [bowtieCode b]
                            (PFormula fw)))
       | FwInRegion t sx es =>
           (let (rt, st1) = internTerm t st in
              case internSimplex cxs sx st1 of
              | NONE => NONE
              | SOME (rs, st2) =>
                (case internExtSet cxs es st2 of
                 | NONE => NONE
                 | SOME (re, st3) =>
                     SOME (pushRec st3 33 13 [rt; rs; re] [] (PFormula fw))))
       | FwAnd a b =>
           (let x = internFwire cxs a st in
              case x of
              | NONE => NONE
              | SOME (ra, st1) =>
                let y = internFwire cxs b st1 in
                  case y of
                  | NONE => NONE
                  | SOME (rb, st2) =>
                      SOME (pushRec st2 34 9 [ra; rb] [] (PFormula fw)))
       | FwOr a b =>
           (let x = internFwire cxs a st in
              case x of
              | NONE => NONE
              | SOME (ra, st1) =>
                let y = internFwire cxs b st1 in
                  case y of
                  | NONE => NONE
                  | SOME (rb, st2) =>
                      SOME (pushRec st2 35 9 [ra; rb] [] (PFormula fw))))
End

Definition internJudg_def:
  internJudg (cxs:simpc list) (j:fwire # fwire) (st:istate)
             : (num # istate) option =
    case ALOOKUP st.imemo (PJudg (FST j) (SND j)) of
    | SOME off => SOME (off, st)
    | NONE =>
      (case internFwire cxs (FST j) st of
       | NONE => NONE
       | SOME (rp, st1) =>
         (case internFwire cxs (SND j) st1 of
          | NONE => NONE
          | SOME (rq, st2) =>
            let andLR =
              (case SND j of
               | FwAnd a b =>
                   (case ALOOKUP st2.imemo (PFormula a) of
                    | NONE => NONE
                    | SOME ra =>
                      (case ALOOKUP st2.imemo (PFormula b) of
                       | NONE => NONE
                       | SOME rb => SOME (ra, rb)))
               | _ => NONE) in
            let isIR = (case SND j of FwInRegion t sx es => T | _ => F) in
            let (off, st3) =
              pushRec st2 48 9 [rp; rq] [] (PJudg (FST j) (SND j)) in
              SOME (off,
                    st3 with
                    <| ijinfo := (off, (rp, rq, andLR, isIR))::st3.ijinfo ;
                       ijcont := ((rp, rq), off)::st3.ijcont |>)))
End

Datatype:
  ndat = <| dr : num ; dv : num ; dconcl : num ; dprefs : num list ;
            dscal : num option ; dden : num option ;
            dpath : (num list # num list) option ; dkids : num list |>
End

Definition internFlds_def:
  internFlds (cxs:simpc list) (fs:vfld list) (st:istate)
             : (num list # istate) option =
    case fs of
    | [] => SOME ([], st)
    | (f::rest) =>
      (case (case f of
             | VFT t => SOME (internTerm t st)
             | VFF w => internFwire cxs w st
             | VFS s => internSimplex cxs s st
             | VFE e => internExtSet cxs e st) of
       | NONE => NONE
       | SOME (r, st1) =>
         (case internFlds cxs rest st1 of
          | NONE => NONE
          | SOME (rs, st2) => SOME (r::rs, st2)))
End

Definition emitTree_def:
  (emitTree (cxs:simpc list) (t:vtree) (st:istate) (ns:ndat list)
            : (num # istate # ndat list) option =
    case t of
    | VTree r v cj flds sc th dn pa kids =>
      (case emitKids cxs kids st ns of
       | NONE => NONE
       | SOME (kords, st1, ns1) =>
         (case internJudg cxs cj st1 of
          | NONE => NONE
          | SOME (cjOff, st2) =>
            (case internFlds cxs flds st2 of
             | NONE => NONE
             | SOME (prefs, st3) =>
               (case (case th of
                      | NONE => SOME (NONE, st3)
                      | SOME q =>
                          (let (toff, st4) = internTerm (TmConst q) st3 in
                             SOME (SOME toff, st4))) of
                | NONE => NONE
                | SOME (thOff, st5) =>
                    let scal =
                      (if r = 26 then
                         SOME (case thOff of
                               | NONE => 4294967295
                               | SOME x => x)
                       else sc) in
                      SOME (LENGTH ns1, st5,
                            ns1 ++
                            [<| dr := r ; dv := v ; dconcl := cjOff ;
                                dprefs := prefs ; dscal := scal ;
                                dden := dn ; dpath := pa ;
                                dkids := kords |>])))))) /\
  (emitKids (cxs:simpc list) (ts:vtree list) (st:istate) (ns:ndat list)
            : (num list # istate # ndat list) option =
    case ts of
    | [] => SOME ([], st, ns)
    | (t::rest) =>
      (case emitTree cxs t st ns of
       | NONE => NONE
       | SOME (o1, st1, ns1) =>
         (case emitKids cxs rest st1 ns1 of
          | NONE => NONE
          | SOME (os, st2, ns2) => SOME (o1::os, st2, ns2))))
Termination
  WF_REL_TAC `measure (\x. case x of
         | INL (cxs, t, st, ns) => vtree_size t
         | INR (cxs, ts, st, ns) => list_size vtree_size ts)`
  >> rw[fetch "-" "vtree_size_def", listTheory.list_size_def]
  >> gvs[]
End

Definition childInfo_def:
  childInfo (ns:ndat list) (st:istate) (nd:ndat)
            : (num # num # (num # num) option # bool) option =
    case nd.dkids of
    | [] => NONE
    | (c::rest) =>
      (case oEL c ns of
       | NONE => NONE
       | SOME cnd => ALOOKUP st.ijinfo cnd.dconcl)
End

Definition escPreC_def:
  escPreC (ns:ndat list) (st:istate) (nd:ndat) <=>
    nd.dr = 4 /\
    (case childInfo ns st nd of
     | NONE => F
     | SOME (preR, postR, andLR, isIR) =>
       (case andLR of
        | NONE => F
        | SOME (l, r) =>
            ALOOKUP st.ijcont (preR, if nd.dv = 1 then r else l) <> NONE))
End

Definition escPre2C_def:
  escPre2C (ns:ndat list) (st:istate) (nd:ndat) <=>
    (nd.dr = 4 /\
     (case childInfo ns st nd of
      | NONE => F
      | SOME (preR, postR, andLR, isIR) => IS_SOME andLR)) \/
    (nd.dr = 9 /\
     (case childInfo ns st nd of
      | NONE => F
      | SOME (preR, postR, andLR, isIR) => isIR))
End

Definition escapesOf_def:
  escapesOf (ns:ndat list) (st:istate) : num list # num list =
    (FILTER (\i. case oEL i ns of
                 | NONE => F
                 | SOME nd => escPreC ns st nd) (COUNT_LIST (LENGTH ns)),
     FILTER (\i. case oEL i ns of
                 | NONE => F
                 | SOME nd => escPre2C ns st nd) (COUNT_LIST (LENGTH ns)))
End

Definition symRecBytes_def:
  symRecBytes (nw:num) (auxBase:num) (ty:tensortype) : num list =
    [kindCode ty.dtype.kind; signCode ty.dtype.sign; extCode ty.dtype.ext;
     0] ++
    u32leG (LENGTH ty.shape) ++
    u64leG auxBase ++
    REPLICATE 8 255 ++
    u64leG 0
End

Definition symtabBytes_def:
  symtabBytes (ws:tensortype list) : num list =
    let nw = LENGTH ws in
    let recs =
      FLAT (GENLIST
              (\i. case oEL i ws of
                   | NONE => []
                   | SOME ty =>
                       symRecBytes nw
                         (32 * nw +
                          8 * SUM (GENLIST
                                     (\j. case oEL j ws of
                                          | NONE => 0
                                          | SOME t2 => LENGTH t2.shape) i))
                         ty)
              nw) in
    let aux = FLAT (MAP (\ty. FLAT (MAP u64leG ty.shape)) ws) in
      recs ++ aux
End

Definition complexBytes_def:
  complexBytes (cx:simpc) : num list =
    u32leG cx.nVertices ++ u32leG cx.ambDim ++
    FLAT (MAP encRatV0 (FLAT cx.coord)) ++
    u32leG (LENGTH cx.simplices) ++
    FLAT (MAP encBits cx.simplices) ++
    u32leG (LENGTH cx.cells) ++
    FLAT (MAP (\c. encBits (FST c) ++ encBits (SND c)) cx.cells)
End

Definition diagramBytes_def:
  diagramBytes (cxs:simpc list) : num list =
    u32leG (LENGTH cxs) ++ FLAT (MAP complexBytes cxs) ++ u32leG 0
End

Definition nodeLenOf_def:
  nodeLenOf (nd:ndat) : num =
    nodeLenR nd.dr
             (case nd.dpath of NONE => [] | SOME p => FST p)
             (case nd.dpath of NONE => [] | SOME p => SND p)
             (LENGTH nd.dkids)
End

Definition hdrBytes_def:
  hdrBytes (ws:tensortype list) (cxs:simpc list) (nNodes:num)
           (rootOff:num) (thetaRef:num) (prfLen:num) : num list =
    let sy = symtabBytes ws in
    let dia = diagramBytes cxs in
    let symLen = LENGTH sy in
    let payOff = ((128 + symLen + 63) DIV 64) * 64 in
    let diaOff = payOff in
    let prfOff = diaOff + LENGTH dia in
      bernMagic ++ u32leG 1 ++ u32leG 0 ++
      u64leG 128 ++ u64leG symLen ++
      u64leG payOff ++ u64leG 0 ++
      u64leG diaOff ++ u64leG (LENGTH dia) ++
      u64leG prfOff ++ u64leG prfLen ++
      u32leG (LENGTH ws) ++ u32leG 0 ++
      u32leG nNodes ++ u32leG (LENGTH cxs) ++
      u64leG rootOff ++ u32leG thetaRef ++
      REPLICATE 20 0 ++
      sy ++ REPLICATE (payOff - (128 + symLen)) 0 ++ dia
End

Definition compTag_def:
  compTag (r:num) (v:num) : num =
    if v = 0 then r
    else if r = 4 then 27 else if r = 5 then 28 else 29
End

Definition assembleCols_def:
  assembleCols (ws:tensortype list) (cxs:simpc list) (ns:ndat list)
               (st:istate) (thetaRef:num) : columns =
    let poolTotal = st.ioff in
    let nodeStart = 8 + poolTotal in
    let lens = MAP nodeLenOf ns in
    let offs = GENLIST (\i. nodeStart + SUM (TAKE i lens)) (LENGTH ns) in
    let prfLen = nodeStart + SUM lens in
    let rootOff = (if ns = [] then 0 else LAST offs) in
    let (esc1, esc2) = escapesOf ns st in
      <| hdrImage :=
           hdrBytes ws cxs (LENGTH ns) rootOff thetaRef prfLen ;
         topoMode := 0 ;
         denDefault := 0 ;
         nNodes := LENGTH ns ;
         nPool := LENGTH st.itags ;
         blockSize := 0 ;
         nodeTag := MAP (\nd. compTag nd.dr nd.dv) ns ;
         nodeArity :=
           MAP (\nd. LENGTH nd.dkids) (FILTER (\nd. nd.dr = 26) ns) ;
         nodeTopo := [] ;
         nodeConcl := MAP (\nd. nd.dconcl) ns ;
         nodePref := FLAT (MAP (\nd. nd.dprefs) ns) ;
         nodeScal :=
           FLAT (MAP (\nd. case nd.dscal of
                           | NONE => []
                           | SOME x => [x]) ns) ;
         nodeDen :=
           FLAT (GENLIST
                   (\i. case oEL i ns of
                        | NONE => []
                        | SOME nd =>
                          (case nd.dden of
                           | NONE => []
                           | SOME d => if d = 0 then [] else [(i, d)]))
                   (LENGTH ns)) ;
         nodePath :=
           FLAT (MAP (\nd. case nd.dpath of
                           | NONE => []
                           | SOME p => [p]) ns) ;
         nodeRat := [] ;
         nodeEsc := esc1 ;
         nodeEsc2 := esc2 ;
         poolTag := REVERSE st.itags ;
         poolRef := REVERSE st.irefs ;
         poolNumLen := REVERSE st.inlens ;
         poolDenId := REVERSE st.idids ;
         poolDenDict := st.idict ;
         poolNum := REVERSE st.inums ;
         poolMisc := REVERSE st.imisc |>
End

Definition colsU32OK_def:
  colsU32OK (cols:columns) <=>
    EVERY (\x. x < 4294967296) cols.nodeConcl /\
    EVERY (\x. x < 4294967296) cols.nodePref /\
    EVERY (\x. x < 4294967296) cols.nodeScal /\
    EVERY (\x. x < 4294967296) cols.poolRef /\
    EVERY (\x. x < 4294967296) cols.poolNumLen /\
    EVERY (\p. SND p < 18446744073709551616) cols.nodeDen
End

Definition certElems_def:
  certElems (tb:rowtbls) : num list =
    FILTER (\e. sortAt tb e = SOME VsCert) (COUNT_LIST (LENGTH tb.tsorts))
End

Definition gCert_def:
  gCert (tb:rowtbls)
        : (num # num # num # num # num # rat option) option =
    case certElems tb of
    | [ce] =>
      (case fldElem tb VfCertRoot ce of
       | NONE => NONE
       | SOME rootE =>
         (case fldNat tb VfCertNWires ce of
          | NONE => NONE
          | SOME nw =>
            (case fldNat tb VfCertNApps ce of
             | NONE => NONE
             | SOME na =>
               (case fldNat tb VfCertNComplexes ce of
                | NONE => NONE
                | SOME nc =>
                  (case fldAt tb VfCertTheta ce of
                   | NONE => SOME (ce, nw, na, nc, rootE, NONE)
                   | SOME tv =>
                     (case qOfVal tv of
                      | NONE => NONE
                      | SOME q => SOME (ce, nw, na, nc, rootE, SOME q)))))))
    | _ => NONE
End

Definition rootShapeV_def:
  rootShapeV (t:vtree) <=>
    case t of
    | VTree r v cj flds sc th dn pa kids =>
        (case FST cj of
         | FwAnd phi FwSpH => T
         | _ => F)
End

Definition certOfRows_def:
  certOfRows (pins:pins) (g:geolog) : cres =
    case g.commits of
    | [] => CErr CUnread "no_commits" 0
    | (c0::rest) =>
      let tip = LAST (c0::rest) in
      let deps = tip.cskel.deps in
      (case scanOps pins deps tip.cbody.ops of
       | ScErr c t w => CErr c t w
       | ScOk tb =>
         (case gCert tb of
          | NONE => CErr CUnread "cert_element" 0
          | SOME (ce, nw, na, nc, rootE, thQ) =>
            if na <> 0 then CErr CUnsupp "apps_out_of_v0_fragment" na else
            if 4294967294 < nw then CErr CUnread "n_wires_range" nw else
            (case gWires tb nw of
             | NONE => CErr CUnread "wires" 0
             | SOME (rwid, ws) =>
               (case gComplexes tb nc of
                | NONE => CErr CUnread "complexes" 0
                | SOME (cxE, cxs) =>
                  let rc = <| rtb := tb ; rwid := rwid ;
                              rcxE := cxE ; rcxs := cxs |> in
                    (case gProofF rc (LENGTH tb.tsorts + 1) rootE of
                     | NONE => CErr CUnread "proof_tree" 0
                     | SOME vt =>
                       if ~rootShapeV vt then CErr CUnread "root_shape" 0
                       else
                         (case emitTree cxs vt iInit [] of
                          | NONE => CErr CUnread "emission" 0
                          | SOME (rootOrd, st0, ns) =>
                            (case (case thQ of
                                   | NONE => SOME (4294967295, st0)
                                   | SOME q =>
                                       (let (toff, st1) =
                                          internTerm (TmConst q) st0 in
                                          SOME (toff, st1))) of
                             | NONE => CErr CUnread "theta" 0
                             | SOME (thetaRef, stF) =>
                               let cols =
                                 assembleCols ws cxs ns stF thetaRef in
                                 if colsU32OK cols then COk cols
                                 else CErr CUnread "u32_overflow" 0)))))))
End

Definition rosterChids_def:
  rosterChids (pins:pins) : (num list) list = MAP (\p. FST (FST p)) pins
End

Definition firstContentPrereqR_def:
  firstContentPrereqR (pins:pins) (g:geolog) (ps:prereq list) (i:num)
                      : (string # num) option =
    case ps of
    | [] => NONE
    | (p::rest) =>
        if contentRefd g p.pchid /\
           ~(p.pflag = 1 /\ MEM p.pchid (rosterChids pins))
        then SOME (prereqFlagTag p.pflag, i)
        else firstContentPrereqR pins g rest (i + 1)
End

Definition sealedBindCheckR_def:
  sealedBindCheckR (pins:pins) (g:geolog) (b:bindinfo)
                   : (string # num) option =
    let tips = tipsOf g b.bchids in
      if LENGTH tips <> 1 then SOME ("tip_not_unique", LENGTH tips)
      else firstContentPrereqR pins g g.prereqs 0
End

Definition readGeologCert_def:
  readGeologCert (pins:pins) (bs:num list) : cres =
    case readGeologSealed bs of
    | RErr c t w => CErr c t w
    | ROk g =>
      (case bindChain g of
       | BindErr c t w => CErr c t w
       | BindOk b =>
         (case sealedBindCheckR pins g b of
          | SOME (t, w) => CErr CUnsupp t w
          | NONE => certOfRows pins g))
End

Theorem assembleCols_shape:
  !ws cxs ns st thetaRef.
    (assembleCols ws cxs ns st thetaRef).topoMode = 0 /\
    (assembleCols ws cxs ns st thetaRef).blockSize = 0 /\
    (assembleCols ws cxs ns st thetaRef).denDefault = 0 /\
    (assembleCols ws cxs ns st thetaRef).nodeTopo = [] /\
    (assembleCols ws cxs ns st thetaRef).nodeRat = [] /\
    (assembleCols ws cxs ns st thetaRef).nNodes =
      LENGTH (assembleCols ws cxs ns st thetaRef).nodeTag /\
    (assembleCols ws cxs ns st thetaRef).nPool =
      LENGTH (assembleCols ws cxs ns st thetaRef).poolTag /\
    LENGTH (assembleCols ws cxs ns st thetaRef).nodeConcl =
      (assembleCols ws cxs ns st thetaRef).nNodes
Proof
  rw[assembleCols_def] >> pairarg_tac >> gvs[]
QED

Theorem certOfRows_O2:
  !pins g.
    (?c t w. certOfRows pins g = CErr c t w) \/
    (?cols. certOfRows pins g = COk cols /\
            cols.topoMode = 0 /\ cols.blockSize = 0 /\
            cols.nodeTopo = [] /\ cols.nodeRat = [] /\
            cols.nNodes = LENGTH cols.nodeTag /\
            cols.nPool = LENGTH cols.poolTag /\
            LENGTH cols.nodeConcl = cols.nNodes /\
            EVERY (\x. x < 4294967296) cols.nodeConcl /\
            EVERY (\x. x < 4294967296) cols.poolRef)
Proof
  rpt gen_tac
  >> Cases_on `certOfRows pins g` >> simp[]
  >> pop_assum mp_tac
  >> simp[certOfRows_def, AllCaseEqs()]
  >> strip_tac >> gvs[colsU32OK_def]
  >> simp[assembleCols_shape]
QED

Theorem readGeologCert_O2:
  !pins bs.
    (?c t w. readGeologCert pins bs = CErr c t w) \/
    (?g b cols.
       readGeologCert pins bs = COk cols /\
       readGeologSealed bs = ROk g /\ wfGeolog g /\
       EVERY (\c. EVERY coreOp c.cbody.ops) g.commits /\
       bindChain g = BindOk b /\
       LENGTH b.bchids = LENGTH g.commits /\
       EVERY (\h. LENGTH h = 32 /\ EVERY (\x. x < 256) h) b.bchids /\
       b.btip = LAST b.bchids /\
       cols.topoMode = 0 /\ cols.blockSize = 0 /\
       cols.nNodes = LENGTH cols.nodeTag /\
       cols.nPool = LENGTH cols.poolTag /\
       LENGTH cols.nodeConcl = cols.nNodes)
Proof
  rpt gen_tac
  >> Cases_on `readGeologCert pins bs` >> simp[]
  >> pop_assum mp_tac
  >> simp[readGeologCert_def, AllCaseEqs()]
  >> strip_tac
  >> rename [`certOfRows pins g = COk cols`]
  >> imp_res_tac readGeologSealed_wf
  >> imp_res_tac bindChain_shape
  >> qspecl_then [`pins`, `g`] mp_tac certOfRows_O2
  >> strip_tac >> gvs[]
QED
