(*
  bindChain — the hash-chain binding layer over the reader's result:
  commit identity (BLAKE3 of the skeleton bytes as found), body binding
  (body hash matches the skeleton's field), containment sanity
  (contained commit ids distinct) and reference sanity (every dep index
  used by a ruled-table op is within the commit's dep count).
*)
Theory geolog_bind

Ancestors
  arithmetic list rich_list option pair sorting string geolog_read
  blake3

Definition refDeps_def:
  refDeps (r:elemref) : num list =
    case r of ERExt d c => [d] | ERLocal _ => []
End

Definition valDeps_def:
  valDeps (v:gvalue) : num list =
    case v of
    | GVRef r => refDeps r
    | GVCommitId i => [i]
    | _ => []
End

Definition opDeps_def:
  opDeps (op:gop) : num list =
    case op of
    | GElta r => refDeps r
    | GRela r args => refDeps r ++ FLAT (MAP valDeps args)
    | GFuna r args v => refDeps r ++ FLAT (MAP valDeps args) ++ valDeps v
    | GEltd r => refDeps r
    | _ => []
End

Definition commitUsedDeps_def:
  commitUsedDeps (c:gcommit) : num list =
    FLAT (MAP opDeps c.cbody.ops)
End

Definition firstBadDepIdxA_def:
  firstBadDepIdxA (cs:gcommit list) (i:num) : num option =
    case cs of
    | [] => NONE
    | (c::rest) =>
        if EVERY (\d. d < LENGTH c.cskel.deps) (commitUsedDeps c)
        then firstBadDepIdxA rest (i + 1)
        else SOME i
End

Definition firstBodyMismatchA_def:
  firstBodyMismatchA (cs:gcommit list) (i:num) : num option =
    case cs of
    | [] => NONE
    | (c::rest) =>
        if blake3 c.bodyBytes = c.cskel.bodyHash
        then firstBodyMismatchA rest (i + 1)
        else SOME i
End

Definition dedupAdjL_def:
  dedupAdjL ([]:(num list) list) = ([]:(num list) list) /\
  dedupAdjL [x] = [x] /\
  dedupAdjL (x::y::rest) =
    if x = y then dedupAdjL (y::rest) else x :: dedupAdjL (y::rest)
End

Definition sortedDedup_def:
  sortedDedup (hs:(num list) list) : (num list) list =
    dedupAdjL (QSORT lexLe hs)
End

Definition kahnReady_def:
  kahnReady (contained:(num list) list) (emitted:(num list) list)
            (deps:(num list) list) <=>
    EVERY (\d. MEM d emitted \/ ~MEM d contained) deps
End

Definition kahnLoopF_def:
  kahnLoopF (fuel:num)
            (pending:((num list) # (num list) list) list)
            (contained:(num list) list)
            (emitted:(num list) list)
            (acc:(num list) list) : ((num list) list) option =
    case fuel of
    | 0 => (if pending = [] then SOME acc else NONE)
    | SUC f =>
      if pending = [] then SOME acc
      else
        let ready = FILTER (\p. kahnReady contained emitted (SND p))
                           pending in
          if ready = [] then NONE
          else
            let layer = QSORT (\a b. lexLe (FST a) (FST b)) ready in
            let layerH = MAP FST layer in
            let rest = FILTER (\p. ~MEM (FST p) layerH) pending in
              kahnLoopF f rest contained (emitted ++ layerH)
                        (acc ++ layerH)
End

Definition kahnOrder_def:
  kahnOrder (chids:(num list) list) (depss:((num list) list) list)
            : ((num list) list) option =
    kahnLoopF (LENGTH chids) (ZIP (chids, depss)) chids [] []
End

Definition boundaryOf_def:
  boundaryOf (g:geolog) (chids:(num list) list) : (num list) list =
    sortedDedup
      (FILTER (\d. ~MEM d chids)
              (FLAT (MAP (\c. c.cskel.deps) g.commits)))
End

Definition tipsOf_def:
  tipsOf (g:geolog) (chids:(num list) list) : (num list) list =
    FILTER (\h. ~MEM h (FLAT (MAP (\c. c.cskel.deps) g.commits)))
           chids
End

Datatype:
  bindinfo = <| bchids : (num list) list ; btip : num list |>
End

Datatype:
  bindres = BindOk bindinfo | BindErr rclass string num
End

Definition bindChain_def:
  bindChain (g:geolog) : bindres =
    case firstBodyMismatchA g.commits 0 of
    | SOME i => BindErr CUnread "body_hash_mismatch" i
    | NONE =>
      let chids = MAP (\c. blake3 c.skelBytes) g.commits in
        if LENGTH (sortedDedup chids) <> LENGTH chids
        then BindErr CUnread "duplicate_commit" 0
        else
          (case firstBadDepIdxA g.commits 0 of
           | SOME i => BindErr CUnread "dep_index_over" i
           | NONE =>
             (case kahnOrder chids (MAP (\c. c.cskel.deps) g.commits) of
              | NONE => BindErr CUnread "topo_order" 0
              | SOME canon =>
                  if canon <> chids
                  then BindErr CUnread "topo_order" 0
                  else if MAP (\p. p.pchid) g.prereqs <>
                          boundaryOf g chids
                  then BindErr CUnread "prereq_boundary" 0
                  else BindOk <| bchids := chids ;
                                 btip := LAST chids |>))
End

Definition contentRefd_def:
  contentRefd (g:geolog) (h:num list) <=>
    EXISTS (\c.
      let used = commitUsedDeps c in
        EXISTS (\j. oEL j c.cskel.deps = SOME h /\
                    (c.cskel.parentCount <= j \/ MEM j used))
               (COUNT_LIST (LENGTH c.cskel.deps)))
      g.commits
End

Definition prereqFlagTag_def:
  prereqFlagTag (flag:num) : string =
    if flag = 0 then "prereq_content_assumed_held"
    else if flag = 1 then "prereq_content_roster_unresolved"
    else "prereq_content_findable_unresolved"
End

Definition firstContentPrereqA_def:
  firstContentPrereqA (g:geolog) (ps:prereq list) (i:num)
                      : (string # num) option =
    case ps of
    | [] => NONE
    | (p::rest) =>
        if contentRefd g p.pchid
        then SOME (prereqFlagTag p.pflag, i)
        else firstContentPrereqA g rest (i + 1)
End

Definition sealedBindCheck_def:
  sealedBindCheck (g:geolog) (b:bindinfo) : (string # num) option =
    let tips = tipsOf g b.bchids in
      if LENGTH tips <> 1 then SOME ("tip_not_unique", LENGTH tips)
      else firstContentPrereqA g g.prereqs 0
End

Definition readGeologBind_def:
  readGeologBind (bs:num list) : bindres =
    case readGeolog bs of
    | RErr c t w => BindErr c t w
    | ROk g => bindChain g
End

Definition readGeologSealedBind_def:
  readGeologSealedBind (bs:num list) : bindres =
    case readGeologSealed bs of
    | RErr c t w => BindErr c t w
    | ROk g =>
      (case bindChain g of
       | BindErr c t w => BindErr c t w
       | BindOk b =>
         (case sealedBindCheck g b of
          | SOME (t, w) => BindErr CUnsupp t w
          | NONE => BindOk b))
End

Definition renderChids_def:
  renderChids (hs:(num list) list) (i:num) : string =
    case hs of
    | [] => ""
    | (h::rest) =>
        "chid " ++ numS i ++ ": 0x" ++ hexS h ++ "\n" ++
        renderChids rest (i + 1)
End

Definition renderBindRes_def:
  renderBindRes (r:bindres) : string =
    case r of
    | BindErr c t w =>
        renderClass c ++ " " ++ t ++ " " ++ numS w ++ "\n"
    | BindOk b =>
        "OK tip=0x" ++ hexS b.btip ++ "\n" ++ renderChids b.bchids 0
End
