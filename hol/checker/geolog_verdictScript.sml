(*
  The composed end-to-end verdict: bytes -> readGeologCert -> columns
  -> checkJoins, rendered as a four-way verdict type (unreadable /
  unsupported / reject / verified), each constructor carrying its
  witness. Includes the soundness theorem connecting the verified arm
  to the reference checker through the composition theorem's bridge
  hypotheses.
*)
Theory geolog_verdict

Ancestors
  arithmetic list rich_list option pair string
  geolog_read geolog_bind geolog_o2 geolog_cert
  qtsl_cert qtsl_cols qtsl_wf qtsl_joins

Datatype:
  gverdict = VdUnreadable string num
           | VdUnsupported string num
           | VdReject string num
           | VdVerified (num list) (num list)
End

Definition checkGeologCert_def:
  checkGeologCert (pins:pins) (bs:num list) : gverdict =
    case readGeologSealed bs of
    | RErr CUnread t w => VdUnreadable t w
    | RErr CUnsupp t w => VdUnsupported t w
    | ROk g =>
      (case bindChain g of
       | BindErr CUnread t w => VdUnreadable t w
       | BindErr CUnsupp t w => VdUnsupported t w
       | BindOk b =>
         (case sealedBindCheckR pins g b of
          | SOME (t, w) => VdUnsupported t w
          | NONE =>
            (case certOfRows pins g of
             | CErr CUnread t w => VdUnreadable t w
             | CErr CUnsupp t w => VdUnsupported t w
             | COk cols =>
               (case checkJoins cols of
                | NONE => VdReject "ctx_none" 0
                | SOME F => VdReject "joins" 0
                | SOME T => VdVerified b.btip cols.hdrImage))))
End

Theorem checkGeologCert_unreadable:
  !pins bs t w.
    checkGeologCert pins bs = VdUnreadable t w <=>
    readGeologCert pins bs = CErr CUnread t w
Proof
  rpt gen_tac
  >> simp[checkGeologCert_def, readGeologCert_def]
  >> rpt (BasicProvers.TOP_CASE_TAC >> simp[])
QED

Theorem checkGeologCert_unsupported:
  !pins bs t w.
    checkGeologCert pins bs = VdUnsupported t w <=>
    readGeologCert pins bs = CErr CUnsupp t w
Proof
  rpt gen_tac
  >> simp[checkGeologCert_def, readGeologCert_def]
  >> rpt (BasicProvers.TOP_CASE_TAC >> simp[])
QED

Theorem checkGeologCert_reject:
  !pins bs t w.
    checkGeologCert pins bs = VdReject t w <=>
    ?cols.
      readGeologCert pins bs = COk cols /\ w = 0 /\
      ((t = "ctx_none" /\ checkJoins cols = NONE) \/
       (t = "joins" /\ checkJoins cols = SOME F))
Proof
  rpt gen_tac
  >> simp[checkGeologCert_def, readGeologCert_def]
  >> rpt (BasicProvers.TOP_CASE_TAC >> simp[])
  >> metis_tac[]
QED

Theorem checkGeologCert_verified:
  !pins bs c s.
    checkGeologCert pins bs = VdVerified c s <=>
    ?g b cols.
      readGeologSealed bs = ROk g /\
      bindChain g = BindOk b /\
      sealedBindCheckR pins g b = NONE /\
      certOfRows pins g = COk cols /\
      checkJoins cols = SOME T /\
      c = b.btip /\ s = cols.hdrImage
Proof
  rpt gen_tac
  >> simp[checkGeologCert_def, AllCaseEqs()]
  >> metis_tac[]
QED

Theorem checkGeologCert_verified_chain:
  !pins bs c s.
    checkGeologCert pins bs = VdVerified c s ==>
    ?cols. readGeologCert pins bs = COk cols /\
           checkJoins cols = SOME T /\ s = cols.hdrImage
Proof
  rpt gen_tac
  >> simp[checkGeologCert_verified]
  >> strip_tac
  >> qexists_tac `cols`
  >> simp[readGeologCert_def]
QED

Theorem checkGeologCert_O2:
  !pins bs.
    (?t w. checkGeologCert pins bs = VdUnreadable t w /\
           readGeologCert pins bs = CErr CUnread t w) \/
    (?t w. checkGeologCert pins bs = VdUnsupported t w /\
           readGeologCert pins bs = CErr CUnsupp t w) \/
    (?t cols. checkGeologCert pins bs = VdReject t 0 /\
              readGeologCert pins bs = COk cols /\
              checkJoins cols <> SOME T) \/
    (?g b cols.
       checkGeologCert pins bs = VdVerified b.btip cols.hdrImage /\
       readGeologSealed bs = ROk g /\ wfGeolog g /\
       EVERY (\c. EVERY coreOp c.cbody.ops) g.commits /\
       bindChain g = BindOk b /\
       LENGTH b.bchids = LENGTH g.commits /\
       EVERY (\h. LENGTH h = 32 /\ EVERY (\x. x < 256) h) b.bchids /\
       b.btip = LAST b.bchids /\
       sealedBindCheckR pins g b = NONE /\
       certOfRows pins g = COk cols /\
       readGeologCert pins bs = COk cols /\
       cols.topoMode = 0 /\ cols.blockSize = 0 /\
       cols.nNodes = LENGTH cols.nodeTag /\
       cols.nPool = LENGTH cols.poolTag /\
       LENGTH cols.nodeConcl = cols.nNodes /\
       checkJoins cols = SOME T)
Proof
  rpt gen_tac
  >> Cases_on `checkGeologCert pins bs`
  >- ( disj1_tac
      >> metis_tac[checkGeologCert_unreadable])
  >- ( disj2_tac >> disj1_tac
      >> metis_tac[checkGeologCert_unsupported])
  >- ( disj2_tac >> disj2_tac >> disj1_tac
      >> pop_assum (assume_tac o REWRITE_RULE [checkGeologCert_reject])
      >> gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE,
                            optionTheory.SOME_11])
  >>  rpt disj2_tac
  >> pop_assum (assume_tac o REWRITE_RULE [checkGeologCert_verified])
  >> gvs[]
  >> rename [`readGeologSealed bs = ROk g`]
  >> imp_res_tac readGeologSealed_wf
  >> imp_res_tac bindChain_shape
  >> qspecl_then [`pins`, `g`] mp_tac certOfRows_O2
  >> strip_tac >> gvs[]
  >> simp[readGeologCert_def]
QED

Definition renderVerdict_def:
  renderVerdict (v:gverdict) : string =
    case v of
    | VdUnreadable t w =>
        "VERDICT UNREADABLE " ++ t ++ " " ++ numS w ++ "\n"
    | VdUnsupported t w =>
        "VERDICT UNSUPPORTED " ++ t ++ " " ++ numS w ++ "\n"
    | VdReject t w =>
        "VERDICT REJECT " ++ t ++ " " ++ numS w ++ "\n"
    | VdVerified c s =>
        "VERDICT VERIFIED " ++ hexS c ++ "\n" ++
        "STMTLEN " ++ numS (LENGTH s) ++ "\n"
End

Theorem renderVerdict_verified_prefix:
  !v. isPREFIX "VERDICT VERIFIED" (renderVerdict v) <=>
      ?c s. v = VdVerified c s
Proof
  Cases
  >> simp[renderVerdict_def]
  >> EVAL_TAC >> simp[]
QED

Theorem checkGeologCert_sound:
  !pins bs c s.
    checkGeologCert pins bs = VdVerified c s ==>
    ?g b cols.
      readGeologSealed bs = ROk g /\
      bindChain g = BindOk b /\
      certOfRows pins g = COk cols /\
      c = b.btip /\ s = cols.hdrImage /\
      checkJoins cols = SOME T /\
      !ct ws pf rest.
        mkCtx cols = SOME ct /\ reconTotal cols ct /\
        parseCert (s ++ rest) = SOME (ws, pf) /\
        nodeCorr cols ct (cols.nNodes - 1) pf ==>
        checkPf ws pf
Proof
  rpt gen_tac
  >> simp[checkGeologCert_verified]
  >> strip_tac
  >> qexistsl_tac [`g`, `b`, `cols`] >> simp[]
  >> rpt gen_tac >> strip_tac
  >> `wfColumns cols ct /\ checkNodes cols ct`
       by gvs[checkJoins_def, AllCaseEqs()]
  >> drule_all checkJoins_eq_checkPf_root
  >> simp[]
QED
