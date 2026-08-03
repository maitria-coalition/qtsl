(*
  Decode totality for the geolog reader, stated and proved: on an
  arbitrary byte string, readGeolog either rejects with a named class,
  or accepts and yields a structure satisfying the well-sortedness
  predicate wfGeolog defined here — cell references bounded, value
  cells in their ruled code bands, hashes at their normative extents.
*)
Theory geolog_o2

Ancestors
  geolog_read geolog_bind blake3
  arithmetic list rich_list option pair

Definition wfRef_def:
  wfRef (r:elemref) <=>
    case r of
    | ERLocal n => n <= 4294967295
    | ERExt d c => d <= MAX_DEP_INDEX /\ c <= 4294967295
End

Definition wfVal_def:
  wfVal (v:gvalue) <=>
    case v of
    | GVRef r => wfRef r
    | GVLit code p => code <= 14 /\ litOk code p
    | GVCommitId i => i <= MAX_DEP_INDEX
    | GVExt code p => 16 <= code /\ code <= 63
    | GVAbs code p => 64 <= code /\ code <= 79
End

Definition wfMeta_def:
  wfMeta (m:certmeta) <=>
    (case m.goalJudgmentHash of NONE => T | SOME h => LENGTH h = 32) /\
    (case m.theoryRev of NONE => T | SOME h => LENGTH h = 32) /\
    (case m.rootHash of NONE => T | SOME h => LENGTH h = 32)
End

Definition wfOp_def:
  wfOp (op:gop) <=>
    case op of
    | GElta r => wfRef r
    | GRela r args => wfRef r /\ EVERY wfVal args
    | GFuna r args v => wfRef r /\ EVERY wfVal args /\ wfVal v
    | GEltd r => wfRef r
    | GCert fmt m cert => fmt <= 65535 /\ wfMeta m
    | GUnknown k p => 6 < k
End

Definition wfBody_def:
  wfBody (b:gbody) <=>
    EVERY wfOp b.ops /\
    LENGTH b.ops <= MAX_BODY_OPS /\
    zoneLawsOk b.zoneRuns (tsCellCount b.ops)
End

Definition wfSkel_def:
  wfSkel (s:skel) <=>
    LENGTH s.author = 32 /\
    EVERY (\d. LENGTH d = 32) s.deps /\
    LENGTH s.deps <= 65535 /\
    s.parentCount <= LENGTH s.deps /\
    strictAsc (TAKE s.parentCount s.deps) /\
    strictAsc (DROP s.parentCount s.deps) /\
    noCrossDup (TAKE s.parentCount s.deps) (DROP s.parentCount s.deps) /\
    (case s.message of
     | NONE => T
     | SOME m => LENGTH m <= 4096 /\ utf8Ok m) /\
    LENGTH s.bodyHash = 32
End

Definition wfCommit_def:
  wfCommit (c:gcommit) <=>
    LENGTH c.sigBytes = 64 /\
    92 <= LENGTH c.skelBytes /\
    rdSkeleton c.skelBytes = SOME c.cskel /\
    rdBody c.bodyBytes = BOk c.cbody /\
    wfSkel c.cskel /\
    wfBody c.cbody
End

Definition wfPrereq_def:
  wfPrereq (p:prereq) <=>
    p.pflag <= 2 /\ LENGTH p.pchid = 32 /\
    (case p.prosterId of
     | NONE => p.pflag <> 1
     | SOME r => p.pflag = 1)
End

Definition wfGeolog_def:
  wfGeolog (g:geolog) <=>
    EVERY wfPrereq g.prereqs /\
    prereqAsc g.prereqs /\
    g.commits <> [] /\
    EVERY wfCommit g.commits
End

Definition coreOp_def:
  coreOp (op:gop) <=>
    case op of
    | GElta r => T
    | GRela r args => T
    | GFuna r args v => T
    | _ => F
End

Theorem bytesAt_len:
  !bs off len c. bytesAt bs off len = SOME c ==> LENGTH c = len
Proof
  rw[bytesAt_def] >> simp[LENGTH_TAKE]
QED

Theorem everyP_take:
  !l n. EVERY P l ==> EVERY P (TAKE n l)
Proof
  Induct >> rw[] >> Cases_on `n` >> gvs[]
QED

Theorem everyP_drop:
  !l n. EVERY P l ==> EVERY P (DROP n l)
Proof
  Induct >> rw[] >> Cases_on `n` >> gvs[]
QED

Theorem bytesAt_every:
  !bs off len c. bytesAt bs off len = SOME c /\ EVERY P bs ==> EVERY P c
Proof
  rw[bytesAt_def] >> irule everyP_take >> irule everyP_drop >> simp[]
QED

Theorem rdElemRef_wf:
  !bs pos r p. rdElemRef bs pos = SOME (r, p) ==> wfRef r
Proof
  rpt gen_tac >> strip_tac >>
  gvs[rdElemRef_def, AllCaseEqs(), wfRef_def]
QED

Theorem oneRefExact_wf:
  !b r. oneRefExact b = SOME r ==> wfRef r
Proof
  rpt gen_tac >> strip_tac >> gvs[oneRefExact_def, AllCaseEqs()] >>
  metis_tac[rdElemRef_wf]
QED

Theorem rdValue_wf:
  !bs pos v p. rdValue bs pos = SOME (v, p) ==> wfVal v
Proof
  rpt gen_tac >> strip_tac >>
  gvs[rdValue_def, AllCaseEqs(), wfVal_def] >>
  metis_tac[rdElemRef_wf]
QED

Theorem rdValuesKA_wf:
  !k bs pos acc vs p.
    rdValuesKA bs pos k acc = SOME (vs, p) /\ EVERY wfVal acc ==>
    EVERY wfVal vs
Proof
  Induct >> rpt gen_tac >> simp[Once rdValuesKA_def] >> strip_tac >>
  gvs[AllCaseEqs(), EVERY_REVERSE] >>
  (first_x_assum drule >> impl_tac
   >- (drule rdValue_wf >> simp[]) >>
   strip_tac >> gvs[])
QED

Theorem rdArgsRow_wf:
  !b vs. rdArgsRow b = SOME vs ==> EVERY wfVal vs
Proof
  rpt gen_tac >> strip_tac >>
  gvs[rdArgsRow_def, rdValuesK_def, AllCaseEqs()] >>
  drule rdValuesKA_wf >> simp[]
QED

Theorem rdValueRowExact_wf:
  !b v. rdValueRowExact b = SOME v ==> wfVal v
Proof
  rpt gen_tac >> strip_tac >> gvs[rdValueRowExact_def, AllCaseEqs()] >>
  metis_tac[rdValue_wf]
QED

Theorem rdCertMetaEntries_wf:
  !k b pos prev m m' p.
    rdCertMetaEntries b pos prev k m = SOME (m', p) /\ wfMeta m ==>
    wfMeta m'
Proof
  Induct >> rpt gen_tac >> simp[Once rdCertMetaEntries_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  (first_x_assum drule >> impl_tac
   >- gvs[wfMeta_def] >>
   strip_tac >> gvs[])
QED

Theorem rdCertPayload_wf:
  !b fmt m cert.
    rdCertPayload b = SOME (fmt, m, cert) ==> fmt <= 65535 /\ wfMeta m
Proof
  rpt gen_tac >> strip_tac >> gvs[rdCertPayload_def, AllCaseEqs()] >>
  drule rdCertMetaEntries_wf >> simp[wfMeta_def, emptyCertMeta_def]
QED

Theorem decEltasA_wf:
  !idxs accR accC rs cs.
    decEltasA symbols idxs accR accC = SOME (rs, cs) /\
    EVERY wfRef accR ==>
    EVERY wfRef rs /\ LENGTH rs = LENGTH idxs + LENGTH accR
Proof
  Induct >> rpt gen_tac >> simp[Once decEltasA_def] >> strip_tac >>
  gvs[AllCaseEqs(), EVERY_REVERSE] >>
  (first_x_assum drule >> impl_tac
   >- (drule oneRefExact_wf >> simp[]) >>
   strip_tac >> gvs[ADD1])
QED

Theorem decEltas_wf:
  decEltas symbols idxs = SOME (rs, cs) ==>
  EVERY wfRef rs /\ LENGTH rs = LENGTH idxs
Proof
  strip_tac >> gvs[decEltas_def] >> drule decEltasA_wf >> simp[]
QED

Theorem decRelasA_wf:
  !idxs rows accO accK ops keys.
    decRelasA symbols idxs rows accO accK = SOME (ops, keys) /\
    EVERY wfOp accO ==>
    EVERY wfOp ops /\ LENGTH ops = LENGTH idxs + LENGTH accO
Proof
  Induct >> rpt gen_tac >> simp[Once decRelasA_def] >> strip_tac >>
  gvs[AllCaseEqs(), EVERY_REVERSE] >>
  (first_x_assum drule >> impl_tac
   >- (gvs[wfOp_def] >> metis_tac[oneRefExact_wf, rdArgsRow_wf]) >>
   strip_tac >> gvs[ADD1])
QED

Theorem decRelas_wf:
  decRelas symbols idxs rows = SOME (ops, keys) ==>
  EVERY wfOp ops /\ LENGTH ops = LENGTH idxs
Proof
  strip_tac >> gvs[decRelas_def] >> drule decRelasA_wf >> simp[]
QED

Theorem decFunasA_wf:
  !idxs arows vrows accO accK ops keys.
    decFunasA symbols idxs arows vrows accO accK = SOME (ops, keys) /\
    EVERY wfOp accO ==>
    EVERY wfOp ops /\ LENGTH ops = LENGTH idxs + LENGTH accO
Proof
  Induct >> rpt gen_tac >> simp[Once decFunasA_def] >> strip_tac >>
  gvs[AllCaseEqs(), EVERY_REVERSE] >>
  (first_x_assum drule >> impl_tac
   >- (gvs[wfOp_def] >>
       metis_tac[oneRefExact_wf, rdArgsRow_wf, rdValueRowExact_wf]) >>
   strip_tac >> gvs[ADD1])
QED

Theorem decFunas_wf:
  decFunas symbols idxs arows vrows = SOME (ops, keys) ==>
  EVERY wfOp ops /\ LENGTH ops = LENGTH idxs
Proof
  strip_tac >> gvs[decFunas_def] >> drule decFunasA_wf >> simp[]
QED

Theorem decEltdsA_wf:
  !rows accO accK ops keys.
    decEltdsA rows accO accK = SOME (ops, keys) /\ EVERY wfOp accO ==>
    EVERY wfOp ops /\ LENGTH ops = LENGTH rows + LENGTH accO
Proof
  Induct >> rpt gen_tac >> simp[Once decEltdsA_def] >> strip_tac >>
  gvs[AllCaseEqs(), EVERY_REVERSE] >>
  (first_x_assum drule >> impl_tac
   >- (gvs[wfOp_def] >> metis_tac[oneRefExact_wf]) >>
   strip_tac >> gvs[ADD1])
QED

Theorem decEltds_wf:
  decEltds rows = SOME (ops, keys) ==>
  EVERY wfOp ops /\ LENGTH ops = LENGTH rows
Proof
  strip_tac >> gvs[decEltds_def] >> drule decEltdsA_wf >> simp[]
QED

Theorem decResidualsA_wf:
  !rows acc ops.
    decResidualsA rows acc = SOME ops /\ EVERY wfOp acc ==>
    EVERY wfOp ops /\ LENGTH ops = LENGTH rows + LENGTH acc
Proof
  Induct >> rpt gen_tac >> simp[Once decResidualsA_def] >> strip_tac >>
  gvs[AllCaseEqs(), EVERY_REVERSE] >>
  (first_x_assum drule >> impl_tac
   >- (gvs[wfOp_def] >> TRY (metis_tac[rdCertPayload_wf])) >>
   strip_tac >> gvs[ADD1])
QED

Theorem decResiduals_wf:
  decResiduals rows = SOME ops ==>
  EVERY wfOp ops /\ LENGTH ops = LENGTH rows
Proof
  strip_tac >> gvs[decResiduals_def] >> drule decResidualsA_wf >> simp[]
QED

Theorem rdBody_wf:
  !bb b. rdBody bb = BOk b ==> wfBody b
Proof
  rpt gen_tac >> strip_tac >> gvs[rdBody_def, AllCaseEqs()] >>
  imp_res_tac decEltas_wf >>
  imp_res_tac decRelas_wf >>
  imp_res_tac decFunas_wf >>
  imp_res_tac decEltds_wf >>
  imp_res_tac decResiduals_wf >>
  gvs[wfBody_def, EVERY_APPEND, EVERY_MAP, wfOp_def, SF ETA_ss]
QED

Theorem rdSkelDepsA_wf:
  !k base acc ds.
    rdSkelDepsA sk k base acc = SOME ds /\
    EVERY (\d. LENGTH d = 32) acc ==>
    EVERY (\d. LENGTH d = 32) ds /\ LENGTH ds = k + LENGTH acc
Proof
  Induct >> rpt gen_tac >> simp[Once rdSkelDepsA_def] >> strip_tac >>
  gvs[AllCaseEqs(), EVERY_REVERSE] >>
  (first_x_assum drule >> impl_tac
   >- (imp_res_tac bytesAt_len >> gvs[]) >>
   strip_tac >> gvs[ADD1])
QED

Theorem rdSkelDeps_wf:
  rdSkelDeps sk k base = SOME ds ==>
  EVERY (\d. LENGTH d = 32) ds /\ LENGTH ds = k
Proof
  strip_tac >> gvs[rdSkelDeps_def] >> drule rdSkelDepsA_wf >> simp[]
QED

Theorem rdSkeleton_min:
  !sk s. rdSkeleton sk = SOME s ==> 92 <= LENGTH sk
Proof
  rpt gen_tac >> simp[Once rdSkeleton_def] >> rw[] >> gvs[]
QED

Theorem rdSkeleton_wf:
  !sk s. rdSkeleton sk = SOME s ==> wfSkel s
Proof
  rpt gen_tac >> strip_tac >> gvs[rdSkeleton_def, AllCaseEqs()] >>
  imp_res_tac bytesAt_len >>
  imp_res_tac rdSkelDeps_wf >>
  gvs[wfSkel_def] >>
  CASE_TAC >> gvs[] >>
  imp_res_tac bytesAt_len >> gvs[]
QED

Theorem rdPrereqsA_wf:
  !k pos acc ps p.
    rdPrereqsA bs k pos acc = PROk ps p /\ EVERY wfPrereq acc ==>
    EVERY wfPrereq ps
Proof
  Induct >> rpt gen_tac >> simp[Once rdPrereqsA_def] >> strip_tac >>
  gvs[AllCaseEqs(), EVERY_REVERSE] >>
  (first_x_assum drule >> impl_tac
   >- (imp_res_tac bytesAt_len >> gvs[wfPrereq_def]) >>
   strip_tac >> gvs[])
QED

Theorem rdCommitsA_wf:
  !k pos acc cs p.
    rdCommitsA bs k pos acc = CROk cs p /\ EVERY wfCommit acc ==>
    EVERY wfCommit cs /\ LENGTH cs = k + LENGTH acc
Proof
  Induct >> rpt gen_tac >> simp[Once rdCommitsA_def] >> strip_tac >>
  gvs[AllCaseEqs(), EVERY_REVERSE] >>
  (first_x_assum drule >> impl_tac
   >- (imp_res_tac bytesAt_len >>
       imp_res_tac rdSkeleton_min >>
       imp_res_tac rdSkeleton_wf >>
       imp_res_tac rdBody_wf >>
       gvs[wfCommit_def, LENGTH_TAKE]) >>
   strip_tac >> gvs[ADD1])
QED

Theorem readGeolog_wf:
  !bs g. readGeolog bs = ROk g ==> wfGeolog g
Proof
  rpt gen_tac >> strip_tac >> gvs[readGeolog_def, AllCaseEqs()] >>
  gvs[rdPrereqs_def, rdCommits_def] >>
  drule rdPrereqsA_wf >> simp[] >> strip_tac >>
  drule rdCommitsA_wf >> simp[] >> strip_tac >>
  gvs[wfGeolog_def] >>
  strip_tac >> gvs[]
QED

Theorem readGeolog_O2:
  !bs. (?c t w. readGeolog bs = RErr c t w) \/
       (?g. readGeolog bs = ROk g /\ wfGeolog g)
Proof
  gen_tac >> Cases_on `readGeolog bs` >> simp[] >>
  metis_tac[readGeolog_wf]
QED

Theorem opUnsuppTag_none:
  !op. opUnsuppTag op = NONE <=> coreOp op
Proof
  Cases >> rw[opUnsuppTag_def, coreOp_def]
QED

Theorem firstUnsupp_none:
  !ops. firstUnsupp ops = NONE <=> EVERY coreOp ops
Proof
  Induct >> rw[Once firstUnsupp_def] >>
  Cases_on `opUnsuppTag h` >> gvs[GSYM opUnsuppTag_none]
QED

Triviality flat_firstUnsupp_nil:
  !cs. FLAT (MAP (\c. case firstUnsupp c.cbody.ops of
                      | SOME tw => [tw]
                      | NONE => []) cs) = [] ==>
       EVERY (\c. EVERY coreOp c.cbody.ops) cs
Proof
  Induct >> rw[] >> gvs[AllCaseEqs()] >>
  gvs[firstUnsupp_none]
QED

Theorem sealedCheck_none_imp:
  !g. sealedCheck g = NONE ==>
      EVERY (\c. EVERY coreOp c.cbody.ops) g.commits
Proof
  rw[sealedCheck_def, AllCaseEqs()] >>
  irule flat_firstUnsupp_nil >> gvs[]
QED

Theorem readGeologSealed_wf:
  !bs g. readGeologSealed bs = ROk g ==>
         wfGeolog g /\ EVERY (\c. EVERY coreOp c.cbody.ops) g.commits
Proof
  rpt gen_tac >> strip_tac >>
  gvs[readGeologSealed_def, AllCaseEqs()] >>
  imp_res_tac readGeolog_wf >>
  imp_res_tac sealedCheck_none_imp >> gvs[]
QED

Theorem readGeologSealed_O2:
  !bs. (?c t w. readGeologSealed bs = RErr c t w) \/
       (?g. readGeologSealed bs = ROk g /\ wfGeolog g /\
            EVERY (\c. EVERY coreOp c.cbody.ops) g.commits)
Proof
  gen_tac >> Cases_on `readGeologSealed bs` >> simp[] >>
  metis_tac[readGeologSealed_wf]
QED

Theorem rdPrereqsA_bytes:
  !k pos acc ps p.
    rdPrereqsA bs k pos acc = PROk ps p /\
    EVERY (\x. x < 256) bs /\
    EVERY (\q. EVERY (\x. x < 256) q.pchid) acc ==>
    EVERY (\q. EVERY (\x. x < 256) q.pchid) ps
Proof
  Induct >> rpt gen_tac >> simp[Once rdPrereqsA_def] >> strip_tac >>
  gvs[AllCaseEqs(), EVERY_REVERSE] >>
  (first_x_assum drule >> impl_tac
   >- (imp_res_tac bytesAt_every >> gvs[]) >>
   strip_tac >> gvs[])
QED

Theorem rdCommitsA_bytes:
  !k pos acc cs p.
    rdCommitsA bs k pos acc = CROk cs p /\
    EVERY (\x. x < 256) bs /\
    EVERY (\c. EVERY (\x. x < 256) c.sigBytes /\
               EVERY (\x. x < 256) c.skelBytes /\
               EVERY (\x. x < 256) c.bodyBytes) acc ==>
    EVERY (\c. EVERY (\x. x < 256) c.sigBytes /\
               EVERY (\x. x < 256) c.skelBytes /\
               EVERY (\x. x < 256) c.bodyBytes) cs
Proof
  Induct >> rpt gen_tac >> simp[Once rdCommitsA_def] >> strip_tac >>
  gvs[AllCaseEqs(), EVERY_REVERSE] >>
  (first_x_assum drule >> impl_tac
   >- (imp_res_tac bytesAt_every >>
       gvs[everyP_take, everyP_drop]) >>
   strip_tac >> gvs[])
QED

Theorem readGeolog_bytes256:
  !bs g.
    readGeolog bs = ROk g /\ EVERY (\x. x < 256) bs ==>
    EVERY (\c. EVERY (\x. x < 256) c.sigBytes /\
               EVERY (\x. x < 256) c.skelBytes /\
               EVERY (\x. x < 256) c.bodyBytes) g.commits /\
    EVERY (\p. EVERY (\x. x < 256) p.pchid) g.prereqs
Proof
  rpt gen_tac >> strip_tac >> gvs[readGeolog_def, AllCaseEqs()] >>
  gvs[rdPrereqs_def, rdCommits_def] >>
  drule rdPrereqsA_bytes >> simp[] >> strip_tac >>
  drule rdCommitsA_bytes >> simp[] >> strip_tac >>
  gvs[]
QED

Theorem w32b_shape:
  !w. LENGTH (w32b w) = 4 /\ EVERY (\x. x < 256) (w32b w)
Proof
  rw[w32b_def]
QED

Theorem blake3_length:
  !bs. LENGTH (blake3 bs) = 32 /\ EVERY (\x. x < 256) (blake3 bs)
Proof
  gen_tac >> rw[blake3_def, b3RootBytes_def] >>
  pairarg_tac >> gvs[w32b_shape]
QED

Theorem bindChain_shape:
  !g b.
    bindChain g = BindOk b ==>
    LENGTH b.bchids = LENGTH g.commits /\
    EVERY (\h. LENGTH h = 32 /\ EVERY (\x. x < 256) h) b.bchids /\
    b.btip = LAST b.bchids
Proof
  rpt gen_tac >> strip_tac >> gvs[bindChain_def, AllCaseEqs()] >>
  simp[EVERY_MAP, EVERY_MEM, blake3_length]
QED

Theorem readGeologBind_O2:
  !bs. (?c t w. readGeologBind bs = BindErr c t w) \/
       (?g b. readGeologBind bs = BindOk b /\
              readGeolog bs = ROk g /\ wfGeolog g /\
              LENGTH b.bchids = LENGTH g.commits /\
              EVERY (\h. LENGTH h = 32 /\ EVERY (\x. x < 256) h)
                    b.bchids /\
              b.btip = LAST b.bchids)
Proof
  gen_tac >> Cases_on `readGeologBind bs` >> simp[] >>
  gvs[readGeologBind_def, AllCaseEqs()] >>
  metis_tac[readGeolog_wf, bindChain_shape]
QED

Theorem readGeologSealedBind_O2:
  !bs. (?c t w. readGeologSealedBind bs = BindErr c t w) \/
       (?g b. readGeologSealedBind bs = BindOk b /\
              readGeologSealed bs = ROk g /\ wfGeolog g /\
              EVERY (\c. EVERY coreOp c.cbody.ops) g.commits /\
              LENGTH b.bchids = LENGTH g.commits /\
              EVERY (\h. LENGTH h = 32 /\ EVERY (\x. x < 256) h)
                    b.bchids /\
              b.btip = LAST b.bchids)
Proof
  gen_tac >> Cases_on `readGeologSealedBind bs` >> simp[] >>
  gvs[readGeologSealedBind_def, AllCaseEqs()] >>
  metis_tac[readGeologSealed_wf, bindChain_shape]
QED
