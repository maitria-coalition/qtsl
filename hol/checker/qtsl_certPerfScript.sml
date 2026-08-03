(*
  Performance representations for the verified certificate checker,
  proved EQUAL to the spec functions (parseCert/checkPf) so the
  machine-code theorem statements are unchanged: single flat string
  input in place of a character fold, offset-indexed tables in place of
  association lists, and a fused structural fold that avoids
  re-expanding shared formulas per node. Nothing in the spec layer
  moves; every downstream theorem keeps its statement verbatim.
*)
Theory qtsl_certPerf
Ancestors
  rat integer mlstring mllist sptree[qualified] qtsl_dyadic qtsl_qarith
  qtsl_catalogue qtsl_cert
Libs
  preamble

Definition byteAt_def:
  byteAt (s:mlstring) (i:num) = if i < strlen s then ORD (strsub s i) else 0
End

Theorem byteAt_lt256:
  byteAt s i < 256
Proof
  rw[byteAt_def, stringTheory.ORD_BOUND]
QED

Definition secBytes_def:
  secBytes (s:mlstring) (i:num) (lim:num) =
    MAP ORD (TAKE (lim − i) (DROP i (explode s)))
End

Theorem strlen_explode[local]:
  LENGTH (explode s) = strlen s
Proof
  Cases_on ‘s’ >> simp[]
QED

Theorem secBytes_nil:
  lim ≤ i ∨ strlen s ≤ i ⇒ secBytes s i lim = []
Proof
  rw[secBytes_def]
  >> ‘lim − i = 0 ∨ LENGTH (explode s) ≤ i’ by gvs[strlen_explode]
  >> simp[listTheory.DROP_LENGTH_TOO_LONG]
QED

Theorem secBytes_cons:
  i < lim ∧ i < strlen s ⇒
  secBytes s i lim = byteAt s i :: secBytes s (i + 1) lim
Proof
  rw[secBytes_def]
  >> ‘lim − i = SUC (lim − (i + 1))’ by DECIDE_TAC
  >> pop_assum SUBST1_TAC
  >> ‘i < LENGTH (explode s)’ by gvs[strlen_explode]
  >> drule rich_listTheory.DROP_EL_CONS >> disch_then SUBST1_TAC
  >> simp[byteAt_def]
  >> Cases_on ‘s’ >> gvs[mlstringTheory.strsub_def]
QED

Theorem LENGTH_secBytes:
  LENGTH (secBytes s i lim) = MIN (lim − i) (strlen s − i)
Proof
  rw[secBytes_def, LENGTH_TAKE_EQ, strlen_explode, MIN_DEF] >> DECIDE_TAC
QED

Theorem secBytes_all_lt256:
  EVERY (λb. b < 256) (secBytes s i lim)
Proof
  rw[secBytes_def, EVERY_MEM]
  >> gvs[MEM_MAP, stringTheory.ORD_BOUND]
QED

Definition subBytes_def:
  subBytes (s:mlstring) (i:num) (0:num) = ([]:num list) ∧
  subBytes s i (SUC n) = byteAt s i :: subBytes s (i + 1) n
End

Theorem subBytes_TAKE:
  ∀n i. i + n ≤ strlen s ⇒
        subBytes s i n = MAP ORD (TAKE n (DROP i (explode s)))
Proof
  Induct >> rw[subBytes_def]
  >> ‘i < strlen s ∧ i + 1 + n ≤ strlen s’ by DECIDE_TAC
  >> first_x_assum drule >> disch_then SUBST1_TAC
  >> ‘i < LENGTH (explode s)’ by gvs[strlen_explode]
  >> drule rich_listTheory.DROP_EL_CONS >> disch_then SUBST1_TAC
  >> simp[byteAt_def]
  >> Cases_on ‘s’ >> gvs[mlstringTheory.strsub_def]
QED

Theorem subBytes_all_lt256:
  ∀n i. EVERY (λb. b < 256) (subBytes s i n)
Proof
  Induct >> rw[subBytes_def, byteAt_lt256]
QED

Definition leAt_def:
  leAt (s:mlstring) (i:num) (0:num) = (0:num) ∧
  leAt s i (SUC k) = byteAt s i + 256 * leAt s (i + 1) k
End

Theorem leAt_leN_subBytes:
  ∀k i. leAt s i k = leN (subBytes s i k)
Proof
  Induct >> rw[leAt_def, subBytes_def, leN_def]
QED

Definition rdU8I_def:
  rdU8I (s:mlstring) (lim:num) (i:num) =
    if i < lim ∧ i < strlen s then SOME (byteAt s i, i + 1)
    else NONE : (num # num) option
End

Definition takeNI_def:
  takeNI (s:mlstring) (lim:num) (n:num) (i:num) =
    if i + n ≤ lim ∧ i + n ≤ strlen s then SOME (subBytes s i n, i + n)
    else if n = 0 then SOME ([], i)
    else NONE : (num list # num) option
End

Definition rdLEI_def:
  rdLEI (s:mlstring) (lim:num) (k:num) (i:num) =
    if i + k ≤ lim ∧ i + k ≤ strlen s then SOME (leAt s i k, i + k)
    else if k = 0 then SOME (0, i)
    else NONE : (num # num) option
End

Definition rdRatI_def:
  rdRatI (s:mlstring) (lim:num) (i:num) =
    case rdLEI s lim 4 i of NONE => NONE | SOME (nl, i1) =>
    case rdLEI s lim 4 i1 of NONE => NONE | SOME (dl, i2) =>
    case takeNI s lim nl i2 of NONE => NONE | SOME (nb, i3) =>
    case takeNI s lim dl i3 of NONE => NONE | SOME (db, i4) =>
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
         SOME ((if neg then -(&mag / &d) else (&mag / &d)):rat, i4))
End

Definition rdBitsetI_def:
  rdBitsetI (s:mlstring) (lim:num) (n:num) (i:num) =
    case takeNI s lim ((n + 7) DIV 8) i of
    | NONE => NONE
    | SOME (bs, j) => if padOK bs n then SOME (bitsOf bs n, j) else NONE
End

Definition rdRatsNI_def:
  rdRatsNI (s:mlstring) (lim:num) (0:num) (i:num) = SOME ([]:rat list, i) ∧
  rdRatsNI s lim (SUC k) i =
    case rdRatI s lim i of NONE => NONE
    | SOME (q, i1) =>
      case rdRatsNI s lim k i1 of NONE => NONE
      | SOME (qs, i2) => SOME (q::qs, i2)
End

Definition rdBitsetsNI_def:
  rdBitsetsNI (s:mlstring) (lim:num) (nv:num) (0:num) (i:num) =
    SOME ([]:bool list list, i) ∧
  rdBitsetsNI s lim nv (SUC k) i =
    case rdBitsetI s lim nv i of NONE => NONE
    | SOME (b, i1) =>
      case rdBitsetsNI s lim nv k i1 of NONE => NONE
      | SOME (bs, i2) => SOME (b::bs, i2)
End

Definition rdCellsNI_def:
  rdCellsNI (s:mlstring) (lim:num) (nv:num) (0:num) (i:num) =
    SOME ([]:(bool list # bool list) list, i) ∧
  rdCellsNI s lim nv (SUC k) i =
    case rdBitsetI s lim nv i of NONE => NONE
    | SOME (sm, i1) =>
      case rdBitsetI s lim nv i1 of NONE => NONE
      | SOME (em, i2) =>
        case rdCellsNI s lim nv k i2 of NONE => NONE
        | SOME (cs, i3) => SOME ((sm, em)::cs, i3)
End

Definition rdLEsNI_def:
  rdLEsNI (s:mlstring) (lim:num) (w:num) (0:num) (i:num) =
    SOME ([]:num list, i) ∧
  rdLEsNI s lim w (SUC k) i =
    case rdLEI s lim w i of NONE => NONE
    | SOME (v, i1) =>
      case rdLEsNI s lim w k i1 of NONE => NONE
      | SOME (vs, i2) => SOME (v::vs, i2)
End

Theorem rdU8_corr:
  rdU8 (secBytes s i lim) =
  case rdU8I s lim i of
  | NONE => NONE
  | SOME (v, j) => SOME (v, secBytes s j lim)
Proof
  rw[rdU8I_def]
  >- (imp_res_tac secBytes_cons >> simp[rdU8_def])
  >> ‘lim ≤ i ∨ strlen s ≤ i’ by DECIDE_TAC
  >> simp[secBytes_nil, rdU8_def]
QED

Theorem rdU8I_bounds:
  rdU8I s lim i = SOME (v, j) ⇒ i < j ∧ j ≤ lim ∧ j ≤ strlen s
Proof
  rw[rdU8I_def] >> DECIDE_TAC
QED

Theorem LENGTH_subBytes[simp]:
  ∀n i. LENGTH (subBytes s i n) = n
Proof
  Induct >> rw[subBytes_def]
QED

Theorem takeN_corr:
  takeN n (secBytes s i lim) =
  case takeNI s lim n i of
  | NONE => NONE
  | SOME (bs, j) => SOME (bs, secBytes s j lim)
Proof
  rw[takeNI_def, takeN_def, LENGTH_secBytes]
  >- (gvs[secBytes_def, subBytes_TAKE]
      >> simp[GSYM MAP_TAKE, TAKE_TAKE_MIN]
      >> ‘MIN n (lim − i) = n’ by simp[MIN_DEF]
      >> simp[])
  >> gvs[secBytes_def, GSYM MAP_DROP, DROP_TAKE, rich_listTheory.DROP_DROP_T]
  >> ‘lim − i − n = lim − (i + n) ∧ n + i = i + n’ by DECIDE_TAC
  >> simp[]
QED

Theorem takeNI_bounds:
  i ≤ lim ∧ i ≤ strlen s ∧ takeNI s lim n i = SOME (bs, j) ⇒
  i ≤ j ∧ j ≤ lim ∧ j ≤ strlen s ∧ LENGTH bs = n
Proof
  rw[takeNI_def, AllCaseEqs()] >> simp[]
QED

Theorem rdLE_corr:
  rdLE k (secBytes s i lim) =
  case rdLEI s lim k i of
  | NONE => NONE
  | SOME (v, j) => SOME (v, secBytes s j lim)
Proof
  rw[rdLE_def, rdLEI_def, takeN_corr, takeNI_def, leAt_leN_subBytes]
  >> gvs[leN_def, leAt_leN_subBytes, subBytes_def]
QED

Theorem rdLEI_bounds:
  i ≤ lim ∧ i ≤ strlen s ∧ rdLEI s lim k i = SOME (v, j) ⇒
  i ≤ j ∧ j ≤ lim ∧ j ≤ strlen s
Proof
  rw[rdLEI_def] >> DECIDE_TAC
QED

Theorem rdRat_corr:
  rdRat (secBytes s i lim) =
  case rdRatI s lim i of
  | NONE => NONE
  | SOME (q, j) => SOME (q, secBytes s j lim)
Proof
  rw[rdRat_def, rdRatI_def, rdLE_corr]
  >> Cases_on ‘rdLEI s lim 4 i’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s lim 4 x1’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[takeN_corr]
  >> Cases_on ‘takeNI s lim x0 x1'’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[takeN_corr]
  >> Cases_on ‘takeNI s lim x0' x1''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> rw[]
QED

Theorem rdRatI_bounds:
  i ≤ lim ∧ i ≤ strlen s ∧ rdRatI s lim i = SOME (q, j) ⇒
  i ≤ j ∧ j ≤ lim ∧ j ≤ strlen s
Proof
  rw[rdRatI_def, AllCaseEqs()]
  >> imp_res_tac rdLEI_bounds
  >> imp_res_tac takeNI_bounds
  >> DECIDE_TAC
QED

Theorem rdBitset_corr:
  rdBitset n (secBytes s i lim) =
  case rdBitsetI s lim n i of
  | NONE => NONE
  | SOME (b, j) => SOME (b, secBytes s j lim)
Proof
  rw[rdBitset_def, rdBitsetI_def, takeN_corr]
  >> Cases_on ‘takeNI s lim ((n+7) DIV 8) i’ >> simp[]
  >> PairCases_on ‘x’ >> simp[] >> rw[]
QED

Theorem rdBitsetI_bounds:
  i ≤ lim ∧ i ≤ strlen s ∧ rdBitsetI s lim n i = SOME (b, j) ⇒
  i ≤ j ∧ j ≤ lim ∧ j ≤ strlen s
Proof
  rw[rdBitsetI_def, AllCaseEqs()] >> imp_res_tac takeNI_bounds >> simp[]
QED

Theorem rdRatsN_corr:
  ∀k i.
    rdRatsN k (secBytes s i lim) =
    case rdRatsNI s lim k i of
    | NONE => NONE
    | SOME (qs, j) => SOME (qs, secBytes s j lim)
Proof
  Induct >> rw[rdRatsN_def, rdRatsNI_def, rdRat_corr]
  >> Cases_on ‘rdRatI s lim i’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> Cases_on ‘rdRatsNI s lim k x1’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
QED

Theorem rdRatsNI_bounds:
  ∀k i qs j.
    i ≤ lim ∧ i ≤ strlen s ∧ rdRatsNI s lim k i = SOME (qs, j) ⇒
    i ≤ j ∧ j ≤ lim ∧ j ≤ strlen s
Proof
  Induct >> rw[rdRatsNI_def, AllCaseEqs()] >> simp[]
  >> imp_res_tac rdRatI_bounds >> res_tac >> DECIDE_TAC
QED

Theorem rdBitsetsN_corr:
  ∀k i.
    rdBitsetsN nv k (secBytes s i lim) =
    case rdBitsetsNI s lim nv k i of
    | NONE => NONE
    | SOME (bs, j) => SOME (bs, secBytes s j lim)
Proof
  Induct >> rw[rdBitsetsN_def, rdBitsetsNI_def, rdBitset_corr]
  >> Cases_on ‘rdBitsetI s lim nv i’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> Cases_on ‘rdBitsetsNI s lim nv k x1’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
QED

Theorem rdBitsetsNI_bounds:
  ∀k i bs j.
    i ≤ lim ∧ i ≤ strlen s ∧ rdBitsetsNI s lim nv k i = SOME (bs, j) ⇒
    i ≤ j ∧ j ≤ lim ∧ j ≤ strlen s
Proof
  Induct >> rw[rdBitsetsNI_def, AllCaseEqs()] >> simp[]
  >> imp_res_tac rdBitsetI_bounds >> res_tac >> DECIDE_TAC
QED

Theorem rdCellsN_corr:
  ∀k i.
    rdCellsN nv k (secBytes s i lim) =
    case rdCellsNI s lim nv k i of
    | NONE => NONE
    | SOME (cs, j) => SOME (cs, secBytes s j lim)
Proof
  Induct >> rw[rdCellsN_def, rdCellsNI_def, rdBitset_corr]
  >> Cases_on ‘rdBitsetI s lim nv i’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdBitset_corr]
  >> Cases_on ‘rdBitsetI s lim nv x1’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> Cases_on ‘rdCellsNI s lim nv k x1'’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
QED

Theorem rdCellsNI_bounds:
  ∀k i cs j.
    i ≤ lim ∧ i ≤ strlen s ∧ rdCellsNI s lim nv k i = SOME (cs, j) ⇒
    i ≤ j ∧ j ≤ lim ∧ j ≤ strlen s
Proof
  Induct >> rw[rdCellsNI_def, AllCaseEqs()] >> simp[]
  >> imp_res_tac rdBitsetI_bounds >> res_tac >> DECIDE_TAC
QED

Theorem rdLEsN_corr:
  ∀k i.
    rdLEsN w k (secBytes s i lim) =
    case rdLEsNI s lim w k i of
    | NONE => NONE
    | SOME (vs, j) => SOME (vs, secBytes s j lim)
Proof
  Induct >> rw[rdLEsN_def, rdLEsNI_def, rdLE_corr]
  >> Cases_on ‘rdLEI s lim w i’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> Cases_on ‘rdLEsNI s lim w k x1’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
QED

Theorem rdLEsNI_bounds:
  ∀k i vs j.
    i ≤ lim ∧ i ≤ strlen s ∧ rdLEsNI s lim w k i = SOME (vs, j) ⇒
    i ≤ j ∧ j ≤ lim ∧ j ≤ strlen s
Proof
  Induct >> rw[rdLEsNI_def, AllCaseEqs()] >> simp[]
  >> imp_res_tac rdLEI_bounds >> res_tac >> DECIDE_TAC
QED

Theorem secBytes_all:
  secBytes s 0 (strlen s) = MAP ORD (explode s)
Proof
  rw[secBytes_def, strlen_explode, TAKE_LENGTH_ID_rwt]
QED

Definition parseHeaderI_def:
  parseHeaderI (s:mlstring) =
    let lim = strlen s in
    case takeNI s lim 8 0 of NONE => NONE | SOME (magic, i0) =>
    if magic ≠ bernMagic then NONE else
    case rdLEI s lim 4 i0 of NONE => NONE | SOME (ver, i1) =>
    if ver ≠ (1:num) then NONE else
    case rdLEI s lim 4 i1 of NONE => NONE | SOME (flg, i2) =>
    if flg ≠ (0:num) then NONE else
    case rdLEI s lim 8 i2 of NONE => NONE | SOME (syo, i3) =>
    case rdLEI s lim 8 i3 of NONE => NONE | SOME (syl, i4) =>
    case rdLEI s lim 8 i4 of NONE => NONE | SOME (po, i5) =>
    case rdLEI s lim 8 i5 of NONE => NONE | SOME (pl, i6) =>
    case rdLEI s lim 8 i6 of NONE => NONE | SOME (dio, i7) =>
    case rdLEI s lim 8 i7 of NONE => NONE | SOME (dil, i8) =>
    case rdLEI s lim 8 i8 of NONE => NONE | SOME (pro, i9) =>
    case rdLEI s lim 8 i9 of NONE => NONE | SOME (prl, i10) =>
    case rdLEI s lim 4 i10 of NONE => NONE | SOME (nw, i11) =>
    case rdLEI s lim 4 i11 of NONE => NONE | SOME (na, i12) =>
    case rdLEI s lim 4 i12 of NONE => NONE | SOME (nn, i13) =>
    case rdLEI s lim 4 i13 of NONE => NONE | SOME (nc, i14) =>
    case rdLEI s lim 8 i14 of NONE => NONE | SOME (ro, i15) =>
    case rdLEI s lim 4 i15 of NONE => NONE | SOME (th, i16) =>
    case takeNI s lim 20 i16 of NONE => NONE | SOME (resv, i17) =>
    if ¬ EVERY (λb. b = (0:num)) resv then NONE else
    (let flen = strlen s in
       if ¬(sectionOK flen syo syl ∧ sectionOK flen po pl ∧
            sectionOK flen dio dil ∧ sectionOK flen pro prl) then NONE else
       if nw = (4294967295:num) then NONE else
       if po MOD 64 ≠ (0:num) then NONE else
         SOME <| symOff := syo ; symLen := syl ; payOff := po ; payLen := pl ;
                 diaOff := dio ; diaLen := dil ; prfOff := pro ; prfLen := prl ;
                 nWires := nw ; nApps := na ; nNodes := nn ; nCxs := nc ;
                 rootOff := ro ; thetaRef := th |>)
End

Theorem parseHeaderI_corr:
  parseHeader (MAP ORD (explode s)) = parseHeaderI s
Proof
  rw[parseHeader_def, parseHeaderI_def, GSYM secBytes_all]
  >> simp[takeN_corr]
  >> Cases_on ‘takeNI s (strlen s) 8 0’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> rw[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s (strlen s) 4 x1’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> rw[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s (strlen s) 4 x1'’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> rw[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s (strlen s) 8 x1''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s (strlen s) 8 x1'''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s (strlen s) 8 x1''''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s (strlen s) 8 x1'''''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s (strlen s) 8 x1''''''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s (strlen s) 8 x1'''''''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s (strlen s) 8 x1''''''''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s (strlen s) 8 x1'''''''''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s (strlen s) 4 x1''''''''''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s (strlen s) 4 x1'''''''''''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s (strlen s) 4 x1''''''''''''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s (strlen s) 4 x1'''''''''''''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s (strlen s) 8 x1''''''''''''''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s (strlen s) 4 x1'''''''''''''''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[takeN_corr]
  >> Cases_on ‘takeNI s (strlen s) 20 x1''''''''''''''''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> rw[]
  >> gvs[LENGTH_MAP, mlstringTheory.LENGTH_explode]
  >> rw[]
QED

Theorem secBytes_slice:
  off + len ≤ strlen s ∧ k ≤ len ⇒
  MAP ORD (DROP k (TAKE len (DROP off (explode s)))) =
  secBytes s (off + k) (off + len)
Proof
  rw[secBytes_def, DROP_TAKE, DROP_DROP_T]
QED

Theorem secBytes_slice0:
  off + len ≤ strlen s ⇒
  MAP ORD (TAKE len (DROP off (explode s))) = secBytes s off (off + len)
Proof
  strip_tac
  >> drule_then (qspec_then ‘0’ mp_tac) secBytes_slice
  >> simp[]
QED

Theorem LENGTH_slice:
  off + len ≤ strlen s ⇒
  LENGTH (TAKE len (DROP off (explode s))) = len
Proof
  rw[LENGTH_TAKE_EQ, strlen_explode]
QED

Definition parseSymRecI_def:
  parseSymRecI (s:mlstring) (base:num) (seclen:num) (recslen:num)
               (payOff:num) (payLen:num) (i:num) =
    let lim = base + seclen in
    let p = base + 32 * i in
    case rdU8I s lim p of NONE => NONE | SOME (k, r0) =>
    case rdU8I s lim r0 of NONE => NONE | SOME (sg, r1) =>
    case rdU8I s lim r1 of NONE => NONE | SOME (ex, r2) =>
    case rdU8I s lim r2 of NONE => NONE | SOME (resv, r3) =>
    if resv ≠ (0:num) then NONE else
    case kindOf k of NONE => NONE | SOME kd =>
    case signOf sg of NONE => NONE | SOME sn =>
    case extOf ex of NONE => NONE | SOME et =>
    case rdLEI s lim 4 r3 of NONE => NONE | SOME (rank, r4) =>
    case rdLEI s lim 8 r4 of NONE => NONE | SOME (shOff, r5) =>
    case rdLEI s lim 8 r5 of NONE => NONE | SOME (pOff, r6) =>
    case rdLEI s lim 8 r6 of NONE => NONE | SOME (pLen, r7) =>
    if shOff < recslen ∨ seclen < shOff + 8 * rank then NONE else
    case rdLEsNI s lim 8 rank (base + shOff) of
    | NONE => NONE
    | SOME (shape, r8) =>
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

Definition parseSymtabI_def:
  parseSymtabI (s:mlstring) (base:num) (seclen:num) (nw:num)
               (payOff:num) (payLen:num) =
    if seclen < 32 * nw then NONE else
      optSeq (MAP (parseSymRecI s base seclen (32 * nw) payOff payLen)
                  (rangeL nw))
End

Theorem parseSymRecI_corr:
  base + seclen ≤ strlen s ∧ 32 * i ≤ seclen ⇒
  parseSymRec (TAKE seclen (DROP base (MAP ORD (explode s))))
              seclen recslen payOff payLen i =
  parseSymRecI s base seclen recslen payOff payLen i
Proof
  strip_tac
  >> ‘∀k. k ≤ seclen ⇒
        DROP k (TAKE seclen (DROP base (MAP ORD (explode s)))) =
        secBytes s (base + k) (base + seclen)’
     by (rw[GSYM MAP_DROP, GSYM MAP_TAKE, DROP_TAKE,
            rich_listTheory.DROP_DROP_T, secBytes_def]
         >> ‘k + base = base + k ∧ seclen − k = base + seclen − (base + k)’
              by DECIDE_TAC
         >> simp[])
  >> rw[parseSymRec_def, parseSymRecI_def]
  >> first_assum (qspec_then ‘32 * i’ mp_tac)
  >> impl_tac >- simp[]
  >> disch_then SUBST1_TAC
  >> simp[rdU8_corr]
  >> namedCases_on ‘rdU8I s (base + seclen) (base + 32 * i)’ ["", "p1"] >> simp[]
  >> PairCases_on ‘p1’ >> simp[]
  >> simp[rdU8_corr]
  >> namedCases_on ‘rdU8I s (base + seclen) p11’ ["", "p2"] >> simp[]
  >> PairCases_on ‘p2’ >> simp[]
  >> simp[rdU8_corr]
  >> namedCases_on ‘rdU8I s (base + seclen) p21’ ["", "p3"] >> simp[]
  >> PairCases_on ‘p3’ >> simp[]
  >> simp[rdU8_corr]
  >> namedCases_on ‘rdU8I s (base + seclen) p31’ ["", "p4"] >> simp[]
  >> PairCases_on ‘p4’ >> simp[]
  >> rw[]
  >> namedCases_on ‘kindOf p10’ ["", "kd"] >> simp[]
  >> namedCases_on ‘signOf p20’ ["", "sn"] >> simp[]
  >> namedCases_on ‘extOf p30’ ["", "et"] >> simp[]
  >> simp[rdLE_corr]
  >> namedCases_on ‘rdLEI s (base + seclen) 4 p41’ ["", "p5"] >> simp[]
  >> PairCases_on ‘p5’ >> simp[]
  >> simp[rdLE_corr]
  >> namedCases_on ‘rdLEI s (base + seclen) 8 p51’ ["", "p6"] >> simp[]
  >> PairCases_on ‘p6’ >> simp[]
  >> simp[rdLE_corr]
  >> namedCases_on ‘rdLEI s (base + seclen) 8 p61’ ["", "p7"] >> simp[]
  >> PairCases_on ‘p7’ >> simp[]
  >> simp[rdLE_corr]
  >> namedCases_on ‘rdLEI s (base + seclen) 8 p71’ ["", "p8"] >> simp[]
  >> PairCases_on ‘p8’ >> simp[]
  >> rw[]
  >> qpat_x_assum ‘∀k. _’ (qspec_then ‘p60’ mp_tac)
  >> impl_tac >- DECIDE_TAC
  >> disch_then SUBST1_TAC
  >> simp[rdLEsN_corr]
  >> namedCases_on ‘rdLEsNI s (base + seclen) 8 p50 (base + p60)’ ["", "p9"] >> simp[]
  >> PairCases_on ‘p9’ >> simp[]
  >> rw[]
QED

Theorem parseSymtabI_corr:
  base + seclen ≤ strlen s ⇒
  parseSymtab (TAKE seclen (DROP base (MAP ORD (explode s))))
              seclen nw payOff payLen =
  parseSymtabI s base seclen nw payOff payLen
Proof
  strip_tac
  >> ‘LENGTH (TAKE seclen (DROP base (MAP ORD (explode s)))) = seclen’
       by simp[LENGTH_TAKE_EQ, mlstringTheory.LENGTH_explode]
  >> rw[parseSymtab_def, parseSymtabI_def]
  >> AP_TERM_TAC
  >> irule MAP_CONG >> rw[]
  >> irule parseSymRecI_corr
  >> gvs[qtsl_qarithTheory.MEM_rangeL]
QED

Definition parseComplexI_def:
  parseComplexI (s:mlstring) (lim:num) (i:num) =
    case rdLEI s lim 4 i of NONE => NONE | SOME (nv, i1) =>
    case rdLEI s lim 4 i1 of NONE => NONE | SOME (amb, i2) =>
    case rdRatsNI s lim (nv * amb) i2 of NONE => NONE | SOME (qs, i3) =>
    case rdLEI s lim 4 i3 of NONE => NONE | SOME (nsimp, i4) =>
    case rdBitsetsNI s lim nv nsimp i4 of NONE => NONE | SOME (simps, i5) =>
    case rdLEI s lim 4 i5 of NONE => NONE | SOME (ncell, i6) =>
    case rdCellsNI s lim nv ncell i6 of NONE => NONE | SOME (cells, i7) =>
      SOME (<| nVertices := nv ; ambDim := amb ;
               coord := chunksOf amb qs ;
               simplices := simps ; cells := cells |>, i7)
End

Definition parseComplexesNI_def:
  parseComplexesNI (s:mlstring) (lim:num) (0:num) (i:num) =
    SOME ([]:simpc list, i) ∧
  parseComplexesNI s lim (SUC k) i =
    case parseComplexI s lim i of NONE => NONE
    | SOME (cx, i1) =>
      case parseComplexesNI s lim k i1 of NONE => NONE
      | SOME (cxs, i2) => SOME (cx::cxs, i2)
End

Definition parseDiagramI_def:
  parseDiagramI (s:mlstring) (base:num) (seclen:num) (hnc:num) (hna:num) =
    let lim = base + seclen in
    case rdLEI s lim 4 base of NONE => NONE | SOME (nc, i1) =>
    if nc ≠ hnc then NONE else
    case parseComplexesNI s lim nc i1 of NONE => NONE | SOME (cxs, i2) =>
    case rdLEI s lim 4 i2 of NONE => NONE | SOME (na, i3) =>
    if na ≠ hna ∨ na ≠ (0:num) then NONE else
      SOME cxs
End

Theorem parseComplexI_bounds:
  i ≤ lim ∧ i ≤ strlen s ∧ parseComplexI s lim i = SOME (cx, j) ⇒
  i ≤ j ∧ j ≤ lim ∧ j ≤ strlen s
Proof
  rw[parseComplexI_def, AllCaseEqs()]
  >> imp_res_tac rdLEI_bounds
  >> imp_res_tac rdRatsNI_bounds
  >> imp_res_tac rdBitsetsNI_bounds
  >> imp_res_tac rdCellsNI_bounds
  >> DECIDE_TAC
QED

Theorem parseComplex_corr:
  parseComplex (secBytes s i lim) =
  case parseComplexI s lim i of
  | NONE => NONE
  | SOME (cx, j) => SOME (cx, secBytes s j lim)
Proof
  rw[parseComplex_def, parseComplexI_def, rdLE_corr]
  >> Cases_on ‘rdLEI s lim 4 i’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s lim 4 x1’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdRatsN_corr]
  >> Cases_on ‘rdRatsNI s lim (x0 * x0') x1'’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s lim 4 x1''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdBitsetsN_corr]
  >> Cases_on ‘rdBitsetsNI s lim x0 x0''' x1'''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdLE_corr]
  >> Cases_on ‘rdLEI s lim 4 x1''''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> simp[rdCellsN_corr]
  >> Cases_on ‘rdCellsNI s lim x0 x0''''' x1'''''’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
QED

Theorem parseComplexesNI_bounds:
  ∀k i cxs j.
    i ≤ lim ∧ i ≤ strlen s ∧ parseComplexesNI s lim k i = SOME (cxs, j) ⇒
    i ≤ j ∧ j ≤ lim ∧ j ≤ strlen s
Proof
  Induct >> rw[parseComplexesNI_def, AllCaseEqs()] >> simp[]
  >> imp_res_tac parseComplexI_bounds >> res_tac >> DECIDE_TAC
QED

Theorem parseComplexesN_corr:
  ∀k i.
    parseComplexesN k (secBytes s i lim) =
    case parseComplexesNI s lim k i of
    | NONE => NONE
    | SOME (cxs, j) => SOME (cxs, secBytes s j lim)
Proof
  Induct >> rw[parseComplexesN_def, parseComplexesNI_def, parseComplex_corr]
  >> Cases_on ‘parseComplexI s lim i’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> Cases_on ‘parseComplexesNI s lim k x1’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
QED

Theorem parseDiagram_corr:
  base + seclen ≤ strlen s ⇒
  parseDiagram (TAKE seclen (DROP base (MAP ORD (explode s)))) hnc hna =
  parseDiagramI s base seclen hnc hna
Proof
  strip_tac
  >> ‘TAKE seclen (DROP base (MAP ORD (explode s))) =
      secBytes s base (base + seclen)’
     by simp[GSYM MAP_DROP, GSYM MAP_TAKE, secBytes_slice0]
  >> rw[parseDiagram_def, parseDiagramI_def]
  >> simp[rdLE_corr]
  >> namedCases_on ‘rdLEI s (base + seclen) 4 base’ ["", "p1"] >> simp[]
  >> PairCases_on ‘p1’ >> simp[]
  >> rw[]
  >> simp[parseComplexesN_corr]
  >> namedCases_on ‘parseComplexesNI s (base + seclen) hnc p11’ ["", "p2"] >> simp[]
  >> PairCases_on ‘p2’ >> simp[]
  >> simp[rdLE_corr]
  >> namedCases_on ‘rdLEI s (base + seclen) 4 p21’ ["", "p3"] >> simp[]
  >> PairCases_on ‘p3’ >> simp[]
  >> rw[]
QED

Datatype:
  pobjI = PTermI term
        | PSimplexI simplex
        | PExtSetI extensionset
        | PFormulaI fwire formula bool
        | PJudgI fwire fwire formula formula
End

Definition pobjAbs_def:
  pobjAbs (PTermI t) = PTerm t ∧
  pobjAbs (PSimplexI sx) = PSimplex sx ∧
  pobjAbs (PExtSetI es) = PExtSet es ∧
  pobjAbs (PFormulaI fw fx nos) = PFormula fw ∧
  pobjAbs (PJudgI pw qw px qx) = PJudg pw qw
End

Definition memoOK_def:
  memoOK (PFormulaI fw fx nos) =
    (fx = expandSph FTt fw ∧ nos = fwNoSph fw) ∧
  memoOK (PJudgI pw qw px qx) =
    (px = expandSph FTt pw ∧ qx = expandSph FTt qw) ∧
  memoOK (ob : pobjI) = T
End

Definition ptblRel_def:
  ptblRel (tbl : (num # poolobj) list) (t : pobjI spt) ⇔
    (∀k. ALOOKUP tbl k = OPTION_MAP pobjAbs (sptree$lookup k t)) ∧
    (∀k v. sptree$lookup k t = SOME v ⇒ memoOK v)
End

Definition lookTermI_def:
  lookTermI (t : pobjI spt) (r:num) =
    case sptree$lookup r t of SOME (PTermI tm) => SOME tm | _ => NONE
End

Definition lookSimplexI_def:
  lookSimplexI (t : pobjI spt) (r:num) =
    case sptree$lookup r t of SOME (PSimplexI sx) => SOME sx | _ => NONE
End

Definition lookExtSetI_def:
  lookExtSetI (t : pobjI spt) (r:num) =
    case sptree$lookup r t of SOME (PExtSetI e) => SOME e | _ => NONE
End

Definition lookFormulaI_def:
  lookFormulaI (t : pobjI spt) (r:num) =
    case sptree$lookup r t of
    | SOME (PFormulaI fw fx nos) => SOME (fw, fx, nos)
    | _ => NONE
End

Definition lookJudgI_def:
  lookJudgI (t : pobjI spt) (r:num) =
    case sptree$lookup r t of
    | SOME (PJudgI pw qw px qx) => SOME (pw, qw, px, qx)
    | _ => NONE
End

Theorem lookTermI_corr:
  ptblRel tbl t ⇒ lookTerm tbl r = lookTermI t r
Proof
  rw[ptblRel_def, lookTerm_def, lookTermI_def]
  >> Cases_on ‘sptree$lookup r t’ >> simp[]
  >> Cases_on ‘x’ >> simp[pobjAbs_def]
QED

Theorem lookSimplexI_corr:
  ptblRel tbl t ⇒ lookSimplex tbl r = lookSimplexI t r
Proof
  rw[ptblRel_def, lookSimplex_def, lookSimplexI_def]
  >> Cases_on ‘sptree$lookup r t’ >> simp[]
  >> Cases_on ‘x’ >> simp[pobjAbs_def]
QED

Theorem lookExtSetI_corr:
  ptblRel tbl t ⇒ lookExtSet tbl r = lookExtSetI t r
Proof
  rw[ptblRel_def, lookExtSet_def, lookExtSetI_def]
  >> Cases_on ‘sptree$lookup r t’ >> simp[]
  >> Cases_on ‘x’ >> simp[pobjAbs_def]
QED

Theorem lookFormulaI_corr:
  ptblRel tbl t ⇒
  lookFormula tbl r =
  case lookFormulaI t r of NONE => NONE | SOME (fw, fx, nos) => SOME fw
Proof
  rw[ptblRel_def, lookFormula_def, lookFormulaI_def]
  >> Cases_on ‘sptree$lookup r t’ >> simp[]
  >> Cases_on ‘x’ >> simp[pobjAbs_def]
QED

Theorem lookFormulaI_memo:
  ptblRel tbl t ∧ lookFormulaI t r = SOME (fw, fx, nos) ⇒
  fx = expandSph FTt fw ∧ nos = fwNoSph fw
Proof
  rw[ptblRel_def, lookFormulaI_def, AllCaseEqs()]
  >> res_tac >> gvs[memoOK_def]
QED

Theorem lookJudgI_corr:
  ptblRel tbl t ⇒
  lookJudg tbl r =
  case lookJudgI t r of NONE => NONE | SOME (pw, qw, px, qx) => SOME (pw, qw)
Proof
  rw[ptblRel_def, lookJudg_def, lookJudgI_def]
  >> Cases_on ‘sptree$lookup r t’ >> simp[]
  >> Cases_on ‘x’ >> simp[pobjAbs_def]
QED

Theorem lookJudgI_memo:
  ptblRel tbl t ∧ lookJudgI t r = SOME (pw, qw, px, qx) ⇒
  px = expandSph FTt pw ∧ qx = expandSph FTt qw
Proof
  rw[ptblRel_def, lookJudgI_def, AllCaseEqs()]
  >> res_tac >> gvs[memoOK_def]
QED

Theorem ptblRel_insert:
  ptblRel tbl t ∧ memoOK ob ⇒
  ptblRel ((pos, pobjAbs ob)::tbl) (sptree$insert pos ob t)
Proof
  rw[ptblRel_def, sptreeTheory.lookup_insert]
  >> rw[] >> gvs[AllCaseEqs()]
  >> res_tac
QED

Definition parsePoolRecI_def:
  parsePoolRecI (cxs:simpc list) (t : pobjI spt)
                (s:mlstring) (lim:num) (i:num) =
    case rdU8I s lim i of NONE => NONE | SOME (tag, r0) =>
    if tag = (1:num) then
      (case rdLEI s lim 4 r0 of NONE => NONE
       | SOME (w, r1) => SOME (PTermI (TmVar w), r1))
    else if tag = 2 then
      (case rdRatI s lim r0 of NONE => NONE
       | SOME (q, r1) => SOME (PTermI (TmConst q), r1))
    else if tag = 3 ∨ tag = 4 ∨ tag = 5 then
      (case rdLEI s lim 4 r0 of NONE => NONE | SOME (l, r1) =>
       case rdLEI s lim 4 r1 of NONE => NONE | SOME (rr, r2) =>
       case lookTermI t l of NONE => NONE | SOME tl =>
       case lookTermI t rr of NONE => NONE | SOME tr =>
         SOME (PTermI (if tag = 3 then TmAdd tl tr
                       else if tag = 4 then TmMul tl tr
                       else TmSub tl tr), r2))
    else if tag = 6 then
      (case rdLEI s lim 4 r0 of NONE => NONE | SOME (tm, r1) =>
       case lookTermI t tm of NONE => NONE | SOME tt =>
         SOME (PTermI (TmNeg tt), r1))
    else if tag = 7 then
      (case rdLEI s lim 4 r0 of NONE => NONE | SOME (tm, r1) =>
       case rdLEI s lim 4 r1 of NONE => NONE | SOME (ix, r2) =>
       case lookTermI t tm of NONE => NONE | SOME tt =>
         SOME (PTermI (TmIdx tt ix), r2))
    else if tag = 16 then
      (case rdLEI s lim 4 r0 of NONE => NONE | SOME (cxi, r1) =>
       case oEL cxi cxs of NONE => NONE | SOME cx =>
       case rdBitsetI s lim cx.nVertices r1 of NONE => NONE | SOME (bits, r2) =>
         SOME (PSimplexI <| complex := cx ; vmask := bits |>, r2))
    else if tag = 17 then
      (case rdLEI s lim 4 r0 of NONE => NONE | SOME (so, r1) =>
       case lookSimplexI t so of NONE => NONE | SOME sx =>
       case rdBitsetI s lim sx.complex.nVertices r1 of NONE => NONE
       | SOME (bits, r2) =>
         SOME (PExtSetI <| simplex := sx ; emask := bits |>, r2))
    else if tag = 32 then
      (case rdU8I s lim r0 of NONE => NONE | SOME (bb, r1) =>
       case bowtieOf bb of NONE => NONE | SOME b =>
       case rdLEI s lim 4 r1 of NONE => NONE | SOME (l, r2) =>
       case rdLEI s lim 4 r2 of NONE => NONE | SOME (rr, r3) =>
       case lookTermI t l of NONE => NONE | SOME tl =>
       case lookTermI t rr of NONE => NONE | SOME tr =>
         SOME (PFormulaI (FwAtom b tl tr) (FAtom b tl tr) T, r3))
    else if tag = 33 then
      (case rdLEI s lim 4 r0 of NONE => NONE | SOME (tm, r1) =>
       case rdLEI s lim 4 r1 of NONE => NONE | SOME (so, r2) =>
       case rdLEI s lim 4 r2 of NONE => NONE | SOME (eo, r3) =>
       case lookTermI t tm of NONE => NONE | SOME tt =>
       case lookSimplexI t so of NONE => NONE | SOME sx =>
       case lookExtSetI t eo of NONE => NONE | SOME es =>
         SOME (PFormulaI (FwInRegion tt sx es) (FInRegion tt sx es) T, r3))
    else if tag = 34 ∨ tag = 35 then
      (case rdLEI s lim 4 r0 of NONE => NONE | SOME (l, r1) =>
       case rdLEI s lim 4 r1 of NONE => NONE | SOME (rr, r2) =>
       case lookFormulaI t l of NONE => NONE | SOME (flw, flx, fln) =>
       case lookFormulaI t rr of NONE => NONE | SOME (frw, frx, frn) =>
         SOME (if tag = 34 then
                 PFormulaI (FwAnd flw frw) (FAnd flx frx) (fln ∧ frn)
               else
                 PFormulaI (FwOr flw frw) (FOr flx frx) (fln ∧ frn), r2))
    else if tag = 36 then SOME (PFormulaI FwTt FTt T, r0)
    else if tag = 37 then SOME (PFormulaI FwFf FFf T, r0)
    else if tag = 38 then SOME (PFormulaI FwSpH FTt F, r0)
    else if tag = 48 then
      (case rdLEI s lim 4 r0 of NONE => NONE | SOME (pre, r1) =>
       case rdLEI s lim 4 r1 of NONE => NONE | SOME (post, r2) =>
       case lookFormulaI t pre of NONE => NONE | SOME (prw, prx, prn) =>
       case lookFormulaI t post of NONE => NONE | SOME (posw, posx, posn) =>
       if posn then SOME (PJudgI prw posw prx posx, r2) else NONE)
    else NONE
End

Theorem parsePoolRecI_memo:
  ptblRel tbl t ∧ parsePoolRecI cxs t s lim i = SOME (ob, j) ⇒ memoOK ob
Proof
  rw[parsePoolRecI_def, AllCaseEqs()] >> gvs[memoOK_def]
  >> imp_res_tac lookFormulaI_memo
  >> gvs[expandSph_def, fwNoSph_def]
QED

Theorem parsePoolRecI_corr:
  ptblRel tbl t ⇒
  parsePoolRec cxs tbl (secBytes s i lim) =
  case parsePoolRecI cxs t s lim i of
  | NONE => NONE
  | SOME (ob, j) => SOME (pobjAbs ob, secBytes s j lim)
Proof
  strip_tac
  >> ‘∀r. lookTerm tbl r = lookTermI t r’ by simp[lookTermI_corr]
  >> ‘∀r. lookSimplex tbl r = lookSimplexI t r’ by simp[lookSimplexI_corr]
  >> ‘∀r. lookExtSet tbl r = lookExtSetI t r’ by simp[lookExtSetI_corr]
  >> ‘∀r. lookFormula tbl r =
          case lookFormulaI t r of
          | NONE => NONE
          | SOME (fw, fx, nos) => SOME fw’
     by (gen_tac >> drule lookFormulaI_corr >> simp[])
  >> rw[parsePoolRec_def, parsePoolRecI_def]
  >> simp[rdU8_corr]
  >> namedCases_on ‘rdU8I s lim i’ ["", "p0"] >> simp[]
  >> PairCases_on ‘p0’ >> simp[]
  >> Cases_on ‘p00 = 1’ >> simp[]
  >- (simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 p01’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> rw[pobjAbs_def])
  >> Cases_on ‘p00 = 2’ >> simp[]
  >- (simp[rdRat_corr]
      >> namedCases_on ‘rdRatI s lim p01’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> rw[pobjAbs_def])
  >> Cases_on ‘p00 = 3 ∨ p00 = 4 ∨ p00 = 5’ >> simp[]
  >- (simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 p01’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘lookTermI t q10’ ["", "tl"] >> simp[]
      >> namedCases_on ‘lookTermI t q20’ ["", "tr"] >> simp[]
      >> rw[pobjAbs_def])
  >> Cases_on ‘p00 = 6’ >> simp[]
  >- (simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 p01’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘lookTermI t q10’ ["", "tt"] >> simp[]
      >> rw[pobjAbs_def])
  >> Cases_on ‘p00 = 7’ >> simp[]
  >- (simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 p01’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘lookTermI t q10’ ["", "tt"] >> simp[]
      >> rw[pobjAbs_def])
  >> Cases_on ‘p00 = 16’ >> simp[]
  >- (simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 p01’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘oEL q10 cxs’ ["", "cx"] >> simp[]
      >> simp[rdBitset_corr]
      >> namedCases_on ‘rdBitsetI s lim cx.nVertices q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> rw[pobjAbs_def])
  >> Cases_on ‘p00 = 17’ >> simp[]
  >- (simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 p01’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘lookSimplexI t q10’ ["", "sx"] >> simp[]
      >> simp[rdBitset_corr]
      >> namedCases_on ‘rdBitsetI s lim sx.complex.nVertices q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> rw[pobjAbs_def])
  >> Cases_on ‘p00 = 32’ >> simp[]
  >- (simp[rdU8_corr]
      >> namedCases_on ‘rdU8I s lim p01’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘bowtieOf q10’ ["", "bw"] >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘lookTermI t q20’ ["", "tl"] >> simp[]
      >> namedCases_on ‘lookTermI t q30’ ["", "tr"] >> simp[]
      >> rw[pobjAbs_def])
  >> Cases_on ‘p00 = 33’ >> simp[]
  >- (simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 p01’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘lookTermI t q10’ ["", "tt"] >> simp[]
      >> namedCases_on ‘lookSimplexI t q20’ ["", "sx"] >> simp[]
      >> namedCases_on ‘lookExtSetI t q30’ ["", "es"] >> simp[]
      >> rw[pobjAbs_def])
  >> Cases_on ‘p00 = 34 ∨ p00 = 35’ >> simp[]
  >- (simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 p01’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘lookFormulaI t q10’ ["", "f1"] >> simp[]
      >> PairCases_on ‘f1’ >> simp[]
      >> namedCases_on ‘lookFormulaI t q20’ ["", "f2"] >> simp[]
      >> PairCases_on ‘f2’ >> simp[]
      >> rw[pobjAbs_def])
  >> Cases_on ‘p00 = 36’ >> simp[]
  >- (rw[pobjAbs_def])
  >> Cases_on ‘p00 = 37’ >> simp[]
  >- (rw[pobjAbs_def])
  >> Cases_on ‘p00 = 38’ >> simp[]
  >- (rw[pobjAbs_def])
  >> Cases_on ‘p00 = 48’ >> simp[]
  >- (simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 p01’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘lookFormulaI t q10’ ["", "f1"] >> simp[]
      >> PairCases_on ‘f1’ >> simp[]
      >> qabbrev_tac ‘lf = lookFormulaI t q20’
      >> Cases_on ‘lf’ >> simp[]
      >> PairCases_on ‘x’ >> simp[]
      >> qpat_x_assum ‘Abbrev _’
           (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])
      >> drule_all lookFormulaI_memo
      >> strip_tac
      >> rw[] >> simp[pobjAbs_def])
  >> simp[]
QED

Theorem parsePoolRecI_progress:
  i ≤ lim ∧ i ≤ strlen s ∧ parsePoolRecI cxs t s lim i = SOME (ob, j) ⇒
  i < j ∧ j ≤ lim ∧ j ≤ strlen s
Proof
  rw[parsePoolRecI_def, AllCaseEqs()]
  >> imp_res_tac rdU8I_bounds
  >> imp_res_tac rdLEI_bounds
  >> imp_res_tac rdRatI_bounds
  >> imp_res_tac rdBitsetI_bounds
  >> DECIDE_TAC
QED

Definition poolPassI_def:
  poolPassI (0:num) (cxs:simpc list) (s:mlstring) (lim:num)
            (pos:num) (i:num) (t : pobjI spt) =
    (if i = lim ∨ strlen s ≤ i then SOME t else NONE) ∧
  poolPassI (SUC f) cxs s lim pos i t =
    if i = lim ∨ strlen s ≤ i then SOME t else
    case parsePoolRecI cxs t s lim i of NONE => NONE
    | SOME (ob, i') =>
        if i' < i then NONE else
        poolPassI f cxs s lim (pos + (i' − i)) i'
                  (sptree$insert pos ob t)
End

Theorem NULL_secBytes:
  NULL (secBytes s i lim) ⇔ lim ≤ i ∨ strlen s ≤ i
Proof
  Cases_on ‘lim ≤ i ∨ strlen s ≤ i’
  >- gvs[secBytes_nil]
  >> gvs[arithmeticTheory.NOT_LESS_EQUAL]
  >> ‘secBytes s i lim = byteAt s i :: secBytes s (i + 1) lim’
       by simp[secBytes_cons]
  >> gvs[]
QED

Theorem poolPassI_rel:
  ∀f pos i tbl t.
    ptblRel tbl t ∧ i ≤ lim ∧ i ≤ strlen s ⇒
    (case poolPass f cxs pos (secBytes s i lim) tbl of
     | NONE => poolPassI f cxs s lim pos i t = NONE
     | SOME tbl' =>
         ∃t'. poolPassI f cxs s lim pos i t = SOME t' ∧ ptblRel tbl' t')
Proof
  Induct
  >- (rw[poolPass_def, poolPassI_def, NULL_secBytes] >> gvs[])
  >> rw[poolPass_def, poolPassI_def, NULL_secBytes]
  >> TRY (gvs[] >> NO_TAC)
  >> ‘i ≤ lim ∧ i ≤ strlen s’ by DECIDE_TAC
  >> ‘parsePoolRec cxs tbl (secBytes s i lim) =
      case parsePoolRecI cxs t s lim i of
      | NONE => NONE
      | SOME (ob, j) => SOME (pobjAbs ob, secBytes s j lim)’
     by simp[parsePoolRecI_corr]
  >> pop_assum (fn th => PURE_REWRITE_TAC [th])
  >> qabbrev_tac ‘r = parsePoolRecI cxs t s lim i’
  >> Cases_on ‘r’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> qpat_x_assum ‘Abbrev _’
       (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])
  >> imp_res_tac parsePoolRecI_progress
  >> imp_res_tac parsePoolRecI_memo
  >> ‘LENGTH (secBytes s x1 lim) ≤ LENGTH (secBytes s i lim) ∧
      LENGTH (secBytes s i lim) − LENGTH (secBytes s x1 lim) = x1 − i’
     by (rw[LENGTH_secBytes, MIN_DEF] >> DECIDE_TAC)
  >> ‘¬(LENGTH (secBytes s i lim) < LENGTH (secBytes s x1 lim))’
     by DECIDE_TAC
  >> ‘¬(x1 < i)’ by DECIDE_TAC
  >> ‘pos + LENGTH (secBytes s i lim) − LENGTH (secBytes s x1 lim) =
      x1 + pos − i’ by DECIDE_TAC
  >> simp[]
  >> first_x_assum irule
  >> simp[ptblRel_insert]
QED

Definition ntblRel_def:
  ntblRel (ws:tensortype list)
          (tbl : (num # (certpf # fwire)) list)
          (t : (bool # sequent # fwire) spt) ⇔
    ∀k. (case ALOOKUP tbl k of
         | NONE => sptree$lookup k t = NONE
         | SOME (pf, prew) =>
             sptree$lookup k t =
             SOME (checkPf1 ws (INL pf), certConcl pf, prew))
End

Definition lookNodeI_def:
  lookNodeI (t : (bool # sequent # fwire) spt) (off:num) = sptree$lookup off t
End

Theorem lookNodePf_NONE:
  ntblRel ws tbl t ⇒
  (lookNodePf tbl off = NONE ⇔ lookNodeI t off = NONE)
Proof
  rw[ntblRel_def, lookNodePf_def, lookNodeI_def]
  >> first_x_assum (qspec_then ‘off’ mp_tac)
  >> Cases_on ‘ALOOKUP tbl off’ >> simp[]
  >> Cases_on ‘x’ >> simp[]
QED

Theorem lookNodeI_char:
  ntblRel ws tbl t ∧ lookNodeI t off = SOME (b, sq, pw) ⇒
  ∃pf. lookNodePf tbl off = SOME pf ∧
       b = checkPf1 ws (INL pf) ∧ sq = certConcl pf ∧
       ALOOKUP tbl off = SOME (pf, pw)
Proof
  rw[ntblRel_def, lookNodePf_def, lookNodeI_def]
  >> first_x_assum (qspec_then ‘off’ mp_tac)
  >> Cases_on ‘ALOOKUP tbl off’ >> simp[]
  >> Cases_on ‘x’ >> rw[] >> gvs[]
QED

Definition lookNodesI_def:
  lookNodesI (t : (bool # sequent # fwire) spt) ([]:num list) =
    SOME ([] : (bool # sequent # fwire) list) ∧
  lookNodesI t (off::offs) =
    case lookNodeI t off of NONE => NONE
    | SOME x =>
      case lookNodesI t offs of NONE => NONE
      | SOME xs => SOME (x::xs)
End

Theorem checkPf1_INR_EVERY:
  ∀ps. checkPf1 ws (INR ps) = EVERY (λp. checkPf1 ws (INL p)) ps
Proof
  Induct >> simp[Once checkPf1_def]
  >> simp[Once checkPf1_def]
QED

Theorem lookNodesI_corr:
  ∀offs. ntblRel ws tbl t ⇒
    (case optSeq (MAP (lookNodePf tbl) offs) of
     | NONE => lookNodesI t offs = NONE
     | SOME pfs =>
         ∃xs. lookNodesI t offs = SOME xs ∧
              MAP (λ(b,sq,pw). b) xs = MAP (λp. checkPf1 ws (INL p)) pfs ∧
              MAP (λ(b,sq,pw). sq) xs = MAP certConcl pfs)
Proof
  Induct >> rw[lookNodesI_def, optSeq_def]
  >> first_assum (mp_tac o SIMP_RULE (srw_ss()) [ntblRel_def])
  >> disch_then (qspec_then ‘h’ mp_tac)
  >> Cases_on ‘ALOOKUP tbl h’ >> simp[]
  >- (rw[] >> simp[lookNodePf_def, optSeq_def, lookNodeI_def])
  >> PairCases_on ‘x’ >> rw[]
  >> simp[lookNodePf_def, optSeq_def, lookNodeI_def]
  >> first_x_assum drule >> rw[]
  >> Cases_on ‘optSeq (MAP (lookNodePf tbl) offs)’ >> gvs[]
QED

Definition parseNodeI_def:
  parseNodeI (ws:tensortype list) (pt : pobjI spt)
             (t : (bool # sequent # fwire) spt)
             (s:mlstring) (lim:num) (i:num) =
    case rdU8I s lim i of NONE => NONE | SOME (tag, r0) =>
    case rdU8I s lim r0 of NONE => NONE | SOME (var, r1) =>
    case rdLEI s lim 2 r1 of NONE => NONE | SOME (resv, r2) =>
    if resv ≠ (0:num) then NONE else
    case rdLEI s lim 4 r2 of NONE => NONE | SOME (cj, r3) =>
    case lookJudgI pt cj of NONE => NONE | SOME (prew, postw, prex, postx) =>
    let sq = <| pre := prex ; post := postx |> in
    if tag = (0:num) then
      (if var ≠ (0:num) then NONE else
         SOME ((sq.pre = sq.post), sq, prew, r3))
    else if tag = 1 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLEI s lim 4 r4 of NONE => NONE | SOME (ex, r5) =>
       case lookNodeI t pr of NONE => NONE | SOME (pb, ps, ppw) =>
       case lookFormulaI pt ex of NONE => NONE | SOME (exw, exx, exn) =>
         SOME ((pb ∧ sq.pre = FAnd ps.pre exx ∧ sq.post = ps.post),
               sq, prew, r5))
    else if tag = 2 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 4 r3 of NONE => NONE | SOME (cutf, r4) =>
       case rdLEI s lim 8 r4 of NONE => NONE | SOME (lo, r5) =>
       case rdLEI s lim 8 r5 of NONE => NONE | SOME (ro, r6) =>
       case lookFormulaI pt cutf of NONE => NONE | SOME (cfw, cfx, cfn) =>
       case lookNodeI t lo of NONE => NONE | SOME (lb, ls, lpw) =>
       case lookNodeI t ro of NONE => NONE | SOME (rb, rs, rpw) =>
         SOME ((lb ∧ rb ∧ sq.pre = ls.pre ∧ sq.post = rs.post ∧
                ls.post = cfx ∧ rs.pre = FAnd ls.pre cfx),
               sq, prew, r6))
    else if tag = 3 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (lo, r4) =>
       case rdLEI s lim 8 r4 of NONE => NONE | SOME (ro, r5) =>
       case lookNodeI t lo of NONE => NONE | SOME (lb, ls, lpw) =>
       case lookNodeI t ro of NONE => NONE | SOME (rb, rs, rpw) =>
         SOME ((lb ∧ rb ∧ ls.pre = rs.pre ∧ sq.pre = ls.pre ∧
                sq.post = FAnd ls.post rs.post),
               sq, prew, r5))
    else if tag = 4 ∨ tag = 5 then
      (if ¬(var = 0 ∨ var = 1) then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLEI s lim 4 r4 of NONE => NONE | SOME (ot, r5) =>
       case lookNodeI t pr of NONE => NONE | SOME (pb, ps, ppw) =>
       case lookFormulaI pt ot of NONE => NONE | SOME (otw, otx, otn) =>
         SOME ((if tag = 4 then
                  (if var = 0 then
                     pb ∧ sq.pre = ps.pre ∧ ps.post = FAnd sq.post otx
                   else
                     pb ∧ sq.pre = ps.pre ∧ ps.post = FAnd otx sq.post)
                else
                  (if var = 0 then
                     pb ∧ sq.pre = ps.pre ∧ sq.post = FOr ps.post otx
                   else
                     pb ∧ sq.pre = ps.pre ∧ sq.post = FOr otx ps.post)),
               sq, prew, r5))
    else if tag = 6 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (lo, r4) =>
       case rdLEI s lim 8 r4 of NONE => NONE | SOME (ro, r5) =>
       case rdLEI s lim 4 r5 of NONE => NONE | SOME (plen, r6) =>
       case takeNI s lim plen r6 of NONE => NONE | SOME (stps, r7) =>
       if ¬ EVERY (λst. st ≤ (1:num)) stps then NONE else
       case lookNodeI t lo of NONE => NONE | SOME (lb, ls, lpw) =>
       case lookNodeI t ro of NONE => NONE | SOME (rb, rs, rpw) =>
         SOME ((lb ∧ rb ∧
                (case conjGet sq.pre (stepsToPath stps) of
                 | SOME (FOr d1 d2) =>
                     (conjReplace sq.pre (stepsToPath stps) d1 = SOME ls.pre ∧
                      conjReplace sq.pre (stepsToPath stps) d2 = SOME rs.pre ∧
                      ls.post = sq.post ∧ rs.post = sq.post)
                 | _ => F)),
               sq, prew, r7))
    else if tag = 7 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (eo, r4) =>
       case rdLEI s lim 8 r4 of NONE => NONE | SOME (bo, r5) =>
       case rdLEI s lim 4 r5 of NONE => NONE | SOME (w, r6) =>
       case rdLEI s lim 4 r6 of NONE => NONE | SOME (tt0, r7) =>
       case rdLEI s lim 4 r7 of NONE => NONE | SOME (tu, r8) =>
       case rdLEI s lim 4 r8 of NONE => NONE | SOME (bf, r9) =>
       case lookNodeI t eo of NONE => NONE | SOME (eb, es, epw) =>
       case lookNodeI t bo of NONE => NONE | SOME (bb, bs, bpw) =>
       case lookTermI pt tt0 of NONE => NONE | SOME tT =>
       case lookTermI pt tu of NONE => NONE | SOME tU =>
       case lookFormulaI pt bf of NONE => NONE | SOME (bfw, bfx, bfn) =>
         SOME ((eb ∧ bb ∧
                sq.pre = es.pre ∧ es.pre = bs.pre ∧
                es.post = FAtom BowEq tT tU ∧
                termBshape ws tT = termBshape ws tU ∧
                IS_SOME (termBshape ws tT) ∧
                bs.post = formulaSubst w tT bfx ∧
                sq.post = formulaSubst w tU bfx),
               sq, prew, r9))
    else if tag = 8 ∨ tag = 9 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLEI s lim 4 r4 of NONE => NONE | SOME (tm, r5) =>
       case rdLEI s lim 4 r5 of NONE => NONE | SOME (so, r6) =>
       case rdLEI s lim 4 r6 of NONE => NONE | SOME (eo, r7) =>
       case lookNodeI t pr of NONE => NONE | SOME (pb, ps, ppw) =>
       case lookTermI pt tm of NONE => NONE | SOME tt =>
       case lookSimplexI pt so of NONE => NONE | SOME sx =>
       case lookExtSetI pt eo of NONE => NONE | SOME es =>
         SOME ((if tag = 8 then
                  pb ∧ sq.pre = ps.pre ∧
                  termBshape ws tt = SOME [sx.complex.ambDim] ∧
                  barycentricHalfspaceBuild tt sx es = SOME ps.post ∧
                  sq.post = FInRegion tt sx es
                else
                  pb ∧ sq.pre = ps.pre ∧
                  ps.post = FInRegion tt sx es ∧
                  barycentricHalfspaceBuild tt sx es = SOME sq.post),
               sq, prew, r7))
    else if tag = 10 then
      (if ¬(var = 0 ∨ var = 1) then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLEI s lim 4 r4 of NONE => NONE | SOME (l, r5) =>
       case rdLEI s lim 4 r5 of NONE => NONE | SOME (rr, r6) =>
       case rdU8I s lim r6 of NONE => NONE | SOME (bb, r7) =>
       if (4:num) < bb then NONE else
       case takeNI s lim 3 r7 of NONE => NONE | SOME (pad, r8) =>
       if ¬ EVERY (λb. b = (0:num)) pad then NONE else
       case bowtieOf bb of NONE => NONE | SOME b =>
       case lookNodeI t pr of NONE => NONE | SOME (pb, ps, ppw) =>
       case lookTermI pt l of NONE => NONE | SOME tl =>
       case lookTermI pt rr of NONE => NONE | SOME tr =>
         SOME ((if var = 0 then
                  pb ∧ b ≠ BowNe ∧ sq.pre = ps.pre ∧
                  ps.post = FAtom b (TmSub tl tr) (TmConst 0) ∧
                  sq.post = FAtom b tl tr
                else
                  pb ∧ b ≠ BowNe ∧ sq.pre = ps.pre ∧
                  ps.post = FAtom b tl tr ∧
                  sq.post = FAtom b (TmSub tl tr) (TmConst 0)),
               sq, prew, r8))
    else if tag = 11 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLEI s lim 4 r4 of NONE => NONE | SOME (tx, r5) =>
       case rdLEI s lim 4 r5 of NONE => NONE | SOME (so, r6) =>
       case rdLEI s lim 4 r6 of NONE => NONE | SOME (eo, r7) =>
       case rdLEI s lim 4 r7 of NONE => NONE | SOME (deg, r8) =>
       case rdLEI s lim 4 r8 of NONE => NONE | SOME (po, r9) =>
       case rdLEI s lim 4 r9 of NONE => NONE | SOME (pd, r10) =>
       case lookNodeI t pr of NONE => NONE | SOME (pb, ps, ppw) =>
       case lookTermI pt tx of NONE => NONE | SOME tX =>
       case lookSimplexI pt so of NONE => NONE | SOME sx =>
       case lookExtSetI pt eo of NONE => NONE | SOME es =>
       case lookTermI pt po of NONE => NONE | SOME poly =>
       case lookFormulaI pt pd of NONE => NONE | SOME (pdw, pdx, pdn) =>
         SOME ((pb ∧ sq.pre = ps.pre ∧
                ps.post = FInRegion tX sx es ∧
                polyTieB tX poly ∧
                (if extIsEmptyB es then isConvexPredicateB pdx
                 else isConicPredicateB pdx) ∧
                bernConeCoeffCheck sx es deg poly pdx ∧
                sq.post = formulaSubst predicateHole poly pdx),
               sq, prew, r10))
    else if tag = 12 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 4 r3 of NONE => NONE | SOME (l, r4) =>
       case rdLEI s lim 4 r4 of NONE => NONE | SOME (rr, r5) =>
       case lookTermI pt l of NONE => NONE | SOME tl =>
       case lookTermI pt rr of NONE => NONE | SOME tr =>
         SOME ((polynomialCanonicalEqB tl tr ∧
                termBshape ws tl = termBshape ws tr ∧
                IS_SOME (termBshape ws tl) ∧
                finWiresB ws tl ∧ finWiresB ws tr ∧
                sq.post = FAtom BowEq tl tr),
               sq, prew, r5))
    else if tag = 14 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 4 r3 of NONE => NONE | SOME (cc, r4) =>
       case rdLEI s lim 4 r4 of NONE => NONE | SOME (co, r5) =>
       case rdLEI s lim 8 r5 of NONE => NONE | SOME (dbl, r6) =>
       case lookTermI pt cc of NONE => NONE | SOME ccT =>
       case lookTermI pt co of NONE => NONE | SOME coT =>
         SOME ((IS_SOME (termBshape ws coT) ∧
                finWiresB ws coT ∧
                wiresPosB ws (formulaFreeWires sq.pre ++ termFreeWires coT) ∧
                farkasCheck ccT sq.pre coT ∧
                sq.post = FAtom BowLe coT (TmConst 0)),
               sq, prew, r6))
    else if tag = 23 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 4 r3 of NONE => NONE | SOME (tm, r4) =>
       case lookTermI pt tm of NONE => NONE | SOME tt =>
         SOME ((IS_SOME (termBshape ws tt) ∧ finWiresB ws tt ∧
                sq.post = FAtom BowEq tt tt),
               sq, prew, r4))
    else if tag = 24 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (pr, r4) =>
       case rdLEI s lim 4 r4 of NONE => NONE | SOME (tt0, r5) =>
       case rdLEI s lim 4 r5 of NONE => NONE | SOME (tu, r6) =>
       case lookNodeI t pr of NONE => NONE | SOME (pb, ps, ppw) =>
       case lookTermI pt tt0 of NONE => NONE | SOME tT =>
       case lookTermI pt tu of NONE => NONE | SOME tU =>
         SOME ((pb ∧ sq.pre = ps.pre ∧
                ps.post = FAtom BowEq tT tU ∧
                sq.post = FAtom BowEq tU tT),
               sq, prew, r6))
    else if tag = 25 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 8 r3 of NONE => NONE | SOME (so, r4) =>
       case rdLEI s lim 8 r4 of NONE => NONE | SOME (co, r5) =>
       case rdLEI s lim 4 r5 of NONE => NONE | SOME (ct, r6) =>
       case rdLEI s lim 4 r6 of NONE => NONE | SOME (plen, r7) =>
       case takeNI s lim plen r7 of NONE => NONE | SOME (stps, r8) =>
       if ¬ EVERY (λst. st ≤ (1:num)) stps then NONE else
       case rdLEI s lim 4 r8 of NONE => NONE | SOME (ilen, r9) =>
       case rdLEsNI s lim 4 ilen r9 of NONE => NONE | SOME (iface, r10) =>
       case lookNodeI t so of NONE => NONE | SOME (sb, ss, spw) =>
       case lookNodeI t co of NONE => NONE | SOME (cb, cs, cpw) =>
       case lookFormulaI pt ct of NONE => NONE | SOME (ctw, ctx, ctn) =>
         SOME ((sb ∧ cb ∧
                ss.post = ctx ∧
                conjGet cs.pre (stepsToPath stps) = SOME ctx ∧
                conjReplace cs.pre (stepsToPath stps) ss.pre = SOME sq.pre ∧
                sq.post = cs.post ∧
                (case conjReplace cs.pre (stepsToPath stps) FTt of
                 | SOME ctx0 =>
                     (EVERY (λw. MEM w iface) (formulaFreeWires ctx) ∧
                      EVERY (λw. (MEM w (formulaFreeWires ctx0) ∨
                                  MEM w (formulaFreeWires sq.post)) ⇒
                                 MEM w iface)
                            (formulaFreeWires ss.pre))
                 | NONE => F)),
               sq, prew, r10))
    else if tag = 26 then
      (if var ≠ 0 then NONE else
       case rdLEI s lim 4 r3 of NONE => NONE | SOME (ncomp, r4) =>
       case rdLEsNI s lim 8 ncomp r4 of NONE => NONE | SOME (coffs, r5) =>
       case rdLEI s lim 4 r5 of NONE => NONE | SOME (cc, r6) =>
       case rdLEI s lim 4 r6 of NONE => NONE | SOME (co, r7) =>
       case rdLEI s lim 8 r7 of NONE => NONE | SOME (dbl, r8) =>
       case rdLEI s lim 4 r8 of NONE => NONE | SOME (th, r9) =>
       case lookNodesI t coffs of NONE => NONE | SOME comps =>
       case lookTermI pt cc of NONE => NONE | SOME ccT =>
       case lookTermI pt co of NONE => NONE | SOME coT =>
       (let bsum =
          (EVERY (λ(b,csq,cpw). b) comps ∧
           (let cseqs = MAP (λ(b,csq,cpw). csq) comps in
              EVERY (λc. premiseContainsB sq.pre c.pre) cseqs ∧
              IS_SOME (termBshape ws coT) ∧
              finWiresB ws coT ∧
              wiresPosB ws (formulaFreeWires sq.pre ++ termFreeWires coT) ∧
              EVERY (λc. wiresPosB ws (formulaFreeWires c.post)) cseqs ∧
              syzygyCheck ccT cseqs sq.pre coT ∧
              sq.post = FAtom BowLe coT (TmConst 0))) in
        if th = (4294967295:num) then
          SOME (bsum, sq, prew, r9)
        else
          (case lookTermI pt th of
           | SOME (TmConst q) => SOME (bsum, sq, prew, r9)
           | _ => NONE)))
    else NONE
End

Theorem EVERY_fst_triple:
  ∀xs pfs (f:'a -> bool).
    MAP (λ(b:bool,sq:sequent,pw:fwire). b) xs = MAP f pfs ⇒
    (EVERY (λ(b,sq,pw). b) xs ⇔ EVERY f pfs)
Proof
  Induct >> rw[]
  >> Cases_on ‘pfs’ >> gvs[]
  >> first_x_assum (qspecl_then [‘t’, ‘f’] mp_tac) >> simp[]
QED

Theorem rdLEI_boundsE:
  rdLEI s lim k i = SOME (v, j) ⇒ i ≤ lim ∧ i ≤ strlen s ⇒
  i ≤ j ∧ j ≤ lim ∧ j ≤ strlen s
Proof
  metis_tac[rdLEI_bounds]
QED

Theorem takeNI_boundsE:
  takeNI s lim n i = SOME (bs, j) ⇒ i ≤ lim ∧ i ≤ strlen s ⇒
  i ≤ j ∧ j ≤ lim ∧ j ≤ strlen s ∧ LENGTH bs = n
Proof
  metis_tac[takeNI_bounds]
QED

Theorem rdLEsNI_boundsE:
  rdLEsNI s lim w k i = SOME (vs, j) ⇒ i ≤ lim ∧ i ≤ strlen s ⇒
  i ≤ j ∧ j ≤ lim ∧ j ≤ strlen s
Proof
  metis_tac[rdLEsNI_bounds]
QED

Theorem parseNodeI_bounds:
  i ≤ lim ∧ i ≤ strlen s ∧ parseNodeI ws pt t s lim i = SOME (b, sq, prew, j) ⇒
  i < j ∧ j ≤ lim ∧ j ≤ strlen s
Proof

  strip_tac
  >> qpat_x_assum ‘parseNodeI _ _ _ _ _ _ = _’ mp_tac
  >> simp[parseNodeI_def]
  >> namedCases_on ‘rdU8I s lim i’ ["", "q0"] >> simp[]
  >> PairCases_on ‘q0’ >> simp[]
  >> namedCases_on ‘rdU8I s lim q01’ ["", "v0"] >> simp[]
  >> PairCases_on ‘v0’ >> simp[]
  >> namedCases_on ‘rdLEI s lim 2 v01’ ["", "r0"] >> simp[]
  >> PairCases_on ‘r0’ >> simp[]
  >> TRY (IF_CASES_TAC >> simp[])
  >> namedCases_on ‘rdLEI s lim 4 r01’ ["", "cj"] >> simp[]
  >> PairCases_on ‘cj’ >> simp[]
  >> namedCases_on ‘lookJudgI pt cj0’ ["", "lj"] >> simp[]
  >> PairCases_on ‘lj’ >> simp[]
  >> Cases_on ‘q00 = 0’ >> simp[]
  >- (rw[]
      >> rpt (dxrule_all_then strip_assume_tac rdU8I_bounds
              ORELSE dxrule_all_then strip_assume_tac rdLEI_boundsE
              ORELSE dxrule_all_then strip_assume_tac takeNI_boundsE
              ORELSE dxrule_all_then strip_assume_tac rdLEsNI_boundsE)
      >> DECIDE_TAC)
  >> Cases_on ‘q00 = 1’ >> simp[]
  >- (namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘lookNodeI t q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookFormulaI pt q20’ ["", "f1"] >> simp[]
      >> PairCases_on ‘f1’ >> simp[]
      >> strip_tac >> gvs[]
      >> rpt (dxrule_all_then strip_assume_tac rdU8I_bounds
              ORELSE dxrule_all_then strip_assume_tac rdLEI_boundsE
              ORELSE dxrule_all_then strip_assume_tac takeNI_boundsE
              ORELSE dxrule_all_then strip_assume_tac rdLEsNI_boundsE)
      >> DECIDE_TAC)
  >> Cases_on ‘q00 = 2’ >> simp[]
  >- (namedCases_on ‘rdLEI s lim 4 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 8 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 8 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘lookFormulaI pt q10’ ["", "f1"] >> simp[]
      >> PairCases_on ‘f1’ >> simp[]
      >> namedCases_on ‘lookNodeI t q20’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookNodeI t q30’ ["", "e2"] >> simp[]
      >> PairCases_on ‘e2’ >> simp[]
      >> strip_tac >> gvs[]
      >> rpt (dxrule_all_then strip_assume_tac rdU8I_bounds
              ORELSE dxrule_all_then strip_assume_tac rdLEI_boundsE
              ORELSE dxrule_all_then strip_assume_tac takeNI_boundsE
              ORELSE dxrule_all_then strip_assume_tac rdLEsNI_boundsE)
      >> DECIDE_TAC)
  >> Cases_on ‘q00 = 3’ >> simp[]
  >- (namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 8 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘lookNodeI t q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookNodeI t q20’ ["", "e2"] >> simp[]
      >> PairCases_on ‘e2’ >> simp[]
      >> strip_tac >> gvs[]
      >> rpt (dxrule_all_then strip_assume_tac rdU8I_bounds
              ORELSE dxrule_all_then strip_assume_tac rdLEI_boundsE
              ORELSE dxrule_all_then strip_assume_tac takeNI_boundsE
              ORELSE dxrule_all_then strip_assume_tac rdLEsNI_boundsE)
      >> DECIDE_TAC)
  >> Cases_on ‘q00 = 4 ∨ q00 = 5’ >> simp[]
  >- (namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘lookNodeI t q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookFormulaI pt q20’ ["", "f1"] >> simp[]
      >> PairCases_on ‘f1’ >> simp[]
      >> strip_tac >> gvs[]
      >> rpt (dxrule_all_then strip_assume_tac rdU8I_bounds
              ORELSE dxrule_all_then strip_assume_tac rdLEI_boundsE
              ORELSE dxrule_all_then strip_assume_tac takeNI_boundsE
              ORELSE dxrule_all_then strip_assume_tac rdLEsNI_boundsE)
      >> DECIDE_TAC)
  >> Cases_on ‘q00 = 6’ >> simp[]
  >- (namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 8 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘takeNI s lim q30 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> TRY (IF_CASES_TAC >> simp[])
      >> namedCases_on ‘lookNodeI t q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookNodeI t q20’ ["", "e2"] >> simp[]
      >> PairCases_on ‘e2’ >> simp[]
      >> strip_tac >> gvs[]
      >> rpt (dxrule_all_then strip_assume_tac rdU8I_bounds
              ORELSE dxrule_all_then strip_assume_tac rdLEI_boundsE
              ORELSE dxrule_all_then strip_assume_tac takeNI_boundsE
              ORELSE dxrule_all_then strip_assume_tac rdLEsNI_boundsE)
      >> DECIDE_TAC)
  >> Cases_on ‘q00 = 7’ >> simp[]
  >- (namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 8 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q41’ ["", "q5"] >> simp[]
      >> PairCases_on ‘q5’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q51’ ["", "q6"] >> simp[]
      >> PairCases_on ‘q6’ >> simp[]
      >> namedCases_on ‘lookNodeI t q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookNodeI t q20’ ["", "e2"] >> simp[]
      >> PairCases_on ‘e2’ >> simp[]
      >> namedCases_on ‘lookTermI pt q40’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q50’ ["", "tB"] >> simp[]
      >> namedCases_on ‘lookFormulaI pt q60’ ["", "f1"] >> simp[]
      >> PairCases_on ‘f1’ >> simp[]
      >> strip_tac >> gvs[]
      >> rpt (dxrule_all_then strip_assume_tac rdU8I_bounds
              ORELSE dxrule_all_then strip_assume_tac rdLEI_boundsE
              ORELSE dxrule_all_then strip_assume_tac takeNI_boundsE
              ORELSE dxrule_all_then strip_assume_tac rdLEsNI_boundsE)
      >> DECIDE_TAC)
  >> Cases_on ‘q00 = 8 ∨ q00 = 9’ >> simp[]
  >- (namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> namedCases_on ‘lookNodeI t q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookSimplexI pt q30’ ["", "sA"] >> simp[]
      >> namedCases_on ‘lookExtSetI pt q40’ ["", "eA"] >> simp[]
      >> strip_tac >> gvs[]
      >> rpt (dxrule_all_then strip_assume_tac rdU8I_bounds
              ORELSE dxrule_all_then strip_assume_tac rdLEI_boundsE
              ORELSE dxrule_all_then strip_assume_tac takeNI_boundsE
              ORELSE dxrule_all_then strip_assume_tac rdLEsNI_boundsE)
      >> DECIDE_TAC)
  >> Cases_on ‘q00 = 10’ >> simp[]
  >- (namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘rdU8I s lim q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> TRY (IF_CASES_TAC >> simp[])
      >> namedCases_on ‘takeNI s lim 3 q41’ ["", "q5"] >> simp[]
      >> PairCases_on ‘q5’ >> simp[]
      >> TRY (IF_CASES_TAC >> simp[])
      >> namedCases_on ‘bowtieOf q40’ ["", "bw"] >> simp[]
      >> namedCases_on ‘lookNodeI t q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q30’ ["", "tB"] >> simp[]
      >> strip_tac >> gvs[]
      >> rpt (dxrule_all_then strip_assume_tac rdU8I_bounds
              ORELSE dxrule_all_then strip_assume_tac rdLEI_boundsE
              ORELSE dxrule_all_then strip_assume_tac takeNI_boundsE
              ORELSE dxrule_all_then strip_assume_tac rdLEsNI_boundsE)
      >> DECIDE_TAC)
  >> Cases_on ‘q00 = 11’ >> simp[]
  >- (namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q41’ ["", "q5"] >> simp[]
      >> PairCases_on ‘q5’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q51’ ["", "q6"] >> simp[]
      >> PairCases_on ‘q6’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q61’ ["", "q7"] >> simp[]
      >> PairCases_on ‘q7’ >> simp[]
      >> namedCases_on ‘lookNodeI t q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookSimplexI pt q30’ ["", "sA"] >> simp[]
      >> namedCases_on ‘lookExtSetI pt q40’ ["", "eA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q60’ ["", "tB"] >> simp[]
      >> namedCases_on ‘lookFormulaI pt q70’ ["", "f1"] >> simp[]
      >> PairCases_on ‘f1’ >> simp[]
      >> strip_tac >> gvs[]
      >> rpt (dxrule_all_then strip_assume_tac rdU8I_bounds
              ORELSE dxrule_all_then strip_assume_tac rdLEI_boundsE
              ORELSE dxrule_all_then strip_assume_tac takeNI_boundsE
              ORELSE dxrule_all_then strip_assume_tac rdLEsNI_boundsE)
      >> DECIDE_TAC)
  >> Cases_on ‘q00 = 12’ >> simp[]
  >- (namedCases_on ‘rdLEI s lim 4 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘lookTermI pt q10’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tB"] >> simp[]
      >> strip_tac >> gvs[]
      >> rpt (dxrule_all_then strip_assume_tac rdU8I_bounds
              ORELSE dxrule_all_then strip_assume_tac rdLEI_boundsE
              ORELSE dxrule_all_then strip_assume_tac takeNI_boundsE
              ORELSE dxrule_all_then strip_assume_tac rdLEsNI_boundsE)
      >> DECIDE_TAC)
  >> Cases_on ‘q00 = 14’ >> simp[]
  >- (namedCases_on ‘rdLEI s lim 4 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 8 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘lookTermI pt q10’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tB"] >> simp[]
      >> strip_tac >> gvs[]
      >> rpt (dxrule_all_then strip_assume_tac rdU8I_bounds
              ORELSE dxrule_all_then strip_assume_tac rdLEI_boundsE
              ORELSE dxrule_all_then strip_assume_tac takeNI_boundsE
              ORELSE dxrule_all_then strip_assume_tac rdLEsNI_boundsE)
      >> DECIDE_TAC)
  >> Cases_on ‘q00 = 23’ >> simp[]
  >- (namedCases_on ‘rdLEI s lim 4 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘lookTermI pt q10’ ["", "tA"] >> simp[]
      >> strip_tac >> gvs[]
      >> rpt (dxrule_all_then strip_assume_tac rdU8I_bounds
              ORELSE dxrule_all_then strip_assume_tac rdLEI_boundsE
              ORELSE dxrule_all_then strip_assume_tac takeNI_boundsE
              ORELSE dxrule_all_then strip_assume_tac rdLEsNI_boundsE)
      >> DECIDE_TAC)
  >> Cases_on ‘q00 = 24’ >> simp[]
  >- (namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘lookNodeI t q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q30’ ["", "tB"] >> simp[]
      >> strip_tac >> gvs[]
      >> rpt (dxrule_all_then strip_assume_tac rdU8I_bounds
              ORELSE dxrule_all_then strip_assume_tac rdLEI_boundsE
              ORELSE dxrule_all_then strip_assume_tac takeNI_boundsE
              ORELSE dxrule_all_then strip_assume_tac rdLEsNI_boundsE)
      >> DECIDE_TAC)
  >> Cases_on ‘q00 = 25’ >> simp[]
  >- (namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 8 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> namedCases_on ‘takeNI s lim q40 q41’ ["", "q5"] >> simp[]
      >> PairCases_on ‘q5’ >> simp[]
      >> TRY (IF_CASES_TAC >> simp[])
      >> namedCases_on ‘rdLEI s lim 4 q51’ ["", "q6"] >> simp[]
      >> PairCases_on ‘q6’ >> simp[]
      >> namedCases_on ‘rdLEsNI s lim 4 q60 q61’ ["", "q7"] >> simp[]
      >> PairCases_on ‘q7’ >> simp[]
      >> namedCases_on ‘lookNodeI t q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookNodeI t q20’ ["", "e2"] >> simp[]
      >> PairCases_on ‘e2’ >> simp[]
      >> namedCases_on ‘lookFormulaI pt q30’ ["", "f1"] >> simp[]
      >> PairCases_on ‘f1’ >> simp[]
      >> strip_tac >> gvs[]
      >> rpt (dxrule_all_then strip_assume_tac rdU8I_bounds
              ORELSE dxrule_all_then strip_assume_tac rdLEI_boundsE
              ORELSE dxrule_all_then strip_assume_tac takeNI_boundsE
              ORELSE dxrule_all_then strip_assume_tac rdLEsNI_boundsE)
      >> DECIDE_TAC)
  >> Cases_on ‘q00 = 26’ >> simp[]
  >- (namedCases_on ‘rdLEI s lim 4 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘rdLEsNI s lim 8 q10 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 8 q41’ ["", "q5"] >> simp[]
      >> PairCases_on ‘q5’ >> simp[]
      >> namedCases_on ‘rdLEI s lim 4 q51’ ["", "q6"] >> simp[]
      >> PairCases_on ‘q6’ >> simp[]
      >> namedCases_on ‘lookNodesI t q20’ ["", "cmp"] >> simp[]
      >> namedCases_on ‘lookTermI pt q30’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q40’ ["", "tB"] >> simp[]
      >> TRY (IF_CASES_TAC >> simp[])
      >> TRY (namedCases_on ‘lookTermI pt q60’ ["", "tv"] >> simp[]
              >> Cases_on ‘tv’ >> simp[])
      >> strip_tac >> gvs[]
      >> rpt (dxrule_all_then strip_assume_tac rdU8I_bounds
              ORELSE dxrule_all_then strip_assume_tac rdLEI_boundsE
              ORELSE dxrule_all_then strip_assume_tac takeNI_boundsE
              ORELSE dxrule_all_then strip_assume_tac rdLEsNI_boundsE)
      >> DECIDE_TAC)
  >> simp[]
QED

Theorem parseNodeI_corr:
  ptblRel ptbl pt ∧ ntblRel ws tbl t ⇒
  (case parseNode ptbl tbl (secBytes s i lim) of
   | NONE => parseNodeI ws pt t s lim i = NONE
   | SOME (pf, prew, rest) =>
       ∃j. parseNodeI ws pt t s lim i =
             SOME (checkPf1 ws (INL pf), certConcl pf, prew, j) ∧
           rest = secBytes s j lim)
Proof
  strip_tac
  >> ‘∀r. lookTerm ptbl r = lookTermI pt r’ by simp[lookTermI_corr]
  >> ‘∀r. lookSimplex ptbl r = lookSimplexI pt r’ by simp[lookSimplexI_corr]
  >> ‘∀r. lookExtSet ptbl r = lookExtSetI pt r’ by simp[lookExtSetI_corr]
  >> ‘∀r. lookFormula ptbl r =
          case lookFormulaI pt r of
          | NONE => NONE
          | SOME (fw, fx, nos) => SOME fw’
     by (gen_tac >> drule lookFormulaI_corr >> simp[])
  >> ‘∀r. lookJudg ptbl r =
          case lookJudgI pt r of
          | NONE => NONE
          | SOME (pw, qw, px, qx) => SOME (pw, qw)’
     by (gen_tac >> drule lookJudgI_corr >> simp[])
  >> ‘∀off. lookNodeI t off =
        case ALOOKUP tbl off of
        | NONE => NONE
        | SOME (pf, pw) => SOME (checkPf1 ws (INL pf), certConcl pf, pw)’
     by (gen_tac
         >> qpat_assum ‘ntblRel _ _ _’ (mp_tac o SIMP_RULE (srw_ss()) [ntblRel_def])
         >> disch_then (qspec_then ‘off’ mp_tac)
         >> Cases_on ‘ALOOKUP tbl off’ >> simp[lookNodeI_def]
         >> Cases_on ‘x’ >> simp[lookNodeI_def])
  >> rw[parseNode_def, parseNodeI_def, lookNodePf_def]
  >> simp[rdU8_corr]
  >> namedCases_on ‘rdU8I s lim i’ ["", "p0"] >> simp[]
  >> PairCases_on ‘p0’ >> simp[]
  >> simp[rdU8_corr]
  >> namedCases_on ‘rdU8I s lim p01’ ["", "v0"] >> simp[]
  >> PairCases_on ‘v0’ >> simp[]
  >> simp[rdLE_corr]
  >> namedCases_on ‘rdLEI s lim 2 v01’ ["", "r0"] >> simp[]
  >> PairCases_on ‘r0’ >> simp[]
  >> rw[]
  >> simp[rdLE_corr]
  >> namedCases_on ‘rdLEI s lim 4 r01’ ["", "cj"] >> simp[]
  >> PairCases_on ‘cj’ >> simp[]
  >> qabbrev_tac ‘lj = lookJudgI pt cj0’
  >> Cases_on ‘lj’ >> simp[]
  >> PairCases_on ‘x’ >> simp[]
  >> qpat_x_assum ‘Abbrev _’
       (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])
  >> imp_res_tac lookJudgI_memo
  >> Cases_on ‘p00 = 0’ >> simp[]
  >- (rw[]
      >> simp[Once checkPf1_def, certConcl_def, judgSeq_def]
      >> gvs[Once checkPf1_def, certConcl_def, judgSeq_def])
  >> Cases_on ‘p00 = 1’ >> simp[]
  >- (rw[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘ALOOKUP tbl q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> qabbrev_tac ‘vf = lookFormulaI pt q20’
      >> Cases_on ‘vf’ >> simp[]
      >> PairCases_on ‘x’ >> simp[]
      >> qpat_x_assum ‘Abbrev _’
     (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])
      >> imp_res_tac lookFormulaI_memo
      >> simp[Once checkPf1_def, certConcl_def, judgSeq_def]
      >> gvs[Once checkPf1_def, certConcl_def, judgSeq_def])
  >> Cases_on ‘p00 = 2’ >> simp[]
  >- (rw[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> qabbrev_tac ‘vf = lookFormulaI pt q10’
      >> Cases_on ‘vf’ >> simp[]
      >> PairCases_on ‘x’ >> simp[]
      >> qpat_x_assum ‘Abbrev _’
     (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])
      >> imp_res_tac lookFormulaI_memo
      >> namedCases_on ‘ALOOKUP tbl q20’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘ALOOKUP tbl q30’ ["", "e2"] >> simp[]
      >> PairCases_on ‘e2’ >> simp[]
      >> simp[Once checkPf1_def, certConcl_def, judgSeq_def]
      >> gvs[Once checkPf1_def, certConcl_def, judgSeq_def])
  >> Cases_on ‘p00 = 3’ >> simp[]
  >- (rw[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘ALOOKUP tbl q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘ALOOKUP tbl q20’ ["", "e2"] >> simp[]
      >> PairCases_on ‘e2’ >> simp[]
      >> simp[Once checkPf1_def, certConcl_def, judgSeq_def]
      >> gvs[Once checkPf1_def, certConcl_def, judgSeq_def])
  >> Cases_on ‘p00 = 4 ∨ p00 = 5’ >> simp[]
  >- (rw[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘ALOOKUP tbl q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> qabbrev_tac ‘vf = lookFormulaI pt q20’
      >> Cases_on ‘vf’ >> simp[]
      >> PairCases_on ‘x’ >> simp[]
      >> qpat_x_assum ‘Abbrev _’
     (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])
      >> imp_res_tac lookFormulaI_memo
      >> simp[Once checkPf1_def, certConcl_def, judgSeq_def]
      >> gvs[Once checkPf1_def, certConcl_def, judgSeq_def])
  >> Cases_on ‘p00 = 6’ >> simp[]
  >- (rw[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> simp[takeN_corr]
      >> namedCases_on ‘takeNI s lim q30 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> rw[]
      >> namedCases_on ‘ALOOKUP tbl q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘ALOOKUP tbl q20’ ["", "e2"] >> simp[]
      >> PairCases_on ‘e2’ >> simp[]
      >> simp[Once checkPf1_def, certConcl_def, judgSeq_def]
      >> gvs[Once checkPf1_def, certConcl_def, judgSeq_def])
  >> Cases_on ‘p00 = 7’ >> simp[]
  >- (rw[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q41’ ["", "q5"] >> simp[]
      >> PairCases_on ‘q5’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q51’ ["", "q6"] >> simp[]
      >> PairCases_on ‘q6’ >> simp[]
      >> namedCases_on ‘ALOOKUP tbl q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘ALOOKUP tbl q20’ ["", "e2"] >> simp[]
      >> PairCases_on ‘e2’ >> simp[]
      >> namedCases_on ‘lookTermI pt q40’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q50’ ["", "tB"] >> simp[]
      >> qabbrev_tac ‘vf = lookFormulaI pt q60’
      >> Cases_on ‘vf’ >> simp[]
      >> PairCases_on ‘x’ >> simp[]
      >> qpat_x_assum ‘Abbrev _’
     (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])
      >> imp_res_tac lookFormulaI_memo
      >> simp[Once checkPf1_def, certConcl_def, judgSeq_def]
      >> gvs[Once checkPf1_def, certConcl_def, judgSeq_def])
  >> Cases_on ‘p00 = 8 ∨ p00 = 9’ >> simp[]
  >- (rw[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> namedCases_on ‘ALOOKUP tbl q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookSimplexI pt q30’ ["", "sA"] >> simp[]
      >> namedCases_on ‘lookExtSetI pt q40’ ["", "eA"] >> simp[]
      >> simp[Once checkPf1_def, certConcl_def, judgSeq_def]
      >> gvs[Once checkPf1_def, certConcl_def, judgSeq_def])
  >> Cases_on ‘p00 = 10’ >> simp[]
  >- (rw[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> simp[rdU8_corr]
      >> namedCases_on ‘rdU8I s lim q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> rw[]
      >> simp[takeN_corr]
      >> namedCases_on ‘takeNI s lim 3 q41’ ["", "q5"] >> simp[]
      >> PairCases_on ‘q5’ >> simp[]
      >> rw[]
      >> namedCases_on ‘bowtieOf q40’ ["", "bw"] >> simp[]
      >> namedCases_on ‘ALOOKUP tbl q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q30’ ["", "tB"] >> simp[]
      >> simp[Once checkPf1_def, certConcl_def, judgSeq_def]
      >> gvs[Once checkPf1_def, certConcl_def, judgSeq_def])
  >> Cases_on ‘p00 = 11’ >> simp[]
  >- (rw[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q41’ ["", "q5"] >> simp[]
      >> PairCases_on ‘q5’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q51’ ["", "q6"] >> simp[]
      >> PairCases_on ‘q6’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q61’ ["", "q7"] >> simp[]
      >> PairCases_on ‘q7’ >> simp[]
      >> namedCases_on ‘ALOOKUP tbl q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookSimplexI pt q30’ ["", "sA"] >> simp[]
      >> namedCases_on ‘lookExtSetI pt q40’ ["", "eA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q60’ ["", "tB"] >> simp[]
      >> qabbrev_tac ‘vf = lookFormulaI pt q70’
      >> Cases_on ‘vf’ >> simp[]
      >> PairCases_on ‘x’ >> simp[]
      >> qpat_x_assum ‘Abbrev _’
     (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])
      >> imp_res_tac lookFormulaI_memo
      >> simp[Once checkPf1_def, certConcl_def, judgSeq_def]
      >> gvs[Once checkPf1_def, certConcl_def, judgSeq_def])
  >> Cases_on ‘p00 = 12’ >> simp[]
  >- (rw[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> namedCases_on ‘lookTermI pt q10’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tB"] >> simp[]
      >> simp[Once checkPf1_def, certConcl_def, judgSeq_def]
      >> gvs[Once checkPf1_def, certConcl_def, judgSeq_def])
  >> Cases_on ‘p00 = 14’ >> simp[]
  >- (rw[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘lookTermI pt q10’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tB"] >> simp[]
      >> simp[Once checkPf1_def, certConcl_def, judgSeq_def]
      >> gvs[Once checkPf1_def, certConcl_def, judgSeq_def])
  >> Cases_on ‘p00 = 23’ >> simp[]
  >- (rw[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> namedCases_on ‘lookTermI pt q10’ ["", "tA"] >> simp[]
      >> simp[Once checkPf1_def, certConcl_def, judgSeq_def]
      >> gvs[Once checkPf1_def, certConcl_def, judgSeq_def])
  >> Cases_on ‘p00 = 24’ >> simp[]
  >- (rw[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> namedCases_on ‘ALOOKUP tbl q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘lookTermI pt q20’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q30’ ["", "tB"] >> simp[]
      >> simp[Once checkPf1_def, certConcl_def, judgSeq_def]
      >> gvs[Once checkPf1_def, certConcl_def, judgSeq_def])
  >> Cases_on ‘p00 = 25’ >> simp[]
  >- (rw[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> simp[takeN_corr]
      >> namedCases_on ‘takeNI s lim q40 q41’ ["", "q5"] >> simp[]
      >> PairCases_on ‘q5’ >> simp[]
      >> rw[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q51’ ["", "q6"] >> simp[]
      >> PairCases_on ‘q6’ >> simp[]
      >> simp[rdLEsN_corr]
      >> namedCases_on ‘rdLEsNI s lim 4 q60 q61’ ["", "q7"] >> simp[]
      >> PairCases_on ‘q7’ >> simp[]
      >> namedCases_on ‘ALOOKUP tbl q10’ ["", "e1"] >> simp[]
      >> PairCases_on ‘e1’ >> simp[]
      >> namedCases_on ‘ALOOKUP tbl q20’ ["", "e2"] >> simp[]
      >> PairCases_on ‘e2’ >> simp[]
      >> qabbrev_tac ‘vf = lookFormulaI pt q30’
      >> Cases_on ‘vf’ >> simp[]
      >> PairCases_on ‘x’ >> simp[]
      >> qpat_x_assum ‘Abbrev _’
     (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])
      >> imp_res_tac lookFormulaI_memo
      >> simp[Once checkPf1_def, certConcl_def, judgSeq_def]
      >> gvs[Once checkPf1_def, certConcl_def, judgSeq_def])
  >> Cases_on ‘p00 = 26’ >> simp[]
  >- (rw[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 cj1’ ["", "q1"] >> simp[]
      >> PairCases_on ‘q1’ >> simp[]
      >> simp[rdLEsN_corr]
      >> namedCases_on ‘rdLEsNI s lim 8 q10 q11’ ["", "q2"] >> simp[]
      >> PairCases_on ‘q2’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q21’ ["", "q3"] >> simp[]
      >> PairCases_on ‘q3’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q31’ ["", "q4"] >> simp[]
      >> PairCases_on ‘q4’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 8 q41’ ["", "q5"] >> simp[]
      >> PairCases_on ‘q5’ >> simp[]
      >> simp[rdLE_corr]
      >> namedCases_on ‘rdLEI s lim 4 q51’ ["", "q6"] >> simp[]
      >> PairCases_on ‘q6’ >> simp[]
      >> qpat_assum ‘ntblRel _ _ _’ (assume_tac o MATCH_MP lookNodesI_corr)
      >> pop_assum (qspec_then ‘q20’ assume_tac)
      >> Cases_on ‘optSeq (MAP (lookNodePf tbl) q20)’ >> gvs[]
      >> namedCases_on ‘lookTermI pt q30’ ["", "tA"] >> simp[]
      >> namedCases_on ‘lookTermI pt q40’ ["", "tB"] >> simp[]
      >> rw[]
      >> TRY (namedCases_on ‘lookTermI pt q60’ ["", "tv"] >> simp[]
              >> Cases_on ‘tv’ >> simp[])
      >> imp_res_tac EVERY_fst_triple
      >> simp[Once checkPf1_def, certConcl_def, judgSeq_def,
              checkPf1_INR_EVERY]
      >> gvs[Once checkPf1_def, certConcl_def, judgSeq_def,
             checkPf1_INR_EVERY])
  >> simp[]
QED

Definition nodePassI_def:
  nodePassI (0:num) (ws:tensortype list) (pt : pobjI spt) (s:mlstring)
            (lim:num) (pos:num) (i:num)
            (t : (bool # sequent # fwire) spt) (cnt:num) =
    (if i = lim ∨ strlen s ≤ i then SOME (t, cnt) else NONE) ∧
  nodePassI (SUC f) ws pt s lim pos i t cnt =
    if i = lim ∨ strlen s ≤ i then SOME (t, cnt) else
    case parseNodeI ws pt t s lim i of NONE => NONE
    | SOME (b, sq, prew, i') =>
        if i' < i then NONE else
        nodePassI f ws pt s lim (pos + (i' − i)) i'
                  (sptree$insert pos (b, sq, prew) t) (cnt + 1)
End

Theorem ntblRel_insert:
  ntblRel ws tbl t ∧ b = checkPf1 ws (INL pf) ∧ sq = certConcl pf ⇒
  ntblRel ws ((pos, (pf, prew))::tbl) (sptree$insert pos (b, sq, prew) t)
Proof
  rw[ntblRel_def, sptreeTheory.lookup_insert] >> rw[] >> gvs[]
QED

Theorem nodePassI_rel:
  ∀f pos i cnt tbl t.
    ptblRel ptbl pt ∧ ntblRel ws tbl t ∧ i ≤ lim ∧ i ≤ strlen s ⇒
    (case nodePass f ptbl pos (secBytes s i lim) tbl cnt of
     | NONE => nodePassI f ws pt s lim pos i t cnt = NONE
     | SOME (tbl', cnt') =>
         ∃t'. nodePassI f ws pt s lim pos i t cnt = SOME (t', cnt') ∧
              ntblRel ws tbl' t')
Proof

  Induct
  >- (rw[nodePass_def, nodePassI_def, NULL_secBytes] >> gvs[])
  >> rw[nodePass_def, nodePassI_def, NULL_secBytes]
  >> TRY (gvs[] >> NO_TAC)
  >> ‘i ≤ lim ∧ i ≤ strlen s’ by DECIDE_TAC
  >> drule_all_then (qspecl_then [‘s’, ‘lim’, ‘i’] mp_tac) parseNodeI_corr
  >> qabbrev_tac ‘pn = parseNode ptbl tbl (secBytes s i lim)’
  >> Cases_on ‘pn’ >> simp[]
  >> PairCases_on ‘x’ >> simp[] >> strip_tac
  >> drule_all_then strip_assume_tac parseNodeI_bounds
  >> qpat_x_assum ‘parseNodeI _ _ _ _ _ _ = _’ (fn th => simp[th])
  >> gvs[]
  >> ‘LENGTH (secBytes s j lim) ≤ LENGTH (secBytes s i lim) ∧
      LENGTH (secBytes s i lim) − LENGTH (secBytes s j lim) = j − i’
     by (rw[LENGTH_secBytes, MIN_DEF] >> DECIDE_TAC)
  >> ‘¬(LENGTH (secBytes s i lim) < LENGTH (secBytes s j lim))’ by DECIDE_TAC
  >> ‘¬(j < i)’ by DECIDE_TAC
  >> ‘pos + LENGTH (secBytes s i lim) − LENGTH (secBytes s j lim) =
      j + pos − i’ by DECIDE_TAC
  >> simp[]
  >> first_x_assum irule >> simp[ntblRel_insert]
QED

Definition parseProofSectionI_def:
  parseProofSectionI (ws:tensortype list) (s:mlstring)
                     (base:num) (seclen:num) (cxs:simpc list)
                     (hnn:num) (rootOff:num) (thetaRef:num) =
    let lim = base + seclen in
    case rdLEI s lim 8 base of NONE => NONE | SOME (plen, i1) =>
    if ¬(i1 + plen ≤ lim ∧ i1 + plen ≤ strlen s) then NONE else
    (let poolLim = i1 + plen in
     case poolPassI (SUC plen) cxs s poolLim 0 i1 sptree$LN of
     | NONE => NONE
     | SOME pt =>
     if ¬(thetaRef = (4294967295:num) ∨
          (case lookTermI pt thetaRef of
           | SOME (TmConst q) => T
           | _ => F)) then NONE else

     case nodePassI (SUC (lim − (i1 + plen))) ws pt s lim (8 + plen)
                    poolLim sptree$LN 0 of
     | NONE => NONE
     | SOME (nt, cnt) =>
     if cnt ≠ hnn then NONE else
     case lookNodeI nt rootOff of
     | NONE => NONE
     | SOME (b, sq, prew) =>
         if rootShapeOK prew then SOME b else NONE)
End

Theorem ptblRel_nil:
  ptblRel [] sptree$LN
Proof
  rw[ptblRel_def, sptreeTheory.lookup_def]
QED

Theorem ntblRel_nil:
  ntblRel ws [] sptree$LN
Proof
  rw[ntblRel_def, sptreeTheory.lookup_def]
QED

Theorem takeN_secBytes:
  takeN n (secBytes s i lim) =
  if i + n ≤ lim ∧ i + n ≤ strlen s then
    SOME (secBytes s i (i + n), secBytes s (i + n) lim)
  else if n = 0 then SOME ([], secBytes s i lim)
  else NONE
Proof
  Cases_on ‘i + n ≤ lim ∧ i + n ≤ strlen s’
  >> simp[takeN_corr, takeNI_def]
  >- (‘i + n ≤ strlen s’ by DECIDE_TAC
      >> simp[subBytes_TAKE, secBytes_def]
      >> ‘i + n − i = n’ by DECIDE_TAC
      >> simp[])
  >> Cases_on ‘n = 0’ >> simp[]
QED

Theorem parseProofSectionI_corr:
  base + seclen ≤ strlen s ⇒
  (case parseProofSection (TAKE seclen (DROP base (MAP ORD (explode s))))
                          cxs hnn rootOff thetaRef of
   | NONE => parseProofSectionI ws s base seclen cxs hnn rootOff thetaRef = NONE
   | SOME pf =>
       parseProofSectionI ws s base seclen cxs hnn rootOff thetaRef =
       SOME (checkPf1 ws (INL pf)))
Proof

  strip_tac
  >> ‘TAKE seclen (DROP base (MAP ORD (explode s))) =
      secBytes s base (base + seclen)’
     by simp[GSYM MAP_DROP, GSYM MAP_TAKE, secBytes_slice0]
  >> ‘base ≤ base + seclen ∧ base ≤ strlen s’ by DECIDE_TAC
  >> rw[parseProofSection_def, parseProofSectionI_def]
  >> simp[rdLE_corr]
  >> namedCases_on ‘rdLEI s (base + seclen) 8 base’ ["", "p1"] >> simp[]
  >> PairCases_on ‘p1’ >> simp[]
  >> ‘base ≤ p11 ∧ p11 ≤ base + seclen ∧ p11 ≤ strlen s’
     by (imp_res_tac rdLEI_bounds >> DECIDE_TAC)
  >> simp[takeN_secBytes] >> rw[] >> TRY (gvs[] >> NO_TAC)
  >> ‘LENGTH (secBytes s p11 (p10 + p11)) = p10’
     by (rw[LENGTH_secBytes, MIN_DEF] >> DECIDE_TAC) >> simp[]
  >> mp_tac (Q.INST [‘lim’ |-> ‘p10 + (p11:num)’]
       (Q.SPECL [‘SUC p10’, ‘0’, ‘p11’, ‘[] : (num # poolobj) list’,
                 ‘sptree$LN : pobjI spt’] poolPassI_rel))
  >> impl_tac >- simp[ptblRel_nil]
  >> namedCases_on ‘poolPass (SUC p10) cxs 0 (secBytes s p11 (p10 + p11)) []’
                   ["", "ptb"] >> simp[]
  >> strip_tac >> simp[]
  >> ‘∀r. lookTerm ptb r = lookTermI t' r’ by simp[lookTermI_corr]
  >> simp[] >> rw[] >> TRY (gvs[] >> NO_TAC)
  >> ‘LENGTH (secBytes s (p10 + p11) (base + seclen)) =
      base + seclen − (p10 + p11)’
     by (rw[LENGTH_secBytes, MIN_DEF] >> DECIDE_TAC) >> simp[]
  >> mp_tac (Q.INST [‘lim’ |-> ‘base + (seclen:num)’,
                     ‘ptbl’ |-> ‘ptb’, ‘pt’ |-> ‘t'’]
       (Q.SPECL [‘SUC (base + seclen − (p10 + p11))’, ‘p10 + 8’, ‘p10 + p11’,
                 ‘0’, ‘[] : (num # (certpf # fwire)) list’,
                 ‘sptree$LN : (bool # sequent # fwire) spt’] nodePassI_rel))
  >> impl_tac >- simp[ntblRel_nil]
  >> namedCases_on ‘nodePass (SUC (base + seclen − (p10 + p11))) ptb (p10 + 8)
                      (secBytes s (p10 + p11) (base + seclen)) [] 0’
                   ["", "ntc"] >> simp[]
  >> PairCases_on ‘ntc’ >> simp[] >> strip_tac >> simp[]
  >> rw[] >> TRY (gvs[] >> NO_TAC)
  >> ‘∀off. lookNodeI t'' off =
        case ALOOKUP ntc0 off of
        | NONE => NONE
        | SOME (pf, pw) => SOME (checkPf1 ws (INL pf), certConcl pf, pw)’
     by (gen_tac
         >> qpat_assum ‘ntblRel _ _ _’ (mp_tac o SIMP_RULE (srw_ss()) [ntblRel_def])
         >> disch_then (qspec_then ‘off’ mp_tac)
         >> Cases_on ‘ALOOKUP ntc0 off’ >> simp[lookNodeI_def]
         >> Cases_on ‘x’ >> simp[lookNodeI_def])
  >> simp[]
  >> namedCases_on ‘ALOOKUP ntc0 rootOff’ ["", "rt"] >> simp[]
  >> PairCases_on ‘rt’ >> simp[] >> rw[] >> gvs[]
QED

Definition checkTopI_def:
  checkTopI (s:mlstring) =
    case parseHeaderI s of NONE => F | SOME h =>
    case parseSymtabI s h.symOff h.symLen h.nWires h.payOff h.payLen of
    | NONE => F
    | SOME ws =>
    case parseDiagramI s h.diaOff h.diaLen h.nCxs h.nApps of
    | NONE => F
    | SOME cxs =>
    case parseProofSectionI ws s h.prfOff h.prfLen cxs
                            h.nNodes h.rootOff h.thetaRef of
    | NONE => F
    | SOME b => b
End

Theorem parseHeader_sections:
  parseHeader bytes = SOME h ⇒
  sectionOK (LENGTH bytes) h.symOff h.symLen ∧
  sectionOK (LENGTH bytes) h.payOff h.payLen ∧
  sectionOK (LENGTH bytes) h.diaOff h.diaLen ∧
  sectionOK (LENGTH bytes) h.prfOff h.prfLen
Proof
  rw[parseHeader_def, AllCaseEqs()] >> simp[]
QED

Theorem checkTopI_correct:
  checkTopI s = qtslCheckBytes (explode s)
Proof

  rw[checkTopI_def, qtslCheckBytes_def, parseCert_def,
     GSYM parseHeaderI_corr]
  >> namedCases_on ‘parseHeader (MAP ORD (explode s))’ ["", "h"] >> simp[]
  >> imp_res_tac parseHeader_sections
  >> gvs[sectionOK_def, mlstringTheory.LENGTH_explode]
  >> simp[GSYM parseSymtabI_corr]
  >> namedCases_on ‘parseSymtab (TAKE h.symLen (DROP h.symOff (MAP ORD (explode s))))
                h.symLen h.nWires h.payOff h.payLen’ ["", "wsv"] >> simp[]
  >> simp[GSYM parseDiagram_corr]
  >> namedCases_on ‘parseDiagram (TAKE h.diaLen (DROP h.diaOff (MAP ORD (explode s))))
                h.nCxs h.nApps’ ["", "cxv"] >> simp[]
  >> qspecl_then [‘h.prfOff’, ‘h.prfLen’, ‘wsv’, ‘cxv’,
                  ‘h.nNodes’, ‘h.rootOff’, ‘h.thetaRef’] mp_tac
       (Q.GENL [‘base’, ‘seclen’, ‘ws’, ‘cxs’, ‘hnn’, ‘rootOff’, ‘thetaRef’]
               parseProofSectionI_corr)
  >> impl_tac >- simp[]
  >> namedCases_on
       ‘parseProofSection (TAKE h.prfLen (DROP h.prfOff (MAP ORD (explode s))))
                          cxv h.nNodes h.rootOff h.thetaRef’ ["", "pfv"]
  >> simp[checkPf_def]
QED

Definition qtsl_verdict_strI_def:
  qtsl_verdict_strI (s:mlstring) =
    if checkTopI s then verified_string else reject_string
End

Theorem qtsl_verdict_strI_correct:
  qtsl_verdict_strI (implode cs) = qtsl_verdict cs
Proof
  rw[qtsl_verdict_strI_def, qtsl_verdict_def, checkTopI_correct,
     mlstringTheory.explode_implode]
QED
