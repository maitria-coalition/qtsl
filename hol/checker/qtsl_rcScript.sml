(*
  The static range-coder DECODE kernel for the succinct certificate
  container (bsgc v1): fail-closed, fuel-bounded, and
  translator-friendly, mirroring the reference decoder's carry handling
  byte for byte. The well-formed-model check makes the cumulative
  interval search total, and short payloads decode deterministically
  rather than failing.
*)
Theory qtsl_rc
Ancestors
  mllist
Libs
  preamble

Definition rdVarF_def:
  rdVarF (bs:num list) (pos:num) (0:num) (shift:num) (acc:num)
         : (num # num) option = NONE ∧
  rdVarF bs pos (SUC f) shift acc =
    case oEL pos bs of
    | NONE => NONE
    | SOME b =>
        let acc' = acc + (b MOD 128) * 2 ** shift in
          if b < 128 then SOME (acc', pos + 1)
          else rdVarF bs (pos + 1) f (shift + 7) acc'
End

Definition rdVar_def:
  rdVar (bs:num list) (pos:num) : (num # num) option =
    rdVarF bs pos 10 0 0
End

Definition dApp_def:
  dApp (prev:num) (w:num) (cap:num) : num option =
    if w MOD 2 = 0 then
      (let d = w DIV 2 in
         if prev + d < cap then SOME (prev + d) else NONE)
    else
      (let d = (w + 1) DIV 2 in
         if d ≤ prev then SOME (prev − d) else NONE)
End

Datatype:
  rcmodel = <|
    alpha : num ;
    freqs : (num list) list
  |>
End

Definition rdU16s_def:
  rdU16s (bs:num list) (pos:num) (0:num) : (num list # num) option =
    SOME ([], pos) ∧
  rdU16s bs pos (SUC k) =
    case oEL pos bs of
    | NONE => NONE
    | SOME lo =>
      case oEL (pos + 1) bs of
      | NONE => NONE
      | SOME hi =>
        case rdU16s bs (pos + 2) k of
        | NONE => NONE
        | SOME (vs, p') => SOME ((lo + 256 * hi)::vs, p')
End

Definition rdTables_def:
  rdTables (bs:num list) (pos:num) (alpha:num) (0:num)
           : ((num list) list # num) option = SOME ([], pos) ∧
  rdTables bs pos alpha (SUC c) =
    case rdU16s bs pos alpha of
    | NONE => NONE
    | SOME (t, p1) =>
        if SUM t ≠ 16384 then NONE
        else
          case rdTables bs p1 alpha c of
          | NONE => NONE
          | SOME (ts, p2) => SOME (t::ts, p2)
End

Definition deserModel_def:
  deserModel (bs:num list) (pos:num) : (rcmodel # num) option =
    case rdVar bs pos of
    | NONE => NONE
    | SOME (alpha, p1) =>
      case rdVar bs p1 of
      | NONE => NONE
      | SOME (ctxs, p2) =>
          if alpha = 0 ∨ 256 < alpha ∨ ¬(ctxs = 1 ∨ ctxs = alpha) then NONE
          else
            case rdTables bs p2 alpha ctxs of
            | NONE => NONE
            | SOME (ts, p3) => SOME (<| alpha := alpha ; freqs := ts |>, p3)
End

Datatype:
  rcst = <| code : num ; range : num ; pos : num |>
End

Definition rcByte_def:
  rcByte (bs:num list) (pos:num) : num =
    case oEL pos bs of NONE => 0 | SOME b => b MOD 256
End

Definition rcInit_def:
  rcInit (bs:num list) : rcst =
    <| code := ((rcByte bs 1 * 256 + rcByte bs 2) * 256 + rcByte bs 3) * 256
               + rcByte bs 4 ;
       range := 4294967295 ;
       pos := 5 |>
End

Definition findSymF_def:
  findSymF ([]:num list) (s:num) (cum:num) (th:num)
           : (num # num # num) option = NONE ∧
  findSymF (f::fs) s cum th =
    if th < cum + f then SOME (s, cum, f)
    else findSymF fs (s + 1) (cum + f) th
End

Definition renormF_def:
  renormF (bs:num list) (st:rcst) (0:num) : rcst option =
    (if st.range < 16777216 then NONE else SOME st) ∧
  renormF bs st (SUC f) =
    if st.range < 16777216 then
      renormF bs
        (st with <| code := (st.code * 256 + rcByte bs st.pos) MOD 4294967296 ;
                    range := st.range * 256 ;
                    pos := st.pos + 1 |>) f
    else SOME st
End

Definition rcDecode1_def:
  rcDecode1 (bs:num list) (freq:num list) (st:rcst) : (num # rcst) option =
    let range' = st.range DIV 16384 in
      if range' = 0 then NONE else
      let th = MIN (st.code DIV range') 16383 in
        case findSymF freq 0 0 th of
        | NONE => NONE
        | SOME (sym, start, size) =>
            let st' = st with <| code := st.code − start * range' ;
                                 range := range' * size |> in
              case renormF bs st' 4 of
              | NONE => NONE
              | SOME st'' => SOME (sym, st'')
End

Definition rcDecodeN_def:
  rcDecodeN (bs:num list) (m:rcmodel) (order1:bool) (0:num) (ctx:num)
            (st:rcst) (acc:num list) : (num list # rcst) option =
    SOME (REVERSE acc, st) ∧
  rcDecodeN bs m order1 (SUC n) ctx st acc =
    case oEL ctx m.freqs of
    | NONE => NONE
    | SOME freq =>
      case rcDecode1 bs freq st of
      | NONE => NONE
      | SOME (s, st') =>
          rcDecodeN bs m order1 n (if order1 then s else ctx) st' (s::acc)
End

Definition decompressO01_def:
  decompressO01 (bs:num list) : num list option =
    case oEL 0 bs of
    | NONE => NONE
    | SOME o1 =>
      case deserModel bs 1 of
      | NONE => NONE
      | SOME (m, p1) =>
        case rdVar bs p1 of
        | NONE => NONE
        | SOME (n, p2) =>
          case rdVar bs p2 of
          | NONE => NONE
          | SOME (plen, p3) =>
              if LENGTH bs < p3 + plen then NONE
              else
                let payload = TAKE plen (DROP p3 bs) in
                  case rcDecodeN payload m (o1 ≠ 0) n 0 (rcInit payload) [] of
                  | NONE => NONE
                  | SOME (syms, _) => SOME syms
End

Definition rdBlockIdx_def:
  rdBlockIdx (bs:num list) (pos:num) (0:num)
             : ((num # num) list # num) option = SOME ([], pos) ∧
  rdBlockIdx bs pos (SUC k) =
    case rdVar bs pos of
    | NONE => NONE
    | SOME (src, p1) =>
      case rdVar bs p1 of
      | NONE => NONE
      | SOME (coded, p2) =>
        case rdBlockIdx bs p2 k of
        | NONE => NONE
        | SOME (ix, p3) => SOME ((src, coded)::ix, p3)
End

Definition decBlocks_def:
  decBlocks (bs:num list) (m:rcmodel) (order1:bool) (pos:num)
            ([]:(num # num) list) : num list option = SOME [] ∧
  decBlocks bs m order1 pos ((src, coded)::ix) =
    if LENGTH bs < pos + coded then NONE
    else
      let payload = TAKE coded (DROP pos bs) in
        case rcDecodeN payload m order1 src 0 (rcInit payload) [] of
        | NONE => NONE
        | SOME (syms, _) =>
          case decBlocks bs m order1 (pos + coded) ix of
          | NONE => NONE
          | SOME rest => SOME (syms ++ rest)
End

Definition decompressBlocks_def:
  decompressBlocks (bs:num list) : num list option =
    case oEL 0 bs of
    | NONE => NONE
    | SOME o1 =>
      case deserModel bs 1 of
      | NONE => NONE
      | SOME (m, p1) =>
        case rdVar bs p1 of
        | NONE => NONE
        | SOME (nb, p2) =>
          case rdBlockIdx bs p2 nb of
          | NONE => NONE
          | SOME (ix, p3) => decBlocks bs m (o1 ≠ 0) p3 ix
End

Definition rdLens_def:
  rdLens (bs:num list) (pos:num) (0:num) : (num list # num) option =
    SOME ([], pos) ∧
  rdLens bs pos (SUC k) =
    case rdVar bs pos of
    | NONE => NONE
    | SOME (l, p1) =>
      case rdLens bs p1 k of
      | NONE => NONE
      | SOME (ls, p2) => SOME (l::ls, p2)
End

Definition blockedRaw_def:
  blockedRaw (bs:num list) : num list option =
    case rdVar bs 0 of
    | NONE => NONE
    | SOME (nb, p1) =>
      case rdLens bs p1 nb of
      | NONE => NONE
      | SOME (ls, p2) =>
          if LENGTH bs < p2 + SUM ls then NONE
          else SOME (TAKE (SUM ls) (DROP p2 bs))
End
