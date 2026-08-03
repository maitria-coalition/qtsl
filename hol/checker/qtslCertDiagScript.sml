(*
  Diagnostic main program (UNVERIFIED — a debugging instrument, not
  part of the assurance chain): certificate bytes on stdin, per-stage
  parse verdict on stdout, with a deepest-first checker diagnosis that
  reports the first failing obligation labelled by constructor. Reuses
  the banked stage-1 translation; carries no correctness theorem.
*)
Theory qtslCertDiag
Ancestors
  basis_ffi qtsl_cert qtslCertProg
Libs
  preamble basis

val _ = translation_extends "qtslCertProg";

Definition firstFail_def:
  (firstFail (ws:tensortype list) (INL (CertPf sq nd) : certpf + certpf list) =
     case nd of
     | CnAx => (if sq.pre = sq.post then NONE else SOME (strlit "Ax:pre<>post"))
     | CnWeaken p extra =>
         (case firstFail ws (INL p) of SOME m => SOME m | NONE =>
          let ps = certConcl p in
          if sq.pre ≠ FAnd ps.pre extra then SOME (strlit "Weaken:pre") else
          if sq.post ≠ ps.post then SOME (strlit "Weaken:post") else NONE)
     | CnCut cutf lp rp =>
         (case firstFail ws (INL lp) of SOME m => SOME m | NONE =>
          case firstFail ws (INL rp) of SOME m => SOME m | NONE =>
          let ls = certConcl lp in
          let rs = certConcl rp in
          if sq.pre ≠ ls.pre then SOME (strlit "Cut:pre") else
          if sq.post ≠ rs.post then SOME (strlit "Cut:post") else
          if ls.post ≠ cutf then SOME (strlit "Cut:lpost") else
          if rs.pre ≠ FAnd ls.pre cutf then SOME (strlit "Cut:rpre") else NONE)
     | CnAndI lp rp =>
         (case firstFail ws (INL lp) of SOME m => SOME m | NONE =>
          case firstFail ws (INL rp) of SOME m => SOME m | NONE =>
          let ls = certConcl lp in
          let rs = certConcl rp in
          if ls.pre ≠ rs.pre then SOME (strlit "AndI:pres") else
          if sq.pre ≠ ls.pre then SOME (strlit "AndI:pre") else
          if sq.post ≠ FAnd ls.post rs.post then SOME (strlit "AndI:post")
          else NONE)
     | CnAndEL p other =>
         (case firstFail ws (INL p) of SOME m => SOME m | NONE =>
          let ps = certConcl p in
          if sq.pre ≠ ps.pre then SOME (strlit "AndEL:pre") else
          if ps.post ≠ FAnd sq.post other then SOME (strlit "AndEL:post")
          else NONE)
     | CnAndER p other =>
         (case firstFail ws (INL p) of SOME m => SOME m | NONE =>
          let ps = certConcl p in
          if sq.pre ≠ ps.pre then SOME (strlit "AndER:pre") else
          if ps.post ≠ FAnd other sq.post then SOME (strlit "AndER:post")
          else NONE)
     | CnOrIL p other =>
         (case firstFail ws (INL p) of SOME m => SOME m | NONE =>
          let ps = certConcl p in
          if sq.pre ≠ ps.pre then SOME (strlit "OrIL:pre") else
          if sq.post ≠ FOr ps.post other then SOME (strlit "OrIL:post")
          else NONE)
     | CnOrIR p other =>
         (case firstFail ws (INL p) of SOME m => SOME m | NONE =>
          let ps = certConcl p in
          if sq.pre ≠ ps.pre then SOME (strlit "OrIR:pre") else
          if sq.post ≠ FOr other ps.post then SOME (strlit "OrIR:post")
          else NONE)
     | CnOrE lp rp path =>
         (case firstFail ws (INL lp) of SOME m => SOME m | NONE =>
          case firstFail ws (INL rp) of SOME m => SOME m | NONE =>
          let ls = certConcl lp in
          let rs = certConcl rp in
            case conjGet sq.pre path of
            | SOME (FOr d1 d2) =>
                (if conjReplace sq.pre path d1 ≠ SOME ls.pre
                   then SOME (strlit "OrE:replL") else
                 if conjReplace sq.pre path d2 ≠ SOME rs.pre
                   then SOME (strlit "OrE:replR") else
                 if ls.post ≠ sq.post then SOME (strlit "OrE:lpost") else
                 if rs.post ≠ sq.post then SOME (strlit "OrE:rpost")
                 else NONE)
            | _ => SOME (strlit "OrE:conjGet"))
     | CnEqElim ep bp w tT tU bodyForm =>
         (case firstFail ws (INL ep) of SOME m => SOME m | NONE =>
          case firstFail ws (INL bp) of SOME m => SOME m | NONE =>
          let es = certConcl ep in
          let bs = certConcl bp in
          if sq.pre ≠ es.pre then SOME (strlit "EqElim:pre") else
          if es.pre ≠ bs.pre then SOME (strlit "EqElim:pres") else
          if es.post ≠ FAtom BowEq tT tU then SOME (strlit "EqElim:eqform") else
          if termBshape ws tT ≠ termBshape ws tU then SOME (strlit "EqElim:bshape") else
          if ¬IS_SOME (termBshape ws tT) then SOME (strlit "EqElim:bshapeNone") else
          if bs.post ≠ formulaSubst w tT bodyForm then SOME (strlit "EqElim:bpost") else
          if sq.post ≠ formulaSubst w tU bodyForm then SOME (strlit "EqElim:post")
          else NONE)
     | CnConvIntro p t sx es =>
         (case firstFail ws (INL p) of SOME m => SOME m | NONE =>
          let ps = certConcl p in
          if sq.pre ≠ ps.pre then SOME (strlit "ConvIntro:pre") else
          if termBshape ws t ≠ SOME [sx.complex.ambDim] then SOME (strlit "ConvIntro:bshape") else
          if barycentricHalfspaceBuild t sx es ≠ SOME ps.post then SOME (strlit "ConvIntro:bary") else
          if sq.post ≠ FInRegion t sx es then SOME (strlit "ConvIntro:post")
          else NONE)
     | CnConvElim p t sx es =>
         (case firstFail ws (INL p) of SOME m => SOME m | NONE =>
          let ps = certConcl p in
          if sq.pre ≠ ps.pre then SOME (strlit "ConvElim:pre") else
          if ps.post ≠ FInRegion t sx es then SOME (strlit "ConvElim:ppost") else
          if barycentricHalfspaceBuild t sx es ≠ SOME sq.post then SOME (strlit "ConvElim:bary")
          else NONE)
     | CnArithFold p tl tr b =>
         (case firstFail ws (INL p) of SOME m => SOME m | NONE =>
          if b = BowNe then SOME (strlit "ArithFold:ne") else
          let ps = certConcl p in
          if sq.pre ≠ ps.pre then SOME (strlit "ArithFold:pre") else
          if ps.post ≠ FAtom b (TmSub tl tr) (TmConst 0) then SOME (strlit "ArithFold:ppost") else
          if sq.post ≠ FAtom b tl tr then SOME (strlit "ArithFold:post")
          else NONE)
     | CnArithUnfold p tl tr b =>
         (case firstFail ws (INL p) of SOME m => SOME m | NONE =>
          if b = BowNe then SOME (strlit "ArithUnfold:ne") else
          let ps = certConcl p in
          if sq.pre ≠ ps.pre then SOME (strlit "ArithUnfold:pre") else
          if ps.post ≠ FAtom b tl tr then SOME (strlit "ArithUnfold:ppost") else
          if sq.post ≠ FAtom b (TmSub tl tr) (TmConst 0) then SOME (strlit "ArithUnfold:post")
          else NONE)
     | CnBernCone p tX sx es deg poly pred =>
         (case firstFail ws (INL p) of SOME m => SOME m | NONE =>
          let ps = certConcl p in
          if sq.pre ≠ ps.pre then SOME (strlit "BernCone:pre") else
          if ps.post ≠ FInRegion tX sx es then SOME (strlit "BernCone:ppost") else
          if ¬polyTieB tX poly then SOME (strlit "BernCone:polyTie") else
          if ¬(if extIsEmptyB es then isConvexPredicateB pred
               else isConicPredicateB pred) then SOME (strlit "BernCone:predClass") else
          if ¬bernConeCoeffCheck sx es deg poly pred then SOME (strlit "BernCone:coeff") else
          if sq.post ≠ formulaSubst predicateHole poly pred then SOME (strlit "BernCone:post")
          else NONE)
     | CnNorm tl tr =>
         (if ¬polynomialCanonicalEqB tl tr then SOME (strlit "Norm:canon") else
          if termBshape ws tl ≠ termBshape ws tr then SOME (strlit "Norm:bshape") else
          if ¬IS_SOME (termBshape ws tl) then SOME (strlit "Norm:bshapeNone") else
          if ¬finWiresB ws tl then SOME (strlit "Norm:finL") else
          if ¬finWiresB ws tr then SOME (strlit "Norm:finR") else
          if sq.post ≠ FAtom BowEq tl tr then SOME (strlit "Norm:post")
          else NONE)
     | CnFarkas cc concl dbl =>
         (if ¬IS_SOME (termBshape ws concl) then SOME (strlit "Farkas:bshape") else
          if ¬finWiresB ws concl then SOME (strlit "Farkas:fin") else
          if ¬wiresPosB ws (formulaFreeWires sq.pre ++ termFreeWires concl)
            then SOME (strlit "Farkas:wpos") else
          if ¬farkasCheck cc sq.pre concl then SOME (strlit "Farkas:check") else
          if sq.post ≠ FAtom BowLe concl (TmConst 0) then SOME (strlit "Farkas:post")
          else NONE)
     | CnEqRefl t =>
         (if ¬IS_SOME (termBshape ws t) then SOME (strlit "EqRefl:bshape") else
          if ¬finWiresB ws t then SOME (strlit "EqRefl:fin") else
          if sq.post ≠ FAtom BowEq t t then SOME (strlit "EqRefl:post")
          else NONE)
     | CnEqSym p tT tU =>
         (case firstFail ws (INL p) of SOME m => SOME m | NONE =>
          let ps = certConcl p in
          if sq.pre ≠ ps.pre then SOME (strlit "EqSym:pre") else
          if ps.post ≠ FAtom BowEq tT tU then SOME (strlit "EqSym:ppost") else
          if sq.post ≠ FAtom BowEq tU tT then SOME (strlit "EqSym:post")
          else NONE)
     | CnPromise sp cp contract path iface =>
         (case firstFail ws (INL sp) of SOME m => SOME m | NONE =>
          case firstFail ws (INL cp) of SOME m => SOME m | NONE =>
          let ss = certConcl sp in
          let cs = certConcl cp in
          if ss.post ≠ contract then SOME (strlit "Promise:contract") else
          if conjGet cs.pre path ≠ SOME contract then SOME (strlit "Promise:conjGet") else
          if conjReplace cs.pre path ss.pre ≠ SOME sq.pre then SOME (strlit "Promise:repl") else
          if sq.post ≠ cs.post then SOME (strlit "Promise:post") else
          (case conjReplace cs.pre path FTt of
           | SOME ctx =>
               (if ¬EVERY (λw. MEM w iface) (formulaFreeWires contract)
                  then SOME (strlit "Promise:ifaceContract") else
                if ¬EVERY (λw. (MEM w (formulaFreeWires ctx) ∨
                                MEM w (formulaFreeWires sq.post)) ⇒
                               MEM w iface)
                          (formulaFreeWires ss.pre)
                  then SOME (strlit "Promise:ifaceSep") else NONE)
           | NONE => SOME (strlit "Promise:ctxNone")))
     | CnSyzygy comps cc concl dbl th =>
         (case firstFail ws (INR comps) of SOME m => SOME m | NONE =>
          let cseqs = MAP certConcl comps in
          if ¬EVERY (λc. premiseContainsB sq.pre c.pre) cseqs
            then SOME (strlit "Syzygy:contains") else
          if ¬IS_SOME (termBshape ws concl) then SOME (strlit "Syzygy:bshape") else
          if ¬finWiresB ws concl then SOME (strlit "Syzygy:fin") else
          if ¬wiresPosB ws (formulaFreeWires sq.pre ++ termFreeWires concl)
            then SOME (strlit "Syzygy:wpos") else
          if ¬EVERY (λc. wiresPosB ws (formulaFreeWires c.post)) cseqs
            then SOME (strlit "Syzygy:cpos") else
          if ¬syzygyCheck cc cseqs sq.pre concl then SOME (strlit "Syzygy:check") else
          if sq.post ≠ FAtom BowLe concl (TmConst 0) then SOME (strlit "Syzygy:post")
          else NONE)) ∧
  (firstFail ws (INR ([]:certpf list)) = NONE) ∧
  (firstFail ws (INR (p::ps)) =
     case firstFail ws (INL p) of
     | SOME m => SOME m
     | NONE => firstFail ws (INR ps))
Termination
  WF_REL_TAC ‘measure (λx. case SND x of
                           | INL pf => certpf_size pf
                           | INR ps => list_size certpf_size ps)’
  >> rw[fetch "qtsl_cert" "cnode_size_def", listTheory.list_size_def]
  >> simp[]
End

Definition diagVerdict_def:
  diagVerdict (cs:char list) =
    let bytes = MAP ORD cs in
    case parseHeader bytes of
    | NONE => strlit "STAGE:header NONE\n"
    | SOME h =>
    case parseSymtab (TAKE h.symLen (DROP h.symOff bytes)) h.symLen
                     h.nWires h.payOff h.payLen of
    | NONE => strlit "STAGE:symtab NONE\n"
    | SOME ws =>
    case parseDiagram (TAKE h.diaLen (DROP h.diaOff bytes)) h.nCxs
                      h.nApps of
    | NONE => strlit "STAGE:diagram NONE\n"
    | SOME cxs =>
    case parseProofSection (TAKE h.prfLen (DROP h.prfOff bytes)) cxs
                           h.nNodes h.rootOff h.thetaRef of
    | NONE => strlit "STAGE:proof NONE\n"
    | SOME pf =>
        if checkPf ws pf then strlit "STAGE:ALL VERIFIED\n"
        else concat [strlit "STAGE:checkPf FALSE first="
                    ; (case firstFail ws (INL pf) of
                       | SOME m => m
                       | NONE => strlit "(firstFail disagrees: NONE)")
                    ; strlit "\n"]
End

val r = translate (firstFail_def
                   |> PURE_REWRITE_RULE [ml_translatorTheory.MEMBER_INTRO]);
val r = translate diagVerdict_def;

Definition diag_rev_def:
  diag_rev (rcs:char list) = diagVerdict (REVERSE rcs)
End

val r = translate diag_rev_def;

Quote add_cakeml:
  fun diagmain u =
    case TextIO.foldChars consstep [] None of
      Some rcs => TextIO.print (diag_rev rcs)
    | None => TextIO.print (diag_rev [])
End

val prog_tm = ml_progLib.get_prog (get_ml_prog_state ());
val call_tm = process_topdecs `val _ = diagmain ();`;

Definition qtsl_diag_prog_def:
  qtsl_diag_prog = ^prog_tm ++ ^call_tm
End
