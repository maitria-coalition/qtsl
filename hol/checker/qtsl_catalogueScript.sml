(*
  The rule-catalogue check functions: the first-order computational
  surface of the certificate contract (simplices, extension sets,
  barycentric-halfspace conjunctions, Farkas/syzygy leaf checks and
  their kin), ported side-by-side from the Lean development's
  Core/Catalogue module. Structures with proof fields become
  proof-field-free records; dependent function fields become lists
  read through total default-valued accessors.
*)
Theory qtsl_catalogue
Ancestors
  rat integer mlstring qtsl_dyadic qtsl_qarith
Libs
  preamble

Datatype:
  kind = KBool | KInt | KRat | KF16 | KBF16 | KF32 | KF64
End

Datatype:
  sign = Nn | Signed
End

Datatype:
  ext = ExtFin | ExtExt
End

Datatype:
  dtype = <| kind : kind ; sign : sign ; ext : ext |>
End

Datatype:
  roundmode = Rne | Rtz | Rup | Rdn | Rexact
End

Definition kindFmt_def:
  kindFmt KBool = NONE ∧
  kindFmt KInt = NONE ∧
  kindFmt KRat = NONE ∧
  kindFmt KF16 = SOME f16 ∧
  kindFmt KBF16 = SOME bf16 ∧
  kindFmt KF32 = SOME f32 ∧
  kindFmt KF64 = SOME f64
End

Definition ratMax_def:
  ratMax (a:rat) b = if a ≤ b then b else a
End

Definition kindRoundQ_def:
  kindRoundQ KBool r (q:rat) = (if q ≤ 0 then 0 else 1) ∧
  kindRoundQ KInt r q =
    (case r of
     | Rdn => rat_of_int (ratFloor q)
     | Rup => rat_of_int (ratCeil q)
     | Rtz => if 0 ≤ q then rat_of_int (ratFloor q) else rat_of_int (ratCeil q)
     | Rne => rat_of_int (roundNQ q)
     | Rexact => rat_of_int (ratFloor q)) ∧
  kindRoundQ KRat r q = q ∧
  kindRoundQ k r q =
    (case kindFmt k of
     | SOME fmt =>
       (case r of
        | Rdn => rdn fmt q
        | Rup => rup fmt q
        | Rtz => rtz fmt q
        | Rne => rne fmt q
        | Rexact => rne fmt q)
     | NONE => q)
End

Definition dtypeRoundE_def:
  dtypeRoundE dt r (q:rat) =
    case kindFmt dt.kind of
    | NONE =>
        Fin (if dt.sign = Nn then ratMax 0 (kindRoundQ dt.kind r q)
             else kindRoundQ dt.kind r q)
    | SOME fmt =>
        if dt.sign = Nn ∧ q < 0 then Fin 0
        else if dt.ext = ExtExt ∧
                ((r = Rup ∧ maxFin fmt < q) ∨
                 (r = Rne ∧ maxFin fmt + pow2i (fmt.eMax - 1) ≤ q))
        then PosInf
        else if dt.ext = ExtExt ∧
                ((r = Rdn ∧ q < -maxFin fmt) ∨
                 (r = Rne ∧ q ≤ -(maxFin fmt + pow2i (fmt.eMax - 1))))
        then NegInf
        else Fin (if dt.sign = Nn then ratMax 0 (kindRoundQ dt.kind r q)
                  else kindRoundQ dt.kind r q)
End

Definition dtB_def:
  dtB = <| kind := KBool ; sign := Nn ; ext := ExtFin |>
End
Definition dtN_def:
  dtN = <| kind := KInt ; sign := Nn ; ext := ExtFin |>
End
Definition dtZ_def:
  dtZ = <| kind := KInt ; sign := Signed ; ext := ExtFin |>
End
Definition dtQ_def:
  dtQ = <| kind := KRat ; sign := Signed ; ext := ExtFin |>
End
Definition dtQnn_def:
  dtQnn = <| kind := KRat ; sign := Nn ; ext := ExtFin |>
End
Definition dtF64_def:
  dtF64 = <| kind := KF64 ; sign := Signed ; ext := ExtExt |>
End

Type shape = “:num list”
Type wire = “:num”

Definition shapeRank_def:
  shapeRank (s:shape) = LENGTH s
End

Definition shapeTotalSize_def:
  shapeTotalSize (s:shape) = FOLDR $* 1 s
End

Datatype:
  tensortype = <| shape : shape ; dtype : dtype |>
End

Datatype:
  simpc = <| nVertices : num ; ambDim : num ;
             coord : rat list list ;
             simplices : bool list list ;
             cells : (bool list # bool list) list |>
End

Datatype:
  simplex = <| complex : simpc ; vmask : bool list |>
End

Datatype:
  extensionset = <| simplex : simplex ; emask : bool list |>
End

Datatype:
  term = TmVar num
       | TmConst rat
       | TmAdd term term
       | TmMul term term
       | TmSub term term
       | TmNeg term
       | TmIdx term num
End

Datatype:
  bowtie = BowLt | BowLe | BowEq | BowGe | BowGt | BowNe
End

Datatype:
  formula = FAtom bowtie term term
          | FInRegion term simplex extensionset
          | FAnd formula formula
          | FOr formula formula
          | FTt
          | FFf
End

Datatype:
  sequent = <| pre : formula ; post : formula |>
End

Definition simplexContainsNat_def:
  simplexContainsNat sx v =
    if v < sx.complex.nVertices then getD sx.vmask v F else F
End

Definition extContainsNat_def:
  extContainsNat es v =
    if v < es.simplex.complex.nVertices then getD es.emask v F else F
End

Definition extIsEmptyB_def:
  extIsEmptyB es =
    EVERY (λv. ¬ extContainsNat es v) (rangeL es.simplex.complex.nVertices)
End

Definition chainAnd_def:
  chainAnd [] = FTt ∧
  chainAnd [f] = f ∧
  chainAnd (f::g::rest) = FAnd f (chainAnd (g::rest))
End

Definition chainOr_def:
  chainOr [] = FFf ∧
  chainOr [f] = f ∧
  chainOr (f::g::rest) = FOr f (chainOr (g::rest))
End

Definition termToPoly_def:
  termToPoly (TmVar w) = polyVar w ∧
  termToPoly (TmConst c) = polyConst c ∧
  termToPoly (TmAdd l r) = polyAdd (termToPoly l) (termToPoly r) ∧
  termToPoly (TmMul l r) = polyMul (termToPoly l) (termToPoly r) ∧
  termToPoly (TmSub l r) = polySub (termToPoly l) (termToPoly r) ∧
  termToPoly (TmNeg t) = polyNeg (termToPoly t) ∧
  termToPoly (TmIdx t i) = polyConst 0
End

Definition termEvalQ_def:
  termEvalQ (TmVar w) = NONE ∧
  termEvalQ (TmConst c) = SOME c ∧
  termEvalQ (TmAdd l r) =
    (case termEvalQ l of NONE => NONE
     | SOME a => case termEvalQ r of NONE => NONE | SOME b => SOME (a + b)) ∧
  termEvalQ (TmMul l r) =
    (case termEvalQ l of NONE => NONE
     | SOME a => case termEvalQ r of NONE => NONE | SOME b => SOME (a * b)) ∧
  termEvalQ (TmSub l r) =
    (case termEvalQ l of NONE => NONE
     | SOME a => case termEvalQ r of NONE => NONE | SOME b => SOME (a - b)) ∧
  termEvalQ (TmNeg t) =
    (case termEvalQ t of NONE => NONE | SOME a => SOME (-a)) ∧
  termEvalQ (TmIdx t i) = NONE
End

Definition bowtieEvalQ_def:
  bowtieEvalQ BowLt (x:rat) y = (x < y) ∧
  bowtieEvalQ BowLe x y = (x ≤ y) ∧
  bowtieEvalQ BowEq x y = (x = y) ∧
  bowtieEvalQ BowGe x y = (y ≤ x) ∧
  bowtieEvalQ BowGt x y = (y < x) ∧
  bowtieEvalQ BowNe x y = (x ≠ y)
End

Definition formulaEvalClosed_def:
  formulaEvalClosed (FAtom b l r) =
    (case termEvalQ l of NONE => NONE
     | SOME x => case termEvalQ r of NONE => NONE
                 | SOME y => SOME (bowtieEvalQ b x y)) ∧
  formulaEvalClosed (FInRegion t sx es) = NONE ∧
  formulaEvalClosed (FAnd l r) =
    (case formulaEvalClosed l of NONE => NONE
     | SOME x => case formulaEvalClosed r of NONE => NONE
                 | SOME y => SOME (x ∧ y)) ∧
  formulaEvalClosed (FOr l r) =
    (case formulaEvalClosed l of NONE => NONE
     | SOME x => case formulaEvalClosed r of NONE => NONE
                 | SOME y => SOME (x ∨ y)) ∧
  formulaEvalClosed FTt = SOME T ∧
  formulaEvalClosed FFf = SOME F
End

Definition baryLambdas1D_def:
  baryLambdas1D cx dmask t =
    if cx.ambDim = 1 then
      (case FILTER (λv. getD dmask v F) (rangeL cx.nVertices) of
       | [a; b] =>
           (let v0 = getD (getD cx.coord a []) 0 (0:rat) in
            let v1 = getD (getD cx.coord b []) 0 (0:rat) in
            let den = v1 - v0 in
              if den = 0 then NONE
              else SOME
                [(a, TmAdd (TmConst (v1 / den))
                           (TmMul (TmConst (-(&1) / den)) t));
                 (b, TmAdd (TmConst (-v0 / den))
                           (TmMul (TmConst (&1 / den)) t))])
       | _ => NONE)
    else NONE
End

Definition termFreeWires_def:
  termFreeWires (TmVar w) = [w:num] ∧
  termFreeWires (TmConst c) = [] ∧
  termFreeWires (TmAdd l r) = termFreeWires l ++ termFreeWires r ∧
  termFreeWires (TmMul l r) = termFreeWires l ++ termFreeWires r ∧
  termFreeWires (TmSub l r) = termFreeWires l ++ termFreeWires r ∧
  termFreeWires (TmNeg t) = termFreeWires t ∧
  termFreeWires (TmIdx t i) = termFreeWires t
End

Definition termIdxFree_def:
  termIdxFree (TmVar w) = T ∧
  termIdxFree (TmConst c) = T ∧
  termIdxFree (TmAdd l r) = (termIdxFree l ∧ termIdxFree r) ∧
  termIdxFree (TmMul l r) = (termIdxFree l ∧ termIdxFree r) ∧
  termIdxFree (TmSub l r) = (termIdxFree l ∧ termIdxFree r) ∧
  termIdxFree (TmNeg t) = termIdxFree t ∧
  termIdxFree (TmIdx t i) = F
End

Definition termIdxBounded_def:
  termIdxBounded n (TmVar w) = T ∧
  termIdxBounded n (TmConst c) = T ∧
  termIdxBounded n (TmAdd l r) = (termIdxBounded n l ∧ termIdxBounded n r) ∧
  termIdxBounded n (TmMul l r) = (termIdxBounded n l ∧ termIdxBounded n r) ∧
  termIdxBounded n (TmSub l r) = (termIdxBounded n l ∧ termIdxBounded n r) ∧
  termIdxBounded n (TmNeg t) = termIdxBounded n t ∧
  termIdxBounded n (TmIdx t i) = (i < n ∧ termIdxBounded n t)
End

Definition formulaFreeWires_def:
  formulaFreeWires (FAtom b l r) = termFreeWires l ++ termFreeWires r ∧
  formulaFreeWires (FInRegion t sx es) = termFreeWires t ∧
  formulaFreeWires (FAnd l r) = formulaFreeWires l ++ formulaFreeWires r ∧
  formulaFreeWires (FOr l r) = formulaFreeWires l ++ formulaFreeWires r ∧
  formulaFreeWires FTt = [] ∧
  formulaFreeWires FFf = []
End

Definition termVarHead_def:
  termVarHead (TmVar w) = SOME w ∧
  termVarHead _ = NONE
End

Definition termSubst_def:
  termSubst w t (TmVar w') = (if w' = w then t else TmVar w') ∧
  termSubst w t (TmConst c) = TmConst c ∧
  termSubst w t (TmAdd l r) = TmAdd (termSubst w t l) (termSubst w t r) ∧
  termSubst w t (TmMul l r) = TmMul (termSubst w t l) (termSubst w t r) ∧
  termSubst w t (TmSub l r) = TmSub (termSubst w t l) (termSubst w t r) ∧
  termSubst w t (TmNeg u) = TmNeg (termSubst w t u) ∧
  termSubst w t (TmIdx u i) = TmIdx (termSubst w t u) i
End

Definition formulaSubst_def:
  formulaSubst w t (FAtom b l r) =
    FAtom b (termSubst w t l) (termSubst w t r) ∧
  formulaSubst w t (FInRegion u sx es) = FInRegion (termSubst w t u) sx es ∧
  formulaSubst w t (FAnd l r) =
    FAnd (formulaSubst w t l) (formulaSubst w t r) ∧
  formulaSubst w t (FOr l r) =
    FOr (formulaSubst w t l) (formulaSubst w t r) ∧
  formulaSubst w t FTt = FTt ∧
  formulaSubst w t FFf = FFf
End

Definition atomicCompareFormB_def:
  atomicCompareFormB b l r fm ⇔ fm = FAtom b l r
End

Definition atomicCompareZeroB_def:
  atomicCompareZeroB b l r fm ⇔ fm = FAtom b (TmSub l r) (TmConst 0)
End

Definition substituteInFormulaB_def:
  substituteInFormulaB fm w t fm' ⇔ fm' = formulaSubst w t fm
End

Definition baryCoeffs1D_def:
  baryCoeffs1D cx dmask =
    if cx.ambDim = 1 then
      (case FILTER (λv. getD dmask v F) (rangeL cx.nVertices) of
       | [a; b] =>
           (let v0 = getD (getD cx.coord a []) 0 (0:rat) in
            let v1 = getD (getD cx.coord b []) 0 (0:rat) in
            let den = v1 - v0 in
              if den = 0 then NONE
              else SOME [(a, v1 / den, -(&1) / den);
                         (b, -v0 / den, &1 / den)])
       | _ => NONE)
    else NONE
End

Definition intAbsNum_def:
  intAbsNum (i:int) = if i < 0 then Num (-i) else Num i
End

Definition primAffine_def:
  primAffine (s:rat) (c:rat) =
    if c = 0 then
      ((if s < 0 then -1 else if s = 0 then 0 else 1) : rat, 0:rat)
    else
      let l = lcm (RATD s) (RATD c) in
      let g = gcd (intAbsNum (RATN s * &(l DIV RATD s)))
                  (intAbsNum (RATN c * &(l DIV RATD c))) in

      let k = if &g = (0:rat) then 0 else &l / &g in
        (k * s, k * c)
End

Definition f4Lhs_def:
  f4Lhs (s':rat) (c':rat) t =
    if c' = 0 then TmMul (TmConst s') t
    else TmAdd (TmMul (TmConst s') t) (TmConst c')
End

Definition f4VertexAtom_def:
  f4VertexAtom inS (off:rat) (slp:rat) t =
    let sc = if inS then primAffine slp off else primAffine (-slp) (-off) in
      FAtom BowLe (f4Lhs (FST sc) (SND sc) t) (TmConst 0)
End

Definition barycentricHalfspaceBuild_def:
  barycentricHalfspaceBuild t sx es =
    if es.simplex = sx then
      (case baryCoeffs1D sx.complex sx.vmask of
       | NONE => NONE
       | SOME cs =>
         (case MAP (λ(v,off,slp). f4VertexAtom (extContainsNat es v) off slp t)
               cs of
          | [x; y] => SOME (FAnd x y)
          | _ => NONE))
    else NONE
End

Definition barycentricHalfspaceFormB_def:
  barycentricHalfspaceFormB t sx es fm ⇔
    barycentricHalfspaceBuild t sx es = SOME fm
End

Definition predicateHole_def:
  predicateHole = 4294967295n
End

Definition applyPredicateToTermB_def:
  applyPredicateToTermB p arg fm ⇔ fm = formulaSubst predicateHole arg p
End

Datatype:
  predclass = <| conic : bool ; upClosed : bool |>
End

Definition bowtieFlip_def:
  bowtieFlip BowLt = BowGt ∧
  bowtieFlip BowLe = BowGe ∧
  bowtieFlip BowGe = BowLe ∧
  bowtieFlip BowGt = BowLt ∧
  bowtieFlip BowEq = BowEq ∧
  bowtieFlip BowNe = BowNe
End

Definition parseHoleSide_def:
  parseHoleSide (TmVar w) =
    (if w = predicateHole then SOME (&1 :rat) else NONE) ∧
  parseHoleSide (TmMul (TmConst a) (TmVar w)) =
    (if w = predicateHole ∧ 0 < a then SOME a else NONE) ∧
  parseHoleSide (TmMul (TmVar w) (TmConst a)) =
    (if w = predicateHole ∧ 0 < a then SOME a else NONE) ∧
  parseHoleSide _ = NONE
End

Definition classifyOriented2_def:
  classifyOriented2 b l r =
    case parseHoleSide r of
    | NONE => NONE
    | SOME _ =>
      (case termEvalQ l of
       | NONE => NONE
       | SOME c => SOME (bowtieFlip b, c))
End

Definition classifyOriented_def:
  classifyOriented b l r =
    case parseHoleSide l of
    | NONE => classifyOriented2 b l r
    | SOME _ =>
      (case termEvalQ r of
       | NONE => classifyOriented2 b l r
       | SOME c => SOME (b, c))
End

Definition classifyPredAtom_def:
  classifyPredAtom (FAtom b l r) =
    (case classifyOriented b l r of
     | SOME (BowGe, c) => SOME <| conic := (c = 0) ; upClosed := T |>
     | SOME (BowLe, c) => SOME <| conic := (c = 0) ; upClosed := F |>
     | SOME (BowEq, c) =>
         (if c = 0 then SOME <| conic := T ; upClosed := F |> else NONE)
     | _ => NONE) ∧
  classifyPredAtom _ = NONE
End

Definition classifyPred_def:
  classifyPred (FAnd l r) =
    (case classifyPred l of
     | NONE => NONE
     | SOME a =>
       (case classifyPred r of
        | NONE => NONE
        | SOME b => SOME <| conic := (a.conic ∧ b.conic) ;
                            upClosed := (a.upClosed ∧ b.upClosed) |>)) ∧
  classifyPred fm = classifyPredAtom fm
End

Definition isConicPredicateB_def:
  isConicPredicateB p = case classifyPred p of SOME c => c.conic | NONE => F
End

Definition isConvexPredicateB_def:
  isConvexPredicateB p = IS_SOME (classifyPred p)
End

Definition isUpwardClosedConicPredicateB_def:
  isUpwardClosedConicPredicateB p =
    case classifyPred p of SOME c => (c.conic ∧ c.upClosed) | NONE => F
End

Definition polynomialCanonicalEqB_def:
  polynomialCanonicalEqB l r ⇔
    termIdxFree l ∧ termIdxFree r ∧ termToPoly l = termToPoly r
End

Definition satisfiesPredQ_def:
  satisfiesPredQ p (c:rat) =
    (formulaEvalClosed (formulaSubst predicateHole (TmConst c) p) = SOME T)
End

Definition termAsCoordPolyIdx_def:
  termAsCoordPolyIdx (TmVar w) = NONE ∧
  termAsCoordPolyIdx (TmConst c) = SOME (polyConst c) ∧
  termAsCoordPolyIdx (TmAdd l r) =
    (case termAsCoordPolyIdx l of NONE => NONE
     | SOME a => case termAsCoordPolyIdx r of NONE => NONE
                 | SOME b => SOME (polyAdd a b)) ∧
  termAsCoordPolyIdx (TmMul l r) =
    (case termAsCoordPolyIdx l of NONE => NONE
     | SOME a => case termAsCoordPolyIdx r of NONE => NONE
                 | SOME b => SOME (polyMul a b)) ∧
  termAsCoordPolyIdx (TmSub l r) =
    (case termAsCoordPolyIdx l of NONE => NONE
     | SOME a => case termAsCoordPolyIdx r of NONE => NONE
                 | SOME b => SOME (polySub a b)) ∧
  termAsCoordPolyIdx (TmNeg t) =
    (case termAsCoordPolyIdx t of NONE => NONE | SOME a => SOME (polyNeg a)) ∧
  termAsCoordPolyIdx (TmIdx (TmVar w) i) = SOME (polyVar i) ∧
  termAsCoordPolyIdx (TmIdx t i) = NONE
End

Definition termAsCoordPoly_def:
  termAsCoordPoly t =
    if termIdxFree t then
      (let p = termToPoly t in
       case polyVars p of
       | [] => SOME p
       | [v] => SOME (MAP (λ(m,c). (MAP (λ(vv,e). (0:num,e)) m, c)) p)
       | _ => NONE)
    else termAsCoordPolyIdx t
End

Definition bernConeCoeffCheck_def:
  bernConeCoeffCheck sx es dg pl pr =
    if es.simplex = sx then
      (let cx = sx.complex in
       let verts = FILTER (λv. simplexContainsNat sx v) (rangeL cx.nVertices) in
       if LENGTH verts = cx.ambDim + 1 then
         (case termAsCoordPoly pl of
          | NONE => F
          | SOME p =>
            if termIdxFree pl then
              (if polyVars p ≠ [] ∧ cx.ambDim ≠ 1 then F
               else
                 let coords = MAP (λv. MAP (λj. getD (getD cx.coord v []) j (0:rat))
                                           (rangeL cx.ambDim)) verts in
                 let smask = MAP (λv. extContainsNat es v) verts in
                 case fdBernstein coords smask dg p of
                 | SOME table => gridAll (satisfiesPredQ pr) table
                 | NONE => F)
            else
              (if extIsEmptyB es ∧ termIdxBounded cx.ambDim pl then
                 (let coords = MAP (λv. MAP (λj. getD (getD cx.coord v []) j (0:rat))
                                            (rangeL cx.ambDim)) verts in
                  let smask = MAP (λv. extContainsNat es v) verts in
                  case fdBernstein coords smask dg p of
                  | SOME table => gridAll (satisfiesPredQ pr) table
                  | NONE => F)
               else F))
       else F)
    else F
End

Definition bernConeIntvCheck_def:
  bernConeIntvCheck sx es dg pl pr dt =
    if es.simplex = sx then
      (let cx = sx.complex in
       let verts = FILTER (λv. simplexContainsNat sx v) (rangeL cx.nVertices) in
       if LENGTH verts = cx.ambDim + 1 then
         (case termAsCoordPoly pl of
          | NONE => F
          | SOME p =>
            if ¬ termIdxFree pl then F
            else if polyVars p ≠ [] ∧ cx.ambDim ≠ 1 then F
            else
              let coords = MAP (λv. MAP (λj. getD (getD cx.coord v []) j (0:rat))
                                        (rangeL cx.ambDim)) verts in
              let smask = MAP (λv. extContainsNat es v) verts in
              case fdBernstein coords smask dg p of
              | SOME table =>
                  gridAll (λc. case dtypeRoundE dt Rdn c of
                               | Fin lo => (lo ≤ c ∧ satisfiesPredQ pr lo)
                               | _ => F) table
              | NONE => F)
       else F)
    else F
End

Definition conjunctList_def:
  conjunctList (FAnd l r) = conjunctList l ++ conjunctList r ∧
  conjunctList fm = [fm]
End

Definition atomLeZeroPolys_def:
  atomLeZeroPolys (FAtom BowLe l r) = [polySub (termToPoly l) (termToPoly r)] ∧
  atomLeZeroPolys (FAtom BowLt l r) = [polySub (termToPoly l) (termToPoly r)] ∧
  atomLeZeroPolys (FAtom BowGe l r) = [polySub (termToPoly r) (termToPoly l)] ∧
  atomLeZeroPolys (FAtom BowGt l r) = [polySub (termToPoly r) (termToPoly l)] ∧
  atomLeZeroPolys (FAtom BowEq l r) = [polySub (termToPoly l) (termToPoly r);
                                       polySub (termToPoly r) (termToPoly l)] ∧
  atomLeZeroPolys _ = []
End

Definition farkasEntries_def:
  farkasEntries (TmConst c) = (if c = 0 then SOME [] else NONE) ∧
  farkasEntries (TmAdd (TmMul (TmConst l) e) rest) =
    (case farkasEntries rest of
     | NONE => NONE
     | SOME es => SOME ((l,e)::es)) ∧
  farkasEntries _ = NONE
End

Definition atomSidesIdxFree_def:
  atomSidesIdxFree (FAtom b l r) = (termIdxFree l ∧ termIdxFree r) ∧
  atomSidesIdxFree _ = T
End

Definition farkasCheckCore_def:
  farkasCheckCore cc premise conclusion =
    case farkasEntries cc of
    | NONE => F
    | SOME entries =>
        (let atoms = conjunctList premise in
         termIdxFree conclusion ∧
         EVERY (λ(l,e).
           0 ≤ l ∧
           EXISTS (λa. atomSidesIdxFree a ∧
                       EXISTS (λpa. pa = termToPoly e) (atomLeZeroPolys a))
                  atoms) entries ∧
         (FOLDR (λ(l,e) acc. polyAdd (polyScale l (termToPoly e)) acc)
                [] entries =
          termToPoly conclusion))
End

Definition wireCoordKey_def:
  wireCoordKey (w:num) (i:num) =
    if w < i then i * i + w else w * w + w + i
End

Definition asCoordPolyIdxW_def:
  asCoordPolyIdxW (TmVar w) = NONE ∧
  asCoordPolyIdxW (TmConst c) = SOME (polyConst c) ∧
  asCoordPolyIdxW (TmAdd l r) =
    (case asCoordPolyIdxW l of NONE => NONE | SOME pl =>
     case asCoordPolyIdxW r of NONE => NONE | SOME pr =>
       SOME (polyAdd pl pr)) ∧
  asCoordPolyIdxW (TmMul l r) =
    (case asCoordPolyIdxW l of NONE => NONE | SOME pl =>
     case asCoordPolyIdxW r of NONE => NONE | SOME pr =>
       SOME (polyMul pl pr)) ∧
  asCoordPolyIdxW (TmSub l r) =
    (case asCoordPolyIdxW l of NONE => NONE | SOME pl =>
     case asCoordPolyIdxW r of NONE => NONE | SOME pr =>
       SOME (polySub pl pr)) ∧
  asCoordPolyIdxW (TmNeg t) =
    (case asCoordPolyIdxW t of NONE => NONE | SOME p =>
       SOME (polyNeg p)) ∧
  asCoordPolyIdxW (TmIdx t i) =
    (case t of
     | TmVar w => SOME (polyVar (wireCoordKey w i))
     | _ => NONE)
End

Definition atomLeZeroPolysW_def:
  atomLeZeroPolysW (FAtom b l r) =
    (case asCoordPolyIdxW l of NONE => [] | SOME pl =>
     case asCoordPolyIdxW r of NONE => [] | SOME pr =>
       (case b of
        | BowLe => [polySub pl pr]
        | BowLt => [polySub pl pr]
        | BowGe => [polySub pr pl]
        | BowGt => [polySub pr pl]
        | BowEq => [polySub pl pr; polySub pr pl]
        | BowNe => [])) ∧
  atomLeZeroPolysW _ = []
End

Definition farkasEntriesW_def:
  farkasEntriesW ([]:(rat # term) list) = SOME ([]:(rat # poly) list) ∧
  farkasEntriesW ((l,e)::rest) =
    (case asCoordPolyIdxW e of NONE => NONE | SOME pe =>
     case farkasEntriesW rest of NONE => NONE | SOME ps =>
       SOME ((l,pe)::ps))
End

Definition farkasCheckW_def:
  farkasCheckW cc premise conclusion =
    case farkasEntries cc of NONE => F | SOME entries =>
    case farkasEntriesW entries of NONE => F | SOME pentries =>
    case asCoordPolyIdxW conclusion of NONE => F | SOME pc =>
      (let atoms = conjunctList premise in
       EVERY (λ(l,pe).
         0 ≤ l ∧
         EXISTS (λa. EXISTS (λpa. pa = pe) (atomLeZeroPolysW a)) atoms)
             pentries ∧
       (FOLDR (λ(l,pe) acc. polyAdd (polyScale l pe) acc) [] pentries =
        pc))
End

Definition farkasCheck_def:
  farkasCheck cc premise conclusion ⇔
    farkasCheckCore cc premise conclusion ∨
    farkasCheckW cc premise conclusion
End

Datatype:
  conjpath = CPHere | CPLeft conjpath | CPRight conjpath
End

Definition conjGet_def:
  conjGet fm CPHere = SOME fm ∧
  conjGet fm (CPLeft p) =
    (case fm of FAnd l r => conjGet l p | _ => NONE) ∧
  conjGet fm (CPRight p) =
    (case fm of FAnd l r => conjGet r p | _ => NONE)
Termination
  WF_REL_TAC ‘measure (conjpath_size o SND)’ >> rw[]
End

Definition conjReplace_def:
  conjReplace fm CPHere g = SOME g ∧
  conjReplace fm (CPLeft p) g =
    (case fm of
     | FAnd l r =>
        (case conjReplace l p g of
         | NONE => NONE
         | SOME l' => SOME (FAnd l' r))
     | _ => NONE) ∧
  conjReplace fm (CPRight p) g =
    (case fm of
     | FAnd l r =>
        (case conjReplace r p g of
         | NONE => NONE
         | SOME r' => SOME (FAnd l r'))
     | _ => NONE)
Termination
  WF_REL_TAC ‘measure (conjpath_size o FST o SND)’ >> rw[]
End

Definition isEqAtom_def:
  isEqAtom (FAtom BowEq l r) = T ∧
  isEqAtom _ = F
End

Definition syzygyCheckCore_def:
  syzygyCheckCore cc components premise conclusion =
    case farkasEntries cc of
    | NONE => F
    | SOME entries =>
        termIdxFree conclusion ∧
        EVERY (λ(l,e).
          0 ≤ l ∧
          (EXISTS (λc. atomSidesIdxFree c.post ∧
                       EXISTS (λpa. pa = termToPoly e) (atomLeZeroPolys c.post))
                  components ∨
           EXISTS (λa. isEqAtom a ∧ atomSidesIdxFree a ∧
                       EXISTS (λpa. pa = termToPoly e) (atomLeZeroPolys a))
                  (conjunctList premise))) entries ∧
        (FOLDR (λ(l,e) acc. polyAdd (polyScale l (termToPoly e)) acc)
               [] entries =
         termToPoly conclusion)
End

Definition syzygyCheckW_def:
  syzygyCheckW cc components premise conclusion =
    case farkasEntries cc of NONE => F | SOME entries =>
    case farkasEntriesW entries of NONE => F | SOME pentries =>
    case asCoordPolyIdxW conclusion of NONE => F | SOME pc =>
      EVERY (λ(l,pe).
        0 ≤ l ∧
        (EXISTS (λc. EXISTS (λpa. pa = pe) (atomLeZeroPolysW c.post))
                components ∨
         EXISTS (λa. isEqAtom a ∧
                     EXISTS (λpa. pa = pe) (atomLeZeroPolysW a))
                (conjunctList premise))) pentries ∧
      (FOLDR (λ(l,pe) acc. polyAdd (polyScale l pe) acc) [] pentries =
       pc)
End

Definition syzygyCheck_def:
  syzygyCheck cc components premise conclusion ⇔
    syzygyCheckCore cc components premise conclusion ∨
    syzygyCheckW cc components premise conclusion
End

Definition extInterval1D_def:
  extInterval1D es =
    if es.simplex.complex.ambDim = 1 then
      (if extIsEmptyB es then
         (case FILTER (λv. simplexContainsNat es.simplex v)
                      (rangeL es.simplex.complex.nVertices) of
          | [a; b] =>
              (let v0 = getD (getD es.simplex.complex.coord a []) 0 (0:rat) in
               let v1 = getD (getD es.simplex.complex.coord b []) 0 (0:rat) in
               if v0 < v1 then SOME (v0, v1)
               else if v1 < v0 then SOME (v1, v0)
               else NONE)
          | _ => NONE)
       else NONE)
    else NONE
End

Definition coverExtendPass_def:
  coverExtendPass ivs (r:rat) =
    FOLDL (λr iv. if FST iv ≤ r ∧ r < SND iv then SND iv else r) r ivs
End

Definition coverReach_def:
  coverReach 0 ivs (r:rat) = r ∧
  coverReach (SUC n) ivs r = coverReach n ivs (coverExtendPass ivs r)
End

Definition coverChainCheck_def:
  coverChainCheck ivs (lo:rat) hi = (hi ≤ coverReach (LENGTH ivs) ivs lo)
End

Definition coverCheck_def:
  coverCheck sx es branches =
    case extInterval1D es of
    | NONE => F
    | SOME (lo, hi) =>
        (es.simplex = sx ∧
         EVERY (λ(bsx,bes). bes.simplex = bsx ∧ IS_SOME (extInterval1D bes))
               branches ∧
         coverChainCheck
           (FLAT (MAP (λ(bsx,bes). case extInterval1D bes of
                                   | NONE => []
                                   | SOME iv => [iv]) branches))
           lo hi)
End

Definition cxB_def:
  cxB = <| nVertices := 2 ; ambDim := 1 ;
           coord := [[&1]; [&2]] ;
           simplices := [[T;T]; [T;F]; [F;T]] ;
           cells := [] |>
End

Definition simplexB_def:
  simplexB = <| complex := cxB ; vmask := [T;T] |>
End

Definition Sempty_def:
  Sempty = <| simplex := simplexB ; emask := [F;F] |>
End

Definition demoW0_def:
  demoW0 = TmVar 0
End

Definition polyB_def:
  polyB = TmAdd (TmConst ((&1:rat) / &2)) (TmMul (TmConst 2) demoW0)
End

Definition predP1_def:
  predP1 = FAtom BowGe (TmVar predicateHole) (TmConst 0)
End

Definition simplexPt_def:
  simplexPt = <| complex := cxB ; vmask := [T;F] |>
End

Definition SemptyPt_def:
  SemptyPt = <| simplex := simplexPt ; emask := [F;F] |>
End

Definition cxL_def:
  cxL = <| nVertices := 2 ; ambDim := 1 ;
           coord := [[&1]; [(&3:rat) / &2]] ;
           simplices := [[T;T]; [T;F]; [F;T]] ;
           cells := [] |>
End
Definition simplexL_def:
  simplexL = <| complex := cxL ; vmask := [T;T] |>
End
Definition SemptyL_def:
  SemptyL = <| simplex := simplexL ; emask := [F;F] |>
End

Definition cxR_def:
  cxR = <| nVertices := 2 ; ambDim := 1 ;
           coord := [[(&3:rat) / &2]; [&2]] ;
           simplices := [[T;T]; [T;F]; [F;T]] ;
           cells := [] |>
End
Definition simplexR_def:
  simplexR = <| complex := cxR ; vmask := [T;T] |>
End
Definition SemptyR_def:
  SemptyR = <| simplex := simplexR ; emask := [F;F] |>
End

Definition cxG_def:
  cxG = <| nVertices := 2 ; ambDim := 1 ;
           coord := [[&1]; [(&4:rat) / &3]] ;
           simplices := [[T;T]; [T;F]; [F;T]] ;
           cells := [] |>
End
Definition simplexG_def:
  simplexG = <| complex := cxG ; vmask := [T;T] |>
End
Definition SemptyG_def:
  SemptyG = <| simplex := simplexG ; emask := [F;F] |>
End

Definition SextB_def:
  SextB = <| simplex := simplexB ; emask := [T;F] |>
End

Definition subBranches_def:
  subBranches = [(simplexL, SemptyL); (simplexR, SemptyR)]
End

Definition creceipts_def:
  creceipts =
    [ (strlit "bernConeCoeffCheck (branch B)",
       bernConeCoeffCheck simplexB Sempty 1 polyB predP1) ;
      (strlit "mutant goal_tightened_minus5 rejected",
       ¬ bernConeCoeffCheck simplexB Sempty 1
           (TmAdd (TmConst (-&5)) (TmMul (TmConst 2) demoW0)) predP1) ;
      (strlit "mutant wrong_dynamics_sign rejected",
       ¬ bernConeCoeffCheck simplexB Sempty 1
           (TmAdd (TmConst ((&1:rat) / &2)) (TmMul (TmConst (-&2)) demoW0))
           predP1) ;
      (strlit "mutant degree_lie_off_by_one rejected",
       ¬ bernConeCoeffCheck simplexB Sempty 1 (TmMul demoW0 demoW0) predP1) ;
      (strlit "mutant nonconvex_predicate rejected",
       ¬ isConvexPredicateB
           (FOr (FAtom BowGe (TmVar predicateHole) (TmConst 1))
                (FAtom BowLe (TmVar predicateHole) (TmConst 0)))) ;
      (strlit "mutant corrupted-simplex (sub-dimensional) rejected",
       ¬ bernConeCoeffCheck simplexPt SemptyPt 1 polyB predP1) ;
      (strlit "barycentricHalfspaceForm (canonical conjunction)",
       barycentricHalfspaceBuild demoW0 simplexB Sempty =
       SOME (FAnd (FAtom BowGe (TmAdd (TmConst 2)
                                      (TmMul (TmConst (-&1)) demoW0))
                          (TmConst 0))
                  (FAtom BowGe (TmAdd (TmConst (-&1))
                                      (TmMul (TmConst 1) demoW0))
                          (TmConst 0)))) ;
      (strlit "farkasCheck (lambda = 1 re-canonicalization)",
       farkasCheck
         (TmAdd (TmMul (TmConst 1) (TmSub demoW0 (TmConst 2))) (TmConst 0))
         (FAtom BowLe demoW0 (TmConst 2))
         (TmSub demoW0 (TmConst 2))) ;
      (strlit "polynomialCanonicalEq (w0+w0 = 2*w0)",
       polynomialCanonicalEqB (TmAdd demoW0 demoW0)
                              (TmMul (TmConst 2) demoW0)) ;
      (strlit "polynomialCanonicalEq scale-preserving (F7) rejected",
       ¬ polynomialCanonicalEqB (TmMul (TmConst 2) demoW0) demoW0) ;
      (strlit "bernConeIntvCheck f64 (exact-dyadic accepts)",
       bernConeIntvCheck simplexB Sempty 1 polyB predP1 dtF64) ;
      (strlit "bernConeIntvCheck f64 (pred >= 5/2 accepts)",
       bernConeIntvCheck simplexB Sempty 1 polyB
         (FAtom BowGe (TmVar predicateHole) (TmConst ((&5:rat) / &2)))
         dtF64) ;
      (strlit "bernConeIntvCheck f64 (pred >= 5/2+1/3 rejects)",
       ¬ bernConeIntvCheck simplexB Sempty 1 polyB
           (FAtom BowGe (TmVar predicateHole)
                  (TmConst ((&5:rat) / &2 + (&1:rat) / &3)))
           dtF64) ;

      (strlit "coverCheck [1,3/2]u[3/2,2] over [1,2]",
       coverCheck simplexB Sempty subBranches) ;
      (strlit "coverCheck mutant gap (4/3, 3/2) rejected",
       ¬ coverCheck simplexB Sempty [(simplexG, SemptyG); (simplexR, SemptyR)]) ;
      (strlit "coverCheck mutant point-supported branch rejected",
       ¬ coverCheck simplexB Sempty [(simplexPt, SemptyPt)]) ;
      (strlit "coverCheck mutant ray parent (S <> empty) rejected",
       ¬ coverCheck simplexB SextB subBranches) ;
      (strlit "coverCheck mutant untied branch simplices rejected",
       ¬ coverCheck simplexB Sempty [(simplexR, SemptyL); (simplexL, SemptyR)]) ;
      (strlit "roundE ext saturation (+inf at 2^2000, rup)",
       eratEq (dtypeRoundE dtF64 Rup (&(2 ** 2000))) PosInf) ;

      (strlit "roundE int nn clamp: N.rdn(-3/2) = 0",
       eratEq (dtypeRoundE dtN Rdn (-((&3:rat) / &2))) (Fin 0)) ;

      (strlit "syzygyCheck accept (component + eq-premise)",
       syzygyCheck
         (TmAdd (TmMul (TmConst 1) (TmSub demoW0 (TmConst 2)))
           (TmAdd (TmMul (TmConst 1) (TmSub (TmVar 1) (TmConst 3)))
             (TmConst 0)))
         [<| pre := FTt ; post := FAtom BowLe demoW0 (TmConst 2) |>]
         (FAtom BowEq (TmVar 1) (TmConst 3))
         (TmSub (TmAdd demoW0 (TmVar 1)) (TmConst 5))) ;

      (strlit "syzygyCheck rejects ineq premise atom as entry source",
       ¬ syzygyCheck
           (TmAdd (TmMul (TmConst 1) (TmSub demoW0 (TmConst 2)))
             (TmAdd (TmMul (TmConst 1) (TmSub (TmVar 1) (TmConst 3)))
               (TmConst 0)))
           [<| pre := FTt ; post := FAtom BowLe demoW0 (TmConst 2) |>]
           (FAtom BowLe (TmVar 1) (TmConst 3))
           (TmSub (TmAdd demoW0 (TmVar 1)) (TmConst 5))) ;

      (strlit "syzygyCheck rejects negative weight",
       ¬ syzygyCheck
           (TmAdd (TmMul (TmConst (-&1)) (TmSub demoW0 (TmConst 2)))
             (TmConst 0))
           [<| pre := FTt ; post := FAtom BowLe demoW0 (TmConst 2) |>]
           FTt
           (TmSub (TmConst 2) demoW0))
    ]
End

Definition creceipts_string_def:
  creceipts_string =
    concat (MAP receipt_line creceipts ++
            [if EVERY SND creceipts then strlit "== ALL CATALOGUE CHECKS PASS ==\n"
             else strlit "== CATALOGUE FAILURES PRESENT ==\n"])
End

