import Qtsl.Wire

/-!
# The first-order certificate checker

`checkProof H t` decides, per node, exactly the propositional fields of
the corresponding rule payload — the same propositions a `ProofObject`
elaboration would establish, run through the same `Decidable` instances
and check functions. Field-for-field correspondence is the audit
surface: each `req` line names the payload field it decides. Rule
coverage: all wire tags, with disjunction elimination checked in its
context-carrying form.
-/

namespace PPLC
namespace Wire

def req (rule which : String) (p : Prop) [Decidable p] : R Unit :=
  if p then pure () else throw (.obligation rule which)

def wiresPosOn (H : Hypernet) (ws : List Wire) : Prop :=
  ∀ w ∈ ws, ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape

instance (H : Hypernet) (ws : List Wire) : Decidable (wiresPosOn H ws) :=
  inferInstanceAs (Decidable (∀ w ∈ ws, _))

instance (f : Formula) (iface : List Wire) :
    Decidable (formulaWiresWithin f iface) :=
  inferInstanceAs (Decidable (∀ w ∈ f.freeWires, w ∈ iface))

instance (left ctx post : Formula) (iface : List Wire) :
    Decidable (wiresSeparated left ctx post iface) :=
  inferInstanceAs (Decidable (∀ w ∈ left.freeWires,
    (w ∈ ctx.freeWires ∨ w ∈ post.freeWires) → w ∈ iface))

instance (pre sub : Formula) : Decidable (premiseContains pre sub) :=
  inferInstanceAs (Decidable (∀ a ∈ sub.conjunctList, a ∈ pre.conjunctList))

instance (cc : Term) (components : List Sequent) (premise : Formula)
    (conclusion : Term) :
    Decidable (syzygyCombinationValid cc components premise conclusion) :=
  inferInstanceAs (Decidable (_ = true))

def syzygyConclusionFormCheck (conclusion : Term) (F : Formula) : Prop :=
  F = .atom .le conclusion (.const 0)
  ∨ (match conclusion with
     | .neg e => F = .atom .ge e (.const 0)
     | _ => False)
  ∨ (match conclusion with
     | .sub l r => F = .atom .le l r
     | _ => False)

instance (conclusion : Term) (F : Formula) :
    Decidable (syzygyConclusionFormCheck conclusion F) := by
  unfold syzygyConclusionFormCheck
  cases conclusion <;> (dsimp only; infer_instance)

theorem syzygyConclusionForm_iff_check (conclusion : Term) (F : Formula) :
    syzygyConclusionForm conclusion F ↔
      syzygyConclusionFormCheck conclusion F := by
  unfold syzygyConclusionForm syzygyConclusionFormCheck
  cases conclusion <;> simp [and_assoc]

instance (conclusion : Term) (F : Formula) :
    Decidable (syzygyConclusionForm conclusion F) :=
  decidable_of_iff _ (syzygyConclusionForm_iff_check conclusion F).symm

mutual

/-- Per-node payload checking over a parsed proof tree: decides exactly
the propositional fields of each rule payload. -/
def checkProof (H : Hypernet) : PTree → R Unit
  | .mk seq k => do
    match k with
    | .ax =>
      req "ax" "preEqPost" (seq.pre = seq.post)
    | .weaken premise extra => do
      checkProof H premise
      let p := premise.concludes
      req "weaken" "preEq" (seq.pre = .and p.pre extra)
      req "weaken" "postEq" (seq.post = p.post)
    | .cut cutFormula left right => do
      checkProof H left
      checkProof H right
      let l := left.concludes ; let r := right.concludes
      req "cut" "preEq" (seq.pre = l.pre)
      req "cut" "postEq" (seq.post = r.post)
      req "cut" "cutLeft" (l.post = cutFormula)
      req "cut" "cutRight" (r.pre = .and l.pre cutFormula)
    | .andI left right => do
      checkProof H left
      checkProof H right
      let l := left.concludes ; let r := right.concludes
      req "andI" "preMatch" (l.pre = r.pre)
      req "andI" "preEq" (seq.pre = l.pre)
      req "andI" "postEq" (seq.post = .and l.post r.post)
    | .andE which premise other => do
      checkProof H premise
      let p := premise.concludes
      req "andE" "preEq" (seq.pre = p.pre)
      match which with
      | .left  => req "andE" "postEq(left)"  (p.post = .and seq.post other)
      | .right => req "andE" "postEq(right)" (p.post = .and other seq.post)
    | .orI which premise other => do
      checkProof H premise
      let p := premise.concludes
      req "orI" "preEq" (seq.pre = p.pre)
      match which with
      | .left  => req "orI" "postEq(left)"  (seq.post = .or p.post other)
      | .right => req "orI" "postEq(right)" (seq.post = .or other p.post)
    | .orE left right path => do
      checkProof H left
      checkProof H right

      let l := left.concludes ; let r := right.concludes
      match hget : seq.pre.conjGet? path with
      | some (.or d₁ d₂) => do
        req "orE" "leftPre"  (seq.pre.conjReplace? path d₁ = some l.pre)
        req "orE" "rightPre" (seq.pre.conjReplace? path d₂ = some r.pre)
        req "orE" "leftPost"  (l.post = seq.post)
        req "orE" "rightPost" (r.post = seq.post)
      | _ => throw (.obligation "orE" "pathReads (path must address a disjunction)")
    | .eqElim eqProof bodyProof wire termT termU bodyForm => do
      checkProof H eqProof
      checkProof H bodyProof
      let e := eqProof.concludes ; let b := bodyProof.concludes
      req "eqElim" "preEq" (seq.pre = e.pre)
      req "eqElim" "preMatch" (e.pre = b.pre)
      req "eqElim" "eqPost" (e.post = .atom .eq termT termU)
      req "eqElim" "tyEq"
        (∃ s, termT.bshape H = some s ∧ termU.bshape H = some s)
      req "eqElim" "bodySubT" (substituteInFormula bodyForm wire termT b.post)
      req "eqElim" "conclSubU" (substituteInFormula bodyForm wire termU seq.post)
    | .convIntro premise term simplex S => do
      checkProof H premise
      let p := premise.concludes
      req "convIntro" "preEq" (seq.pre = p.pre)
      req "convIntro" "termShape" (term.bshape H = some [simplex.complex.ambDim])
      req "convIntro" "halfspace" (barycentricHalfspaceForm term simplex S p.post)
      req "convIntro" "postEq" (seq.post = .inRegion term simplex S)
    | .convElim premise term simplex S => do
      checkProof H premise
      let p := premise.concludes
      req "convElim" "preEq" (seq.pre = p.pre)
      req "convElim" "premiseForm" (p.post = .inRegion term simplex S)
      req "convElim" "halfspace" (barycentricHalfspaceForm term simplex S seq.post)
    | .arithAtom dir premise termL termR b => do
      checkProof H premise
      let p := premise.concludes
      req "arithAtom" "notNE" (b ≠ .ne)
      req "arithAtom" "preEq" (seq.pre = p.pre)
      match dir with
      | .left => do
        req "arithAtom" "premiseIsZero" (atomicCompareZero b termL termR p.post)
        req "arithAtom" "conclIsDirect" (atomicCompareForm b termL termR seq.post)
      | .right => do
        req "arithAtom" "premiseIsDirect" (atomicCompareForm b termL termR p.post)
        req "arithAtom" "conclIsZero" (atomicCompareZero b termL termR seq.post)
    | .bernCone regionProof termX simplex S degree polynomial predicate => do
      checkProof H regionProof
      let rp := regionProof.concludes
      req "bernCone" "preEq" (seq.pre = rp.pre)
      req "bernCone" "regionPost" (rp.post = .inRegion termX simplex S)
      req "bernCone" "polyTie"
        (polynomial.freeWires = []
          ∨ ∃ w, termX = Term.var w ∧ polynomial.freeWires ⊆ [w])
      req "bernCone" "predShape"
        ((¬ isExtensionSetEmpty S → isConicPredicate predicate)
          ∧ (isExtensionSetEmpty S → isConvexPredicate predicate))
      req "bernCone" "coefficients"
        (allForwardDiffBernCoeffsSatisfyP simplex S degree polynomial predicate)
      req "bernCone" "postApply"
        (applyPredicateToTerm predicate polynomial seq.post)
    | .norm termL termR => do
      req "norm" "canonEq" (polynomialCanonicalEq termL termR)
      req "norm" "tyEq" (termL.bshape H = termR.bshape H)
      req "norm" "tyDef" (∃ s, termL.bshape H = some s)
      req "norm" "finL" (termL.finWires H)
      req "norm" "finR" (termR.finWires H)
      req "norm" "postEq" (seq.post = .atom .eq termL termR)
    | .farkas combinationCoeffs conclusion _denBoundLog2 => do
      req "farkas" "conclShape" (∃ s, conclusion.bshape H = some s)
      req "farkas" "conclFin" (conclusion.finWires H)
      req "farkas" "wiresPos"
        (wiresPosOn H (seq.pre.freeWires ++ conclusion.freeWires))
      req "farkas" "valid"
        (farkasCombinationValid combinationCoeffs seq.pre conclusion)
      req "farkas" "postEq" (seq.post = .atom .le conclusion (.const 0))
    | .subdivide regionProof termX simplex S branches cover _denBoundLog2 => do
      checkProof H regionProof
      checkBranchProofs H branches
      let rp := regionProof.concludes
      let n := branches.length
      let bSimp : Fin n → Simplex := fun k => (branches.get k).1
      let bS : Fin n → ExtensionSet := fun k => (branches.get k).2.1
      let bPrem : Fin n → Sequent := fun k => (branches.get k).2.2.concludes
      req "subdivide" "preEq" (seq.pre = rp.pre)
      req "subdivide" "regionPost" (rp.post = .inRegion termX simplex S)
      req "subdivide" "branchPre"
        (∀ k, (bPrem k).pre
          = .and rp.pre (.inRegion termX (bSimp k) (bS k)))
      req "subdivide" "branchPost" (∀ k, (bPrem k).post = seq.post)
      req "subdivide" "coverValid"
        (coverInfeasibilityValid termX simplex S n bSimp bS cover)
    | .lirpa lower upper preact post a b al be ga de _den => do
      checkProof H lower
      checkProof H upper
      let lo := lower.concludes ; let hi := upper.concludes
      req "lirpa" "link" (reluLinked H preact post)
      req "lirpa" "hAneg" (a < 0)
      req "lirpa" "hBpos" (0 < b)
      req "lirpa" "hLower1" (al * a + be ≤ 0)
      req "lirpa" "hLower2" (be ≤ 0)
      req "lirpa" "hLower3" (al * b + be ≤ b)
      req "lirpa" "hUpper1" (0 ≤ ga * a + de)
      req "lirpa" "hUpper2" (0 ≤ de)
      req "lirpa" "hUpper3" (b ≤ ga * b + de)
      req "lirpa" "preEq" (seq.pre = lo.pre)
      req "lirpa" "preMatch" (lo.pre = hi.pre)
      req "lirpa" "lowerPost" (lo.post = .atom .le (.const a) (.var preact))
      req "lirpa" "upperPost" (hi.post = .atom .le (.var preact) (.const b))
      req "lirpa" "postForm" (lirpaConclusionForm preact post al be ga de seq.post)
    | .reluPos premise preact post => do
      checkProof H premise
      let p := premise.concludes
      req "reluPos" "link" (reluLinked H preact post)
      req "reluPos" "preEq" (seq.pre = p.pre)
      req "reluPos" "premisePost" (p.post = .atom .ge (.var preact) (.const 0))
      req "reluPos" "conclPost" (seq.post = .atom .eq (.var post) (.var preact))
    | .reluNeg premise preact post => do
      checkProof H premise
      let p := premise.concludes
      req "reluNeg" "link" (reluLinked H preact post)
      req "reluNeg" "preEq" (seq.pre = p.pre)
      req "reluNeg" "premisePost" (p.post = .atom .le (.var preact) (.const 0))
      req "reluNeg" "conclPost" (seq.post = .atom .eq (.var post) (.const 0))
    | .reluNN preact post => do
      req "reluNN" "link" (reluLinked H preact post)
      req "reluNN" "conclPost" (seq.post = .atom .ge (.var post) (.const 0))
    | .reluAbove preact post => do
      req "reluAbove" "link" (reluLinked H preact post)
      req "reluAbove" "conclPost" (seq.post = .atom .ge (.var post) (.var preact))
    | .cellInInterior premise appIdx whichI => do
      checkProof H premise
      let p := premise.concludes
      match H.applications[appIdx]? with
      | some (.cell schema input outputs) =>
        if hI : whichI < schema.cells.length then do
          let k : Fin schema.cells.length := ⟨whichI, hI⟩
          req "cellInInterior" "inputShape"
            (∃ τ, H.wireType input = some τ ∧ τ.shape = [schema.ambDim])
          req "cellInInterior" "outputsScalar"
            (∀ o ∈ outputs, ∃ τ, H.wireType o = some τ ∧
              Shape.totalSize τ.shape = 1)
          req "cellInInterior" "preEq" (seq.pre = p.pre)
          req "cellInInterior" "interiorPremise"
            (cellStrictInteriorForm schema (.var input) k p.post)
          req "cellInInterior" "postOneHot"
            (cellOneHotForm schema outputs k seq.post)
        else throw (.malformedNode "cellInInterior" "whichI out of range")
      | _ => throw (.malformedNode "cellInInterior" "app_idx is not a cell application")
    | .cellOut premise appIdx whichJ witnessVertex => do
      checkProof H premise
      let p := premise.concludes
      match H.applications[appIdx]? with
      | some (.cell schema input outputs) =>
        if hJ : whichJ < schema.cells.length then
          if hV : witnessVertex < schema.nVertices then do
            let k : Fin schema.cells.length := ⟨whichJ, hJ⟩
            let v : Fin schema.nVertices := ⟨witnessVertex, hV⟩
            req "cellOut" "inputShape"
              (∃ τ, H.wireType input = some τ ∧ τ.shape = [schema.ambDim])
            req "cellOut" "outputsScalar"
              (∀ o ∈ outputs, ∃ τ, H.wireType o = some τ ∧
                Shape.totalSize τ.shape = 1)
            req "cellOut" "preEq" (seq.pre = p.pre)
            req "cellOut" "outWitness"
              (cellOutWitnessForm schema (.var input) k v p.post)
            req "cellOut" "postZero"
              (cellOutZeroForm schema outputs k seq.post)
          else throw (.malformedNode "cellOut" "witnessVertex out of range")
        else throw (.malformedNode "cellOut" "whichJ out of range")
      | _ => throw (.malformedNode "cellOut" "app_idx is not a cell application")
    | .eqRefl term => do
      req "eqRefl" "tyDef" (∃ s, term.bshape H = some s)
      req "eqRefl" "fin" (term.finWires H)
      req "eqRefl" "postEq" (seq.post = .atom .eq term term)
    | .eqSym premise termT termU => do
      checkProof H premise
      let p := premise.concludes
      req "eqSym" "preEq" (seq.pre = p.pre)
      req "eqSym" "premisePost" (p.post = .atom .eq termT termU)
      req "eqSym" "postEq" (seq.post = .atom .eq termU termT)
    | .promise supplier consumer contract path iface => do
      checkProof H supplier
      checkProof H consumer
      let sup := supplier.concludes ; let con := consumer.concludes
      req "promise" "supplierPost" (sup.post = contract)
      req "promise" "pathReads" (con.pre.conjGet? path = some contract)
      req "promise" "prePlumb"
        (con.pre.conjReplace? path sup.pre = some seq.pre)
      req "promise" "postEq" (seq.post = con.post)
      match con.pre.conjReplace? path .tt with
      | some ctx => do
        req "promise" "contractConfined" (formulaWiresWithin contract iface)
        req "promise" "separation" (wiresSeparated sup.pre ctx seq.post iface)
      | none => throw (.obligation "promise" "ctxReads")
    | .syzygy components combination conclusion _den _theta => do
      checkProofList H components
      let comps := components.map PTree.concludes
      req "syzygy" "preContains" (∀ c ∈ comps, premiseContains seq.pre c.pre)
      req "syzygy" "conclShape" (∃ s, conclusion.bshape H = some s)
      req "syzygy" "conclFin" (conclusion.finWires H)
      req "syzygy" "wiresPos"
        (wiresPosOn H (seq.pre.freeWires ++ conclusion.freeWires))
      req "syzygy" "compPostWiresPos"
        (∀ c ∈ comps, ∀ w ∈ c.post.freeWires,
          ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape)
      req "syzygy" "valid"
        (syzygyCombinationValid combination comps seq.pre conclusion)

      req "syzygy" "postForm" (syzygyConclusionForm conclusion seq.post)

def checkProofList (H : Hypernet) : List PTree → R Unit
  | [] => pure ()
  | p :: rest => do
    checkProof H p
    checkProofList H rest

def checkBranchProofs (H : Hypernet) :
    List (Simplex × ExtensionSet × PTree) → R Unit
  | [] => pure ()
  | (_, _, p) :: rest => do
    checkProof H p
    checkBranchProofs H rest

end

def checkCert (c : ParsedCert) : R Unit := do
  req "root" "concludes"
    (c.proof.concludes.pre = .and c.goalPre c.hypernet.spConjunction
      ∧ c.proof.concludes.post = c.goalPost)
  req "root" "holeFresh" ((c.hypernet.wireType predicateHole).isNone = true)
  checkProof c.hypernet c.proof

/-- End-to-end acceptance: parse, elevate, and check every node's payload
obligations. -/
def acceptBytes (b : ByteArray) : R Unit := do
  checkCert (← parseCertificate b)

end Wire
end PPLC
