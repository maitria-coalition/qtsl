import Qtsl.WireCheck

/-!
# Runtime elaboration into proof objects

`elabPO` turns a parsed proof tree into an inhabitant of the dependent
proof-object type: every propositional payload field is discharged at
run time through the same `Decidable` instances the first-order
checker consults, so success *constructs* the typed proof object — the
reflection principle in its purest form. Downstream, soundness is the
already-established structural theorem on proof objects; nothing about
this module needs to be trusted for that theorem to apply, because a
successful elaboration is itself the witness.

Fragment note, stated plainly: disjunction elimination is elaborated
in its root form (`ConjPath.here`). The context-carrying form decided
by the first-order checker has no direct payload constructor in the
proof-object calculus; a tree using it refuses here (a completeness
boundary, never a soundness one).
-/

namespace PPLC
namespace Wire

theorem memOfGetElem? {α : Type _} :
    ∀ {l : List α} {i : Nat} {a : α}, l[i]? = some a → a ∈ l
  | [], i, _, h => by cases h
  | x :: _, 0, _, h => by cases h; exact List.mem_cons_self ..
  | _ :: xs, i + 1, a, h => List.mem_cons_of_mem _ (memOfGetElem? (l := xs) h)

mutual

/-- Elaborate one parsed proof node into a proof object. -/
def elabPO (H : Hypernet) : (t : PTree) → Option (ProofObject H t.concludes)
  | .mk seq k =>
    match k with
    | .ax =>
      if h : seq.pre = seq.post then
        some (.mk H seq .ax (.ax H seq (.mk H seq h)))
      else none
    | .weaken premise extra => do
      let pp ← elabPO H premise
      let p := premise.concludes
      if h1 : seq.pre = .and p.pre extra then
        if h2 : seq.post = p.post then
          some (.mk H seq .weaken (.weaken H seq (.mk H seq p pp extra h1 h2)))
        else none
      else none
    | .cut cutFormula left right => do
      let lp ← elabPO H left
      let rp ← elabPO H right
      let l := left.concludes
      let r := right.concludes
      if h1 : seq.pre = l.pre then
        if h2 : seq.post = r.post then
          if h3 : l.post = cutFormula then
            if h4 : r.pre = .and l.pre cutFormula then
              some (.mk H seq .cut
                (.cut H seq (.mk H seq cutFormula l lp r rp h1 h2 h3 h4)))
            else none
          else none
        else none
      else none
    | .andI left right => do
      let lp ← elabPO H left
      let rp ← elabPO H right
      let l := left.concludes
      let r := right.concludes
      if h1 : l.pre = r.pre then
        if h2 : seq.pre = l.pre then
          if h3 : seq.post = .and l.post r.post then
            some (.mk H seq .andI (.andI H seq (.mk H seq l lp r rp h1 h2 h3)))
          else none
        else none
      else none
    | .andE which premise other => do
      let pp ← elabPO H premise
      let p := premise.concludes
      if h1 : seq.pre = p.pre then
        match which with
        | .left =>
          if h2 : p.post = .and seq.post other then
            some (.mk H seq .andE (.andE H seq (.left H seq p pp other h1 h2)))
          else none
        | .right =>
          if h2 : p.post = .and other seq.post then
            some (.mk H seq .andE (.andE H seq (.right H seq p pp other h1 h2)))
          else none
      else none
    | .orI which premise other => do
      let pp ← elabPO H premise
      let p := premise.concludes
      if h1 : seq.pre = p.pre then
        match which with
        | .left =>
          if h2 : seq.post = .or p.post other then
            some (.mk H seq .orI (.orI H seq (.left H seq p pp other h1 h2)))
          else none
        | .right =>
          if h2 : seq.post = .or other p.post then
            some (.mk H seq .orI (.orI H seq (.right H seq p pp other h1 h2)))
          else none
      else none
    | .orE left right path => do
      let lp ← elabPO H left
      let rp ← elabPO H right
      let l := left.concludes
      let r := right.concludes
      match path with
      | .here =>
        if h1 : l.post = r.post then
          if h2 : seq.pre = .or l.pre r.pre then
            if h3 : seq.post = l.post then
              some (.mk H seq .orE (.orE H seq (.mk H seq l lp r rp h1 h2 h3)))
            else none
          else none
        else none
      | _ => none
    | .eqElim eqProof bodyProof wire termT termU bodyForm => do
      let ep ← elabPO H eqProof
      let bp ← elabPO H bodyProof
      let e := eqProof.concludes
      let b := bodyProof.concludes
      if h1 : seq.pre = e.pre then
        if h2 : e.pre = b.pre then
          if h3 : e.post = .atom .eq termT termU then
            if h4 : ∃ s, termT.bshape H = some s ∧ termU.bshape H = some s then
              if h5 : substituteInFormula bodyForm wire termT b.post then
                if h6 : substituteInFormula bodyForm wire termU seq.post then
                  some (.mk H seq .eqElim (.eqElim H seq
                    (.mk H seq e ep b bp wire termT termU bodyForm
                      h1 h2 h3 h4 h5 h6)))
                else none
              else none
            else none
          else none
        else none
      else none
    | .convIntro premise term simplex S => do
      let pp ← elabPO H premise
      let p := premise.concludes
      if h1 : seq.pre = p.pre then
        if h2 : term.bshape H = some [simplex.complex.ambDim] then
          if h3 : barycentricHalfspaceForm term simplex S p.post then
            if h4 : seq.post = .inRegion term simplex S then
              some (.mk H seq .convIntro (.convIntro H seq
                (.mk H seq p pp term simplex S h1 h2 h3 h4)))
            else none
          else none
        else none
      else none
    | .convElim premise term simplex S => do
      let pp ← elabPO H premise
      let p := premise.concludes
      if h1 : seq.pre = p.pre then
        if h2 : p.post = .inRegion term simplex S then
          if h3 : barycentricHalfspaceForm term simplex S seq.post then
            some (.mk H seq .convElim (.convElim H seq
              (.mk H seq p pp term simplex S h1 h2 h3)))
          else none
        else none
      else none
    | .arithAtom dir premise termL termR b => do
      let pp ← elabPO H premise
      let p := premise.concludes
      if hne : b ≠ .ne then
        if h1 : seq.pre = p.pre then
          match dir with
          | .left =>
            if h2 : atomicCompareZero b termL termR p.post then
              if h3 : atomicCompareForm b termL termR seq.post then
                some (.mk H seq .arithAtom (.arithAtom H seq
                  (.fold H seq p pp termL termR b hne h1 h2 h3)))
              else none
            else none
          | .right =>
            if h2 : atomicCompareForm b termL termR p.post then
              if h3 : atomicCompareZero b termL termR seq.post then
                some (.mk H seq .arithAtom (.arithAtom H seq
                  (.unfold H seq p pp termL termR b hne h1 h2 h3)))
              else none
            else none
        else none
      else none
    | .bernCone regionProof termX simplex S degree polynomial predicate => do
      let rpp ← elabPO H regionProof
      let rp := regionProof.concludes
      if h1 : seq.pre = rp.pre then
        if h2 : rp.post = .inRegion termX simplex S then
          if h3 : polynomial.freeWires = []
              ∨ ∃ w, termX = Term.var w ∧ polynomial.freeWires ⊆ [w] then
            if h4 : (¬ isExtensionSetEmpty S → isConicPredicate predicate)
                ∧ (isExtensionSetEmpty S → isConvexPredicate predicate) then
              if h5 : allForwardDiffBernCoeffsSatisfyP simplex S degree
                  polynomial predicate then
                if h6 : applyPredicateToTerm predicate polynomial seq.post then
                  some (.mk H seq .bernCone (.bernCone H seq
                    (.mk H seq rp rpp termX simplex S degree polynomial
                      predicate h1 h2 h3 h4 h5 h6)))
                else none
              else none
            else none
          else none
        else none
      else none
    | .norm termL termR =>
      if h1 : polynomialCanonicalEq termL termR then
        if h2 : termL.bshape H = termR.bshape H then
          if h3 : ∃ s, termL.bshape H = some s then
            if h4 : termL.finWires H then
              if h5 : termR.finWires H then
                if h6 : seq.post = .atom .eq termL termR then
                  some (.mk H seq .norm (.norm H seq
                    (.mk H seq termL termR h1 h2 h3 h4 h5 h6)))
                else none
              else none
            else none
          else none
        else none
      else none
    | .farkas combinationCoeffs conclusion denBoundLog2 =>
      if h1 : ∃ s, conclusion.bshape H = some s then
        if h2 : conclusion.finWires H then
          if h3 : wiresPosOn H (seq.pre.freeWires ++ conclusion.freeWires) then
            if h4 : farkasCombinationValid combinationCoeffs seq.pre
                conclusion then
              if h5 : seq.post = .atom .le conclusion (.const 0) then
                some (.mk H seq .farkas (.farkas H seq
                  (.mk H seq combinationCoeffs conclusion denBoundLog2
                    h1 h2 h3 h4 h5)))
              else none
            else none
          else none
        else none
      else none
    | .subdivide regionProof termX simplex S branches cover denBoundLog2 => do
      let rpp ← elabPO H regionProof
      let bps ← elabPOBranches H branches
      let rp := regionProof.concludes
      let n := branches.length
      let bSimp : Fin n → Simplex := fun k => (branches.get k).1
      let bS : Fin n → ExtensionSet := fun k => (branches.get k).2.1
      let bPrem : Fin n → Sequent := fun k => (branches.get k).2.2.concludes
      if h1 : seq.pre = rp.pre then
        if h2 : rp.post = .inRegion termX simplex S then
          if h3 : ∀ k, (bPrem k).pre
              = .and rp.pre (.inRegion termX (bSimp k) (bS k)) then
            if h4 : ∀ k, (bPrem k).post = seq.post then
              if h5 : coverInfeasibilityValid termX simplex S n bSimp bS
                  cover then
                some (.mk H seq .subdivide (.subdivide H seq
                  (.mk H seq rp rpp termX simplex S n bSimp bS bPrem bps
                    cover denBoundLog2 h1 h2 h3 h4 h5)))
              else none
            else none
          else none
        else none
      else none
    | .lirpa lower upper preact post a b al be ga de den => do
      let lop ← elabPO H lower
      let upp ← elabPO H upper
      let lo := lower.concludes
      let hi := upper.concludes
      if hl : reluLinked H preact post then
        if c1 : a < 0 then
          if c2 : 0 < b then
            if c3 : al * a + be ≤ 0 then
              if c4 : be ≤ 0 then
                if c5 : al * b + be ≤ b then
                  if c6 : 0 ≤ ga * a + de then
                    if c7 : 0 ≤ de then
                      if c8 : b ≤ ga * b + de then
                        if h1 : seq.pre = lo.pre then
                          if h2 : lo.pre = hi.pre then
                            if h3 : lo.post
                                = .atom .le (.const a) (.var preact) then
                              if h4 : hi.post
                                  = .atom .le (.var preact) (.const b) then
                                if h5 : lirpaConclusionForm preact post
                                    al be ga de seq.post then
                                  some (.mk H seq .lirpa (.lirpa H seq
                                    (.mk H seq lo lop hi upp preact post
                                      a b al be ga de den hl c1 c2 c3 c4 c5
                                      c6 c7 c8 h1 h2 h3 h4 h5)))
                                else none
                              else none
                            else none
                          else none
                        else none
                      else none
                    else none
                  else none
                else none
              else none
            else none
          else none
        else none
      else none
    | .reluPos premise preact post => do
      let pp ← elabPO H premise
      let p := premise.concludes
      if hl : reluLinked H preact post then
        if h1 : seq.pre = p.pre then
          if h2 : p.post = .atom .ge (.var preact) (.const 0) then
            if h3 : seq.post = .atom .eq (.var post) (.var preact) then
              some (.mk H seq .reluPos (.reluPos H seq
                (.mk H seq p pp preact post hl h1 h2 h3)))
            else none
          else none
        else none
      else none
    | .reluNeg premise preact post => do
      let pp ← elabPO H premise
      let p := premise.concludes
      if hl : reluLinked H preact post then
        if h1 : seq.pre = p.pre then
          if h2 : p.post = .atom .le (.var preact) (.const 0) then
            if h3 : seq.post = .atom .eq (.var post) (.const 0) then
              some (.mk H seq .reluNeg (.reluNeg H seq
                (.mk H seq p pp preact post hl h1 h2 h3)))
            else none
          else none
        else none
      else none
    | .reluNN preact post =>
      if hl : reluLinked H preact post then
        if h1 : seq.post = .atom .ge (.var post) (.const 0) then
          some (.mk H seq .reluNN (.reluNN H seq (.mk H seq preact post hl h1)))
        else none
      else none
    | .reluAbove preact post =>
      if hl : reluLinked H preact post then
        if h1 : seq.post = .atom .ge (.var post) (.var preact) then
          some (.mk H seq .reluAbove (.reluAbove H seq
            (.mk H seq preact post hl h1)))
        else none
      else none
    | .cellInInterior premise appIdx whichI => do
      let pp ← elabPO H premise
      let p := premise.concludes
      match happ : H.applications[appIdx]? with
      | some (.cell schema input outputs) =>
        if hI : whichI < schema.cells.length then
          let kk : Fin schema.cells.length := ⟨whichI, hI⟩
          if h1 : ∃ τ, H.wireType input = some τ ∧ τ.shape = [schema.ambDim] then
            if h2 : ∀ o ∈ outputs, ∃ τ, H.wireType o = some τ ∧
                Shape.totalSize τ.shape = 1 then
              if h3 : seq.pre = p.pre then
                if h4 : cellStrictInteriorForm schema (.var input) kk p.post then
                  if h5 : cellOneHotForm schema outputs kk seq.post then
                    some (.mk H seq .cellInInterior (.cellInInterior H seq
                      (.mk H seq p pp schema input outputs kk
                        (memOfGetElem? happ) h1 h2 h3 h4 h5)))
                  else none
                else none
              else none
            else none
          else none
        else none
      | _ => none
    | .cellOut premise appIdx whichJ witnessVertex => do
      let pp ← elabPO H premise
      let p := premise.concludes
      match happ : H.applications[appIdx]? with
      | some (.cell schema input outputs) =>
        if hJ : whichJ < schema.cells.length then
          if hV : witnessVertex < schema.nVertices then
            let kk : Fin schema.cells.length := ⟨whichJ, hJ⟩
            let vv : Fin schema.nVertices := ⟨witnessVertex, hV⟩
            if h1 : ∃ τ, H.wireType input = some τ ∧
                τ.shape = [schema.ambDim] then
              if h2 : ∀ o ∈ outputs, ∃ τ, H.wireType o = some τ ∧
                  Shape.totalSize τ.shape = 1 then
                if h3 : seq.pre = p.pre then
                  if h4 : cellOutWitnessForm schema (.var input) kk vv
                      p.post then
                    if h5 : cellOutZeroForm schema outputs kk seq.post then
                      some (.mk H seq .cellOut (.cellOut H seq
                        (.mk H seq p pp schema input outputs kk vv
                          (memOfGetElem? happ) h1 h2 h3 h4 h5)))
                    else none
                  else none
                else none
              else none
            else none
          else none
        else none
      | _ => none
    | .eqRefl term =>
      if h1 : ∃ s, term.bshape H = some s then
        if h2 : term.finWires H then
          if h3 : seq.post = .atom .eq term term then
            some (.mk H seq .eqRefl (.eqRefl H seq (.mk H seq term h1 h2 h3)))
          else none
        else none
      else none
    | .eqSym premise termT termU => do
      let pp ← elabPO H premise
      let p := premise.concludes
      if h1 : seq.pre = p.pre then
        if h2 : p.post = .atom .eq termT termU then
          if h3 : seq.post = .atom .eq termU termT then
            some (.mk H seq .eqSym (.eqSym H seq
              (.mk H seq p pp termT termU h1 h2 h3)))
          else none
        else none
      else none
    | .promise supplier consumer contract path iface => do
      let sp ← elabPO H supplier
      let cp ← elabPO H consumer
      let sup := supplier.concludes
      let con := consumer.concludes
      if h1 : sup.post = contract then
        if h2 : con.pre.conjGet? path = some contract then
          if h3 : con.pre.conjReplace? path sup.pre = some seq.pre then
            if h4 : seq.post = con.post then
              match hctx : con.pre.conjReplace? path .tt with
              | some ctx =>
                if h5 : formulaWiresWithin contract iface then
                  if h6 : wiresSeparated sup.pre ctx seq.post iface then
                    some (.mk H seq .promise (.promise H seq
                      (.mk H seq sup sp con cp contract path iface ctx
                        h1 h2 h3 h4 hctx h5 h6)))
                  else none
                else none
              | none => none
            else none
          else none
        else none
      else none
    | .syzygy components combination conclusion den theta => do
      let cps ← elabPOSeqList H components
      let comps := components.map PTree.concludes
      if h1 : ∀ c ∈ comps, premiseContains seq.pre c.pre then
        if h2 : ∃ s, conclusion.bshape H = some s then
          if h3 : conclusion.finWires H then
            if h4 : wiresPosOn H (seq.pre.freeWires
                ++ conclusion.freeWires) then
              if h5 : ∀ c ∈ comps, ∀ w ∈ c.post.freeWires,
                  ∃ τ, H.wireType w = some τ ∧
                    0 < Shape.totalSize τ.shape then
                if h6 : syzygyCombinationValid combination comps seq.pre
                    conclusion then
                  if h7 : syzygyConclusionForm conclusion seq.post then
                    some (.mk H seq .syzygy (.syzygy H seq
                      (.mk H seq comps cps combination conclusion den
                        h1 h2 h3 h4 h5 h6 h7)))
                  else none
                else none
              else none
            else none
          else none
        else none
      else none

/-- Elaborate a component list into a `ProofSeqList`. -/
def elabPOSeqList (H : Hypernet) :
    (ts : List PTree) → Option (ProofSeqList H (ts.map PTree.concludes))
  | [] => some (.nil H)
  | t :: rest => do
    let hd ← elabPO H t
    let tl ← elabPOSeqList H rest
    pure (.cons H t.concludes (rest.map PTree.concludes) hd tl)

/-- Elaborate subdivision branches into the dependent branch family. -/
def elabPOBranches (H : Hypernet) :
    (bs : List (Simplex × ExtensionSet × PTree)) →
    Option ((k : Fin bs.length) → ProofObject H (bs.get k).2.2.concludes)
  | [] => some (fun k => absurd k.isLt (Nat.not_lt_zero _))
  | b :: rest => do
    let hd ← elabPO H b.2.2
    let tl ← elabPOBranches H rest
    pure (fun k => Fin.cases hd (fun j => tl j) k)

end

end Wire
end PPLC
