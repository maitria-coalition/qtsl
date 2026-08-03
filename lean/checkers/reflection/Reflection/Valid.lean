import Qtsl.Soundness
import Qtsl.Admissible
import Reflection.Elab

/-!
# Runtime elaboration of semantic validity

`elabValid` walks a parsed proof tree and produces, at run time, a
*proof of semantic validity* for its root sequent: each rule's side
conditions are discharged through the same `Decidable` instances the
first-order checker consults, and the corresponding structural
soundness lemma is applied to the recursively obtained validities of
the premises. Compiled, the proof content erases and the function
performs exactly the checker's work; evaluated by the kernel, a
successful run *is* the acceptance theorem for those bytes.

Compared with `elabPO` (which constructs an inhabitant of the
dependent proof-object type), this elaborator also covers
context-carrying disjunction elimination through the admissible-rule
seam (`sound_orECtx`), matching the executable checker's accepted
fragment exactly: proof objects are compositional data and cannot
span that seam, while validity proofs compose across it.
-/

namespace PPLC
namespace Wire

/-- Validity witness for a sequent, carried through `Option`. -/
abbrev VW (H : Hypernet) (t : PTree) : Type :=
  PLift (t.concludes.semanticallyValid H)

mutual

/-- Elaborate a validity proof for one parsed proof node. -/
def elabValid (H : Hypernet) : (t : PTree) → Option (VW H t)
  | .mk seq k =>
    match k with
    | .ax =>
      if h : seq.pre = seq.post then some ⟨sound_ax h⟩ else none
    | .weaken premise extra => do
      let pv ← elabValid H premise
      let p := premise.concludes
      if h1 : seq.pre = .and p.pre extra then
        if h2 : seq.post = p.post then
          some ⟨sound_weaken pv.down h1 h2⟩
        else none
      else none
    | .cut cutFormula left right => do
      let lv ← elabValid H left
      let rv ← elabValid H right
      let l := left.concludes
      let r := right.concludes
      if h1 : seq.pre = l.pre then
        if h2 : seq.post = r.post then
          if h3 : l.post = cutFormula then
            if h4 : r.pre = .and l.pre cutFormula then
              some ⟨sound_cut lv.down rv.down h1 h2 h3 h4⟩
            else none
          else none
        else none
      else none
    | .andI left right => do
      let lv ← elabValid H left
      let rv ← elabValid H right
      let l := left.concludes
      let r := right.concludes
      if hm : l.pre = r.pre then
        if h1 : seq.pre = l.pre then
          if h2 : seq.post = .and l.post r.post then
            some ⟨sound_andI lv.down rv.down hm h1 h2⟩
          else none
        else none
      else none
    | .andE which premise other => do
      let pv ← elabValid H premise
      let p := premise.concludes
      if h1 : seq.pre = p.pre then
        match which with
        | .left =>
          if h2 : p.post = .and seq.post other then
            some ⟨sound_andE_left pv.down h1 h2⟩
          else none
        | .right =>
          if h2 : p.post = .and other seq.post then
            some ⟨sound_andE_right pv.down h1 h2⟩
          else none
      else none
    | .orI which premise other => do
      let pv ← elabValid H premise
      let p := premise.concludes
      if h1 : seq.pre = p.pre then
        match which with
        | .left =>
          if h2 : seq.post = .or p.post other then
            some ⟨sound_orI_left pv.down h1 h2⟩
          else none
        | .right =>
          if h2 : seq.post = .or other p.post then
            some ⟨sound_orI_right pv.down h1 h2⟩
          else none
      else none
    | .orE left right path => do
      let lv ← elabValid H left
      let rv ← elabValid H right
      let l := left.concludes
      let r := right.concludes
      match hget : seq.pre.conjGet? path with
      | some (.or d₁ d₂) =>
        if hl : seq.pre.conjReplace? path d₁ = some l.pre then
          if hr : seq.pre.conjReplace? path d₂ = some r.pre then
            if hlp : l.post = seq.post then
              if hrp : r.post = seq.post then
                some ⟨sound_orECtx
                  ⟨seq, l, r, path, d₁, d₂, hget, hl, hr, hlp, hrp⟩
                  lv.down rv.down⟩
              else none
            else none
          else none
        else none
      | _ => none
    | .eqElim eqProof bodyProof wire termT termU bodyForm => do
      let ev ← elabValid H eqProof
      let bv ← elabValid H bodyProof
      let e := eqProof.concludes
      let b := bodyProof.concludes
      if h1 : seq.pre = e.pre then
        if h2 : e.pre = b.pre then
          if h3 : e.post = .atom .eq termT termU then
            if h4 : ∃ s, termT.bshape H = some s ∧ termU.bshape H = some s then
              if h5 : substituteInFormula bodyForm wire termT b.post then
                if h6 : substituteInFormula bodyForm wire termU seq.post then
                  some ⟨sound_eqElim ev.down bv.down h1 h2 h3 h4 h5 h6⟩
                else none
              else none
            else none
          else none
        else none
      else none
    | .convIntro premise term simplex S => do
      let pv ← elabValid H premise
      let p := premise.concludes
      if h1 : seq.pre = p.pre then
        if h2 : term.bshape H = some [simplex.complex.ambDim] then
          if h3 : barycentricHalfspaceForm term simplex S p.post then
            if h4 : seq.post = .inRegion term simplex S then
              some ⟨sound_convIntro pv.down h1 h2 h3 h4⟩
            else none
          else none
        else none
      else none
    | .convElim premise term simplex S => do
      let pv ← elabValid H premise
      let p := premise.concludes
      if h1 : seq.pre = p.pre then
        if h2 : p.post = .inRegion term simplex S then
          if h3 : barycentricHalfspaceForm term simplex S seq.post then
            some ⟨sound_convElim pv.down h1 h2 h3⟩
          else none
        else none
      else none
    | .arithAtom dir premise termL termR b => do
      let pv ← elabValid H premise
      let p := premise.concludes
      if _hne : b ≠ .ne then
        if h1 : seq.pre = p.pre then
          match dir with
          | .left =>
            if h2 : atomicCompareZero b termL termR p.post then
              if h3 : atomicCompareForm b termL termR seq.post then
                some ⟨sound_arithAtom_fold pv.down h1 h2 h3⟩
              else none
            else none
          | .right =>
            if h2 : atomicCompareForm b termL termR p.post then
              if h3 : atomicCompareZero b termL termR seq.post then
                some ⟨sound_arithAtom_unfold pv.down h1 h2 h3⟩
              else none
            else none
        else none
      else none
    | .bernCone regionProof termX simplex S degree polynomial predicate => do
      let rv ← elabValid H regionProof
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
                  some ⟨sound_bernCone rv.down h1 h2 h3 h4 h5 h6⟩
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
                  some ⟨sound_norm h1 h2 h3 h4 h5 h6⟩
                else none
              else none
            else none
          else none
        else none
      else none
    | .farkas combinationCoeffs conclusion _den =>
      if h1 : ∃ s, conclusion.bshape H = some s then
        if h2 : conclusion.finWires H then
          if h3 : wiresPosOn H (seq.pre.freeWires ++ conclusion.freeWires) then
            if h4 : farkasCombinationValid combinationCoeffs seq.pre
                conclusion then
              if h5 : seq.post = .atom .le conclusion (.const 0) then
                some ⟨sound_farkas h1 h2 h3 h4 h5⟩
              else none
            else none
          else none
        else none
      else none
    | .subdivide regionProof termX simplex S branches cover _den => do
      let rv ← elabValid H regionProof
      let bv ← elabValidBranches H branches
      let rp := regionProof.concludes
      let n := branches.length
      let bSimp : Fin n → Simplex := fun j => (branches.get j).1
      let bS : Fin n → ExtensionSet := fun j => (branches.get j).2.1
      let bPrem : Fin n → Sequent := fun j => (branches.get j).2.2.concludes
      if h1 : seq.pre = rp.pre then
        if h2 : rp.post = .inRegion termX simplex S then
          if h3 : ∀ j, (bPrem j).pre
              = .and rp.pre (.inRegion termX (bSimp j) (bS j)) then
            if h4 : ∀ j, (bPrem j).post = seq.post then
              if h5 : coverInfeasibilityValid termX simplex S n bSimp bS
                  cover then
                some ⟨sound_subdivide rv.down (fun j => bv.down j)
                  h1 h2 h3 h4 h5⟩
              else none
            else none
          else none
        else none
      else none
    | .lirpa lower upper preact post a b al be ga de _den => do
      let lv ← elabValid H lower
      let uv ← elabValid H upper
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
                                  some ⟨sound_lirpa lv.down uv.down hl
                                    c1 c2 c3 c4 c5 c6 c7 c8 h1 h2 h3 h4 h5⟩
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
      let pv ← elabValid H premise
      let p := premise.concludes
      if hl : reluLinked H preact post then
        if h1 : seq.pre = p.pre then
          if h2 : p.post = .atom .ge (.var preact) (.const 0) then
            if h3 : seq.post = .atom .eq (.var post) (.var preact) then
              some ⟨sound_reluPos pv.down hl h1 h2 h3⟩
            else none
          else none
        else none
      else none
    | .reluNeg premise preact post => do
      let pv ← elabValid H premise
      let p := premise.concludes
      if hl : reluLinked H preact post then
        if h1 : seq.pre = p.pre then
          if h2 : p.post = .atom .le (.var preact) (.const 0) then
            if h3 : seq.post = .atom .eq (.var post) (.const 0) then
              some ⟨sound_reluNeg pv.down hl h1 h2 h3⟩
            else none
          else none
        else none
      else none
    | .reluNN preact post =>
      if hl : reluLinked H preact post then
        if h1 : seq.post = .atom .ge (.var post) (.const 0) then
          some ⟨sound_reluNN hl h1⟩
        else none
      else none
    | .reluAbove preact post =>
      if hl : reluLinked H preact post then
        if h1 : seq.post = .atom .ge (.var post) (.var preact) then
          some ⟨sound_reluAbove hl h1⟩
        else none
      else none
    | .cellInInterior premise appIdx whichI => do
      let pv ← elabValid H premise
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
                    some ⟨sound_cellInInterior pv.down (memOfGetElem? happ)
                      h1 h2 h3 h4 h5⟩
                  else none
                else none
              else none
            else none
          else none
        else none
      | _ => none
    | .cellOut premise appIdx whichJ witnessVertex => do
      let pv ← elabValid H premise
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
                      some ⟨sound_cellOut pv.down (memOfGetElem? happ)
                        h1 h2 h3 h4 h5⟩
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
            some ⟨sound_eqRefl h1 h2 h3⟩
          else none
        else none
      else none
    | .eqSym premise termT termU => do
      let pv ← elabValid H premise
      let p := premise.concludes
      if h1 : seq.pre = p.pre then
        if h2 : p.post = .atom .eq termT termU then
          if h3 : seq.post = .atom .eq termU termT then
            some ⟨sound_eqSym pv.down h1 h2 h3⟩
          else none
        else none
      else none
    | .promise supplier consumer contract path iface => do
      let sv ← elabValid H supplier
      let cv ← elabValid H consumer
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
                    some ⟨sound_promise
                      ⟨seq, sup, con, contract, path, iface, ctx,
                        h1, h2, h3, h4, hctx, h5, h6⟩
                      sv.down cv.down⟩
                  else none
                else none
              | none => none
            else none
          else none
        else none
      else none
    | .syzygy components combination conclusion _den _theta => do
      let cvs ← elabValidList H components
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
                    some ⟨sound_syzygy
                      ⟨seq, comps, combination, conclusion,
                        h1, h2, h3, h4, h5, h6, h7⟩
                      cvs.down⟩
                  else none
                else none
              else none
            else none
          else none
        else none
      else none

/-- Validity proofs for a component list. -/
def elabValidList (H : Hypernet) : (ts : List PTree) →
    Option (PLift (∀ c ∈ ts.map PTree.concludes, c.semanticallyValid H))
  | [] => some ⟨fun _ hc => nomatch hc⟩
  | t :: rest => do
    let hd ← elabValid H t
    let tl ← elabValidList H rest
    pure ⟨fun c hc =>
      match List.mem_cons.mp hc with
      | .inl heq => heq ▸ hd.down
      | .inr hm => tl.down c hm⟩

/-- Validity proofs for subdivision branches, as the dependent family. -/
def elabValidBranches (H : Hypernet) :
    (bs : List (Simplex × ExtensionSet × PTree)) →
    Option (PLift (∀ k : Fin bs.length,
      ((bs.get k).2.2.concludes).semanticallyValid H))
  | [] => some ⟨fun k => absurd k.isLt (Nat.not_lt_zero _)⟩
  | b :: rest => do
    let hd ← elabValid H b.2.2
    let tl ← elabValidBranches H rest
    pure ⟨fun k => Fin.cases hd.down (fun j => tl.down j) k⟩

end

end Wire
end PPLC
