import Qtsl.Soundness
import Qtsl.ReluSplit
import DoubleCat.Virtual.Presentation
import DoubleCat.ImplDouble

/-!
# The certificate calculus as a presented virtual double category, with
# its semantic components

The structural core of the certificate calculus's rule set, read as a
presentation (`DoubleCat.Virtual.Presentation`): sequents are the loose
generators over a single claim context, each rule instance is a gated
multicell generator whose gate carries the rule's row-shaped side
conditions, and the semantic component on each generator is the landed
per-rule soundness lemma of `Qtsl.Soundness` — `sound_cut` behind the
cut generator, `sound_weaken` behind weakening, and so on.  The target
is the implication double category (`DoubleCat.ImplDouble`): a sequent
is interpreted as its semantic validity over a fixed hypernet, and a
rule's component is the entailment its soundness lemma proves.

The remaining rule tags of the calculus (`RuleTag`: the conversion,
arithmetic, cone, subdivision, activation-split, cell-membership,
equality, promise, and certificate families) follow the identical
pattern — their per-rule lemmas are assembled in `ProofObject.sound` —
and enter as further generators of the same presentation as they are
wired.  Wired beyond the structural core so far: the equality family
(`eqRefl`/`eqSym`/`antisym`/`eqElim`), the arithmetic-atom conversions
(`arithAtomFold`/`arithAtomUnfold`), polynomial normalization (`norm`),
the linear cone (`farkas`), closed evaluation (`pConstExact`), region
conversion (`convIntro`/`convElim`), the Bernstein cone
(`bernConeEmpty`/`bernCone`), promise plumbing (`promise`), the
PSD-certificate family (`psdCertOf`/`psdCertT`/`psdCertDD`/`psdCertK`),
the activation-split family
(`reluNN`/`reluAbove`/`reluPos`/`reluNeg`/`reluSplit`/`lirpa` — the
split rule's lemma living in its satellite `Qtsl.ReluSplit`), cell
membership
(`cellInInterior`/`cellOut`), and — through the `LoosePath.ofFin`/`ofList`
builders, whose interpreted folds the `fold_ofFin_valid`/`fold_ofList_valid`
lemmas below read as universally-quantified premise validity — the
n-ary-premise residue: subdivision (`subdivide`, `Fin`-indexed branches),
the premise-bound rule (`pBound`, `List`-indexed components), and the
syzygy rule (`syzygy`, whose H-parametrized payload `SyzygyStep H` enters
by the promise treatment: payload data as constructor data, payload proof
fields as gate, the structure reassembled in the arm).  With these,
every per-rule lemma of `Qtsl.Soundness`'s roster — 37 with the
antisymmetry rule (`sound_antisym`, the equality-from-inequalities
inference) — is wired, plus the satellite split rule.

**The presentation is hypernet-indexed.**  The structural core's gates
were hypernet-free, and the original header claimed pure syntacticity
for the presentation; the equality, cone, and conversion families
falsify that posture — their side conditions consult the hypernet's
declaration tables (`Term.bshape`, `Term.finWires`,
`Hypernet.wireType`), which at the row stratum are declaration rows of
the certificate's own hypernet section.  The activation-split and
cell-membership families consult one section deeper: their gates cite
the hypernet's *application* rows (`reluLinked`,
`PrimApp.cell … ∈ H.applications`).  So the hypernet — declarations and
applications both — is part of the presented artifact, not of the
semantics: the presentation `blPresentation H` carries it in the gates,
and no semantic notion (validity, the credal face) enters before the
interpretation, exactly as before.

The assembly (`blInterpretation.sem`, in `SuFunctor.QtslSem.Fixture`)
is the free-promotion transpose: the components on the generators are
the only semantic obligations, and functoriality on every composite
derivation is the universal property of the free construction.
-/

namespace SuFunctor

namespace QtslSem

open PPLC CategoryTheory

/-- The single claim context of the structural fragment.  (An earlier
form of this docstring reserved many objects and nonidentity tight
arrows for system-level presentations; the reservation is lifted by
`SuFunctor.QtslSem.BLMulti`, where the product-lattice rule's
inter-context transport takes hypernets as contexts and extension
witnesses as tights, and this presentation becomes the one-context
slice.) -/
structure BLCtx : Type where
  /-- The context. -/
  pt ::

instance : CategoryTheory.Category.{0} BLCtx where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

/-- The structural core of the rule set, as rule instances: each
constructor carries the sequents and formulas its side conditions
mention (the row shape of the corresponding proof-object payload). -/
inductive BLRule : Type
  /-- `ax`: the axiom rule. -/
  | ax (seq : Sequent)
  /-- `weaken`: weakening of the premise. -/
  | weaken (seq premise : Sequent) (extra : Formula)
  /-- `cut`: cut along a formula. -/
  | cut (seq leftPremise rightPremise : Sequent) (cutFormula : Formula)
  /-- `andI`: conjunction introduction. -/
  | andI (seq leftPremise rightPremise : Sequent)
  /-- `andE` (left projection). -/
  | andELeft (seq premise : Sequent) (other : Formula)
  /-- `andE` (right projection). -/
  | andERight (seq premise : Sequent) (other : Formula)
  /-- `orI` (left injection). -/
  | orILeft (seq premise : Sequent) (other : Formula)
  /-- `orI` (right injection). -/
  | orIRight (seq premise : Sequent) (other : Formula)
  /-- `orE`: disjunction elimination. -/
  | orE (seq leftPremise rightPremise : Sequent)
  /-- `eqRefl`: reflexivity of equality on a well-shaped term. -/
  | eqRefl (seq : Sequent) (t : Term)
  /-- `eqSym`: symmetry of equality. -/
  | eqSym (seq premise : Sequent) (tT tU : Term)
  /-- `antisym`: equality from `≤` and `≥` premises at the same term
  pair. -/
  | antisym (seq premiseLe premiseGe : Sequent) (tT tU : Term)
  /-- `eqElim`: substitution of equals in a formula body. -/
  | eqElim (seq eqPremise bodyPremise : Sequent) (wire : Wire)
      (termT termU : Term) (bodyForm : Formula)
  /-- `arithAtomFold`: fold an atomic comparison to compare-with-zero
  form. -/
  | arithAtomFold (seq premise : Sequent) (termL termR : Term) (b : BowTie)
  /-- `arithAtomUnfold`: unfold a compare-with-zero atom to direct
  comparison form. -/
  | arithAtomUnfold (seq premise : Sequent) (termL termR : Term) (b : BowTie)
  /-- `norm`: polynomial-canonical equality of terms. -/
  | norm (seq : Sequent) (termL termR : Term)
  /-- `farkas`: a nonnegative linear combination of premise atoms
  bounding the conclusion. -/
  | farkas (seq : Sequent) (combinationCoeffs conclusion : Term)
  /-- `pConstExact`: closed evaluation of a ground atom. -/
  | pConstExact (seq : Sequent) (e₁ e₂ : Term) (b : BowTie)
  /-- `convIntro`: region membership from its barycentric halfspace
  form. -/
  | convIntro (seq premise : Sequent) (term : Term) (simplex : Simplex)
      (S : ExtensionSet)
  /-- `convElim`: barycentric halfspace form from region membership. -/
  | convElim (seq premise : Sequent) (term : Term) (simplex : Simplex)
      (S : ExtensionSet)
  /-- `bernConeEmpty`: the Bernstein-coefficient cone rule, empty
  extension-set case (convex predicates). -/
  | bernConeEmpty (seq regionPremise : Sequent) (termX : Term)
      (simplex : Simplex) (S : ExtensionSet) (degree : Nat)
      (polynomial : Term) (predicate : Formula)
  /-- `bernCone`: the Bernstein-coefficient cone rule, general case. -/
  | bernCone (seq regionPremise : Sequent) (termX : Term)
      (simplex : Simplex) (S : ExtensionSet) (degree : Nat)
      (polynomial : Term) (predicate : Formula)
  /-- `promise`: supplier/consumer plumbing along a conjunction path. -/
  | promise (seq supplier consumer : Sequent) (contract : Formula)
      (path : ConjPath) (iface : List Wire) (ctx : Formula)
  /-- `psdCertOf`: the negated quadratic form of a PSD matrix bounds the
  conclusion (semantic PSD hypothesis). -/
  | psdCertOf (seq : Sequent) (a : Nat) (M : Fin a → Fin a → ℚ)
      (ts : List Term) (conclusion : Term)
  /-- `psdCertT`: PSD by the triangular-factorization witness
  (`PsdCert.checkT`). -/
  | psdCertT (seq : Sequent) (a : Nat) (A Z : Fin a → Fin a → ℚ)
      (ts : List Term) (conclusion : Term)
  /-- `psdCertDD`: PSD by the diagonal-dominance-after-congruence
  witness (`PsdCert.checkDD`). -/
  | psdCertDD (seq : Sequent) (a : Nat) (A Z : Fin a → Fin a → ℚ)
      (ts : List Term) (conclusion : Term)
  /-- `psdCertK`: PSD by the kernel-congruence witness with its inner
  triangular/diagonal-dominance check (`PsdCert.checkK`). -/
  | psdCertK (seq : Sequent) (m k : Nat)
      (A : Fin (m + k) → Fin (m + k) → ℚ) (N : Fin m → Fin k → ℚ)
      (B : Fin m → Fin m → ℚ) (innerT : Bool) (Z : Fin m → Fin m → ℚ)
      (ts : List Term) (conclusion : Term)
  /-- `reluNN`: nonnegativity of a relu output. -/
  | reluNN (seq : Sequent) (preact post : Wire)
  /-- `reluAbove`: a relu output dominates its preactivation. -/
  | reluAbove (seq : Sequent) (preact post : Wire)
  /-- `reluPos`: on the nonnegative branch, relu is the identity. -/
  | reluPos (seq premise : Sequent) (preact post : Wire)
  /-- `reluNeg`: on the nonpositive branch, relu vanishes. -/
  | reluNeg (seq premise : Sequent) (preact post : Wire)
  /-- `reluSplit`: case-split on the sign of a relu input — the marked
  body formula holds with the preactivation substituted on the
  nonnegative branch and with zero substituted on the nonpositive
  branch, so it holds with the relu output substituted. -/
  | reluSplit (seq activePremise inactivePremise : Sequent)
      (preact post marker : Wire) (bodyForm : Formula)
  /-- `lirpa`: affine relaxation bounds for a relu from interval bounds
  on the preactivation. -/
  | lirpa (seq lowerPremise upperPremise : Sequent) (preact post : Wire)
      (a b α β γ δ : ℚ)
  /-- `cellInInterior`: strict-interior membership selects a cell
  complex's one-hot indicator. -/
  | cellInInterior (seq premise : Sequent) (schema : SimpC)
      (input : Wire) (outputs : List Wire)
      (whichI : Fin schema.cells.length)
  /-- `cellOut`: a strict-sign witness at a contained vertex zeroes a
  cell's indicator. -/
  | cellOut (seq premise : Sequent) (schema : SimpC) (input : Wire)
      (outputs : List Wire) (whichJ : Fin schema.cells.length)
      (wv : Fin schema.nVertices)
  /-- `subdivide`: a region hypothesis subdivided along a certified
  cover; the conclusion follows from every branch. -/
  | subdivide (seq regionPremise : Sequent) (nBranches : Nat)
      (branchPremise : Fin nBranches → Sequent) (termX : Term)
      (simplex : Simplex) (S : ExtensionSet)
      (branchSimplex : Fin nBranches → Simplex)
      (branchS : Fin nBranches → ExtensionSet) (coverCertificate : Term)
  /-- `pBound`: a certified nonnegative combination of component
  conclusions bounding the conclusion (the syzygy machinery with the
  payload unbundled). -/
  | pBound (seq : Sequent) (components : List Sequent)
      (combination conclusion : Term)
  /-- `syzygy`: the syzygy step — the `SyzygyStep` payload's data
  fields as constructor data (the promise treatment; its proof fields
  are the gate, and the arm reassembles the structure). -/
  | syzygy (seq : Sequent) (components : List Sequent)
      (combination conclusion : Term)

namespace BLRule

/-- The side conditions of a rule instance — the row-shaped hypotheses
of its per-rule soundness lemma, verbatim.  The hypernet parameter is
consulted only by the declaration-aware families (shape, finiteness,
wire typing); the structural core ignores it. -/
def gate (H : Hypernet) : BLRule → Prop
  | .ax seq => seq.pre = seq.post
  | .weaken seq premise extra =>
      seq.pre = .and premise.pre extra ∧ seq.post = premise.post
  | .cut seq l r c =>
      seq.pre = l.pre ∧ seq.post = r.post ∧ l.post = c ∧
        r.pre = .and l.pre c
  | .andI seq l r =>
      l.pre = r.pre ∧ seq.pre = l.pre ∧ seq.post = .and l.post r.post
  | .andELeft seq p other =>
      seq.pre = p.pre ∧ p.post = .and seq.post other
  | .andERight seq p other =>
      seq.pre = p.pre ∧ p.post = .and other seq.post
  | .orILeft seq p other =>
      seq.pre = p.pre ∧ seq.post = .or p.post other
  | .orIRight seq p other =>
      seq.pre = p.pre ∧ seq.post = .or other p.post
  | .orE seq l r =>
      l.post = r.post ∧ seq.pre = .or l.pre r.pre ∧ seq.post = l.post
  | .eqRefl seq t =>
      (∃ s, t.bshape H = some s) ∧ t.finWires H ∧
        seq.post = .atom .eq t t
  | .eqSym seq p tT tU =>
      seq.pre = p.pre ∧ p.post = .atom .eq tT tU ∧
        seq.post = .atom .eq tU tT
  | .antisym seq pLe pGe tT tU =>
      seq.pre = pLe.pre ∧ seq.pre = pGe.pre ∧
        pLe.post = .atom .le tT tU ∧
        pGe.post = .atom .ge tT tU ∧
        seq.post = .atom .eq tT tU
  | .eqElim seq eqP bodyP wire termT termU bodyForm =>
      seq.pre = eqP.pre ∧ eqP.pre = bodyP.pre ∧
        eqP.post = .atom .eq termT termU ∧
        (∃ s, termT.bshape H = some s ∧ termU.bshape H = some s) ∧
        substituteInFormula bodyForm wire termT bodyP.post ∧
        substituteInFormula bodyForm wire termU seq.post
  | .arithAtomFold seq p termL termR b =>
      seq.pre = p.pre ∧ atomicCompareZero b termL termR p.post ∧
        atomicCompareForm b termL termR seq.post
  | .arithAtomUnfold seq p termL termR b =>
      seq.pre = p.pre ∧ atomicCompareForm b termL termR p.post ∧
        atomicCompareZero b termL termR seq.post
  | .norm seq termL termR =>
      polynomialCanonicalEq termL termR ∧
        termL.bshape H = termR.bshape H ∧
        (∃ s, termL.bshape H = some s) ∧
        termL.finWires H ∧ termR.finWires H ∧
        seq.post = .atom .eq termL termR
  | .farkas seq combinationCoeffs conclusion =>
      (∃ s, conclusion.bshape H = some s) ∧ conclusion.finWires H ∧
        (∀ w ∈ seq.pre.freeWires ++ conclusion.freeWires,
          ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape) ∧
        farkasCombinationValid combinationCoeffs seq.pre conclusion ∧
        seq.post = .atom .le conclusion (.const 0)
  | .pConstExact seq e₁ e₂ b =>
      (Formula.atom b e₁ e₂).evalClosed = some true ∧
        seq.post = .atom b e₁ e₂
  | .convIntro seq p term simplex S =>
      seq.pre = p.pre ∧
        term.bshape H = some [simplex.complex.ambDim] ∧
        barycentricHalfspaceForm term simplex S p.post ∧
        seq.post = .inRegion term simplex S
  | .convElim seq p term simplex S =>
      seq.pre = p.pre ∧ p.post = .inRegion term simplex S ∧
        barycentricHalfspaceForm term simplex S seq.post
  | .bernConeEmpty seq regionP termX simplex S degree polynomial
      predicate =>
      seq.pre = regionP.pre ∧
        regionP.post = .inRegion termX simplex S ∧
        (polynomial.freeWires = [] ∨
          ∃ w, termX = Term.var w ∧ polynomial.freeWires ⊆ [w]) ∧
        (isExtensionSetEmpty S → isConvexPredicate predicate) ∧
        isExtensionSetEmpty S ∧
        allForwardDiffBernCoeffsSatisfyP simplex S degree polynomial
          predicate ∧
        applyPredicateToTerm predicate polynomial seq.post
  | .bernCone seq regionP termX simplex S degree polynomial predicate =>
      seq.pre = regionP.pre ∧
        regionP.post = .inRegion termX simplex S ∧
        (polynomial.freeWires = [] ∨
          ∃ w, termX = Term.var w ∧ polynomial.freeWires ⊆ [w]) ∧
        ((¬ isExtensionSetEmpty S → isConicPredicate predicate) ∧
          (isExtensionSetEmpty S → isConvexPredicate predicate)) ∧
        allForwardDiffBernCoeffsSatisfyP simplex S degree polynomial
          predicate ∧
        applyPredicateToTerm predicate polynomial seq.post
  | .promise seq supplier consumer contract path iface ctx =>
      supplier.post = contract ∧
        consumer.pre.conjGet? path = some contract ∧
        consumer.pre.conjReplace? path supplier.pre = some seq.pre ∧
        seq.post = consumer.post ∧
        consumer.pre.conjReplace? path .tt = some ctx ∧
        formulaWiresWithin contract iface ∧
        wiresSeparated supplier.pre ctx seq.post iface
  | .psdCertOf seq a M ts conclusion =>
      (∀ x : Fin a → ℚ, 0 ≤ PsdCert.finQSum a fun i =>
        PsdCert.finQSum a fun j => M i j * x i * x j) ∧
        PsdCert.conclCheck a M ts conclusion = true ∧
        (∃ s, conclusion.bshape H = some s) ∧
        conclusion.finWires H ∧
        (∀ w ∈ conclusion.freeWires,
          ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape) ∧
        syzygyConclusionForm conclusion seq.post
  | .psdCertT seq a A Z ts conclusion =>
      PsdCert.checkT a A Z = true ∧
        PsdCert.conclCheck a A ts conclusion = true ∧
        (∃ s, conclusion.bshape H = some s) ∧
        conclusion.finWires H ∧
        (∀ w ∈ conclusion.freeWires,
          ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape) ∧
        syzygyConclusionForm conclusion seq.post
  | .psdCertDD seq a A Z ts conclusion =>
      PsdCert.checkDD a A Z = true ∧
        PsdCert.conclCheck a A ts conclusion = true ∧
        (∃ s, conclusion.bshape H = some s) ∧
        conclusion.finWires H ∧
        (∀ w ∈ conclusion.freeWires,
          ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape) ∧
        syzygyConclusionForm conclusion seq.post
  | .psdCertK seq m k A N B innerT Z ts conclusion =>
      PsdCert.checkK m k A N B innerT Z = true ∧
        PsdCert.conclCheck (m + k) A ts conclusion = true ∧
        (∃ s, conclusion.bshape H = some s) ∧
        conclusion.finWires H ∧
        (∀ w ∈ conclusion.freeWires,
          ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape) ∧
        syzygyConclusionForm conclusion seq.post
  | .reluNN seq preact post =>
      reluLinked H preact post ∧
        seq.post = .atom .ge (.var post) (.const 0)
  | .reluAbove seq preact post =>
      reluLinked H preact post ∧
        seq.post = .atom .ge (.var post) (.var preact)
  | .reluPos seq premise preact post =>
      reluLinked H preact post ∧ seq.pre = premise.pre ∧
        premise.post = .atom .ge (.var preact) (.const 0) ∧
        seq.post = .atom .eq (.var post) (.var preact)
  | .reluNeg seq premise preact post =>
      reluLinked H preact post ∧ seq.pre = premise.pre ∧
        premise.post = .atom .le (.var preact) (.const 0) ∧
        seq.post = .atom .eq (.var post) (.const 0)
  | .reluSplit seq activeP inactiveP preact post marker bodyForm =>
      reluLinked H preact post ∧
        (∃ τ, H.wireType post = some τ ∧ τ.shape = []) ∧
        activeP.pre = .and seq.pre (.atom .ge (.var preact) (.const 0)) ∧
        inactiveP.pre = .and seq.pre (.atom .le (.var preact) (.const 0)) ∧
        substituteInFormula bodyForm marker (.var preact) activeP.post ∧
        substituteInFormula bodyForm marker (.const 0) inactiveP.post ∧
        substituteInFormula bodyForm marker (.var post) seq.post
  | .lirpa seq lowerPremise upperPremise preact post a b α β γ δ =>
      reluLinked H preact post ∧ a < 0 ∧ 0 < b ∧
        α * a + β ≤ 0 ∧ β ≤ 0 ∧ α * b + β ≤ b ∧
        0 ≤ γ * a + δ ∧ 0 ≤ δ ∧ b ≤ γ * b + δ ∧
        seq.pre = lowerPremise.pre ∧
        lowerPremise.pre = upperPremise.pre ∧
        lowerPremise.post = .atom .le (.const a) (.var preact) ∧
        upperPremise.post = .atom .le (.var preact) (.const b) ∧
        lirpaConclusionForm preact post α β γ δ seq.post
  | .cellInInterior seq premise schema input outputs whichI =>
      PrimApp.cell schema input outputs ∈ H.applications ∧
        (∃ τ, H.wireType input = some τ ∧ τ.shape = [schema.ambDim]) ∧
        (∀ o ∈ outputs, ∃ τ, H.wireType o = some τ ∧
          Shape.totalSize τ.shape = 1) ∧
        seq.pre = premise.pre ∧
        cellStrictInteriorForm schema (.var input) whichI premise.post ∧
        cellOneHotForm schema outputs whichI seq.post
  | .cellOut seq premise schema input outputs whichJ wv =>
      PrimApp.cell schema input outputs ∈ H.applications ∧
        (∃ τ, H.wireType input = some τ ∧ τ.shape = [schema.ambDim]) ∧
        (∀ o ∈ outputs, ∃ τ, H.wireType o = some τ ∧
          Shape.totalSize τ.shape = 1) ∧
        seq.pre = premise.pre ∧
        cellOutWitnessForm schema (.var input) whichJ wv premise.post ∧
        cellOutZeroForm schema outputs whichJ seq.post
  | .subdivide seq regionPremise nBranches branchPremise termX simplex S
      branchSimplex branchS coverCertificate =>
      seq.pre = regionPremise.pre ∧
        regionPremise.post = .inRegion termX simplex S ∧
        (∀ k, (branchPremise k).pre
          = .and regionPremise.pre
              (.inRegion termX (branchSimplex k) (branchS k))) ∧
        (∀ k, (branchPremise k).post = seq.post) ∧
        coverInfeasibilityValid termX simplex S nBranches
          branchSimplex branchS coverCertificate
  | .pBound seq components combination conclusion =>
      (∀ c ∈ components, premiseContains seq.pre c.pre) ∧
        (∃ s, conclusion.bshape H = some s) ∧
        conclusion.finWires H ∧
        (∀ w ∈ seq.pre.freeWires ++ conclusion.freeWires,
          ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape) ∧
        (∀ c ∈ components, ∀ w ∈ c.post.freeWires,
          ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape) ∧
        syzygyCombinationValid combination components seq.pre conclusion ∧
        syzygyConclusionForm conclusion seq.post
  | .syzygy seq components combination conclusion =>
      (∀ c ∈ components, premiseContains seq.pre c.pre) ∧
        (∃ s, conclusion.bshape H = some s) ∧
        conclusion.finWires H ∧
        (∀ w ∈ seq.pre.freeWires ++ conclusion.freeWires,
          ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape) ∧
        (∀ c ∈ components, ∀ w ∈ c.post.freeWires,
          ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape) ∧
        syzygyCombinationValid combination components seq.pre conclusion ∧
        syzygyConclusionForm conclusion seq.post

/-- The premise string of a rule instance. -/
def tops : BLRule → CategoryTheory.LoosePath (fun _ _ : BLCtx => Sequent)
    BLCtx.pt BLCtx.pt
  | .ax _ => .nil
  | .weaken _ premise _ => .single premise
  | .cut _ l r _ => .cons (b := .pt) l (.single r)
  | .andI _ l r => .cons (b := .pt) l (.single r)
  | .andELeft _ p _ => .single p
  | .andERight _ p _ => .single p
  | .orILeft _ p _ => .single p
  | .orIRight _ p _ => .single p
  | .orE _ l r => .cons (b := .pt) l (.single r)
  | .eqRefl _ _ => .nil
  | .eqSym _ p _ _ => .single p
  | .antisym _ pLe pGe _ _ => .cons (b := .pt) pLe (.single pGe)
  | .eqElim _ eqP bodyP _ _ _ _ => .cons (b := .pt) eqP (.single bodyP)
  | .arithAtomFold _ p _ _ _ => .single p
  | .arithAtomUnfold _ p _ _ _ => .single p
  | .norm _ _ _ => .nil
  | .farkas _ _ _ => .nil
  | .pConstExact _ _ _ _ => .nil
  | .convIntro _ p _ _ _ => .single p
  | .convElim _ p _ _ _ => .single p
  | .bernConeEmpty _ regionP _ _ _ _ _ _ => .single regionP
  | .bernCone _ regionP _ _ _ _ _ _ => .single regionP
  | .promise _ supplier consumer _ _ _ _ =>
      .cons (b := .pt) supplier (.single consumer)
  | .psdCertOf _ _ _ _ _ => .nil
  | .psdCertT _ _ _ _ _ _ => .nil
  | .psdCertDD _ _ _ _ _ _ => .nil
  | .psdCertK _ _ _ _ _ _ _ _ _ _ => .nil
  | .reluNN _ _ _ => .nil
  | .reluAbove _ _ _ => .nil
  | .reluPos _ premise _ _ => .single premise
  | .reluNeg _ premise _ _ => .single premise
  | .reluSplit _ activeP inactiveP _ _ _ _ =>
      .cons (b := .pt) activeP (.single inactiveP)
  | .lirpa _ lowerPremise upperPremise _ _ _ _ _ _ _ _ =>
      .cons (b := .pt) lowerPremise (.single upperPremise)
  | .cellInInterior _ premise _ _ _ _ => .single premise
  | .cellOut _ premise _ _ _ _ _ => .single premise
  | .subdivide _ regionPremise _ branchPremise _ _ _ _ _ _ =>
      .cons (b := .pt) regionPremise (.ofFin branchPremise)
  | .pBound _ components _ _ => .ofList components
  | .syzygy _ components _ _ => .ofList components

/-- The conclusion of a rule instance. -/
def concl : BLRule → Sequent
  | .ax seq => seq
  | .weaken seq _ _ => seq
  | .cut seq _ _ _ => seq
  | .andI seq _ _ => seq
  | .andELeft seq _ _ => seq
  | .andERight seq _ _ => seq
  | .orILeft seq _ _ => seq
  | .orIRight seq _ _ => seq
  | .orE seq _ _ => seq
  | .eqRefl seq _ => seq
  | .eqSym seq _ _ _ => seq
  | .antisym seq _ _ _ _ => seq
  | .eqElim seq _ _ _ _ _ _ => seq
  | .arithAtomFold seq _ _ _ _ => seq
  | .arithAtomUnfold seq _ _ _ _ => seq
  | .norm seq _ _ => seq
  | .farkas seq _ _ => seq
  | .pConstExact seq _ _ _ => seq
  | .convIntro seq _ _ _ _ => seq
  | .convElim seq _ _ _ _ => seq
  | .bernConeEmpty seq _ _ _ _ _ _ _ => seq
  | .bernCone seq _ _ _ _ _ _ _ => seq
  | .promise seq _ _ _ _ _ _ => seq
  | .psdCertOf seq _ _ _ _ => seq
  | .psdCertT seq _ _ _ _ _ => seq
  | .psdCertDD seq _ _ _ _ _ => seq
  | .psdCertK seq _ _ _ _ _ _ _ _ _ => seq
  | .reluNN seq _ _ => seq
  | .reluAbove seq _ _ => seq
  | .reluPos seq _ _ _ => seq
  | .reluNeg seq _ _ _ => seq
  | .reluSplit seq _ _ _ _ _ _ => seq
  | .lirpa seq _ _ _ _ _ _ _ _ _ _ => seq
  | .cellInInterior seq _ _ _ _ _ => seq
  | .cellOut seq _ _ _ _ _ _ => seq
  | .subdivide seq _ _ _ _ _ _ _ _ _ => seq
  | .pBound seq _ _ _ => seq
  | .syzygy seq _ _ _ => seq

end BLRule

/-- The presentation: sequents as loose generators over the single
claim context, the wired rule families as gated multicell generators.
Indexed by the hypernet, which the declaration-aware gates consult (see
the module header): the hypernet is part of the presented artifact, and
no semantic notion enters until the interpretation. -/
def blPresentation (H : Hypernet) : VdcPresentation BLCtx where
  Loose _ _ := Sequent
  Rule := BLRule
  gate := BLRule.gate H
  srcL _ := BLCtx.pt
  srcR _ := BLCtx.pt
  tgtL _ := BLCtx.pt
  tgtR _ := BLCtx.pt
  tops := BLRule.tops
  bot := BLRule.concl
  left _ := ⟨⟩
  right _ := ⟨⟩

/-- The tight functor of the interpretation: the wrapping bijection on
the single context. -/
def blTight : BLCtx ⥤ ImplDouble BLCtx where
  obj x := ⟨x⟩
  map f := f

/-- **The fold lemma for the list builder, at the implication carrier**:
the interpreted fold of a list-built premise string is the validity of
every component.  Both directions definitional at each step (the
implication carrier's loose composition is conjunction with `True` as
unit), so the lemma is the induction and nothing else. -/
theorem fold_ofList_valid (H : Hypernet) :
    ∀ (l : List Sequent),
    ((LoosePath.ofList (a := BLCtx.pt)
        (L := fun _ _ : BLCtx => Sequent) l).map blTight.obj
      (fun seq => seq.semanticallyValid H)).fold ↔
      ∀ c ∈ l, c.semanticallyValid H
  | [] => ⟨fun _ c hc => (nomatch hc), fun _ => trivial⟩
  | c :: t => by
      rw [List.forall_mem_cons]
      exact and_congr Iff.rfl (fold_ofList_valid H t)

/-- **The fold lemma for the family builder, at the implication
carrier**: the interpreted fold of a `Fin`-built premise string is the
validity of every branch. -/
theorem fold_ofFin_valid (H : Hypernet) :
    ∀ {n : Nat} (f : Fin n → Sequent),
    ((LoosePath.ofFin (a := BLCtx.pt)
        (L := fun _ _ : BLCtx => Sequent) f).map blTight.obj
      (fun seq => seq.semanticallyValid H)).fold ↔
      ∀ k, (f k).semanticallyValid H
  | 0, _ => ⟨fun _ k => k.elim0, fun _ => trivial⟩
  | n + 1, f => by
      rw [Fin.forall_fin_succ]
      exact and_congr Iff.rfl (fold_ofFin_valid H fun k => f k.succ)

/-- **The interpretation of the wired fragment**: a sequent is
read as its semantic validity over `H`, and each rule generator's
component is its landed soundness lemma, the gate supplying the
row-shaped side conditions. -/
def blInterpretation (H : Hypernet) :
    VdcInterpretation (blPresentation H) (ImplDouble BLCtx) where
  tight := blTight
  interpLoose := fun seq => seq.semanticallyValid H
  component := fun r hr =>
    match r, hr with
    | .ax _, h => by exact ⟨fun _ => sound_ax h⟩
    | .weaken _ _ _, ⟨h₁, h₂⟩ => by
        exact ⟨fun hs => sound_weaken hs.1 h₁ h₂⟩
    | .cut _ _ _ _, ⟨h₁, h₂, h₃, h₄⟩ => by
        exact ⟨fun hs => sound_cut hs.1 hs.2.1 h₁ h₂ h₃ h₄⟩
    | .andI _ _ _, ⟨h₁, h₂, h₃⟩ => by
        exact ⟨fun hs => sound_andI hs.1 hs.2.1 h₁ h₂ h₃⟩
    | .andELeft _ _ _, ⟨h₁, h₂⟩ => by
        exact ⟨fun hs => sound_andE_left hs.1 h₁ h₂⟩
    | .andERight _ _ _, ⟨h₁, h₂⟩ => by
        exact ⟨fun hs => sound_andE_right hs.1 h₁ h₂⟩
    | .orILeft _ _ _, ⟨h₁, h₂⟩ => by
        exact ⟨fun hs => sound_orI_left hs.1 h₁ h₂⟩
    | .orIRight _ _ _, ⟨h₁, h₂⟩ => by
        exact ⟨fun hs => sound_orI_right hs.1 h₁ h₂⟩
    | .orE _ _ _, ⟨h₁, h₂, h₃⟩ => by
        exact ⟨fun hs => sound_orE hs.1 hs.2.1 h₁ h₂ h₃⟩
    | .eqRefl _ _, ⟨h₁, h₂, h₃⟩ => by
        exact ⟨fun _ => sound_eqRefl h₁ h₂ h₃⟩
    | .eqSym _ _ _ _, ⟨h₁, h₂, h₃⟩ => by
        exact ⟨fun hs => sound_eqSym hs.1 h₁ h₂ h₃⟩
    | .antisym _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅⟩ => by
        exact ⟨fun hs => sound_antisym hs.1 hs.2.1 h₁ h₂ h₃ h₄ h₅⟩
    | .eqElim _ _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨fun hs => sound_eqElim hs.1 hs.2.1 h₁ h₂ h₃ h₄ h₅ h₆⟩
    | .arithAtomFold _ _ _ _ _, ⟨h₁, h₂, h₃⟩ => by
        exact ⟨fun hs => sound_arithAtom_fold hs.1 h₁ h₂ h₃⟩
    | .arithAtomUnfold _ _ _ _ _, ⟨h₁, h₂, h₃⟩ => by
        exact ⟨fun hs => sound_arithAtom_unfold hs.1 h₁ h₂ h₃⟩
    | .norm _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨fun _ => sound_norm h₁ h₂ h₃ h₄ h₅ h₆⟩
    | .farkas _ _ _, ⟨h₁, h₂, h₃, h₄, h₅⟩ => by
        exact ⟨fun _ => sound_farkas h₁ h₂ h₃ h₄ h₅⟩
    | .pConstExact _ _ _ _, ⟨h₁, h₂⟩ => by
        exact ⟨fun _ => sound_pConstExact h₁ h₂⟩
    | .convIntro _ _ _ _ _, ⟨h₁, h₂, h₃, h₄⟩ => by
        exact ⟨fun hs => sound_convIntro hs.1 h₁ h₂ h₃ h₄⟩
    | .convElim _ _ _ _ _, ⟨h₁, h₂, h₃⟩ => by
        exact ⟨fun hs => sound_convElim hs.1 h₁ h₂ h₃⟩
    | .bernConeEmpty _ _ _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => by
        exact ⟨fun hs => sound_bernCone_empty hs.1 h₁ h₂ h₃ h₄ h₅ h₆ h₇⟩
    | .bernCone _ _ _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨fun hs => sound_bernCone hs.1 h₁ h₂ h₃ h₄ h₅ h₆⟩
    | .promise seq supplier consumer contract path iface ctx,
        ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => by
        exact ⟨fun hs => sound_promise
          ⟨seq, supplier, consumer, contract, path, iface, ctx,
            h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ hs.1 hs.2.1⟩
    | .psdCertOf _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨fun _ => sound_psdCertOf h₁ h₂ h₃ h₄ h₅ h₆⟩
    | .psdCertT _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨fun _ => sound_psdCertT h₁ h₂ h₃ h₄ h₅ h₆⟩
    | .psdCertDD _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨fun _ => sound_psdCertDD h₁ h₂ h₃ h₄ h₅ h₆⟩
    | .psdCertK _ _ _ _ _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨fun _ => sound_psdCertK h₁ h₂ h₃ h₄ h₅ h₆⟩
    | .reluNN _ _ _, ⟨h₁, h₂⟩ => by
        exact ⟨fun _ => sound_reluNN h₁ h₂⟩
    | .reluAbove _ _ _, ⟨h₁, h₂⟩ => by
        exact ⟨fun _ => sound_reluAbove h₁ h₂⟩
    | .reluPos _ _ _ _, ⟨h₁, h₂, h₃, h₄⟩ => by
        exact ⟨fun hs => sound_reluPos hs.1 h₁ h₂ h₃ h₄⟩
    | .reluNeg _ _ _ _, ⟨h₁, h₂, h₃, h₄⟩ => by
        exact ⟨fun hs => sound_reluNeg hs.1 h₁ h₂ h₃ h₄⟩
    | .reluSplit _ _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => by
        exact ⟨fun hs => sound_reluSplit hs.1 hs.2.1 h₁ h₂ h₃ h₄ h₅ h₆ h₇⟩
    | .lirpa _ _ _ _ _ _ _ _ _ _ _,
        ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄⟩ => by
        exact ⟨fun hs => sound_lirpa hs.1 hs.2.1 h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
          h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄⟩
    | .cellInInterior _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨fun hs => sound_cellInInterior hs.1 h₁ h₂ h₃ h₄ h₅ h₆⟩
    | .cellOut _ _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => by
        exact ⟨fun hs => sound_cellOut hs.1 h₁ h₂ h₃ h₄ h₅ h₆⟩
    | .subdivide _ _ _ branchPremise _ _ _ _ _ _, ⟨h₁, h₂, h₃, h₄, h₅⟩ => by
        exact ⟨fun hs => sound_subdivide hs.1
          ((fold_ofFin_valid H branchPremise).mp hs.2) h₁ h₂ h₃ h₄ h₅⟩
    | .pBound _ components _ _, ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => by
        exact ⟨fun hs => sound_pBound
          ((fold_ofList_valid H components).mp hs) h₁ h₂ h₃ h₄ h₅ h₆ h₇⟩
    | .syzygy seq components combination conclusion,
        ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => by
        exact ⟨fun hs => sound_syzygy
          ⟨seq, components, combination, conclusion,
            h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
          ((fold_ofList_valid H components).mp hs)⟩

end QtslSem

end SuFunctor
