import SuFunctor.QtslSem.Decode.Acceptance
import Qtsl.Elaborators

/-!
# The alias-citation tier through acceptance (v1.1)

Three rows of the acceptance-coverage ledger, discharged:
**TaylorBound**,
**RootEval**, and **QSatFromRegion** all unpack to the `pConstExact`
class the acceptance theorem accepts, and this module drives each
through the ACTUAL acceptor — staged rows in, accepted value with
carried proof out, alias semantic face recovered from the accepted
value through the landed unpacking lemmas (`Qtsl.Elaborators`).

* **TaylorBound (T7)** — producer-side unpack: the staged leaf IS the
  elaborated `taylorFormula` (partial sum expanded before the wire, the
  transcendental target in no row).  The plain evaluation route accepts
  it (`accept_taylor`), and `accepted_taylor_le_exp` recovers
  `q ≤ e^{θT}` from the accepted value via `taylorElab_le_exp` — the
  θ-nonnegativity side condition supplied at recovery, producer-side
  data by design.
* **RootEval (T19) / QSatFromRegion** — the citation proper: a claim
  carrying a ternary `qsat_warrant` (a region-satisfaction child whose
  formula is the cited `SInit` face's argument, over a `qraSublevel`
  atom) AND `qsat_eval` (the initial-membership leaf,
  `rootEvalFormula`'s shape — the QSatFromRegion dissolution's demand
  set).  The v1.1 walk
  (`resolveCitation` + `sequentMatchesSublevel`, `Decode.Acceptance`)
  resolves the citation to its unpacked core and accepts it
  (`accept_citation`); `accepted_rootEval_member` recovers the exact
  membership `V(x₀) ≤ thr` from the accepted value via
  `rootEvalFormula_true_iff`.

Refusal fixtures, one per citation check, each a green theorem and a
preregistered mutant witness (MA1–MA3b; MA4's
witness is the landed `refuse_region_tier`): a mis-tied warrant, a
box region atom in the sublevel slot, a threshold that does not match
the leaf's right side, and a non-`.le` comparator under an otherwise
coherent citation.  Every refusal fires BEFORE the evaluation gate, so
all four stay bare kernel `decide` (the prereg addendum's reorder).

The honest boundary (the module docs of `Decode.Acceptance`, repeated
where the fixtures live): the accepted conclusion per claim is the
LEAF-level SU judgment; the warrant's region-satisfaction premise is
recorded and structurally verified, not discharged, and the
cert-family content tie (leaf left side vs the family's table
polynomial) is class-stratum campaign material.
-/

namespace SuFunctor

namespace QtslSem

namespace Decode

open PPLC PPLC.Geolog

/-! ## TaylorBound: the elaborated leaf through the plain route

TaylorDemo's constants (q = 8/3, θ = 1/2, T = 2, n = 3): the order-3
partial sum of `e¹` is exactly 8/3, so the staged leaf `8/3 ≤ 8/3`
holds tight at equality — a partial-sum corruption cannot hide in
slack.  Element layout: 0–8 as the standard fixture; 9 the one shared
`Term` literal (both sides of the comparison); 10–11 the formulas. -/

/-- The TaylorBound fixture's element declarations. -/
def taylorDecls : List GOp :=
  [.elta (.ext 0 141),   -- 0 : QJudgment
   .elta (.ext 0 111),   -- 1 : System
   .elta (.ext 0 103),    -- 2 : Spec
   .elta (.ext 0 64),    -- 3 : ForallSpec
   .elta (.ext 0 63),    -- 4 : PathPred
   .elta (.ext 0 151),   -- 5 : QSat
   .elta (.ext 0 142),   -- 6 : QProof
   .elta (.ext 0 17),    -- 7 : Proof
   .elta (.ext 0 16),    -- 8 : Judgment
   .elta (.ext 0 14),    -- 9 : Term (8/3, shared by both sides)
   .elta (.ext 0 15),    -- 10 : Formula (⊤)
   .elta (.ext 0 15)]    -- 11 : Formula (8/3 ≤ 8/3)

/-- The TaylorBound fixture's ground rows: the producer-expanded
partial sum is the literal `8/3`, cited on both sides of the `≤`. -/
def taylorGround : List GOp :=
  [.funa (.ext 0 336) [.lit 0 [1, 8, 3]] (.ref (.loc 9)),    -- TConst 8/3
   .funa (.ext 0 352) [] (.ref (.loc 10)),                   -- FTrue
   .funa (.ext 0 343) [.ref (.loc 9), .ref (.loc 9)]
     (.ref (.loc 11)),                                       -- FAtomLE
   .funa (.ext 0 354) [.ref (.loc 8)] (.ref (.loc 10)),      -- Judgment/pre
   .funa (.ext 0 355) [.ref (.loc 8)] (.ref (.loc 11)),      -- Judgment/post
   .funa (.ext 0 358) [.ref (.loc 7)] (.ref (.loc 8))]       -- Proof/concludes

/-- The TaylorBound fixture's claim rows: the plain evaluation route. -/
def taylorClaimRows : List GOp :=
  [.funa (.ext 0 917) [.ref (.loc 5)] (.ref (.loc 0)),       -- QSat/judgment
   .funa (.ext 0 918) [.ref (.loc 5)] (.ref (.loc 1)),       -- QSat/sys
   .funa (.ext 0 919) [.ref (.loc 5)] (.ref (.loc 2)),       -- QSat/spec
   .rela (.ext 0 921) [.ref (.loc 7), .ref (.loc 5)],        -- qsat_eval (eval, sat)
   .funa (.ext 0 899) [.ref (.loc 6)] (.ref (.loc 0))]       -- QProof/concludes

/-- The TaylorBound fixture's op list. -/
def taylorOps : List GOp :=
  taylorDecls ++ taylorGround ++ fixtureSpecRows ++ taylorClaimRows

/-- Its scanned tables. -/
def taylorTbls : QRowTbls :=
  match scanQtslOps fixtureDeps taylorOps with
  | .ok t => t
  | .error _ => ⟨[], [], []⟩

/-- Its expected decoded presentation. -/
def taylorExpected : QtslPresentation :=
  { judgments := [0]
    sats := [⟨5, 0, 1,
      ⟨2, [⟨3, "SProbGE", [.lit 0 [1, 9, 10], .ref (.loc 4)]⟩], []⟩,
      none, some 7⟩]
    satConfs := []
    specEquivs := []
    regionSats := []
    invScopes := []
    proofs := [⟨6, 0⟩] }

/-- The decoded TaylorBound leaf sequent: `⊤ ⊢ 8/3 ≤ 8/3`.  (`mkRat`
spelling throughout the decode-facing defs: the decoder's `qOfVal`
produces `mkRat`, and division-spelled literals are not
elaborator-defeq to it — the r1 lesson; the pretty `8/3` reappears in
the recovery layer through `mkRat_83`.) -/
def taylorLeafSeq : Sequent :=
  ⟨.tt, .atom .le (.const (mkRat 8 3)) (.const (mkRat 8 3))⟩

/-- The staged literal, prettily: `mkRat 8 3 = 8/3`. -/
theorem mkRat_83 : mkRat 8 3 = (8/3 : Rat) := by
  rw [Rat.mkRat_eq_div]
  norm_num

/-- The staged leaf's gate fact. -/
theorem taylorEval :
    (Formula.atom .le (.const (mkRat 8 3))
      (.const (mkRat 8 3))).evalClosed = some true := by
  norm_num [mkRat_83, Formula.evalClosed, Term.evalQ?, BowTie.evalQ]

/-- The expected accepted TaylorBound leaf. -/
def taylorLeaf : AcceptedLeaf where
  elem := 5
  seq := taylorLeafSeq
  cmp := .le
  lhs := .const (mkRat 8 3)
  rhs := .const (mkRat 8 3)
  post_eq := rfl
  eval_true := taylorEval
  preWF := rfl
  postWF := rfl
  valid := ⟨fun H => groundLeaf_valid_through_M taylorEval rfl H⟩

/-- The expected accepted value. -/
def taylorAccepted : QtslAccepted :=
  ⟨taylorExpected, [taylorLeaf]⟩

/-- The staged TaylorBound leaf decodes. -/
theorem taylor_leaf_seq :
    leafSequent taylorTbls 7 = .ok taylorLeafSeq := by
  rfl

/-- The TaylorBound leaf is accepted (kernel-first discipline: the one
stuck redex — the Rat gate — crossed by `dif_pos` with its `norm_num`
fact). -/
theorem acceptGroundLeaf_taylor :
    acceptGroundLeaf 5 taylorLeafSeq = some taylorLeaf := by
  have key : acceptGroundLeaf 5 taylorLeafSeq =
      if _h : (Formula.atom .le (.const (mkRat 8 3))
          (.const (mkRat 8 3))).evalClosed = some true then
        some taylorLeaf
      else none := rfl
  rw [key, dif_pos taylorEval]

/-- Through the decode. -/
theorem acceptLeaf_taylor :
    acceptLeaf taylorTbls 5 7 = some taylorLeaf := by
  have key : acceptLeaf taylorTbls 5 7 =
      acceptGroundLeaf 5 taylorLeafSeq := by
    unfold acceptLeaf
    rw [taylor_leaf_seq]
  rw [key, acceptGroundLeaf_taylor]

/-- The claim roster whole. -/
theorem acceptLeaves_taylor :
    acceptLeaves taylorTbls taylorExpected.regionSats
      taylorExpected.sats = some [taylorLeaf] := by
  have key : acceptLeaves taylorTbls taylorExpected.regionSats
      taylorExpected.sats =
      (match acceptLeaf taylorTbls 5 7 with
       | none => none
       | some l => some [l]) := rfl
  rw [key, acceptLeaf_taylor]

/-- **The TaylorBound fixture**: a container exercising the TaylorBound
alias — its elaborated leaf staged as rows — is accepted whole by the
acceptor. -/
theorem accept_taylor :
    acceptQtslOps fixtureDeps taylorOps = some taylorAccepted := by
  have k1 : acceptQtslOps fixtureDeps taylorOps =
      (match assembleQtsl taylorTbls with
       | .error _ => none
       | .ok pres =>
         if acceptFragmentGate pres then
           match acceptLeaves taylorTbls pres.regionSats pres.sats with
           | none => none
           | some ls => some ⟨pres, ls⟩
         else none) := by
    unfold acceptQtslOps
    rw [(by decide :
      scanQtslOps fixtureDeps taylorOps = .ok taylorTbls)]
    all_goals first | rfl | with_unfolding_all rfl
  rw [k1, (by decide :
    assembleQtsl taylorTbls = .ok taylorExpected)]
  show (if acceptFragmentGate taylorExpected then
          match acceptLeaves taylorTbls taylorExpected.regionSats
            taylorExpected.sats with
          | none => none
          | some ls => some (⟨taylorExpected, ls⟩ : QtslAccepted)
        else none) = some taylorAccepted
  rw [if_pos (by decide : acceptFragmentGate taylorExpected = true),
    acceptLeaves_taylor]
  rfl

/-- The TaylorBound leaf at the SU endpoint, through acceptance. -/
theorem accepted_taylor_su_sound (H : Hypernet) :
    Adequacy.cylWallW H taylorLeafSeq ∈
      (Adequacy.sequentSpec H taylorLeafSeq).modelClass :=
  (Adequacy.semanticallyValid_iff_fibre H taylorLeafSeq).mp
    (acceptQtslOps_sound fixtureDeps taylorOps taylorAccepted
      accept_taylor taylorLeaf (List.Mem.head _) H)

/-- The producer-side partial-sum identity: the staged literal IS the
order-3 Taylor partial sum of `e^{(1/2)·2}`. -/
theorem taylorPartialSum_demo : taylorPartialSum (1/2) 2 3 = 8/3 := by
  norm_num [taylorPartialSum, Finset.sum_range_succ, Nat.factorial]

/-- **The TaylorBound semantic face, recovered from the accepted
value**: `8/3 ≤ e^{(1/2)·2}` — the transcendental conclusion the
checker never computed, read back through the landed unpacking lemma
(`taylorElab_le_exp`) from the accepted leaf's carried gate fact.  The
θ-nonnegativity is supplied here, at recovery: it is producer-side
data, in no row by design. -/
theorem accepted_taylor_le_exp (a : QtslAccepted)
    (h : acceptQtslOps fixtureDeps taylorOps = some a) :
    ((8/3 : Rat) : ℝ) ≤ Real.exp (((1/2 : Rat) : ℝ) * ((2 : Nat) : ℝ)) := by
  have ha : a = taylorAccepted := by
    rw [accept_taylor] at h
    injection h with h
    exact h.symm
  subst ha
  have heval : (taylorFormula (8/3) (1/2) 2 3).evalClosed = some true := by
    unfold taylorFormula
    rw [taylorPartialSum_demo, ← mkRat_83]
    exact taylorLeaf.eval_true
  exact taylorElab_le_exp (by norm_num) heval

/-! ## RootEval / QSatFromRegion: the citation proper

The demo instance: `V = (1/4)·x₀ + 1/2` at `x₀ = (2, 0, …)`,
threshold 1 — `V(x₀) = 1`, tight at equality, so no walk corruption
can hide in slack.  The claim carries BOTH routes; the warrant's
region-satisfaction child is rooted at the spec's root over a
`qraSublevel` atom at the leaf's own threshold. -/

/-- The evaluation point `(2, 0, 0, …)`. -/
def x0demo : Nat → Rat :=
  fun i => if i = 0 then 2 else 0

/-- The sparse polynomial `(1/4)·x₀ + 1/2` (`mkRat` spelling — the
decode-facing coefficient form, per the r1 lesson; `Poly.eval` reads
it identically). -/
def Vdemo : QArith.Poly :=
  [([(0, 1)], mkRat 1 4), ([], mkRat 1 2)]

/-- The citation fixture's element declarations. -/
def citationDecls : List GOp :=
  [.elta (.ext 0 141),   -- 0 : QJudgment
   .elta (.ext 0 111),   -- 1 : System
   .elta (.ext 0 103),    -- 2 : Spec
   .elta (.ext 0 64),    -- 3 : ForallSpec (the SInit face)
   .elta (.ext 0 61),    -- 4 : StatePred (φ, the face's argument)
   .elta (.ext 0 151),   -- 5 : QSat
   .elta (.ext 0 142),   -- 6 : QProof
   .elta (.ext 0 17),    -- 7 : Proof
   .elta (.ext 0 16),    -- 8 : Judgment
   .elta (.ext 0 14),    -- 9 : Term (1)
   .elta (.ext 0 14),    -- 10 : Term (2)
   .elta (.ext 0 14),    -- 11 : Term (1·2 — the power)
   .elta (.ext 0 14),    -- 12 : Term ((1·2)·1 — the monomial)
   .elta (.ext 0 14),    -- 13 : Term (1/4)
   .elta (.ext 0 14),    -- 14 : Term (1/4 · mono)
   .elta (.ext 0 14),    -- 15 : Term (1/2)
   .elta (.ext 0 14),    -- 16 : Term (1/2 · 1)
   .elta (.ext 0 14),    -- 17 : Term (0)
   .elta (.ext 0 14),    -- 18 : Term (the tail sum)
   .elta (.ext 0 14),    -- 19 : Term (the closed polynomial)
   .elta (.ext 0 15),    -- 20 : Formula (⊤)
   .elta (.ext 0 15),    -- 21 : Formula (the membership atom)
   .elta (.ext 0 146),   -- 22 : QRegionAtom
   .elta (.ext 0 143),   -- 23 : QCertFam
   .elta (.ext 0 155)]   -- 24 : QRegionSat

/-- The citation fixture's ground rows: `polyClosedTerm x0demo Vdemo`
staged literally (the builders' fold structure, elements 9–19), the
membership atom `… ≤ 1` sharing the threshold literal (element 9), and
the judgment/leaf hops. -/
def citationGround : List GOp :=
  [.funa (.ext 0 336) [.lit 0 [1, 1, 1]] (.ref (.loc 9)),    -- TConst 1
   .funa (.ext 0 336) [.lit 0 [1, 2, 1]] (.ref (.loc 10)),   -- TConst 2
   .funa (.ext 0 338) [.ref (.loc 9), .ref (.loc 10)]
     (.ref (.loc 11)),                                       -- TMul (power)
   .funa (.ext 0 338) [.ref (.loc 11), .ref (.loc 9)]
     (.ref (.loc 12)),                                       -- TMul (mono)
   .funa (.ext 0 336) [.lit 0 [1, 1, 4]] (.ref (.loc 13)),   -- TConst 1/4
   .funa (.ext 0 338) [.ref (.loc 13), .ref (.loc 12)]
     (.ref (.loc 14)),                                       -- TMul (scaled)
   .funa (.ext 0 336) [.lit 0 [1, 1, 2]] (.ref (.loc 15)),   -- TConst 1/2
   .funa (.ext 0 338) [.ref (.loc 15), .ref (.loc 9)]
     (.ref (.loc 16)),                                       -- TMul (const mono)
   .funa (.ext 0 336) [.lit 0 [1, 0, 1]] (.ref (.loc 17)),   -- TConst 0
   .funa (.ext 0 337) [.ref (.loc 16), .ref (.loc 17)]
     (.ref (.loc 18)),                                       -- TAdd (tail)
   .funa (.ext 0 337) [.ref (.loc 14), .ref (.loc 18)]
     (.ref (.loc 19)),                                       -- TAdd (poly)
   .funa (.ext 0 352) [] (.ref (.loc 20)),                   -- FTrue
   .funa (.ext 0 343) [.ref (.loc 19), .ref (.loc 9)]
     (.ref (.loc 21)),                                       -- FAtomLE
   .funa (.ext 0 354) [.ref (.loc 8)] (.ref (.loc 20)),      -- Judgment/pre
   .funa (.ext 0 355) [.ref (.loc 8)] (.ref (.loc 21)),      -- Judgment/post
   .funa (.ext 0 358) [.ref (.loc 7)] (.ref (.loc 8))]       -- Proof/concludes

/-- The citation fixture's specification rows: the `SInit`-formed face
over φ (element 4) — the only face form the event-4 tie admits —
attached by `spec_forall` (f, spec). -/
def citationSpecRows : List GOp :=
  [.funa (.ext 0 653) [.ref (.loc 4)] (.ref (.loc 3)),       -- SInit
   .rela (.ext 0 742) [.ref (.loc 3), .ref (.loc 2)]]        -- spec_forall

/-- The citation fixture's decoded specification. -/
def citationSpecVal : QSpecVal :=
  ⟨2, [⟨3, "SInit", [.ref (.loc 4)]⟩], []⟩

/-- The citation fixture's claim rows: BOTH routes — the ternary
warrant citing the `SInit` face and the evaluation leaf, each at the
event-4 wire order. -/
def citationClaimRows : List GOp :=
  [.funa (.ext 0 917) [.ref (.loc 5)] (.ref (.loc 0)),       -- QSat/judgment
   .funa (.ext 0 918) [.ref (.loc 5)] (.ref (.loc 1)),       -- QSat/sys
   .funa (.ext 0 919) [.ref (.loc 5)] (.ref (.loc 2)),       -- QSat/spec
   .rela (.ext 0 920)
     [.ref (.loc 3), .ref (.loc 5), .ref (.loc 24)],         -- qsat_warrant (f, sat, warrant)
   .rela (.ext 0 921) [.ref (.loc 7), .ref (.loc 5)],        -- qsat_eval (eval, sat)
   .funa (.ext 0 899) [.ref (.loc 6)] (.ref (.loc 0))]       -- QProof/concludes

/-- The citation fixture's region rows: the warrant child whose formula
IS the face's `SInit` argument φ, over a `qraSublevel` atom at
threshold 1. -/
def citationRegionRows : List GOp :=
  [.funa (.ext 0 938) [.ref (.loc 24)] (.ref (.loc 0)),      -- QRegionSat/judgment
   .funa (.ext 0 939) [.ref (.loc 24)] (.ref (.loc 4)),      -- QRegionSat/formula = φ
   .funa (.ext 0 940) [.ref (.loc 24)] (.ref (.loc 22)),     -- QRegionSat/region
   .funa (.ext 0 906) [.ref (.loc 23), .lit 0 [1, 1, 1]]
     (.ref (.loc 22))]                                       -- qraSublevel

/-- The citation fixture's op list. -/
def citationOps : List GOp :=
  citationDecls ++ citationGround ++ citationSpecRows ++
    citationClaimRows ++ citationRegionRows

/-- Its scanned tables. -/
def citationTbls : QRowTbls :=
  match scanQtslOps fixtureDeps citationOps with
  | .ok t => t
  | .error _ => ⟨[], [], []⟩

/-- Its expected decoded presentation: the claim with BOTH routes, the
region-satisfaction roster carrying the cited child. -/
def citationExpected : QtslPresentation :=
  { judgments := [0]
    sats := [⟨5, 0, 1, citationSpecVal, some (3, 24), some 7⟩]
    satConfs := []
    specEquivs := []
    regionSats := [⟨24, 0, 4, 22⟩]
    invScopes := []
    proofs := [⟨6, 0⟩] }

/-- The decoded membership leaf sequent:
`⊤ ⊢ polyClosedTerm x0demo Vdemo ≤ 1` — `rootEvalFormula`'s shape,
exactly. -/
def citationLeafSeq : Sequent :=
  ⟨.tt, rootEvalFormula x0demo Vdemo 1⟩

/-- The membership leaf's gate fact: `V(x₀) = 1 ≤ 1`, exact.  (Bare
`decide +kernel`: the kernel replays the closed Rat evaluation — r1
measured the `norm_num` fallback dead.) -/
theorem citationEval :
    (rootEvalFormula x0demo Vdemo 1).evalClosed = some true := by
  decide +kernel

/-- The expected accepted citation leaf: the `pConstExact` core the
walk unpacks to. -/
def citationLeaf : AcceptedLeaf where
  elem := 5
  seq := citationLeafSeq
  cmp := .le
  lhs := polyClosedTerm x0demo Vdemo
  rhs := .const 1
  post_eq := rfl
  eval_true := citationEval
  preWF := rfl
  postWF := rfl
  valid := ⟨fun H => groundLeaf_valid_through_M citationEval rfl H⟩

/-- The expected accepted value. -/
def citationAccepted : QtslAccepted :=
  ⟨citationExpected, [citationLeaf]⟩

/-- The staged membership leaf decodes to exactly the elaborated
formula. -/
theorem citation_leaf_seq :
    leafSequent citationTbls 7 = .ok citationLeafSeq := by
  rfl

/-- The citation walk resolves: face membership, `SInit` form, root
tie, sublevel shape, family sort — threshold 1 out. -/
theorem resolveCitation_citation :
    resolveCitation citationTbls citationExpected.regionSats
      citationSpecVal 3 24 = some 1 := by
  decide

/-- The decoded leaf is the sublevel's own membership reading. -/
theorem sequentMatches_citation :
    sequentMatchesSublevel citationLeafSeq 1 = true := by
  decide

/-- The membership core is accepted (the key's dite condition spelled
via `rootEvalFormula` so `dif_pos citationEval` matches — the r1
pattern-mismatch lesson; the spellings are defeq, which is all the
`rfl` needs). -/
theorem acceptGroundLeaf_citation :
    acceptGroundLeaf 5 citationLeafSeq = some citationLeaf := by
  have key : acceptGroundLeaf 5 citationLeafSeq =
      if _h : (rootEvalFormula x0demo Vdemo 1).evalClosed = some true then
        some citationLeaf
      else none := rfl
  rw [key, dif_pos citationEval]

/-- The claim roster whole, THROUGH the citation arm: the key equation
is projection-only (`rfl`), the walk stages ride their own kernel
verdicts (`resolveCitation_citation`, `citation_leaf_seq`,
`sequentMatches_citation`), and the one stuck redex is crossed by the
accepted core. -/
theorem acceptLeaves_citation :
    acceptLeaves citationTbls citationExpected.regionSats
      citationExpected.sats = some [citationLeaf] := by
  have key : acceptLeaves citationTbls citationExpected.regionSats
      citationExpected.sats =
      (match resolveCitation citationTbls citationExpected.regionSats
          citationSpecVal 3 24 with
       | none => none
       | some thr =>
         match leafSequent citationTbls 7 with
         | .error _ => none
         | .ok s =>
           if sequentMatchesSublevel s thr then
             match acceptGroundLeaf 5 s with
             | none => none
             | some l => some [l]
           else none) := rfl
  rw [key, resolveCitation_citation, citation_leaf_seq]
  show (if sequentMatchesSublevel citationLeafSeq 1 then
          match acceptGroundLeaf 5 citationLeafSeq with
          | none => none
          | some l => some [l]
        else none) = some [citationLeaf]
  rw [if_pos sequentMatches_citation, acceptGroundLeaf_citation]

/-- **The citation fixture**: a container exercising QSatFromRegion's
citation shape — warrant and membership leaf together — is accepted
whole by the acceptor, its region-satisfaction premise recorded on the
accepted presentation. -/
theorem accept_citation :
    acceptQtslOps fixtureDeps citationOps = some citationAccepted := by
  have k1 : acceptQtslOps fixtureDeps citationOps =
      (match assembleQtsl citationTbls with
       | .error _ => none
       | .ok pres =>
         if acceptFragmentGate pres then
           match acceptLeaves citationTbls pres.regionSats pres.sats with
           | none => none
           | some ls => some ⟨pres, ls⟩
         else none) := by
    unfold acceptQtslOps
    rw [(by decide :
      scanQtslOps fixtureDeps citationOps = .ok citationTbls)]
    all_goals first | rfl | with_unfolding_all rfl
  rw [k1, (by decide :
    assembleQtsl citationTbls = .ok citationExpected)]
  show (if acceptFragmentGate citationExpected then
          match acceptLeaves citationTbls citationExpected.regionSats
            citationExpected.sats with
          | none => none
          | some ls => some (⟨citationExpected, ls⟩ : QtslAccepted)
        else none) = some citationAccepted
  rw [if_pos (by decide : acceptFragmentGate citationExpected = true),
    acceptLeaves_citation]
  rfl

/-- The membership leaf at the SU endpoint, through acceptance. -/
theorem accepted_citation_su_sound (H : Hypernet) :
    Adequacy.cylWallW H citationLeafSeq ∈
      (Adequacy.sequentSpec H citationLeafSeq).modelClass :=
  (Adequacy.semanticallyValid_iff_fibre H citationLeafSeq).mp
    (acceptQtslOps_sound fixtureDeps citationOps citationAccepted
      accept_citation citationLeaf (List.Mem.head _) H)

/-- **The RootEval semantic face, recovered from the accepted value**:
the exact membership `V(x₀) ≤ 1` — the `QSat/eval` leaf's semantic
witness, read back through the landed wire-level exactness identity
(`rootEvalFormula_true_iff`) from the accepted leaf's carried gate
fact, never recomputed. -/
theorem accepted_rootEval_member (a : QtslAccepted)
    (h : acceptQtslOps fixtureDeps citationOps = some a) :
    QArith.Poly.eval x0demo Vdemo ≤ 1 := by
  have ha : a = citationAccepted := by
    rw [accept_citation] at h
    injection h with h
    exact h.symm
  subst ha
  exact (rootEvalFormula_true_iff x0demo Vdemo 1).mp citationLeaf.eval_true

/-! ## Refusal fixtures: a mis-cited alias refuses

One per citation check; each fires before the evaluation gate (bare
`decide`); each is a prereg'd mutant witness. -/

/-- Mis-rooted citation: the warrant's formula is a SECOND state
formula (element 25), not the claim's spec root. -/
def citationOpsMisrooted : List GOp :=
  (citationDecls ++ [.elta (.ext 0 61)]) ++                  -- 25 : StatePred (≠ φ)
    citationGround ++ citationSpecRows ++ citationClaimRows ++
    [.funa (.ext 0 938) [.ref (.loc 24)] (.ref (.loc 0)),
     .funa (.ext 0 939) [.ref (.loc 24)] (.ref (.loc 25)),   -- formula ≠ φ
     .funa (.ext 0 940) [.ref (.loc 24)] (.ref (.loc 22)),
     .funa (.ext 0 906) [.ref (.loc 23), .lit 0 [1, 1, 1]]
       (.ref (.loc 22))]

/-- **A mis-rooted citation refuses** (`ax/qsat/root_tie`, checked at
the row stratum): the walk would otherwise unpack against the wrong
formula. -/
theorem refuse_misrooted_citation :
    acceptQtslOps fixtureDeps citationOpsMisrooted = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- Box-region citation: a `qraBox` atom (over a staged `Box`, element
25) in the sublevel slot — a region whose membership demand is interval
containment, not an evaluation leaf. -/
def citationOpsBoxRegion : List GOp :=
  (citationDecls ++ [.elta (.ext 0 56)]) ++                  -- 25 : Box
    citationGround ++ citationSpecRows ++ citationClaimRows ++
    [.funa (.ext 0 938) [.ref (.loc 24)] (.ref (.loc 0)),
     .funa (.ext 0 939) [.ref (.loc 24)] (.ref (.loc 4)),
     .funa (.ext 0 940) [.ref (.loc 24)] (.ref (.loc 22)),
     .funa (.ext 0 907) [.ref (.loc 25)] (.ref (.loc 22))]   -- qraBox

/-- **A box-region citation refuses**: the eval-leaf route is the
degenerate-box-vs-sublevel pair's; other constructor pairs ride other
dischargers. -/
theorem refuse_box_region_citation :
    acceptQtslOps fixtureDeps citationOpsBoxRegion = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- Affine-region citation: a malformed-but-scannable `qraAffine` row
mimicking the sublevel arg shape (a `QCertFam` first argument + a `Q`
literal — the scan stores args raw; per-arg reading is the walk's).
The name check alone refuses it: arity and family sort both pass, so
this is the constructor-name conjunct's single-locus witness (the box
fixture above is jointly guarded by name + arity, documented in the
prereg's MA2 amendment). -/
def citationOpsAffineRegion : List GOp :=
  citationDecls ++ citationGround ++ citationSpecRows ++
    citationClaimRows ++
    [.funa (.ext 0 938) [.ref (.loc 24)] (.ref (.loc 0)),
     .funa (.ext 0 939) [.ref (.loc 24)] (.ref (.loc 4)),
     .funa (.ext 0 940) [.ref (.loc 24)] (.ref (.loc 22)),
     .funa (.ext 0 908) [.ref (.loc 23), .lit 0 [1, 1, 1]]
       (.ref (.loc 22))]                                     -- qraAffine

/-- **An affine-region citation refuses** at the constructor name:
sublevel membership is `qraSublevel`'s reading, and an affine
combination — even one whose staged row apes the sublevel shape — is a
different region language. -/
theorem refuse_affine_region_citation :
    acceptQtslOps fixtureDeps citationOpsAffineRegion = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- Threshold mismatch: the sublevel atom at threshold 2, the leaf's
right side still the literal 1 (the leaf itself still evaluates true —
the refusal is the tie's, not the gate's). -/
def citationOpsThrMismatch : List GOp :=
  citationDecls ++ citationGround ++ citationSpecRows ++
    citationClaimRows ++
    [.funa (.ext 0 938) [.ref (.loc 24)] (.ref (.loc 0)),
     .funa (.ext 0 939) [.ref (.loc 24)] (.ref (.loc 4)),
     .funa (.ext 0 940) [.ref (.loc 24)] (.ref (.loc 22)),
     .funa (.ext 0 906) [.ref (.loc 23), .lit 0 [1, 2, 1]]
       (.ref (.loc 22))]                                     -- thr 2 ≠ 1

/-- **A threshold mismatch refuses**: the leaf must be the sublevel's
OWN membership reading — a true leaf against a different threshold is a
different claim. -/
theorem refuse_threshold_mismatch :
    acceptQtslOps fixtureDeps citationOpsThrMismatch = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- Comparator mismatch: the standard fixture's `(2+4) = 6` leaf under
an otherwise-coherent citation at threshold 6 — right side ties, but
the comparator is `.eq`, not the sublevel's `.le`. -/
def citationOpsEqComparator : List GOp :=
  (fixtureDecls ++
    [.elta (.ext 0 146),                                     -- 17 : QRegionAtom
     .elta (.ext 0 143),                                     -- 18 : QCertFam
     .elta (.ext 0 155),                                     -- 19 : QRegionSat
     .elta (.ext 0 61)]) ++                                  -- 20 : StatePred (φ)
    fixtureGround ++
    [.funa (.ext 0 653) [.ref (.loc 20)] (.ref (.loc 3)),    -- SInit (the face)
     .rela (.ext 0 742) [.ref (.loc 3), .ref (.loc 2)]] ++   -- spec_forall
    fixtureClaimRows ++
    [.rela (.ext 0 920)
       [.ref (.loc 3), .ref (.loc 5), .ref (.loc 19)],       -- qsat_warrant (f, sat, warrant)
     .funa (.ext 0 938) [.ref (.loc 19)] (.ref (.loc 0)),
     .funa (.ext 0 939) [.ref (.loc 19)] (.ref (.loc 20)),   -- formula = φ
     .funa (.ext 0 940) [.ref (.loc 19)] (.ref (.loc 17)),
     .funa (.ext 0 906) [.ref (.loc 18), .lit 0 [1, 6, 1]]
       (.ref (.loc 17))]                                     -- qraSublevel thr 6

/-- **A non-`.le` comparator refuses** under a citation: sublevel
membership is a `≤` reading, and an equality leaf — even a true one at
the right threshold — is not it. -/
theorem refuse_eq_comparator_citation :
    acceptQtslOps fixtureDeps citationOpsEqComparator = none :=
  Option.isNone_iff_eq_none.mp (by decide)

end Decode

end QtslSem

end SuFunctor
