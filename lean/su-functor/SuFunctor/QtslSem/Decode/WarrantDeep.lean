import SuFunctor.QtslSem.Decode.Warrant
import SuFunctor.QtslSem.Decode.AliasAcceptance

/-!
# Deep region decode and the sublevel membership-tie discharge

Two residues of the warrant route, discharged beside it — the landed
`Decode.Warrant` and `Decode.Acceptance` are imported and not modified.

**Deep region-atom reads.**  `readRegionAtom` reads a region-atom
element into a value covering all three pinned constructors —
`qraSublevel (cert, thr)`, `qraBox b`, `qraAffine (row, thr)` — through
`ctorRowsOf` against the landed roster, fail-closed on a missing,
duplicated, or foreign constructor row, a wrong arity, an ill-sorted
argument, or an unreadable threshold.  The sublevel arm is
`resolveCitation`'s own idiom, now returning the family element beside
the threshold; box and affine ride as sort-checked references (their
content — the `Box` intervals, the combination list — is outside the S1
fragment).

**The deepened warrant and the membership-tie discharge.**
`acceptWarrantSatDeep` re-stages the warrant route checks-first: the
citation resolution, root tie, and init-membership demand, then the
deep sublevel read and the leaf's sublevel-shape match at the SAME
threshold, and only then the evaluation gate — so every deep refusal
below is pure table-and-match work for the kernel, and the accepted
value (`AcceptedSublevelWarrant`) carries the deep-read and shape facts
as proof fields.  Only the sublevel constructor is deep-accepted: a box
region's membership demand is interval containment, not an evaluation
leaf, and its content is not decodable at this stratum — a box or
affine citation deep-refuses (one-sided, by design).

**The honesty split, stated where it binds.**  Checked content, no
hypotheses: the deep-read facts, the shape facts, and the leaf's
exact-ℚ evaluation — `checked_le` extracts `∃ v, lhs.evalQ? = some v ∧
v ≤ thr` from the carried gate fact, and where the leaf's left side is
syntactically the closed polynomial term of the producer convention,
`checked_poly_le` reads off the exact membership `Poly.eval x₀ V ≤ thr`
with no hypotheses at all.  Named-hypothesis content, exactly two:

* `hpoly` — the **cert-family content tie**: the leaf's left side
  evaluates to the region polynomial's value at the subject's initial
  point.  The event-3 rows do not carry this into the S1 fragment (the
  family's polynomial lives in its `QCertTable` — `qctCons` rows, a
  class-stratum decode — and the initial point is likewise outside the
  fragment), so `discharge_sublevel` takes it as a hypothesis whose
  discharge is: a `QCertTable → Poly` decode, an initial-point decode,
  and the producer's `polyClosedTerm` conformance — at which point
  `polyClosedTerm_evalQ` + `polyToMv_eval` close it, exactly as
  `discharge_polyClosed` closes it for the syntactic form.
* `hchild` — the cited region row's own claim (its concluding proof
  node is the S5 seam), as in `Decode.Warrant`.

Given those, **the `heval` hypothesis of
`Qtsl.Aliases.sound_QSatFromRegion_sublevel` is DISCHARGED from checked
data** — the point of this module: where `AcceptedWarrant.resolve_pointwise`
consumed an assumed init-in-region inclusion (`hinit`), the sublevel
shape replaces the assumption at the initial point with the leaf's
checked exact-ℚ evaluation.  (Under a class-stratum identification of
the penalty space with the lemma's `σ → ℝ`, `discharge_sublevel` at
`sat := (· ∈ A.formulaCpl w.phiElem)` is `resolve_pointwise` with
`hinit` replaced by checked data; the identification is the class-
stratum campaign's.)

**General conservativity** (v2 = v1·embed): on warrant-free
presentations the widened acceptor agrees with the landed v1 acceptor
modulo the `.inl` embedding — the two fragment gates are one function
(`acceptFragmentGateW_eq_gate`, definitional), and on the warrant-free
class both pass iff the statistical, spec-equivalence, invariance-scope
AND region tiers are all empty (`gate_warrantFree`: with no warrants,
any region row fails the coverage conjunct).

Proof-engineering note, honest: the route's two field-feeding rechecks
(the `hread` dite after the deep-read match, the `hlm` dite after the
gate) are redundant at runtime — each re-checks a fact the preceding
stage established — and exist so the acceptance value's proof fields
ride dite binders (`dif_pos` + proof irrelevance in fixture proofs, the
landed `acceptGroundLeaf` discipline) rather than match-equation
binders.
-/

namespace SuFunctor

namespace QtslSem

namespace Decode

open PPLC PPLC.Geolog

/-! ## The deep region-atom read -/

/-- A deep-read region atom: the three pinned constructors.  Box and
affine carry sort-checked references (content outside the S1
fragment); the sublevel carries its family element and exact
threshold. -/
inductive QRegionAtomVal where
  | sublevel (certFam : Nat) (thr : Rat)
  | box (b : Nat)
  | affine (row : Nat) (thr : Rat)
  deriving Repr, DecidableEq

/-- Read a region-atom element's constructor row, fail-closed: exactly
one row against the landed roster, the arity of its constructor, sorted
arguments (`QCertFam` family, `Box` box, `QCertCombList` row), readable
threshold.  (No subject sort check — region references reach here
through the assembly's own `QRegionAtom` sort demand, `resolveCitation`'s
idiom.) -/
def readRegionAtom (tb : QRowTbls) (e : Nat) : Option QRegionAtomVal :=
  match tb.ctorRowsOf regionAtomCtors e with
  | [("qraSublevel", [c, t])] =>
    match elemOfVal c, qOfVal t with
    | some cf, some thr =>
      if tb.sortAt cf == some "QCertFam" then some (.sublevel cf thr)
      else none
    | _, _ => none
  | [("qraBox", [b])] =>
    match elemOfVal b with
    | some bx =>
      if tb.sortAt bx == some "Box" then some (.box bx) else none
    | none => none
  | [("qraAffine", [r, t])] =>
    match elemOfVal r, qOfVal t with
    | some row, some thr =>
      if tb.sortAt row == some "QCertCombList" then some (.affine row thr)
      else none
    | _, _ => none
  | _ => none

/-! ## The deepened warrant -/

/-- An accepted sublevel-warranted claim: the landed `AcceptedWarrant`
plus the deep-read fact — the cited region atom constructs by
`qraSublevel` over `certFam` at `thr` — and the shape fact that the
membership leaf is the sublevel's OWN reading at that same
threshold. -/
structure AcceptedSublevelWarrant (tb : QRowTbls) where
  /-- The landed warrant value (subject, spec root, region row, root
  tie, membership leaf with carried validity). -/
  base : AcceptedWarrant
  /-- The sublevel's certificate-family element. -/
  certFam : Nat
  /-- The sublevel's exact threshold. -/
  thr : Rat
  /-- The deep read: the cited atom IS this sublevel. -/
  atom_read : readRegionAtom tb base.region.region
    = some (.sublevel certFam thr)
  /-- The membership leaf matches the sublevel shape at the same
  threshold. -/
  leaf_match : sequentMatchesSublevel base.leaf.seq thr = true

/-- Accept one sublevel-warranted claim, checks first: citation
resolution, face membership + `SInit` form + root tie (the event-4
grid, the v2 walk's checks verbatim), init-membership demand at the
(region, sys) wire order, the deep sublevel read, and the leaf-shape
match all precede the evaluation gate, so every refusal below is pure
table-and-match work.  Box and affine region
atoms refuse here (deep acceptance is the sublevel discharger's).  The
two trailing dites re-check established facts to feed the proof
fields (module note). -/
def acceptWarrantSatDeep (tb : QRowTbls) (regs : List QRegionSatVal)
    (sat : QSatVal) (f w p : Nat) : Option (AcceptedSublevelWarrant tb) :=
  match regs.find? (fun r => r.elem == w) with
  | none => none
  | some reg =>
    match sat.spec.forallComps.find? (fun c => c.elem == f) with
    | none => none
    | some c =>
      match c.former, c.args with
      | "SInit", [.ref (.loc phi)] =>
        if htie : reg.formula = phi then
          if (tb.relRows "qtsl_init_member").contains
              [.ref (.loc reg.region), .ref (.loc sat.sys)] then
            match readRegionAtom tb reg.region with
            | some (.sublevel cf thr) =>
              if hread : readRegionAtom tb reg.region
                  = some (.sublevel cf thr) then
                match leafSequent tb p with
                | .error _ => none
                | .ok s =>
                  if sequentMatchesSublevel s thr then
                    match acceptGroundLeaf sat.elem s with
                    | none => none
                    | some l =>
                      if hlm : sequentMatchesSublevel l.seq thr then
                        some { base := { elem := sat.elem,
                                         sysElem := sat.sys,
                                         fElem := f, phiElem := phi,
                                         region := reg, root_tie := htie,
                                         leaf := l },
                               certFam := cf, thr := thr,
                               atom_read := hread, leaf_match := hlm }
                      else none
                  else none
              else none
            | _ => none
          else none
        else none
      | _, _ => none

/-! ## The checked facts (no hypotheses) -/

/-- The shape facts, extracted from the carried match: the leaf's
comparator is `≤` and its right side is the sublevel's own threshold
literal. -/
theorem AcceptedSublevelWarrant.shape {tb : QRowTbls}
    (dw : AcceptedSublevelWarrant tb) :
    dw.base.leaf.cmp = .le ∧ dw.base.leaf.rhs = .const dw.thr := by
  have hm := dw.leaf_match
  unfold sequentMatchesSublevel at hm
  rw [dw.base.leaf.post_eq] at hm
  cases hc : dw.base.leaf.cmp
  case lt => rw [hc] at hm; simp at hm
  case eq => rw [hc] at hm; simp at hm
  case ge => rw [hc] at hm; simp at hm
  case gt => rw [hc] at hm; simp at hm
  case ne => rw [hc] at hm; simp at hm
  case le =>
    rw [hc] at hm
    cases hr : dw.base.leaf.rhs
    case var w => rw [hr] at hm; simp at hm
    case add a b => rw [hr] at hm; simp at hm
    case mul a b => rw [hr] at hm; simp at hm
    case sub a b => rw [hr] at hm; simp at hm
    case neg t => rw [hr] at hm; simp at hm
    case idx t i => rw [hr] at hm; simp at hm
    case const q =>
      rw [hr] at hm
      have hq : q = dw.thr := by simpa using hm
      exact ⟨by simp [hc], by simp [hr, hq]⟩

/-- The leaf's comparator is `≤`. -/
theorem AcceptedSublevelWarrant.cmp_le {tb : QRowTbls}
    (dw : AcceptedSublevelWarrant tb) : dw.base.leaf.cmp = .le :=
  dw.shape.1

/-- The leaf's right side is the sublevel's threshold literal. -/
theorem AcceptedSublevelWarrant.rhs_thr {tb : QRowTbls}
    (dw : AcceptedSublevelWarrant tb) :
    dw.base.leaf.rhs = .const dw.thr :=
  dw.shape.2

/-- **The checked exact-ℚ membership evaluation**: the leaf's left side
evaluates closed to a value at or below the sublevel's threshold —
read off the carried gate fact through the shape facts, no
hypotheses. -/
theorem AcceptedSublevelWarrant.checked_le {tb : QRowTbls}
    (dw : AcceptedSublevelWarrant tb) :
    ∃ v, dw.base.leaf.lhs.evalQ? = some v ∧ v ≤ dw.thr := by
  have h := dw.base.leaf.eval_true
  rw [dw.cmp_le, dw.rhs_thr] at h
  cases hv : dw.base.leaf.lhs.evalQ? with
  | none => simp [Formula.evalClosed, Term.evalQ?, hv] at h
  | some v =>
    refine ⟨v, rfl, ?_⟩
    simp [Formula.evalClosed, hv, Term.evalQ?, BowTie.evalQ] at h
    exact h

/-! ## The membership-tie discharge -/

/-- **The sublevel membership-tie discharge**: for an accepted
sublevel warrant, the `heval` hypothesis of
`Qtsl.Aliases.sound_QSatFromRegion_sublevel` is DISCHARGED from the
leaf's checked exact-ℚ evaluation — where `resolve_pointwise` assumed
the initial point inside the region (`hinit`), this consumes checked
data.  What remains hypothetical, named:

* `hpoly` — the cert-family content tie: the leaf's left side
  evaluates to the region polynomial's value at the subject's initial
  point.  Discharged by a class-stratum `QCertTable → Poly` decode +
  initial-point decode + the producer's `polyClosedTerm` conformance
  (then `polyClosedTerm_evalQ` + `polyToMv_eval` close it —
  `discharge_polyClosed` is that closure for the syntactic form).
* `hchild` — the cited region row's own claim over the real sublevel
  set (the S5 proof-node seam, as in `Decode.Warrant`). -/
theorem AcceptedSublevelWarrant.discharge_sublevel {tb : QRowTbls}
    (dw : AcceptedSublevelWarrant tb) {σ : Type*}
    {sat : (σ → ℝ) → Prop} {P : MvPolynomial σ ℚ} {xq : σ → ℚ}
    (hpoly : dw.base.leaf.lhs.evalQ? = some (MvPolynomial.eval xq P))
    (hchild : ∀ x ∈ {x : σ → ℝ |
      MvPolynomial.eval x (MvPolynomial.map (Rat.castHom ℝ) P)
        ≤ (dw.thr : ℝ)}, sat x) :
    sat (fun i => (xq i : ℝ)) := by
  obtain ⟨v, hv, hle⟩ := dw.checked_le
  have heval : MvPolynomial.eval xq P ≤ dw.thr := by
    rw [hpoly] at hv
    injection hv with hv
    rw [hv]
    exact hle
  exact Qtsl.Aliases.sound_QSatFromRegion_sublevel hchild heval

/-! ### The sparse-polynomial bridge

`QArith.Poly` (the exact computational core, the producer convention's
`polyClosedTerm` side) meets the soundness stock's `MvPolynomial`: the
evident interpretation, with evaluation agreement.  This is what lets
the syntactic content tie discharge the general one. -/

/-- A sparse monomial as an `MvPolynomial`. -/
noncomputable def monoToMv (m : QArith.Mono) : MvPolynomial ℕ ℚ :=
  m.foldr (fun ve a => (MvPolynomial.X ve.1) ^ ve.2 * a) 1

/-- Monomial evaluation agreement. -/
theorem monoToMv_eval (x : ℕ → ℚ) : ∀ m : QArith.Mono,
    MvPolynomial.eval x (monoToMv m)
      = m.foldr (fun ve a => (x ve.1) ^ ve.2 * a) 1
  | [] => by simp [monoToMv]
  | ve :: rest => by
    have ih := monoToMv_eval x rest
    have hcons : monoToMv (ve :: rest)
        = (MvPolynomial.X ve.1) ^ ve.2 * monoToMv rest := rfl
    rw [List.foldr_cons, hcons]
    simp [ih]

/-- A sparse polynomial as an `MvPolynomial`. -/
noncomputable def polyToMv (p : QArith.Poly) : MvPolynomial ℕ ℚ :=
  p.foldr (fun mc acc => MvPolynomial.C mc.2 * monoToMv mc.1 + acc) 0

/-- **Evaluation agreement**: the bridge preserves exact evaluation. -/
theorem polyToMv_eval (x : ℕ → ℚ) : ∀ p : QArith.Poly,
    MvPolynomial.eval x (polyToMv p) = QArith.Poly.eval x p
  | [] => by simp [polyToMv, QArith.Poly.eval]
  | mc :: rest => by
    have ih := polyToMv_eval x rest
    have hcons : polyToMv (mc :: rest)
        = MvPolynomial.C mc.2 * monoToMv mc.1 + polyToMv rest := rfl
    have hev : QArith.Poly.eval x (mc :: rest)
        = mc.2 * (mc.1.foldr (fun ve a => (x ve.1) ^ ve.2 * a) 1)
          + QArith.Poly.eval x rest := rfl
    rw [hcons, hev]
    simp [ih, monoToMv_eval]

/-- **The checked membership at the ℚ face, syntactic tie**: when the
leaf's left side is the closed polynomial term of the producer
convention, the exact membership `Poly.eval x₀ V ≤ thr` is read off the
accepted value with no hypotheses. -/
theorem AcceptedSublevelWarrant.checked_poly_le {tb : QRowTbls}
    (dw : AcceptedSublevelWarrant tb) {x0 : ℕ → ℚ} {V : QArith.Poly}
    (hsyn : dw.base.leaf.lhs = polyClosedTerm x0 V) :
    QArith.Poly.eval x0 V ≤ dw.thr := by
  obtain ⟨v, hv, hle⟩ := dw.checked_le
  rw [hsyn, polyClosedTerm_evalQ] at hv
  injection hv with hv
  rw [hv]
  exact hle

/-- **The full discharge for the syntactic form**: the content tie
closed by `polyClosedTerm_evalQ` + the bridge; only the cited region
row's own claim (`hchild`) remains. -/
theorem AcceptedSublevelWarrant.discharge_polyClosed {tb : QRowTbls}
    (dw : AcceptedSublevelWarrant tb) {x0 : ℕ → ℚ} {V : QArith.Poly}
    {sat : (ℕ → ℝ) → Prop}
    (hsyn : dw.base.leaf.lhs = polyClosedTerm x0 V)
    (hchild : ∀ x ∈ {x : ℕ → ℝ |
      MvPolynomial.eval x (MvPolynomial.map (Rat.castHom ℝ) (polyToMv V))
        ≤ (dw.thr : ℝ)}, sat x) :
    sat (fun i => (x0 i : ℝ)) :=
  dw.discharge_sublevel
    (by rw [hsyn, polyClosedTerm_evalQ, polyToMv_eval]) hchild

/-! ## Correspondence: deep acceptance refines the landed route -/

/-- **Deep ⊆ v2**: a deep-accepted claim is accepted by the landed
`acceptWarrantSat` with the same base value — every landed v2 theorem
(soundness, `SpecJudgLayer` resolution, roster correspondence) applies
to a deep-accepted warrant's base for free. -/
theorem acceptWarrantSatDeep_base {tb : QRowTbls}
    {regs : List QRegionSatVal} {sat : QSatVal} {f w p : Nat}
    {dw : AcceptedSublevelWarrant tb}
    (h : acceptWarrantSatDeep tb regs sat f w p = some dw) :
    acceptWarrantSat tb regs sat f w p = some dw.base := by
  unfold acceptWarrantSatDeep at h
  split at h
  any_goals contradiction
  rename_i reg hfind
  split at h
  any_goals contradiction
  rename_i c hcomp
  split at h
  any_goals contradiction
  rename_i phi hformer hargs
  split at h
  any_goals contradiction
  rename_i htie
  split at h
  any_goals contradiction
  rename_i hmem
  split at h
  any_goals contradiction
  rename_i cf thr hread0
  split at h
  any_goals contradiction
  rename_i hread
  split at h
  any_goals contradiction
  rename_i s hseq
  split at h
  any_goals contradiction
  rename_i hpre
  split at h
  any_goals contradiction
  rename_i l hgl
  split at h
  any_goals contradiction
  rename_i hlm
  injection h with h
  subst h
  unfold acceptWarrantSat
  simp only [hfind, hcomp, hformer, hargs]
  rw [dif_pos htie, if_pos hmem]
  have hal : acceptLeaf tb sat.elem p = some l := by
    unfold acceptLeaf
    rw [hseq]
    exact hgl
  rw [hal]

/-! ## General conservativity: v2 = v1 · embed on warrant-free
presentations -/

/-- The two fragment gates are one function (the v2 gate restated the
v1.1 gate verbatim). -/
theorem acceptFragmentGateW_eq_gate :
    acceptFragmentGateW = acceptFragmentGate := rfl

/-- On a warrant-free claim roster, no region row is cited. -/
private theorem any_warrant_false (e : Nat) :
    ∀ l : List QSatVal, (∀ s ∈ l, s.warrant = none) →
      l.any (fun s => (s.warrant.map Prod.snd) == some e) = false
  | [], _ => rfl
  | s :: rest, h => by
    rw [List.any_cons, h s List.mem_cons_self,
      any_warrant_false e rest (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

/-- **The precise gate class**: on a warrant-free presentation the
(shared) fragment gate reduces to demanding ALL FOUR out-of-fragment
tiers empty — with no warrants, any region-satisfaction row fails the
coverage conjunct. -/
theorem gate_warrantFree {pres : QtslPresentation}
    (h : ∀ s ∈ pres.sats, s.warrant = none) :
    acceptFragmentGateW pres =
      (pres.satConfs.isEmpty && pres.specEquivs.isEmpty &&
        pres.invScopes.isEmpty && pres.regionSats.isEmpty) := by
  have hall : pres.regionSats.all
      (fun r => pres.sats.any
        (fun s => (s.warrant.map Prod.snd) == some r.elem))
      = pres.regionSats.isEmpty := by
    cases hrs : pres.regionSats with
    | nil => rfl
    | cons r rs =>
      rw [List.all_cons, any_warrant_false r.elem pres.sats h]
      rfl
  unfold acceptFragmentGateW
  rw [hall]

/-- On a warrant-free claim roster the widened walk is the landed walk
under the `.inl` embedding. -/
theorem acceptClaimsW_warrantFree (tb : QRowTbls)
    (regs : List QRegionSatVal) :
    ∀ sats : List QSatVal, (∀ s ∈ sats, s.warrant = none) →
      acceptClaimsW tb regs sats
        = (acceptLeaves tb regs sats).map (List.map Sum.inl)
  | [], _ => rfl
  | sat :: rest, h => by
    have hw : sat.warrant = none := h sat List.mem_cons_self
    have ih := acceptClaimsW_warrantFree tb regs rest
      (fun x hx => h x (List.mem_cons_of_mem _ hx))
    unfold acceptClaimsW acceptLeaves
    rw [hw]
    cases he : sat.evalLeaf with
    | none => rfl
    | some p =>
      -- force the two-scrutinee matcher past its (none, some p) arm: the
      -- inner scrutinees sit under the arm binder until the iota happens,
      -- where `cases h : e` cannot reach them (the r1 lesson)
      show (match acceptLeaf tb sat.elem p with
            | none => none
            | some l =>
              match acceptClaimsW tb regs rest with
              | none => none
              | some es => some (Sum.inl l :: es))
          = (match acceptLeaf tb sat.elem p with
             | none => none
             | some l =>
               match acceptLeaves tb regs rest with
               | none => none
               | some ls => some (l :: ls)).map (List.map Sum.inl)
      cases hal : acceptLeaf tb sat.elem p with
      | none => rfl
      | some l =>
        rw [ih]
        cases acceptLeaves tb regs rest with
        | none => rfl
        | some ls => rfl

/-- **General conservativity, op level**: on artifacts whose decoded
presentation is warrant-free, the widened acceptor IS the landed v1
acceptor under the `.inl` embedding — v2 = v1 · embed, exactly. -/
theorem acceptQtslOpsW_conservative (deps : List Bytes) (ops : List GOp)
    (hwf : ∀ pres, decodeQtslPresentationOps deps ops = .ok pres →
      ∀ s ∈ pres.sats, s.warrant = none) :
    acceptQtslOpsW deps ops
      = (acceptQtslOps deps ops).map
          (fun a => ⟨a.pres, a.leaves.map Sum.inl⟩) := by
  unfold acceptQtslOpsW acceptQtslOps
  cases hscan : scanQtslOps deps ops with
  | error e => rfl
  | ok tb =>
    -- force the scan matcher past its ok arm (the r1 lesson)
    show (match assembleQtsl tb with
          | .error _ => none
          | .ok pres =>
            if acceptFragmentGateW pres then
              match acceptClaimsW tb pres.regionSats pres.sats with
              | none => none
              | some es => some (⟨pres, es⟩ : QtslAcceptedW)
            else none)
        = Option.map
            (fun (a : QtslAccepted) =>
              (⟨a.pres, a.leaves.map Sum.inl⟩ : QtslAcceptedW))
            (match assembleQtsl tb with
             | .error _ => none
             | .ok pres =>
               if acceptFragmentGate pres then
                 match acceptLeaves tb pres.regionSats pres.sats with
                 | none => none
                 | some ls => some (⟨pres, ls⟩ : QtslAccepted)
               else none)
    cases hasm : assembleQtsl tb with
    | error e => rfl
    | ok pres =>
      have hdec : decodeQtslPresentationOps deps ops = .ok pres := by
        unfold decodeQtslPresentationOps
        rw [hscan]
        exact hasm
      have hw := hwf pres hdec
      -- and once more past the assemble matcher's ok arm
      show (if acceptFragmentGateW pres then
              match acceptClaimsW tb pres.regionSats pres.sats with
              | none => none
              | some es => some (⟨pres, es⟩ : QtslAcceptedW)
            else none)
          = Option.map
              (fun (a : QtslAccepted) =>
                (⟨a.pres, a.leaves.map Sum.inl⟩ : QtslAcceptedW))
              (if acceptFragmentGate pres then
                match acceptLeaves tb pres.regionSats pres.sats with
                | none => none
                | some ls => some (⟨pres, ls⟩ : QtslAccepted)
              else none)
      rw [acceptFragmentGateW_eq_gate]
      cases hg : acceptFragmentGate pres with
      | false => rfl
      | true =>
        rw [acceptClaimsW_warrantFree tb pres.regionSats pres.sats hw]
        cases acceptLeaves tb pres.regionSats pres.sats with
        | none => rfl
        | some ls => rfl

/-- Sealed-byte conservativity: the same statement through the sealed
reader. -/
theorem acceptQtslSealedW_conservative (bs : Bytes)
    (hwf : ∀ pres, decodeQtslPresentation bs = .ok pres →
      ∀ s ∈ pres.sats, s.warrant = none) :
    acceptQtslSealedW bs
      = (acceptQtslSealed bs).map
          (fun a => ⟨a.pres, a.leaves.map Sum.inl⟩) := by
  unfold acceptQtslSealedW acceptQtslSealed
  cases hread : readGeologSealed bs with
  | err c t w => rfl
  | ok g =>
    -- force the reader matcher past its ok arm (the r1 lesson)
    show (match g.commits with
          | [commit] => acceptQtslOpsW commit.cskel.deps commit.cbody.ops
          | _ => none)
        = Option.map
            (fun (a : QtslAccepted) =>
              (⟨a.pres, a.leaves.map Sum.inl⟩ : QtslAcceptedW))
            (match g.commits with
             | [commit] => acceptQtslOps commit.cskel.deps commit.cbody.ops
             | _ => none)
    cases hcomm : g.commits with
    | nil => rfl
    | cons c1 tail =>
      cases htail : tail with
      | cons c2 rest => rfl
      | nil =>
        exact acceptQtslOpsW_conservative c1.cskel.deps c1.cbody.ops
          (fun pres hdec => hwf pres (by
            unfold decodeQtslPresentation
            rw [hread]
            show (match g.commits with
                  | [commit] => decodeQtslPresentationOps
                      commit.cskel.deps commit.cbody.ops
                  | _ => qerr .unsupported "multi_commit_unsupported"
                      g.commits.length)
                = .ok pres
            rw [hcomm, htail]
            exact hdec))

/-- The embedded value's eval-leaf roster is the v1 roster. -/
theorem conservative_leaves (pres : QtslPresentation) :
    ∀ ls : List AcceptedLeaf,
      (QtslAcceptedW.mk pres (ls.map Sum.inl)).leaves = ls
  | [] => rfl
  | l :: rest => by
    have ih := conservative_leaves pres rest
    show l :: (QtslAcceptedW.mk pres (rest.map Sum.inl)).leaves = l :: rest
    rw [ih]

/-- The embedded value carries no warrants. -/
theorem conservative_warrants (pres : QtslPresentation) :
    ∀ ls : List AcceptedLeaf,
      (QtslAcceptedW.mk pres (ls.map Sum.inl)).warrants = []
  | [] => rfl
  | l :: rest => by
    have ih := conservative_warrants pres rest
    show (QtslAcceptedW.mk pres (rest.map Sum.inl)).warrants = []
    exact ih

/-! ## Fixtures: the deep warranted rows, accepted and discharged

The staged rows are the alias citation fixture (`citationOps`: the
claim with BOTH routes, the region child over a `qraSublevel` atom at
threshold 1, the membership leaf `V(x₀) ≤ 1` for
`V = (1/4)·x₀ + 1/2` at `x₀ = (2, 0, …)`) completed with the
init-membership demand row the v2 route requires — the same container
is v2-green AND deep-green, and on the deep value the content tie is
syntactic (`rfl`), so the fixture discharge carries no tie hypothesis:
rows in, membership tie discharged, only the region row's own claim
remains. -/

/-- The init-membership demand row (`ax/wf/qsat_init`'s witness), at
the event-4 wire order: (region-atom, subject). -/
def rowInitMemberDeep : GOp :=
  .rela (.ext 0 922) [.ref (.loc 22), .ref (.loc 1)]

/-- The deep warranted fixture: the citation rows plus the demand. -/
def deepOps : List GOp := citationOps ++ [rowInitMemberDeep]

/-- Its scanned tables. -/
def deepTbls : QRowTbls :=
  match scanQtslOps fixtureDeps deepOps with
  | .ok t => t
  | .error _ => ⟨[], [], []⟩

/-- The demand row is invisible to the assembly: the presentation is
the citation fixture's verbatim. -/
theorem decode_deepOps_ok :
    decodeQtslPresentationOps fixtureDeps deepOps =
      .ok citationExpected := by
  decide

/-- The deep fixture's claim value (the citation fixture's). -/
def satDemoDeep : QSatVal :=
  ⟨5, 0, 1, citationSpecVal, some (3, 24), some 7⟩

/-- The deep fixture's decoded region roster. -/
def regsDemoDeep : List QRegionSatVal := [⟨24, 0, 4, 22⟩]

/-- The deep fixture's membership leaf decodes as at the citation
fixture (the demand row shifts nothing). -/
theorem deep_leaf_seq :
    leafSequent deepTbls 7 = .ok citationLeafSeq := by
  rfl

/-- The expected base warrant. -/
def deepBase : AcceptedWarrant where
  elem := 5
  sysElem := 1
  fElem := 3
  phiElem := 4
  region := ⟨24, 0, 4, 22⟩
  root_tie := rfl
  leaf := citationLeaf

/-- The expected deep-accepted value: family element 23, threshold 1,
the deep-read and shape facts kernel-checked. -/
def deepFixture : AcceptedSublevelWarrant deepTbls where
  base := deepBase
  certFam := 23
  thr := 1
  atom_read := by decide
  leaf_match := sequentMatches_citation

/-- The deep read on the staged atom. -/
theorem readRegionAtom_fixture :
    readRegionAtom deepTbls 22 = some (.sublevel 23 1) := by
  decide

/-- **The deep route accepts the staged rows** (kernel-first: the
pre-gate checks reduce in the key equation, the one stuck redex — the
membership leaf's Rat gate — is crossed by the landed accepted core,
and the trailing shape recheck rides `dif_pos`). -/
theorem acceptWarrantSatDeep_fixture :
    acceptWarrantSatDeep deepTbls regsDemoDeep satDemoDeep 3 24 7
      = some deepFixture := by
  have key : acceptWarrantSatDeep deepTbls regsDemoDeep satDemoDeep 3 24 7 =
      (match acceptGroundLeaf 5 citationLeafSeq with
       | none => none
       | some l =>
         if hlm : sequentMatchesSublevel l.seq 1 then
           some { base := { elem := 5, sysElem := 1, fElem := 3,
                            phiElem := 4,
                            region := ⟨24, 0, 4, 22⟩, root_tie := rfl,
                            leaf := l },
                  certFam := 23, thr := 1,
                  atom_read := readRegionAtom_fixture,
                  leaf_match := hlm }
         else none) := rfl
  rw [key, acceptGroundLeaf_citation]
  show (if hlm : sequentMatchesSublevel citationLeaf.seq 1 then
          some { base := { elem := 5, sysElem := 1, fElem := 3,
                           phiElem := 4,
                           region := ⟨24, 0, 4, 22⟩, root_tie := rfl,
                           leaf := citationLeaf },
                 certFam := 23, thr := 1,
                 atom_read := readRegionAtom_fixture,
                 leaf_match := hlm }
        else none) = some deepFixture
  rw [dif_pos (show sequentMatchesSublevel citationLeaf.seq 1 = true from
    sequentMatches_citation)]
  rfl

/-- **The same container through the landed v2 route**: the base
warrant, accepted by `acceptWarrantSat` — the composition witness
(`acceptWarrantSatDeep_base`'s fact, at the fixture). -/
theorem acceptWarrantSat_deepOps :
    acceptWarrantSat deepTbls regsDemoDeep satDemoDeep 3 24 7
      = some deepBase := by
  have key : acceptWarrantSat deepTbls regsDemoDeep satDemoDeep 3 24 7 =
      (if (deepTbls.relRows "qtsl_init_member").contains
          [.ref (.loc 22), .ref (.loc 1)] then
        match acceptLeaf deepTbls 5 7 with
        | none => none
        | some l =>
          some { elem := 5, sysElem := 1, fElem := 3, phiElem := 4,
                 region := ⟨24, 0, 4, 22⟩, root_tie := rfl,
                 leaf := l }
      else none) := rfl
  have hleaf : acceptLeaf deepTbls 5 7 = some citationLeaf := by
    have k2 : acceptLeaf deepTbls 5 7 =
        acceptGroundLeaf 5 citationLeafSeq := by
      unfold acceptLeaf
      rw [deep_leaf_seq]
    rw [k2, acceptGroundLeaf_citation]
  rw [key,
    if_pos (by decide :
      ((deepTbls.relRows "qtsl_init_member").contains
        [.ref (.loc 22), .ref (.loc 1)]) = true),
    hleaf]
  rfl

/-- The deep container's claim roster through the landed v2 walk. -/
theorem acceptClaimsW_deepOps :
    acceptClaimsW deepTbls citationExpected.regionSats
      citationExpected.sats = some [.inr deepBase] := by
  have key : acceptClaimsW deepTbls citationExpected.regionSats
      citationExpected.sats =
      (match acceptWarrantSat deepTbls regsDemoDeep satDemoDeep 3 24 7 with
       | none => none
       | some aw => some [.inr aw]) := rfl
  rw [key, acceptWarrantSat_deepOps]

/-- The expected v2-accepted value of the deep container. -/
def deepAccepted : QtslAcceptedW :=
  ⟨citationExpected, [.inr deepBase]⟩

/-- **The deep container is v2-green**: the widened acceptor accepts
the staged rows whole (so every landed v2 soundness and resolution
theorem applies to the deep fixture's base). -/
theorem acceptW_deepOps :
    acceptQtslOpsW fixtureDeps deepOps = some deepAccepted := by
  have k1 : acceptQtslOpsW fixtureDeps deepOps =
      (match assembleQtsl deepTbls with
       | .error _ => none
       | .ok pres =>
         if acceptFragmentGateW pres then
           match acceptClaimsW deepTbls pres.regionSats pres.sats with
           | none => none
           | some es => some ⟨pres, es⟩
         else none) := by
    unfold acceptQtslOpsW
    rw [(by decide : scanQtslOps fixtureDeps deepOps = .ok deepTbls)]
    all_goals first | rfl | with_unfolding_all rfl
  rw [k1, (by decide : assembleQtsl deepTbls = .ok citationExpected)]
  show (if acceptFragmentGateW citationExpected then
          match acceptClaimsW deepTbls citationExpected.regionSats
              citationExpected.sats with
          | none => none
          | some es => some (⟨citationExpected, es⟩ : QtslAcceptedW)
        else none) = some deepAccepted
  rw [if_pos (by decide :
      acceptFragmentGateW citationExpected = true),
    acceptClaimsW_deepOps]
  rfl

/-- **The checked membership, read off the deep fixture**: the exact
`V(x₀) ≤ 1` with no hypotheses — the content tie is syntactic on the
staged rows. -/
theorem deepFixture_checked : QArith.Poly.eval x0demo Vdemo ≤ 1 :=
  deepFixture.checked_poly_le (x0 := x0demo) (V := Vdemo) rfl

/-- **The end-to-end fixture discharge**: rows staged, deep-walked, the
membership tie discharged — for ANY reading of the cited region row's
own claim over the real sublevel set, the claim conclusion holds at the
subject's initial point.  Only `hchild` (the S5 seam) remains. -/
theorem deepFixture_discharge {sat : (ℕ → ℝ) → Prop}
    (hchild : ∀ x ∈ {x : ℕ → ℝ |
      MvPolynomial.eval x
        (MvPolynomial.map (Rat.castHom ℝ) (polyToMv Vdemo))
        ≤ ((1 : Rat) : ℝ)}, sat x) :
    sat (fun i => (x0demo i : ℝ)) :=
  deepFixture.discharge_polyClosed (x0 := x0demo) (V := Vdemo) rfl hchild

/-! ### Refusal fixtures (each green, each pre-gate: pure
table-and-match work for the kernel) -/

/-- **The landed warranted fixture DEEP-REFUSES**: its region atom
(17) deliberately carries no constructor row — v2 accepts it
(`acceptW_fixture_warrant`), the deep route does not.  The
missing-constructor refusal, on the landed rows verbatim. -/
theorem refuse_deep_no_ctor :
    acceptWarrantSatDeep fixtureTblsWarrant [⟨18, 19, 20, 17⟩]
      ⟨5, 0, 1, warrantSpecVal, some (3, 18), some 7⟩ 3 18 7 = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- A second sublevel row for the same atom (at a second threshold). -/
def deepOpsDupCtor : List GOp :=
  deepOps ++
    [.funa (.ext 0 906) [.ref (.loc 23), .lit 0 [1, 2, 1]]
      (.ref (.loc 22))]

/-- Its tables. -/
def deepTblsDupCtor : QRowTbls :=
  match scanQtslOps fixtureDeps deepOpsDupCtor with
  | .ok t => t
  | .error _ => ⟨[], [], []⟩

/-- **A duplicated constructor row refuses**: exactly-one is the
read's discipline (an ambiguous region is no region). -/
theorem refuse_deep_dup_ctor :
    acceptWarrantSatDeep deepTblsDupCtor regsDemoDeep satDemoDeep 3 24 7
      = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- The box-region citation rows, completed with the demand. -/
def deepOpsBox : List GOp := citationOpsBoxRegion ++ [rowInitMemberDeep]

/-- Its tables. -/
def deepTblsBox : QRowTbls :=
  match scanQtslOps fixtureDeps deepOpsBox with
  | .ok t => t
  | .error _ => ⟨[], [], []⟩

/-- **A box region atom deep-refuses** (one-sided by design: the deep
route is the sublevel discharger's; box content is not decodable at
this stratum, so box citations are not deep-accepted at all). -/
theorem refuse_deep_foreign_box :
    acceptWarrantSatDeep deepTblsBox regsDemoDeep satDemoDeep 3 24 7
      = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- The affine-aping-sublevel rows, completed with the demand. -/
def deepOpsAffine : List GOp :=
  citationOpsAffineRegion ++ [rowInitMemberDeep]

/-- Its tables. -/
def deepTblsAffine : QRowTbls :=
  match scanQtslOps fixtureDeps deepOpsAffine with
  | .ok t => t
  | .error _ => ⟨[], [], []⟩

/-- **An affine row aping the sublevel shape deep-refuses**: the
constructor name selects the discharger, and the affine arm's own sort
demand (`QCertCombList`) refuses the `QCertFam`-sorted first argument
besides. -/
theorem refuse_deep_foreign_affine :
    acceptWarrantSatDeep deepTblsAffine regsDemoDeep satDemoDeep 3 24 7
      = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- The threshold-mismatch rows, completed with the demand. -/
def deepOpsThrMismatch : List GOp :=
  citationOpsThrMismatch ++ [rowInitMemberDeep]

/-- Its tables. -/
def deepTblsThrMismatch : QRowTbls :=
  match scanQtslOps fixtureDeps deepOpsThrMismatch with
  | .ok t => t
  | .error _ => ⟨[], [], []⟩

/-- **A threshold mismatch deep-refuses**: the leaf must be the
sublevel's OWN membership reading — a true leaf at a different
threshold is a different claim.  (Fires at the pre-gate shape match;
the evaluation gate is never consulted.) -/
theorem refuse_deep_thr_mismatch :
    acceptWarrantSatDeep deepTblsThrMismatch regsDemoDeep satDemoDeep
      3 24 7 = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- Sublevel rows whose family argument is the `System`-sorted subject
element — an ill-sorted family. -/
def deepOpsIllSortedFam : List GOp :=
  citationDecls ++ citationGround ++ citationSpecRows ++
    citationClaimRows ++
    [.funa (.ext 0 938) [.ref (.loc 24)] (.ref (.loc 0)),
     .funa (.ext 0 939) [.ref (.loc 24)] (.ref (.loc 4)),
     .funa (.ext 0 940) [.ref (.loc 24)] (.ref (.loc 22)),
     .funa (.ext 0 906) [.ref (.loc 1), .lit 0 [1, 1, 1]]
       (.ref (.loc 22)),
     rowInitMemberDeep]

/-- Its tables. -/
def deepTblsIllSortedFam : QRowTbls :=
  match scanQtslOps fixtureDeps deepOpsIllSortedFam with
  | .ok t => t
  | .error _ => ⟨[], [], []⟩

/-- **An ill-sorted certificate family deep-refuses** at the read's
`QCertFam` sort demand. -/
theorem refuse_deep_illsorted_family :
    acceptWarrantSatDeep deepTblsIllSortedFam regsDemoDeep satDemoDeep
      3 24 7 = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-- The eq-comparator citation rows (S1 layout: atom 17, family 18,
region row 19), completed with the demand at that layout. -/
def deepOpsEqComparator : List GOp :=
  citationOpsEqComparator ++
    [.rela (.ext 0 922) [.ref (.loc 17), .ref (.loc 1)]]

/-- Its tables. -/
def deepTblsEqComparator : QRowTbls :=
  match scanQtslOps fixtureDeps deepOpsEqComparator with
  | .ok t => t
  | .error _ => ⟨[], [], []⟩

/-- **A non-`≤` comparator deep-refuses**: sublevel membership is a
`≤` reading — an equality leaf, even true at the right threshold, is
not it. -/
theorem refuse_deep_eq_comparator :
    acceptWarrantSatDeep deepTblsEqComparator [⟨19, 0, 20, 17⟩]
      ⟨5, 0, 1, ⟨2, [⟨3, "SInit", [.ref (.loc 20)]⟩], []⟩,
        some (3, 19), some 7⟩ 3 19 7 = none :=
  Option.isNone_iff_eq_none.mp (by decide)

/-! ## Probes (inline; the barn log is the receipt) -/

#print axioms AcceptedSublevelWarrant.discharge_sublevel
#print axioms AcceptedSublevelWarrant.discharge_polyClosed
#print axioms AcceptedSublevelWarrant.checked_poly_le
#print axioms AcceptedSublevelWarrant.checked_le
#print axioms polyToMv_eval
#print axioms acceptWarrantSatDeep_base
#print axioms acceptFragmentGateW_eq_gate
#print axioms acceptQtslOpsW_conservative
#print axioms acceptQtslSealedW_conservative
#print axioms acceptWarrantSatDeep_fixture
#print axioms acceptW_deepOps
#print axioms deepFixture_checked
#print axioms deepFixture_discharge
#print axioms Qtsl.Aliases.sound_QSatFromRegion_sublevel

end Decode

end QtslSem

end SuFunctor
