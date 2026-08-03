/-
Qtsl/Elaborators.lean — the alias-warrant elaborators for the two
class-stratum aliases whose elaboration target is the wired
`pConstExact` generator: `RootEval` (T19) and `TaylorBound` (T7).

The ℝ-face lemmas these compose with
(`Qtsl.Aliases.taylorLeaf_rat_le_exp`,
`Qtsl.Aliases.rootEval_sublevel_iff` and kin) already live in the
`qtsl-aux` package; this file supplies the wire-level (exact-ℚ)
stratum: closed-term builders, the two leaf formulas with their
replay-exactness identities, and the payload elaborators with their
soundness factorings.

Batch-template shape (`rec:pb-template`): an alias rule A is warranted
by a verified transport of its data into the payload of a SINGLE
target node T; soundness is then a corollary, sound_A = sound_T ∘
transport.  Here T = `pConstExact` for both rows:

  * `RootEval` — membership of the init point in the root atom by
    exact rational evaluation, sublevel branch: (x₀, V, thr) to the
    one `PConstExactData` payload, factoring through
    `sound_pConstExact`.  (The box branch is checker-side registry
    recompute by design — no rule anchor, nothing to elaborate.)
  * `TaylorBound` — the deadline battery's rational surrogate
    `q ≤ Σ_{k ≤ n} (θT)^k / k!` checked in exact ℚ: (q, θ, T, n) to
    the one `PConstExactData` payload, the right side expanded
    producer-side.  The transcendental target `e^{θT}` appears in NO
    field — the checker never needs to know `e` exists — and
    `taylorElab_le_exp` is where it reappears, on the far side of the
    kernel, through `Qtsl.Aliases.taylorLeaf_rat_le_exp`.

Payload discipline, stated once: the elaborator maps the alias's data
plus its own checked leaf to an inhabitant of the target's payload
type, so `notNE` (the comparator confinement — every leaf here uses
`.le`, comfortably inside the admissible set) and the target's two
proof fields are discharged at elaboration.  The checker replays
exactly one closed comparison; the `*_true_iff` lemmas are the
wire-level exactness identities (the ℚ face; the ℝ faces stay where
they were bound, in `QtslAux.QtslAliases`).

Deliberately absent (a preregistered decision): the
`qsatFromRegionElab` stratum — the `QSatFromRegion` row was dissolved
(the record is the judgment; its sublevel content IS
`rootEvalElab`) — and the `QLatticeInv` payload stratum, which is
deferred until it can arrive with its own fixture.

Axiom receipts at the bottom; expected closure ⊆ [propext,
Classical.choice, Quot.sound], zero sorryAx.
-/

import Qtsl.Soundness
import QtslAux.QtslAliases

namespace PPLC

open QArith

/-! ## Closed-term builders (shared by the pConstExact-targeting pair)

`Term` carries no division constructor, and none is needed: every
substituted coordinate and every producer-expanded constant is an
exact ℚ literal, and products/sums of literals are what `Term.evalQ?`
replays.  The builders mirror `QArith.Poly.eval`'s fold structure so
the evaluation lemmas are structural inductions with no
rearrangement. -/

/-- Closed power term: `c^e` as an iterated product of the literal `c`.
`constPowTerm c e` is wire-free by construction. -/
def constPowTerm (c : Rat) : Nat → Term
  | 0 => .const 1
  | e + 1 => .mul (constPowTerm c e) (.const c)

@[simp] theorem constPowTerm_evalQ (c : Rat) :
    ∀ e : Nat, (constPowTerm c e).evalQ? = some (c ^ e)
  | 0 => by simp [constPowTerm, Term.evalQ?]
  | e + 1 => by
    simp [constPowTerm, Term.evalQ?, constPowTerm_evalQ c e, pow_succ]

/-- The closed monomial term at a rational point: each variable
replaced by its coordinate literal, exponents expanded as iterated
products. -/
def monoClosedTerm (x0 : Nat → Rat) (m : Mono) : Term :=
  m.foldr (fun ve a => .mul (constPowTerm (x0 ve.1) ve.2) a) (.const 1)

@[simp] theorem monoClosedTerm_evalQ (x0 : Nat → Rat) :
    ∀ m : Mono, (monoClosedTerm x0 m).evalQ?
      = some (m.foldr (fun ve a => (x0 ve.1) ^ ve.2 * a) 1)
  | [] => by simp [monoClosedTerm, Term.evalQ?]
  | ve :: rest => by
    have ih := monoClosedTerm_evalQ x0 rest
    have hcons : monoClosedTerm x0 (ve :: rest)
        = .mul (constPowTerm (x0 ve.1) ve.2) (monoClosedTerm x0 rest) := rfl
    rw [hcons]
    simp [Term.evalQ?, ih]

/-- The closed polynomial term at a rational point.  Wire-free by
construction, and its exact evaluation is `Poly.eval` at that point
(`polyClosedTerm_evalQ`) — the checker computes the value `V(x₀)`
itself, not an approximation to it. -/
def polyClosedTerm (x0 : Nat → Rat) (p : Poly) : Term :=
  p.foldr (fun mc acc => .add (.mul (.const mc.2) (monoClosedTerm x0 mc.1)) acc)
    (.const 0)

@[simp] theorem polyClosedTerm_evalQ (x0 : Nat → Rat) :
    ∀ p : Poly, (polyClosedTerm x0 p).evalQ? = some (Poly.eval x0 p)
  | [] => by simp [polyClosedTerm, Poly.eval, Term.evalQ?]
  | mc :: rest => by
    have ih := polyClosedTerm_evalQ x0 rest
    have hcons : polyClosedTerm x0 (mc :: rest)
        = .add (.mul (.const mc.2) (monoClosedTerm x0 mc.1))
            (polyClosedTerm x0 rest) := rfl
    have hev : Poly.eval x0 (mc :: rest)
        = mc.2 * (List.foldr (fun ve a => (x0 ve.1) ^ ve.2 * a) 1 mc.1)
          + Poly.eval x0 rest := rfl
    rw [hcons, hev]
    simp [Term.evalQ?, ih, monoClosedTerm_evalQ]

/-! ## RootEval (T19): the membership leaf, elaborated

Sublevel branch: x₀ substituted into the closed left-hand term, the
sublevel atom (V, thr) the comparison's two sides, comparator ≤
(inside the admissible set). -/

/-- The elaborated leaf formula: `V(x₀) ≤ thr` as one closed exact
comparison. -/
def rootEvalFormula (x0 : Nat → Rat) (V : Poly) (thr : Rat) : Formula :=
  .atom .le (polyClosedTerm x0 V) (.const thr)

theorem rootEvalFormula_evalClosed (x0 : Nat → Rat) (V : Poly) (thr : Rat) :
    (rootEvalFormula x0 V thr).evalClosed
      = some (decide (Poly.eval x0 V ≤ thr)) := by
  simp [rootEvalFormula, Formula.evalClosed, Term.evalQ?, BowTie.evalQ]

/-- The wire-level exactness identity, ℚ face: the checker's `true`
verdict IS the exact membership inequality — both directions.  (The ℝ
face stays `Qtsl.Aliases.rootEval_sublevel_iff`.) -/
theorem rootEvalFormula_true_iff (x0 : Nat → Rat) (V : Poly) (thr : Rat) :
    (rootEvalFormula x0 V thr).evalClosed = some true
      ↔ Poly.eval x0 V ≤ thr := by
  rw [rootEvalFormula_evalClosed]
  simp

/-- **The RootEval payload elaborator**, sublevel branch: the alias's
data — point, atom — plus its own checked leaf, to the one
`PConstExactData` inhabitant.  The comparator confinement travels by
construction (`.le ≠ .ne` discharged here, once). -/
def rootEvalElab (H : Hypernet) (seq : Sequent) (x0 : Nat → Rat) (V : Poly)
    (thr : Rat)
    (hEval : (rootEvalFormula x0 V thr).evalClosed = some true)
    (hpost : seq.post = rootEvalFormula x0 V thr) :
    PConstExactData H seq :=
  .mk H seq (polyClosedTerm x0 V) (.const thr) .le (by decide) hEval hpost

/-- The factoring, BL face: the elaborated payload is sound through
the target's kernel-verified lemma — one application of
`sound_pConstExact`, which is itself one step to
`Formula.holds_of_evalClosed_true`. -/
theorem rootEvalElab_sound {H : Hypernet} {seq : Sequent} {x0 : Nat → Rat}
    {V : Poly} {thr : Rat}
    (hEval : (rootEvalFormula x0 V thr).evalClosed = some true)
    (hpost : seq.post = rootEvalFormula x0 V thr) :
    seq.semanticallyValid H :=
  sound_pConstExact
    (show (Formula.atom .le (polyClosedTerm x0 V) (.const thr)).evalClosed
        = some true from hEval)
    (show seq.post = .atom .le (polyClosedTerm x0 V) (.const thr) from hpost)

/-! ## TaylorBound (T7): the deadline battery's rational surrogate,
elaborated

q the left side; θ, T, n survive only through the value of the
right-hand term, expanded producer-side; comparator ≤.  The
transcendental target `e^{θT}` appears in NO field — that is the
point, and `taylorElab_le_exp` is where it reappears, on the far side
of the kernel.  Discrete horizon `T : ℕ`, matching the bound exact-ℚ
face (`taylorLeaf_rat_le_exp`). -/

/-- The order-`n` Taylor partial sum of `exp (θ·T)`, computed in exact
ℚ — the producer-side expansion of the leaf's right side. -/
def taylorPartialSum (θ : Rat) (T n : Nat) : Rat :=
  ∑ k ∈ Finset.range (n + 1), (θ * (T : Rat)) ^ k / (Nat.factorial k : Rat)

/-- The elaborated leaf formula: `q ≤ Σ_{k≤n} (θT)^k / k!` as one
closed exact comparison — the single wire-free comparison. -/
def taylorFormula (q θ : Rat) (T n : Nat) : Formula :=
  .atom .le (.const q) (.const (taylorPartialSum θ T n))

/-- The wire-level replay identity: the checker's `true` verdict is
exactly the ℚ comparison against the partial sum. -/
theorem taylorFormula_true_iff (q θ : Rat) (T n : Nat) :
    (taylorFormula q θ T n).evalClosed = some true
      ↔ q ≤ taylorPartialSum θ T n := by
  simp [taylorFormula, Formula.evalClosed, Term.evalQ?, BowTie.evalQ]

/-- **The TaylorBound payload elaborator**: (q, θ, T, n) plus the
checked comparison, to the one `PConstExactData` inhabitant.  No
`TaylorBound` node sort exists and none is needed — this function is
the catalogue-level name for the producer's elaboration, mechanized. -/
def taylorElab (H : Hypernet) (seq : Sequent) (q θ : Rat) (T n : Nat)
    (hEval : (taylorFormula q θ T n).evalClosed = some true)
    (hpost : seq.post = taylorFormula q θ T n) :
    PConstExactData H seq :=
  .mk H seq (.const q) (.const (taylorPartialSum θ T n)) .le (by decide)
    hEval hpost

/-- The factoring, BL face: `sound_pConstExact` at the elaborated
payload — validity of the posted comparison at every valuation. -/
theorem taylorElab_sound {H : Hypernet} {seq : Sequent} {q θ : Rat} {T n : Nat}
    (hEval : (taylorFormula q θ T n).evalClosed = some true)
    (hpost : seq.post = taylorFormula q θ T n) :
    seq.semanticallyValid H :=
  sound_pConstExact
    (show (Formula.atom .le (.const q)
        (.const (taylorPartialSum θ T n))).evalClosed = some true from hEval)
    (show seq.post = .atom .le (.const q)
        (.const (taylorPartialSum θ T n)) from hpost)

/-- The semantic face, end to end: the checked wire comparison bounds
`q` by `e^{θT}` through the bound enclosure — the elaborator factoring
through the kernel replay into `Qtsl.Aliases.taylorLeaf_rat_le_exp`.
The sign condition `0 ≤ θ` is load-bearing (the proof section's
negative-argument counterexample); the deadline rule's typing supplies
it. -/
theorem taylorElab_le_exp {q θ : Rat} {T n : Nat} (hθ : 0 ≤ θ)
    (hEval : (taylorFormula q θ T n).evalClosed = some true) :
    (q : ℝ) ≤ Real.exp (θ * T) :=
  Qtsl.Aliases.taylorLeaf_rat_le_exp hθ
    ((taylorFormula_true_iff q θ T n).mp hEval)

end PPLC

/-! ## Axiom receipts

Expected closure for everything below: ⊆ `[propext, Classical.choice,
Quot.sound]` — no `sorryAx`. -/

#print axioms PPLC.polyClosedTerm_evalQ
#print axioms PPLC.rootEvalFormula_true_iff
#print axioms PPLC.rootEvalElab
#print axioms PPLC.rootEvalElab_sound
#print axioms PPLC.taylorFormula_true_iff
#print axioms PPLC.taylorElab
#print axioms PPLC.taylorElab_sound
#print axioms PPLC.taylorElab_le_exp
