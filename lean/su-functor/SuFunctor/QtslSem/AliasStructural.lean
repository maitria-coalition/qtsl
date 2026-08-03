import QtslAux.Structural

/-!
# Class-stratum alias fixtures, structural family

Three alias rows of the QTSL stratum — `QFullDomainWeaken`,
`QClosureExact` (T13's EXACT move), `QCountAtomRounding` — in the
alias-derivation fixture pattern (`AliasSmallGain` is the exemplar),
transposed to the class stratum's current state: the aliases' target
rules are not yet wired as generators, so the elaboration lands on the
base rule's **in-repo soundness lemma** with computed arguments, and
the derivation-calculus cell plumbing (the exemplar's steps 4–5)
arrives with the class-stratum presentation.  What the pattern keeps,
verbatim: the alias **structure** whose proof fields carry the side
conditions, the one-line **elaboration** producing the computed
object, the generic **gate** discharged entirely from the structure's
fields (zero hypotheses beyond the structure — the hypothesis-count
collapse, here `2 → 0` / `1 → 0` against the base lemmas' explicit
hypothesis lists), and a **concrete instance** whose constants are
mutant-sensitive (proper inclusions, boundary points, integer
witnesses pinning an off-by-one in either direction).

Decode note: at the S1 fragment depth the row presentation decodes
region and formula content shallowly (sort-checked references), so a
`decodeQtslPresentationOps` hypothesis on these fixtures would be
decorative rather than load-bearing; the decode marriage rides the
campaign's per-row fragment widening.
-/

namespace SuFunctor

namespace QtslSem

open Qtsl.Structural

/-!
## QFullDomainWeaken — a full-domain row restricted to a scope

Catalogue: tier **alias** — a single scope-weakening application at the
region layer (deliberately not BL's `PWeaken`; the D3 axis flag).
Base lemma: `Qtsl.Structural.fullDomainWeaken_sound` (two explicit
hypotheses: the scope bridge and the full-domain row).
-/

/-- A full-domain-weakening step: the domain, the scope, the row
predicate; the proof fields carry the alias's whole content — the
scope bridge and the full-domain row. -/
structure FullDomainWeakenStep (X : Type*) where
  Dm : Set X
  scope : Set X
  P : X → Prop
  bridge : scope ⊆ Dm
  row : ∀ x ∈ Dm, P x

/-- The elaboration: the row restricted to the scope — the alias's
concluded judgment at computed arguments. -/
def FullDomainWeakenStep.scopedRow {X : Type*}
    (st : FullDomainWeakenStep X) : Prop :=
  ∀ x ∈ st.scope, st.P x

/-- **The generic gate**: discharged entirely from the structure's
fields (`fullDomainWeaken_sound` takes two explicit hypotheses; the
step form takes none). -/
theorem fullDomainWeaken_gate {X : Type*} (st : FullDomainWeakenStep X) :
    st.scopedRow :=
  fullDomainWeaken_sound st.Dm st.scope st.P st.bridge st.row

namespace FdwDemo

/-- The concrete step: domain $[0,1]$, scope $[1/4, 3/4]$ — a PROPER
inclusion, so a bridge-direction corruption cannot be semantically
repaired — and the row $x^2 \le 1$. -/
def step : FullDomainWeakenStep ℝ where
  Dm := Set.Icc 0 1
  scope := Set.Icc (1/4) (3/4)
  P x := x ^ 2 ≤ 1
  bridge := Set.Icc_subset_Icc (by norm_num) (by norm_num)
  row x hx := by
    have h := Set.mem_Icc.mp hx
    nlinarith [h.1, h.2]

/-- The properness witness: the demo's inclusion is strict — `0` is in
the domain and outside the scope.  (The constant that makes the
bridge-flip mutant unrepairable.) -/
theorem proper : (0 : ℝ) ∈ step.Dm \ step.scope := by
  constructor
  · norm_num [step, Set.mem_Icc]
  · norm_num [step, Set.mem_Icc]

/-- The concrete face: the scoped row, from the gate alone. -/
theorem face : ∀ x ∈ step.scope, x ^ 2 ≤ 1 :=
  fullDomainWeaken_gate step

/-- The face at a concrete scope point. -/
theorem face_at_half : (1/2 : ℝ) ^ 2 ≤ 1 :=
  face (1/2) (by norm_num [step, Set.mem_Icc])

end FdwDemo

/-!
## QClosureExact — the complement of a strict literal is closed

Catalogue (T13, the EXACT move): complement of a strict atom is closed
— costless, tier **alias** (set identity), definitional.  Base lemma:
`Qtsl.Structural.closureExactGt_sound` (one explicit hypothesis: the
strict-atom bridge).  The concrete instance's load-bearing constant is
the **boundary point**: membership of `c` itself in the elaborated
atom is exactly what distinguishes the closed complement from the
strict one.
-/

/-- A closure-exact step (the `>`-orientation): the polynomial map, the
threshold, the strict atom; the proof field carries the bridge
identifying the strict atom. -/
structure ClosureExactStep (X : Type*) where
  p : X → ℝ
  c : ℝ
  strictAtom : Set X
  bridge : strictAtom = {x | c < p x}

/-- The elaboration: the closed atom the complement rounds to. -/
def ClosureExactStep.closedAtom {X : Type*} (st : ClosureExactStep X) :
    Set X :=
  {x | st.p x ≤ st.c}

/-- **The generic gate**: the complement of the strict atom IS the
elaborated closed atom — an equality, both inclusions at once —
discharged entirely from the structure's field (`closureExactGt_sound`
takes one explicit hypothesis; the step form takes none). -/
theorem closureExact_gate {X : Type*} (st : ClosureExactStep X) :
    st.strictAtomᶜ = st.closedAtom :=
  closureExactGt_sound st.p st.c st.strictAtom st.bridge

namespace ClosureDemo

/-- The concrete step: `p = id`, threshold `3/7`. -/
noncomputable def step : ClosureExactStep ℝ where
  p x := x
  c := 3/7
  strictAtom := {x | 3/7 < x}
  bridge := rfl

/-- **The boundary witness**: the threshold itself lies in the
elaborated atom — the point that distinguishes the closed complement
from the strict one (a strictness mutant proves this false). -/
theorem boundary_mem : (3/7 : ℝ) ∈ step.closedAtom := by
  show (3/7 : ℝ) ≤ 3/7
  norm_num

/-- The concrete face: the gate's equality at the demo constants. -/
theorem face : step.strictAtomᶜ = {x : ℝ | x ≤ 3/7} :=
  closureExact_gate step

end ClosureDemo

/-!
## QCountAtomRounding — integer counters round the complement inward

Catalogue: the complement of $\{k_P \le j\}$ over reachable markings is
$\{k_P \ge j + 1\}$, not $\{k_P > j\}$ — rounding to the next integer
is free and strictly tighter.  Tier **alias**-class (a free tightening
rewrite).  Base lemmas: `countAtomRounding_sound` /
`countAtomRounding_eq` (one explicit hypothesis: integer-valuedness on
the reachable set).  The fixture's face is **two-sided** — the
equality gate carries completeness and soundness at once — and the
concrete instance carries the membership pair `5 ∈ / 4 ∉` that pins
the `+ 1` exactly: an off-by-one in either direction flips one member
of the pair.
-/

/-- A count-rounding step: the counter, the threshold, the reachable
set; the proof field carries integer-valuedness on reach. -/
structure CountRoundStep (X : Type*) where
  k : X → ℝ
  j : ℤ
  Reach : Set X
  integerValued : ∀ x ∈ Reach, ∃ n : ℤ, k x = (n : ℝ)

/-- The elaboration: the tightened atom at the computed threshold
`j + 1`. -/
def CountRoundStep.tightAtom {X : Type*} (st : CountRoundStep X) :
    Set X :=
  {x | (st.j : ℝ) + 1 ≤ st.k x}

/-- **The generic gate, two-sided**: on the reachable set, the
complement of the count atom and the elaborated tightened atom cut out
the same set — discharged entirely from the structure's field
(`countAtomRounding_eq` takes one explicit hypothesis; the step form
takes none). -/
theorem countRound_gate {X : Type*} (st : CountRoundStep X) :
    st.Reach ∩ {x | st.k x ≤ (st.j : ℝ)}ᶜ = st.Reach ∩ st.tightAtom :=
  countAtomRounding_eq st.k st.j st.Reach st.integerValued

/-- The soundness face on its own (the direction a dropped `+ 1` would
break): on reach, the tightened atom refutes the count atom. -/
theorem countRound_sound_face {X : Type*} (st : CountRoundStep X) :
    ∀ x ∈ st.Reach, x ∈ st.tightAtom → x ∈ {x | st.k x ≤ (st.j : ℝ)}ᶜ := by
  intro x _ hx hle
  have h1 : (st.j : ℝ) + 1 ≤ st.k x := hx
  have h2 : st.k x ≤ (st.j : ℝ) := hle
  linarith

namespace CountDemo

/-- The concrete step: the identity counter on the integer points of
`ℝ`, threshold `j = 4`. -/
def step : CountRoundStep ℝ where
  k x := x
  j := 4
  Reach := Set.range (fun n : ℤ => (n : ℝ))
  integerValued x hx := by
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, hn.symm⟩

/-- The membership pair, upper half: `5` is in the tightened atom
(an off-by-one that rounded to `j + 2` would prove this false). -/
theorem five_mem : (5 : ℝ) ∈ step.tightAtom := by
  show ((4 : ℤ) : ℝ) + 1 ≤ 5
  norm_num

/-- The membership pair, lower half: `4` is NOT in the tightened atom
(an off-by-one that dropped the `+ 1` would prove this false). -/
theorem four_not_mem : (4 : ℝ) ∉ step.tightAtom := by
  show ¬ (((4 : ℤ) : ℝ) + 1 ≤ 4)
  norm_num

/-- The concrete face: the two-sided gate at the demo constants. -/
theorem face :
    step.Reach ∩ {x | step.k x ≤ ((4 : ℤ) : ℝ)}ᶜ =
      step.Reach ∩ step.tightAtom :=
  countRound_gate step

end CountDemo

end QtslSem

end SuFunctor
