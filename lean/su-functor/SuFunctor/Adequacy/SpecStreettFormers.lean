import SuFunctor.Adequacy.SpecPathLens

/-! # The Streett metering split: the dwell and cross formers

The record lens reads the occupied stages of a record by two species —
the stage graph (`touch`) and the support of the occupation measure
(`dwell`) — and Streett acceptance transports in **neither** direction
between them, even on con-coupled records
(`exists_streettOn_species_incomparable`).  The surface grammar
therefore splits the Streett former by metering species rather than
parameterizing a single former by a mode: a mode flag would leave every
consuming rule casing on the flag with the type system enforcing
nothing, where two formers make the metering distinction
formation-level.

* **`dwellStreettClass`** (the former *DwellStreett*): acceptance read
  against the occupation-measure support — request occupation forces
  response occupation.  Its infinitary reading meters *time spent* in
  the request region (occupation measure; at unit ticks, step count —
  which is exactly the classical discrete acceptance, so all landed
  step-metered Streett content is dwell content by identity).
* **`crossStreettClass`** (the former *CrossStreett*): acceptance read
  against the stage graph — request contact forces response contact.
  Its infinitary reading meters *entry events* (crossings): the
  countable payable unit of contact — per-instant payment on a
  continuum of contact instants is ill-posed, so the quantitative form
  of contact-metering counts crossings, and its consuming rule prices
  them with the crossing-budget row family (whose non-accumulation
  conclusion is also the definedness evidence under which "infinitely
  many crossings" means crossings at unbounded times).

The two infinitary premises are incomparable in *both* time regimes —
enter-and-stay has infinite occupation with one crossing; instantaneous
recurrent touching has infinitely many crossings with zero occupation —
so the split is intrinsic to the metering, not a continuum artifact.

This module carries the record-stratum content of the split:

* the two denotations, definitionally the species instantiations of the
  landed species-parameterized compile (`recordClass` at `.streett`);
* **the collapse theorems**: at every canonical (uniform) lift — in
  particular at every trajectory cell — the two formers coincide with
  each other and with the incumbent compile (`stages_uniformLift` is
  the whole mechanism).  This is the migration warrant: every landed
  compile-stratum Streett artifact is species-invariant on the cells
  where it was proven;
* **the incomparability**, re-exported in the formers' vocabulary: one
  con-coupled record separates the two formers in both directions;
* **citizenship**: both formers' classes are constructible, inherited
  from the species-generic Streett citizenship.

Scope note: at this stratum the encoding grammar (`PathNnf.streett`)
is unchanged — the formers' distinct denotations are carried by the
species instantiation, and the encoding-level constructor split rides
the formation-table revision together with the polarity-sort roster.
The infinitary acceptance conditions (occupation divergence; entry
counters under a non-accumulation budget) live at the behavioral tier
with the battery rules that conclude into them; the record classes
here are their finite-record occupation shadows, exactly as for the
incumbent former.

Axiom receipts at the bottom; expected closure ⊆ [propext,
Classical.choice, Quot.sound], zero sorryAx. -/

namespace SuFunctor.Universe

open scoped ENNReal
open TopologicalSpace

universe u v

section StreettFormers

variable {X : Type u} [Fintype X] [TopologicalSpace X] {α : Type v}

/-- Dwell-metered Streett acceptance at the record stratum: every
requested pair is answered in the **occupation-measure support** —
request occupation forces response occupation.  The `dwell`-species
instantiation of the Streett compile. -/
def dwellStreettClass (τ : X → ℕ) (A : α → Set X)
    (prs : List (StreettPair α)) :
    Set (NonemptyCompacts X × ProbState X) :=
  recordClass .dwell τ A (.streett prs)

/-- Cross-metered Streett acceptance at the record stratum: every
requested pair is answered in the **stage graph** — request contact
forces response contact.  The `touch`-species instantiation of the
Streett compile; its quantitative meter is the crossing counter. -/
def crossStreettClass (τ : X → ℕ) (A : α → Set X)
    (prs : List (StreettPair α)) :
    Set (NonemptyCompacts X × ProbState X) :=
  recordClass .touch τ A (.streett prs)

theorem mem_dwellStreettClass_iff {τ : X → ℕ} {A : α → Set X}
    {prs : List (StreettPair α)}
    {p : NonemptyCompacts X × ProbState X} :
    p ∈ dwellStreettClass τ A prs
      ↔ streettOn (prs.map (StreettPair.regionPair A))
          (stages .dwell p) :=
  Iff.rfl

theorem mem_crossStreettClass_iff {τ : X → ℕ} {A : α → Set X}
    {prs : List (StreettPair α)}
    {p : NonemptyCompacts X × ProbState X} :
    p ∈ crossStreettClass τ A prs
      ↔ streettOn (prs.map (StreettPair.regionPair A))
          (stages .touch p) :=
  Iff.rfl

/-! ## Citizenship: both formers inherit the constructible class -/

variable [DiscreteTopology X]

/-- The dwell former's record class is constructible — inherited from
the species-generic Streett citizenship. -/
theorem isConstructibleUnion_dwellStreettClass (τ : X → ℕ)
    (A : α → Set X) (prs : List (StreettPair α)) :
    IsConstructibleUnion (dwellStreettClass τ A prs) :=
  isConstructibleUnion_recordClass_streett .dwell τ A prs

/-- The cross former's record class is constructible — inherited from
the species-generic Streett citizenship. -/
theorem isConstructibleUnion_crossStreettClass (τ : X → ℕ)
    (A : α → Set X) (prs : List (StreettPair α)) :
    IsConstructibleUnion (crossStreettClass τ A prs) :=
  isConstructibleUnion_recordClass_streett .touch τ A prs

/-! ## The collapse theorems (the migration warrant)

At a canonical lift both stage readers are the graph
(`stages_uniformLift`), so the two formers coincide with each other and
with the incumbent compile; trajectory cells are the special case that
covers the catalogue's deterministic trajectory semantics. -/

/-- The dwell former at a canonical lift reads the graph directly. -/
theorem dwellStreettClass_uniformLift_iff {τ : X → ℕ} {A : α → Set X}
    {prs : List (StreettPair α)} {G : NonemptyCompacts X} :
    (G, uniformLift G) ∈ dwellStreettClass τ A prs
      ↔ streettOn (prs.map (StreettPair.regionPair A)) (G : Set X) :=
  mem_recordClass_uniformLift_iff

/-- The cross former at a canonical lift reads the graph directly. -/
theorem crossStreettClass_uniformLift_iff {τ : X → ℕ} {A : α → Set X}
    {prs : List (StreettPair α)} {G : NonemptyCompacts X} :
    (G, uniformLift G) ∈ crossStreettClass τ A prs
      ↔ streettOn (prs.map (StreettPair.regionPair A)) (G : Set X) :=
  mem_recordClass_uniformLift_iff

/-- **The species collapse at canonical lifts**: on deterministic
records the two Streett formers coincide — the migration warrant for
every compile-stratum artifact proven on those cells. -/
theorem dwellStreett_crossStreett_collapse_uniformLift {τ : X → ℕ}
    {A : α → Set X} {prs : List (StreettPair α)}
    {G : NonemptyCompacts X} :
    (G, uniformLift G) ∈ dwellStreettClass τ A prs
      ↔ (G, uniformLift G) ∈ crossStreettClass τ A prs := by
  rw [dwellStreettClass_uniformLift_iff,
    crossStreettClass_uniformLift_iff]

/-- The dwell former at a trajectory cell reads the occupied stages of
the trajectory — the incumbent compile's clause. -/
theorem dwellStreettClass_trajLens_iff {τ : X → ℕ} {A : α → Set X}
    {prs : List (StreettPair α)} {w : ℕ → X} {N : ℕ} :
    trajLens w N ∈ dwellStreettClass τ A prs
      ↔ streettOn (prs.map (StreettPair.regionPair A))
          (trajStages w N) :=
  trajLens_mem_recordClass_iff

/-- The cross former at a trajectory cell reads the occupied stages of
the trajectory — the incumbent compile's clause. -/
theorem crossStreettClass_trajLens_iff {τ : X → ℕ} {A : α → Set X}
    {prs : List (StreettPair α)} {w : ℕ → X} {N : ℕ} :
    trajLens w N ∈ crossStreettClass τ A prs
      ↔ streettOn (prs.map (StreettPair.regionPair A))
          (trajStages w N) :=
  trajLens_mem_recordClass_iff

/-- **The species collapse at trajectory cells**: the two formers
agree on every deterministic trajectory record, where the compile
agrees with the catalogue's trajectory semantics on the nose. -/
theorem dwellStreett_crossStreett_collapse_trajLens {τ : X → ℕ}
    {A : α → Set X} {prs : List (StreettPair α)} {w : ℕ → X} {N : ℕ} :
    trajLens w N ∈ dwellStreettClass τ A prs
      ↔ trajLens w N ∈ crossStreettClass τ A prs := by
  rw [dwellStreettClass_trajLens_iff, crossStreettClass_trajLens_iff]

end StreettFormers

/-! ## The incomparability, in the formers' vocabulary

The species separation re-exported against denoted pair lists: one
con-coupled record — full graph over `Bool`, occupation a point mass on
the late stage — separates the two formers in **both** directions.
Neither former subsumes the other, which is why the metering species is
formation data rather than a semantic parameter. -/

section Separation

/-- The two-point atom denotation of the separating record: `true`
denotes the late stage, `false` the early one. -/
def sepAtoms : Bool → Set Bool :=
  fun a => cond a {true} {false}

/-- **The Streett formers are incomparable, even con-coupled**: on one
lens point, the cross former holds where the dwell former fails
(request `{true}`, response `{false}`: the graph answers, the
occupation support requests and cannot answer), and the dwell former
holds where the cross former fails (request `{false}`, response
`∅`: the support never requests — vacuous — while the graph requests
into an unanswerable response). -/
theorem exists_dwellStreett_crossStreett_incomparable :
    ∃ p ∈ recordCon (X := Bool),
      (p ∈ crossStreettClass (fun _ => 0) sepAtoms
          [.base (.atom true) (.atom false)] ∧
        p ∉ dwellStreettClass (fun _ => 0) sepAtoms
          [.base (.atom true) (.atom false)]) ∧
      (p ∈ dwellStreettClass (fun _ => 0) sepAtoms
          [.base (.atom false) .fls] ∧
        p ∉ crossStreettClass (fun _ => 0) sepAtoms
          [.base (.atom false) .fls]) := by
  obtain ⟨p, hcon, ⟨htouch₁, hdwell₁⟩, hdwell₂, htouch₂⟩ :=
    exists_streettOn_species_incomparable
  exact ⟨p, hcon, ⟨htouch₁, hdwell₁⟩, hdwell₂, htouch₂⟩

end Separation

end SuFunctor.Universe

/-! ## Axiom receipts

Expected closure for every statement below: ⊆ `[propext,
Classical.choice, Quot.sound]`, zero `sorryAx`. -/

#print axioms SuFunctor.Universe.mem_dwellStreettClass_iff
#print axioms SuFunctor.Universe.mem_crossStreettClass_iff
#print axioms SuFunctor.Universe.isConstructibleUnion_dwellStreettClass
#print axioms SuFunctor.Universe.isConstructibleUnion_crossStreettClass
#print axioms SuFunctor.Universe.dwellStreettClass_uniformLift_iff
#print axioms SuFunctor.Universe.crossStreettClass_uniformLift_iff
#print axioms SuFunctor.Universe.dwellStreett_crossStreett_collapse_uniformLift
#print axioms SuFunctor.Universe.dwellStreettClass_trajLens_iff
#print axioms SuFunctor.Universe.crossStreettClass_trajLens_iff
#print axioms SuFunctor.Universe.dwellStreett_crossStreett_collapse_trajLens
#print axioms SuFunctor.Universe.exists_dwellStreett_crossStreett_incomparable
