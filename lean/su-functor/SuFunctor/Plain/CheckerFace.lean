import Qtsl.Catalogue
import SuFunctor.Plain.Penalty

/-! # The checker face: sequent validity as a vanishing upper probability

The certificate calculus's verdict — `Sequent.semanticallyValid`: every
admissible valuation satisfying the premise satisfies the conclusion —
is the possibilistic (allowed-or-forbidden) face of the semantic
universe's judgment, read at the sequent's own valuation carrier.  This
module records that identification at the exact stratum, where it is
elementary: the carrier `H.Valuation` is an arbitrary type, the credal
objects are finitely supported subprobability joints (`Plain.Joint`),
and no topology or measure theory enters.

The identification is a chain of two equivalences:

* `semanticallyValid_iff_subset` — the verdict is the behavioural
  superset test: the premise-and-admissibility cylinder is contained in
  the conclusion's event.  (Definitional: currying.)
* `upperProb_eq_zero_iff` — Boolean upper probability: over the credal
  set of joints supported inside a region `B`, the supremal mass
  assigned to an event `E` vanishes iff `E` misses `B`.  The witness
  direction is carried by the Dirac joint at a point of `E ∩ B`.

Composed, `semanticallyValid_iff_face`: the sequent is semantically
valid iff the upper probability of the conclusion's complement vanishes
under the credal compile of the cylinder's possibilistic wall.  The
*ex falso* corner is a named corollary (`face_ex_falso`) and its
mechanism a definitional fact (`suppIn_empty`: the only joint supported
in `∅` is the zero joint — the bottom credal object, whose every event
mass is zero — so an unsatisfiable premise validates every conclusion
in both dialects at once).

Design notes:

* Everything here lives at the exact stratum on purpose: `Joint X` is
  total in `X`, so the countable-discrete valuation carrier needs no
  finiteness hypothesis — the finite-carrier seam to the semantic
  stock (`SuFunctor.Plain.Seam`) is *not* on this module's load path,
  and is deliberately not imported.
* The statements are quantifier-explicit over finitely supported weight
  functions and `ℝ≥0∞` finite sums — the erased-type reading a
  twinning development can consume directly.
* `possWall` is the wall pattern of the wiring layer
  (`SuFunctor.Adequacy`: `wallPen (suppIn B)`) restated with its zero
  set as the defining case split; the alignment with `wallPen` and the
  coupled judgment belongs beside the wiring layer, as does the
  identification of the sequent carrier with a wire object's record
  space — both are stated successors, not imports here.
-/

namespace SuFunctor

namespace Plain

noncomputable section

open scoped NNReal ENNReal

universe u

variable {X : Type u}

/-! ## The credal compile of a region: joints supported inside it -/

/-- The credal set of a region `B`: the joints supported inside it.
This is the compile of the possibilistic penalty of `B` — the zero set
of `possWall B` (`possWall_eq_zero_iff`). -/
def suppIn (B : Set X) : Set (Joint X) :=
  {μ | (↑μ.wt.support : Set X) ⊆ B}

theorem mem_suppIn {B : Set X} {μ : Joint X} :
    μ ∈ suppIn B ↔ (↑μ.wt.support : Set X) ⊆ B :=
  Iff.rfl

/-- The only joint supported in the empty region is the zero joint: the
credal compile of an unsatisfiable region is the bottom credal object. -/
theorem suppIn_empty : suppIn (∅ : Set X) = {Joint.zero X} := by
  ext μ
  simp only [mem_suppIn, Set.subset_empty_iff, Finset.coe_eq_empty,
    Finsupp.support_eq_empty, Set.mem_singleton_iff]
  exact ⟨fun h => Joint.ext (h.trans (Joint.zero_wt X).symm),
    fun h => h ▸ Joint.zero_wt X⟩

open Classical in
/-- The possibilistic wall of a region: permitted exactly on joints
supported inside it, forbidden outright otherwise.  The graded penalty
of a crisp region — the face of the penalty stock the checker's verdict
reads. -/
def possWall (B : Set X) : Pen X :=
  fun μ => if μ ∈ suppIn B then 0 else ⊤

theorem possWall_apply_of_mem {B : Set X} {μ : Joint X}
    (h : μ ∈ suppIn B) : possWall B μ = 0 := if_pos h

theorem possWall_apply_of_notMem {B : Set X} {μ : Joint X}
    (h : μ ∉ suppIn B) : possWall B μ = ⊤ := if_neg h

/-- The wall's zero set is the credal set: `suppIn B` is the compile of
`possWall B`. -/
theorem possWall_eq_zero_iff {B : Set X} {μ : Joint X} :
    possWall B μ = 0 ↔ μ ∈ suppIn B := by
  by_cases h : μ ∈ suppIn B
  · simp [possWall_apply_of_mem h, h]
  · simp [possWall_apply_of_notMem h, h]

/-! ## Event mass and the Dirac witness -/

/-- The mass a joint assigns to an event: the finite sum of its weights
over the support points lying in the event, read in `ℝ≥0∞`. -/
def Joint.massOn (μ : Joint X) (E : Set X) : ℝ≥0∞ :=
  ∑ x ∈ μ.wt.support, E.indicator (fun x => (μ.wt x : ℝ≥0∞)) x

/-- A joint's event mass vanishes iff no support point lies in the
event. -/
theorem Joint.massOn_eq_zero_iff (μ : Joint X) (E : Set X) :
    μ.massOn E = 0 ↔ ∀ x ∈ μ.wt.support, x ∉ E := by
  rw [Joint.massOn, Finset.sum_eq_zero_iff]
  refine forall₂_congr fun x hx => ?_
  constructor
  · intro h hxE
    rw [Set.indicator_of_mem hxE, ENNReal.coe_eq_zero] at h
    exact Finsupp.mem_support_iff.mp hx h
  · intro h
    exact Set.indicator_of_notMem h _

/-- The zero joint assigns no mass to any event. -/
theorem Joint.massOn_zero (E : Set X) : (Joint.zero X).massOn E = 0 := by
  rw [Joint.massOn_eq_zero_iff]
  intro x hx
  rw [Joint.zero_wt] at hx
  exact absurd hx (by simp)

/-- The Dirac joint at a point: unit mass there. -/
def Joint.dirac (x : X) : Joint X :=
  ⟨Finsupp.single x 1, le_of_eq (Finsupp.sum_single_index rfl)⟩

@[simp] theorem Joint.dirac_wt (x : X) :
    (Joint.dirac x).wt = Finsupp.single x 1 := rfl

theorem Joint.dirac_support (x : X) :
    (Joint.dirac x).wt.support = {x} := by
  simp [Joint.dirac_wt, Finsupp.support_single]

/-- The Dirac joint at a point of a region belongs to its credal set. -/
theorem Joint.dirac_mem_suppIn {B : Set X} {x : X} (h : x ∈ B) :
    Joint.dirac x ∈ suppIn B := by
  rw [mem_suppIn, Joint.dirac_support]
  simpa using h

/-- The Dirac joint's mass on an event containing its point is one. -/
theorem Joint.massOn_dirac_of_mem {E : Set X} {x : X} (h : x ∈ E) :
    (Joint.dirac x).massOn E = 1 := by
  rw [Joint.massOn, Joint.dirac_support, Finset.sum_singleton,
    Set.indicator_of_mem h]
  simp

/-! ## Boolean upper probability -/

/-- The upper probability of an event over the credal compile of a
region: the supremal mass any joint supported in `B` assigns to `E`. -/
def upperProb (B E : Set X) : ℝ≥0∞ :=
  ⨆ μ ∈ suppIn B, μ.massOn E

/-- The pointwise reading of a vanishing upper probability: every joint
of the credal set assigns the event zero mass.  (The supremum-free form
of `upperProb_eq_zero_iff`, stated for consumption by developments
without a supremum on the extended nonnegative reals.) -/
theorem upperProb_eq_zero_iff_forall (B E : Set X) :
    upperProb B E = 0 ↔ ∀ μ ∈ suppIn B, μ.massOn E = 0 := by
  simp only [upperProb, ← ENNReal.bot_eq_zero, iSup₂_eq_bot]

/-- **Boolean upper probability**: over the credal compile of `B`, the
upper probability of `E` vanishes iff `E` misses `B`.  The forward
direction is witnessed by the Dirac joint at any point of `E ∩ B`; the
backward direction is the support argument. -/
theorem upperProb_eq_zero_iff (B E : Set X) :
    upperProb B E = 0 ↔ E ∩ B = ∅ := by
  rw [upperProb_eq_zero_iff_forall]
  constructor
  · intro h
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hxE, hxB⟩
    have h1 := h _ (Joint.dirac_mem_suppIn hxB)
    rw [Joint.massOn_dirac_of_mem hxE] at h1
    exact one_ne_zero h1
  · intro h μ hμ
    rw [Joint.massOn_eq_zero_iff]
    intro x hx hxE
    exact absurd (Set.mem_inter hxE (hμ (Finset.mem_coe.mpr hx)))
      (h ▸ Set.notMem_empty x)

end

/-! ## The checker's verdict is the face -/

section CheckerFace

open PPLC

/-- The premise-and-admissibility cylinder of a sequent: the admissible
valuations satisfying the premise.  The region whose possibilistic wall
the verdict reads. -/
def admCyl (H : Hypernet) (seq : Sequent) : Set H.Valuation :=
  {σ | σ.Admissible ∧ seq.pre.holds σ}

/-- The conclusion's event: the valuations satisfying the postcondition. -/
def postEvt (H : Hypernet) (seq : Sequent) : Set H.Valuation :=
  {σ | seq.post.holds σ}

/-- The verdict is the behavioural superset test: semantic validity is
containment of the premise-and-admissibility cylinder in the
conclusion's event.  Definitional (currying). -/
theorem semanticallyValid_iff_subset (H : Hypernet) (seq : Sequent) :
    seq.semanticallyValid H ↔ admCyl H seq ⊆ postEvt H seq :=
  ⟨fun h σ hσ => h σ hσ.1 hσ.2, fun h _ ha hp => h ⟨ha, hp⟩⟩

/-- **The checker face**: a sequent is semantically valid iff, over the
credal compile of its premise-and-admissibility cylinder, the upper
probability of the conclusion's complement vanishes.  The certificate
calculus's verdict and the possibilistic face of the penalty judgment
are one predicate at the sequent's own valuation carrier. -/
theorem semanticallyValid_iff_face (H : Hypernet) (seq : Sequent) :
    seq.semanticallyValid H ↔
      upperProb (admCyl H seq) (postEvt H seq)ᶜ = 0 := by
  rw [semanticallyValid_iff_subset, upperProb_eq_zero_iff]
  constructor
  · intro h
    ext σ
    simp only [Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨hnc, hb⟩
    exact hnc (h hb)
  · intro h σ hσ
    by_contra hnc
    exact Set.notMem_empty σ (h ▸ Set.mem_inter hnc hσ)

/-- The *ex falso* corner, named: an unsatisfiable premise (empty
cylinder) makes the face hold outright — the credal compile is the
bottom object (`suppIn_empty`), every upper probability vanishes, and
the verdict's quantifier is vacuously true.  Same fact, both dialects. -/
theorem face_ex_falso (H : Hypernet) (seq : Sequent)
    (h : admCyl H seq = ∅) :
    upperProb (admCyl H seq) (postEvt H seq)ᶜ = 0 := by
  rw [upperProb_eq_zero_iff, h, Set.inter_empty]

end CheckerFace

end Plain

end SuFunctor
