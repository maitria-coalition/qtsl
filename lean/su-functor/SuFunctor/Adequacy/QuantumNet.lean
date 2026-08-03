import SuFunctor.Adequacy.EnvelopeUnion
import SuFunctor.Adequacy.RecordSpace
import QtslAux.QuantumAssembly

/-! # Adequacy: locally covariant quantum nets (kinematic fragment)

The quantum adequacy square, both faces, at matrix grade over the
derived diamond site.  A locally covariant quantum field theory in the
sense of Brunetti–Fredenhagen–Verch (arXiv:math-ph/0112041,
Definition 2.1) is presented — at the honest finite stratum — by the
landed kinematic fragment `Qtsl.QuantumAssembly.LCQFTFragment`: an
isotone observable net with class-level Einstein causality, the
time-slice surrogate and its genuine Cauchy-determinacy tier, derived
site machinery, and an exhaustive positive record family at a
distinguished ambient diamond.  **The textbook corner of this square
consumes that object nearly verbatim** — no other adequacy square could
reuse its community-facing corner this way, because the fragment's
axioms *are* the community's own (Def. 2.1 (i)–(iii) at fixed
spacetime, the POVM hypotheses, positivity and normalization of
states).

**The carrier is the record space, never the algebra.**  A quantum-net
presentation compiles to probability rows over the declared record
family: the Born/Gell-Mann–Hartle record law
`μ(α) = Re tr(ρ · R α)` (Gell-Mann–Hartle 1993, Phys. Rev. D 47,
3345; the single-window Born rule of any standard quantum probability
text).  The mechanized form of that law is the landed
`recordShadow`, so the connector between the square's left edge and
the community's own formula is definitional — one `rfl`-adjacent
lemma, far cheaper than the chain square's monadic connector.  The
left edge moreover factors through the Brunetti–Fredenhagen–Verch
state object itself: locally equal states at the ambient diamond have
equal rows (`shadowPMF_class_invariant`), so the classical semantics
is a function of the state-presheaf fiber, exactly as the doctrine of
their §5.1 demands.

**The precise face** (`quantum_net_adequacy`): the loose-arrow diagram
denoted by the compiled rows — one probability-pinning constraint per
record index — is isomorphic, by an invertible globular cell of
`Crd κ`, to the singleton-credal inclusion of the Born row.
Compile-then-denote agrees with interpret-then-include.

**The credal face** (`quantum_credal_adequacy`) is the flagship, and
its imprecision is *forced*, not offered: Brunetti–Fredenhagen–Verch
§5.1 (following Holland–Wald; model-independently re-proven under
dynamical locality by Fewster–Verch, arXiv:1106.4785) prove that a
functorial choice of single states is unrealizable — the state object
of the theory is a *set* of states from birth.  Every other former's
imprecise face is modeling generosity; here the community's own
theorem demands the credal stratum.  The face is stated in the
set-valued genre: the declared state set denotes the union of its
members' Born rows (each member carried with its exact-rational row
witness — the certified-index pattern), the compiled side stays
state-free with the state choice as the existentially quantified row
mechanism, and the radially maximal slice, the verdict transfers at
both polarities, and the zero-model degeneracies all follow from the
union machinery at member mass one.  Quantum convex mixtures land
inside the face: for a mixture-closed state set the credal law-set is
closed under rational convex mixture (`quantumLaws_mix`, through the
landed convexity seam `recordShadowPMF_mix`), and the negative witness
`mixLaw_not_mem_pair` shows the closure hypothesis is load-bearing —
the two-element Bell/mixed set does not contain its own midpoint's
row.

**Partiality, exercised at last**: an *incomplete* record family
compiles to a genuine subprobability row — the target stratum's native
mass-loss allowance, which no stochastic former ever exercised, is
exercised naturally by quantum presentations
(`exists_incomplete_mass_lt_one`: three of the four computational-basis
projectors at the maximally mixed state spend mass 3/4).  Dually,
`exists_nonPSD_family_negative_shadow` is the kernel-visible reason
record positivity is load-bearing: a Hermitian family summing to one
without positive-semidefiniteness prices an outcome negatively.

**Degeneracy quoted, never smoothed**: at matrix grade the folium is
flat — every positive unital functional is a unique density matrix
(`Qtsl.QuantumStates.existsUnique_isState_traceRepr`) — so the credal
face's content lives in the set-valuedness and the band, never in fake
folium distinctions; the strict openness of the Bell/mixed credal band
is the landed `exists_shadow_lowerE_lt_upperE`.  **Scope fences**,
stated once: single window (the ambient diamond) and one declared
record family — multi-window histories through the class-operator
machinery of `Qtsl.QuantumRecords` are the named stretch tier; genuine
dynamics (relative Cauchy evolution, stress-energy) lives on the far
side of the kinematic fragment (Fewster–Verch arXiv:1106.4785: no
same-physics-in-all-spacetimes claim survives the full class); the
quasilocal/type-III stratum, where folium distinctions become real, is
deliberately out of scope.

The fibre reading (`su_qnet_adequacy`) re-instantiates the square as a
citizenship statement in the semantic universe's fibre over the
single-window record interface, by pushforward along the record
embedding — the wiring pattern of the assignment interface, reused
verbatim. -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Finset
open Qtsl.Imprecise Qtsl.DiamondSite Qtsl.QuantumDescent
open Qtsl.QuantumStates Qtsl.QuantumAssembly
open scoped ComplexOrder

/-! ## The bridge: finite probability rows into the credal stratum -/

/-- A finite probability mass function, read as a subprobability mass
function: the inclusion of the exact-rational probability vocabulary
into the credal stratum's carrier. -/
noncomputable def _root_.Qtsl.Imprecise.FinPMF.toSubPMF {Z : Type*}
    [Fintype Z] (p : FinPMF Z) : SubPMF Z where
  wt := Finsupp.onFinset Finset.univ p.prob (fun _ _ => Finset.mem_univ _)
  nonneg := p.nonneg
  mass_le_one := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun z _ _ => p.nonneg z)) (le_of_eq ?_)
    exact (Finset.sum_congr rfl fun z _ => rfl).trans p.total

@[simp] theorem _root_.Qtsl.Imprecise.FinPMF.toSubPMF_wt {Z : Type*}
    [Fintype Z] (p : FinPMF Z) (z : Z) : p.toSubPMF.wt z = p.prob z :=
  rfl

/-- A probability mass function spends its whole mass in the credal
stratum. -/
theorem _root_.Qtsl.Imprecise.FinPMF.toSubPMF_mass {Z : Type*}
    [Fintype Z] (p : FinPMF Z) : p.toSubPMF.mass = 1 := by
  classical
  show p.toSubPMF.prob Set.univ = 1
  rw [SubPMF.prob_eq_sum_univ]
  simp only [Set.indicator_univ]
  exact (Finset.sum_congr rfl fun z _ => rfl).trans p.total

/-- The inclusion is injective: distinct rows stay distinct. -/
theorem _root_.Qtsl.Imprecise.FinPMF.toSubPMF_injective {Z : Type*}
    [Fintype Z] : Function.Injective (FinPMF.toSubPMF (Z := Z)) := by
  intro p q h
  apply FinPMF.ext
  intro z
  have := congrArg (fun μ : SubPMF Z => μ.wt z) h
  simpa using this

variable {X : Type*} [PartialOrder X]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι T κ : Type*} [Fintype κ]

/-! ## The textbook corner: the fragment with a distinguished state -/

/-- **A quantum-net system**: a kinematic fragment of a locally
covariant QFT (Brunetti–Fredenhagen–Verch Definition 2.1 at matrix
grade — the landed `LCQFTFragment`, consumed verbatim: its fields ARE
the community's axioms) together with a distinguished state and the
exact-rational witness of its Born row along the fragment's record
family.  The witness hypothesis is the landed `recordShadowPMF` shape:
producers with `ℚ[i]`-entried presentations discharge it by exact
trace arithmetic. -/
structure QNetSystem (X : Type*) [PartialOrder X]
    (n : Type*) [Fintype n] [DecidableEq n]
    (ι T κ : Type*) [Fintype κ] where
  /-- The kinematic fragment: the community's own object. -/
  frag : LCQFTFragment X n ι T κ
  /-- The distinguished state (the precise face's state face). -/
  state : Matrix n n ℂ
  /-- Positivity and normalization — the literature's own state
  hypotheses. -/
  state_isState : IsState state
  /-- The exact-rational Born row. -/
  row : κ → ℚ
  /-- The row witnesses the Born/Gell-Mann–Hartle record law along the
  fragment's record family. -/
  row_spec : ∀ α, (row α : ℝ) = recordShadow frag.records state α

namespace QNetSystem

variable (P : QNetSystem X n ι T κ)

/-- The classical semantics (the square's left edge): the Born row of
the distinguished state along the fragment's record family, as an
honest finite probability mass function — positivity from the record
family's positive-semidefiniteness, total mass one from its
exhaustiveness. -/
noncomputable def shadowPMF : FinPMF κ :=
  recordShadowPMF P.frag.records P.state P.row P.row_spec
    P.frag.records_posSemidef P.frag.records_exhaustive P.state_isState

@[simp] theorem shadowPMF_prob (α : κ) : P.shadowPMF.prob α = P.row α :=
  rfl

/-- The left edge, in the credal stratum's carrier. -/
noncomputable def shadowLaw : SubPMF κ := P.shadowPMF.toSubPMF

@[simp] theorem shadowLaw_wt (α : κ) : P.shadowLaw.wt α = P.row α :=
  rfl

/-- A complete record family spends its whole mass: the target
stratum's partiality allowance is available but unexercised by an
exhaustive family (cf. `exists_incomplete_mass_lt_one` for the
incomplete case, where it is exercised). -/
theorem shadowLaw_mass : P.shadowLaw.mass = 1 :=
  FinPMF.toSubPMF_mass _

/-- **The connector, Born form**: the square's left edge is the
literature's own record law `Re tr(ρ · R α)` — definitionally, through
the row witness and `recordShadow`'s definition. -/
theorem shadowPMF_prob_eq_born (α : κ) :
    ((P.shadowPMF.prob α : ℚ) : ℝ) =
      ((P.state * P.frag.records α).trace).re :=
  P.row_spec α

/-- **The connector, state-object form**: the left edge is the
fragment's own record shadow, read at the class of the distinguished
state in the state-presheaf fiber at the ambient diamond — the
Brunetti–Fredenhagen–Verch state object, genuinely consumed. -/
theorem shadowPMF_eq_fragment_shadow (α : κ) :
    ((P.shadowPMF.prob α : ℚ) : ℝ) =
      P.frag.shadow
        (stateClassMk P.frag.net P.frag.ambient
          ⟨P.state, P.state_isState⟩) α :=
  P.row_spec α

end QNetSystem

/-- **The left edge factors through the state presheaf**: two systems
on one fragment whose states have equal classes at the ambient diamond
— locally equal restrictions, the §5.1 relation — have equal Born
rows.  The classical semantics is a function of the
Brunetti–Fredenhagen–Verch state object, not of the density matrix. -/
theorem shadowPMF_class_invariant (F : LCQFTFragment X n ι T κ)
    {ρ σ : Matrix n n ℂ} (hρ : IsState ρ) (hσ : IsState σ)
    {q₁ q₂ : κ → ℚ}
    (h₁ : ∀ α, ((q₁ α : ℚ) : ℝ) = recordShadow F.records ρ α)
    (h₂ : ∀ α, ((q₂ α : ℚ) : ℝ) = recordShadow F.records σ α)
    (hcls : stateClassMk F.net F.ambient ⟨ρ, hρ⟩ =
      stateClassMk F.net F.ambient ⟨σ, hσ⟩) :
    (QNetSystem.mk F ρ hρ q₁ h₁).shadowPMF =
      (QNetSystem.mk F σ hσ q₂ h₂).shadowPMF := by
  apply FinPMF.ext
  intro α
  have hsh := recordShadow_congr F.records_mem (stateClass_exact hcls)
  show q₁ α = q₂ α
  have h : ((q₁ α : ℚ) : ℝ) = ((q₂ α : ℚ) : ℝ) := by
    rw [h₁ α, h₂ α, hsh]
  exact_mod_cast h

namespace QNet

/-! ## The compiled rows: the row grain, `Finsupp`-mirrored -/

/-- The compiled presentation of a quantum-net system: probability
rows over the record index.  Rows are stored sparsely — a zero entry
and an absent row are the same datum. -/
structure QNetRows (κ : Type*) where
  /-- Outcome rows: record index ↦ stored probability. -/
  outcome : κ →₀ ℚ

/-- Well-formedness of a row set: nonnegative entries of total mass at
most one.  These are the aggregation-seam obligations of the row grain
— asserted at emission, re-derived by a consumer from the whole row
set. -/
structure QNetRows.WF (R : QNetRows κ) : Prop where
  nonneg : ∀ α, 0 ≤ R.outcome α
  mass_le : ∑ α, R.outcome α ≤ 1

/-- Completeness of a row set: the compiled face of an exhaustive
(POVM) record family.  Deliberately separate from well-formedness —
an incomplete family compiles to an honest subprobability row. -/
def QNetRows.Complete (R : QNetRows κ) : Prop :=
  ∑ α, R.outcome α = 1

/-- Compilation: store the Born row.  On the finitely supported
representation, dropping zero rows is definitionally invisible. -/
noncomputable def compile (P : QNetSystem X n ι T κ) : QNetRows κ where
  outcome := Finsupp.onFinset Finset.univ P.row
    (fun _ _ => Finset.mem_univ _)

@[simp] theorem compile_outcome (P : QNetSystem X n ι T κ) (α : κ) :
    (compile P).outcome α = P.row α := rfl

/-- The compiled rows of an exhaustive family are complete — the one
place the record family's exhaustiveness is spent on the compiled
side. -/
theorem compile_complete (P : QNetSystem X n ι T κ) :
    (compile P).Complete :=
  P.shadowPMF.total

theorem compile_wf (P : QNetSystem X n ι T κ) : (compile P).WF where
  nonneg α := P.shadowPMF.nonneg α
  mass_le := le_of_eq (compile_complete P)

/-! ## The rows' law, the atoms, and the feeding lemma -/

/-- The law of a well-formed row set: the subprobability mass function
whose weights are the stored rows. -/
noncomputable def rowsLaw (R : QNetRows κ) (hR : R.WF) : SubPMF κ where
  wt := R.outcome
  nonneg := hR.nonneg
  mass_le_one :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun α _ _ => hR.nonneg α)) hR.mass_le

@[simp] theorem rowsLaw_wt (R : QNetRows κ) (hR : R.WF) (α : κ) :
    (rowsLaw R hR).wt α = R.outcome α := rfl

/-- The mass of the rows' law is the total stored mass. -/
theorem rowsLaw_mass (R : QNetRows κ) (hR : R.WF) :
    (rowsLaw R hR).mass = ∑ α, R.outcome α := by
  classical
  show (rowsLaw R hR).prob Set.univ = _
  rw [SubPMF.prob_eq_sum_univ]
  simp only [Set.indicator_univ]
  exact Finset.sum_congr rfl fun α _ => rfl

/-- A complete row set spends its whole mass. -/
theorem rowsLaw_mass_of_complete (R : QNetRows κ) (hR : R.WF)
    (hC : R.Complete) : (rowsLaw R hR).mass = 1 := by
  rw [rowsLaw_mass]
  exact hC

/-- The record constraint at one index: the model prices that outcome
at the stored row. -/
def rowC (R : QNetRows κ) (α : κ) : SubPMF κ → Prop :=
  fun μ => μ.prob {α} = R.outcome α

/-- The compiled system's constraint atoms: one row constraint per
record index.  Their formal conjunction is the system's denotation —
a loose-arrow diagram of `Crd κ`. -/
noncomputable def atoms (R : QNetRows κ) : List (SubPMF κ → Prop) :=
  Finset.univ.toList.map (rowC R)

theorem satAtoms_unpack (R : QNetRows κ) (μ : SubPMF κ) :
    looseConj (atoms R) μ ↔ ∀ α, rowC R α μ := by
  rw [looseConj_iff]
  constructor
  · intro h α
    exact h _ (List.mem_map.mpr
      ⟨α, Finset.mem_toList.mpr (Finset.mem_univ α), rfl⟩)
  · rintro h c hc
    rcases List.mem_map.mp hc with ⟨α, -, rfl⟩
    exact h α

/-- **The pointwise adequacy equivalence**: a model satisfies the
compiled constraints exactly when it is the rows' law.  Uniqueness is
bare finite extensionality — the singleton probes pin every weight
directly; no induction, and no exhaustiveness hypothesis: completeness
enters only through the mass theorem, never through the feeding
lemma. -/
theorem satAtoms_iff (R : QNetRows κ) (hR : R.WF) (μ : SubPMF κ) :
    looseConj (atoms R) μ ↔ μ = rowsLaw R hR := by
  rw [satAtoms_unpack]
  constructor
  · intro h
    refine SubPMF.ext' (Finsupp.ext fun α => ?_)
    have hα := h α
    rw [rowC, SubPMF.prob_singleton] at hα
    exact hα
  · rintro rfl α
    show (rowsLaw R hR).prob {α} = R.outcome α
    rw [SubPMF.prob_singleton, rowsLaw_wt]

/-- Compilation preserves the law: the sparse rows reconstruct the
Born row exactly. -/
theorem compile_rowsLaw (P : QNetSystem X n ι T κ) :
    rowsLaw (compile P) (compile_wf P) = P.shadowLaw :=
  SubPMF.ext' (Finsupp.ext fun _ => rfl)

/-! ## The incomplete family: partiality, exercised -/

section Incomplete

variable [DecidableEq κ]

/-- Compilation of a record *sub*family: store the Born row on a
subset of the record indices only — the compiled face of an
incomplete (non-exhaustive) family. -/
noncomputable def compileSub (P : QNetSystem X n ι T κ) (J : Finset κ) :
    QNetRows κ where
  outcome := Finsupp.onFinset Finset.univ
    (fun α => if α ∈ J then P.row α else 0)
    (fun _ _ => Finset.mem_univ _)

@[simp] theorem compileSub_outcome (P : QNetSystem X n ι T κ)
    (J : Finset κ) (α : κ) :
    (compileSub P J).outcome α = if α ∈ J then P.row α else 0 := rfl

theorem compileSub_wf (P : QNetSystem X n ι T κ) (J : Finset κ) :
    (compileSub P J).WF where
  nonneg α := by
    rw [compileSub_outcome]
    split
    · exact P.shadowPMF.nonneg α
    · exact le_refl 0
  mass_le := by
    refine le_trans (Finset.sum_le_sum fun α _ => ?_)
      (le_of_eq P.shadowPMF.total)
    rw [compileSub_outcome]
    split
    · exact le_refl _
    · exact P.shadowPMF.nonneg α

/-- The mass of a subfamily's law is the mass the subfamily
captures. -/
theorem compileSub_mass (P : QNetSystem X n ι T κ) (J : Finset κ) :
    (rowsLaw (compileSub P J) (compileSub_wf P J)).mass =
      ∑ α ∈ J, P.row α := by
  rw [rowsLaw_mass]
  simp only [compileSub_outcome]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

end Incomplete

end QNet

/-! ## The precise face -/

/-- **Adequacy of the quantum-net compilation, precise face.**

In the double category `Crd κ` of per-element credal constraints over
the record space: the loose-arrow diagram denoted by the compiled
system — the formal conjunction of one row constraint per record
index — is isomorphic, by an invertible globular cell, to the
singleton-credal inclusion of the Born row of the distinguished state.
Compile-then-denote agrees with interpret-then-include, where the
interpretation is the Born/Gell-Mann–Hartle record law of the
literature (`shadowPMF_prob_eq_born`), read through the
Brunetti–Fredenhagen–Verch state object
(`shadowPMF_eq_fragment_shadow`, `shadowPMF_class_invariant`). -/
theorem quantum_net_adequacy (P : QNetSystem X n ι T κ) {a : Crd κ} :
    ∃ α : Cell (looseConj (QNet.atoms (QNet.compile P)) : Loose a a)
        (singletonC P.shadowLaw) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  refine Crd.looseIso_ofIff fun μ => ?_
  rw [singletonC_iff, QNet.satAtoms_iff _ (QNet.compile_wf P) μ,
    QNet.compile_rowsLaw]

/-! ## The credal face: the state set, forced set-valued -/

namespace QNet

/-- **A rational-shadowed member of a declared state set**: a state of
the set together with the exact-rational witness of its Born row — the
honest index of the credal face at the exact-arithmetic stratum (a
member is carried with its certificate, never bare). -/
structure RatShadowMember (F : LCQFTFragment X n ι T κ)
    (S : Set {ρ : Matrix n n ℂ // IsState ρ}) where
  /-- The member state. -/
  state : {ρ : Matrix n n ℂ // IsState ρ}
  /-- Membership in the declared state set. -/
  mem : state ∈ S
  /-- The exact-rational Born row. -/
  row : κ → ℚ
  /-- The row witnesses the member's record law. -/
  row_spec : ∀ α, (row α : ℝ) = recordShadow F.records state.1 α

variable {F : LCQFTFragment X n ι T κ}
variable {S : Set {ρ : Matrix n n ℂ // IsState ρ}}

/-- The member's Born row, as a probability mass function. -/
noncomputable def RatShadowMember.pmf (w : RatShadowMember F S) :
    FinPMF κ :=
  recordShadowPMF F.records w.state.1 w.row w.row_spec
    F.records_posSemidef F.records_exhaustive w.state.2

/-- The member's law in the credal stratum. -/
noncomputable def RatShadowMember.law (w : RatShadowMember F S) :
    SubPMF κ :=
  w.pmf.toSubPMF

@[simp] theorem RatShadowMember.pmf_prob (w : RatShadowMember F S)
    (α : κ) : w.pmf.prob α = w.row α := rfl

@[simp] theorem RatShadowMember.law_wt (w : RatShadowMember F S)
    (α : κ) : w.law.wt α = w.row α := rfl

/-- Every member's law has full mass — the record family is
exhaustive.  This is what the slice and the lower-verdict transfer
spend. -/
theorem RatShadowMember.law_mass (w : RatShadowMember F S) :
    w.law.mass = 1 :=
  FinPMF.toSubPMF_mass _

/-- **The classical object of the credal face**: the set of Born rows
of the declared state set — the union of singletons over the
rational-shadowed members.  This is the set-valued semantics the
no-preferred-state theorem forces: the theory assigns a set of states,
so its record semantics is a set of laws. -/
def quantumLaws (F : LCQFTFragment X n ι T κ)
    (S : Set {ρ : Matrix n n ℂ // IsState ρ}) : SubPMF κ → Prop :=
  unionSingletons fun w : RatShadowMember F S => w.law

/-- The credal presentation: the union of the members' rays — the
downward-closed denotation of the state-set reading. -/
def quantumCredal (F : LCQFTFragment X n ι T κ)
    (S : Set {ρ : Matrix n n ℂ // IsState ρ}) : SubPMF κ → Prop :=
  unionRays fun w : RatShadowMember F S => w.law

/-- The compiled rows of one member. -/
noncomputable def compileMember (w : RatShadowMember F S) :
    QNetRows κ where
  outcome := Finsupp.onFinset Finset.univ w.row
    (fun _ _ => Finset.mem_univ _)

theorem compileMember_wf (w : RatShadowMember F S) :
    (compileMember w).WF where
  nonneg α := w.pmf.nonneg α
  mass_le := le_of_eq w.pmf.total

theorem compileMember_rowsLaw (w : RatShadowMember F S) :
    rowsLaw (compileMember w) (compileMember_wf w) = w.law :=
  SubPMF.ext' (Finsupp.ext fun _ => rfl)

/-- **The credal reading of the compiled presentation**: the rows stay
state-free, and the state choice is the existentially quantified row
mechanism — a model is admitted exactly when some rational-shadowed
member's compiled rows denote a diagram it satisfies. -/
def qnetCredalC (F : LCQFTFragment X n ι T κ)
    (S : Set {ρ : Matrix n n ℂ // IsState ρ}) : SubPMF κ → Prop :=
  fun μ => ∃ w : RatShadowMember F S,
    looseConj (atoms (compileMember w)) μ

/-- **The pointwise credal equivalence**: admission by some member's
compiled rows is exactly membership in the law-set — the precise
feeding lemma, per member. -/
theorem qnetCredalC_iff (F : LCQFTFragment X n ι T κ)
    (S : Set {ρ : Matrix n n ℂ // IsState ρ}) (μ : SubPMF κ) :
    qnetCredalC F S μ ↔ quantumLaws F S μ := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, (singletonC_iff _ _).mpr ?_⟩
    show μ = w.law
    rw [← compileMember_rowsLaw w]
    exact (satAtoms_iff _ (compileMember_wf w) μ).mp hw
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [satAtoms_iff _ (compileMember_wf w), compileMember_rowsLaw]
    exact (singletonC_iff _ _).mp hw

end QNet

/-- **Adequacy of the quantum-net compilation, credal face** — the
set-valued square whose imprecision is the community's own theorem
(no preferred states, Brunetti–Fredenhagen–Verch §5.1).

In the double category `Crd κ`: the credal reading of the compiled,
state-free rows — admitted by *some* rational-shadowed member of the
declared state set — is isomorphic, by an invertible globular cell, to
the set-valued inclusion of the state set's Born rows. -/
theorem quantum_credal_adequacy (F : LCQFTFragment X n ι T κ)
    (S : Set {ρ : Matrix n n ℂ // IsState ρ}) {a : Crd κ} :
    ∃ α : Cell (QNet.qnetCredalC F S : Loose a a)
        (QNet.quantumLaws F S) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  Crd.looseIso_ofIff (QNet.qnetCredalC_iff F S)

/-- **The quantum slice**: the radially maximal slice of the credal
presentation is exactly the law-set — the equal-mass reconciliation at
mass one, every member's law having full mass. -/
theorem quantum_maxSlice (F : LCQFTFragment X n ι T κ)
    (S : Set {ρ : Matrix n n ℂ // IsState ρ}) (ν : SubPMF κ) :
    maxSlice (QNet.quantumCredal F S) ν ↔ QNet.quantumLaws F S ν :=
  maxSlice_unionRays (fun w => w.law_mass) one_ne_zero ν

/-- The credal reconciliation, packaged as an invertible cell. -/
theorem quantum_ray_singleton_reconciliation
    (F : LCQFTFragment X n ι T κ)
    (S : Set {ρ : Matrix n n ℂ // IsState ρ}) {a : Crd κ} :
    ∃ α : Cell (maxSlice (QNet.quantumCredal F S) : Loose a a)
        (QNet.quantumLaws F S) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  Crd.looseIso_ofIff (quantum_maxSlice F S)

/-- **The lower verdict is the uniform-over-states bound**: a
lower-kind constraint holds of the credal presentation exactly when it
holds of every member's Born row — through the slice. -/
theorem satCredal_lower_quantumCredal (F : LCQFTFragment X n ι T κ)
    (S : Set {ρ : Matrix n n ℂ // IsState ρ})
    (c : SubPMF κ → Prop) :
    SatCredal .lower (QNet.quantumCredal F S) c ↔
      ∀ w : QNet.RatShadowMember F S, c w.law :=
  satCredal_lower_unionRays (fun w => w.law_mass) one_ne_zero c

/-- **The upper verdict is the uniform-over-states bound**, for
down-closed constraints — mass-free, through down-closure. -/
theorem satCredal_upper_quantumCredal (F : LCQFTFragment X n ι T κ)
    (S : Set {ρ : Matrix n n ℂ // IsState ρ})
    {c : SubPMF κ → Prop} (hc : DownClosed c) :
    SatCredal .upper (QNet.quantumCredal F S) c ↔
      ∀ w : QNet.RatShadowMember F S, c w.law :=
  satCredal_upper_unionRays hc

theorem satCredal_lower_quantumLaws (F : LCQFTFragment X n ι T κ)
    (S : Set {ρ : Matrix n n ℂ // IsState ρ})
    (c : SubPMF κ → Prop) :
    SatCredal .lower (QNet.quantumLaws F S) c ↔
      ∀ w : QNet.RatShadowMember F S, c w.law :=
  satCredal_lower_unionSingletons (fun w => w.law_mass) one_ne_zero c

theorem satCredal_upper_quantumLaws (F : LCQFTFragment X n ι T κ)
    (S : Set {ρ : Matrix n n ℂ // IsState ρ})
    (c : SubPMF κ → Prop) :
    SatCredal .upper (QNet.quantumLaws F S) c ↔
      ∀ w : QNet.RatShadowMember F S, c w.law :=
  satCredal_upper_unionSingletons c

/-! ## Degeneracies, mechanized rather than smoothed -/

/-- As soon as one rational-shadowed member exists, the credal
presentation contains the zero model, so the whole-set reading of a
lower-bound atom refuses every positive threshold — the slice
discipline's reason for existing, at the quantum former. -/
theorem not_satCredal_upper_quantumCredal_geC
    (F : LCQFTFragment X n ι T κ)
    (S : Set {ρ : Matrix n n ℂ // IsState ρ})
    [hne : Nonempty (QNet.RatShadowMember F S)]
    {E : Set κ} {q : ℚ} (hq : 0 < q) :
    ¬ SatCredal .upper (QNet.quantumCredal F S) (geC E q) := by
  intro h
  obtain ⟨w⟩ := hne
  have h0 : q ≤ (SubPMF.zero κ).prob E :=
    h (SubPMF.zero _) ⟨w, rayC_zero _⟩
  rw [SubPMF.zero_prob] at h0
  linarith

/-- **The empty member index validates everything**: with no
rational-shadowed members, both verdict kinds pass vacuously — the
∀-over-no-members convention, recorded rather than smoothed. -/
theorem satCredal_quantum_of_isEmpty (F : LCQFTFragment X n ι T κ)
    (S : Set {ρ : Matrix n n ℂ // IsState ρ})
    [h : IsEmpty (QNet.RatShadowMember F S)] (kind : EnvelopeKind)
    (c : SubPMF κ → Prop) :
    SatCredal kind (QNet.quantumCredal F S) c := by
  cases kind with
  | lower =>
    rintro ν ⟨⟨w, -⟩, -⟩
    exact (h.false w).elim
  | upper =>
    rintro ν ⟨w, -⟩
    exact (h.false w).elim

/-! ## Convexity: quantum mixtures land inside the face -/

namespace QNet

variable {F : LCQFTFragment X n ι T κ}
variable {S : Set {ρ : Matrix n n ℂ // IsState ρ}}

/-- Closure of a state set under rational convex mixture — the
hypothesis under which the credal law-set is convex.  The full state
body satisfies it (`isState_mix`); a bare pair of states does not,
and `mixLaw_not_mem_pair` shows the hypothesis is load-bearing. -/
def MixClosed (S : Set {ρ : Matrix n n ℂ // IsState ρ}) : Prop :=
  ∀ ρ σ : {ρ : Matrix n n ℂ // IsState ρ}, ρ ∈ S → σ ∈ S →
    ∀ t : ℚ, ∀ h₀ : 0 ≤ t, ∀ h₁ : t ≤ 1,
      (⟨((t : ℚ) : ℂ) • ρ.1 + (((1 - t : ℚ)) : ℂ) • σ.1,
        isState_mix ρ.2 σ.2 h₀ h₁⟩ :
          {ρ : Matrix n n ℂ // IsState ρ}) ∈ S

/-- **Quantum mixtures land on credal mixtures, at the law-set**: for
a mixture-closed state set, the convex mixture of two members' Born
rows is again a member's Born row — the landed convexity seam
(`recordShadowPMF_mix`), consumed at the set-valued face. -/
theorem quantumLaws_mix (hS : MixClosed S)
    (w₁ w₂ : RatShadowMember F S) {t : ℚ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
    quantumLaws F S (FinPMF.mix w₁.pmf w₂.pmf t h₀ h₁).toSubPMF := by
  refine ⟨⟨⟨((t : ℚ) : ℂ) • w₁.state.1 + (((1 - t : ℚ)) : ℂ) • w₂.state.1,
      isState_mix w₁.state.2 w₂.state.2 h₀ h₁⟩,
      hS w₁.state w₂.state w₁.mem w₂.mem t h₀ h₁,
      fun α => t * w₁.row α + (1 - t) * w₂.row α,
      fun α => recordShadow_mix_rat_witness w₁.row_spec w₂.row_spec α⟩,
    (singletonC_iff _ _).mpr ?_⟩
  exact congrArg FinPMF.toSubPMF
    (recordShadowPMF_mix F.records w₁.state.1 w₂.state.1 w₁.row w₂.row
      w₁.row_spec w₂.row_spec F.records_posSemidef
      F.records_exhaustive w₁.state.2 w₂.state.2 h₀ h₁).symm

end QNet

/-! ## The instance: the two-qubit fragment, Bell and maximally mixed

The square instantiated nonvacuously at the landed
`isingQubitFragment`, whose record family is the four-projector
computational-basis (zz) measurement.  The Bell/mixed pair also feeds
the credal face's negative witnesses; the strict openness of its
credal band is the landed
`Qtsl.QuantumStates.exists_shadow_lowerE_lt_upperE` — graded
information the flat folium
(`Qtsl.QuantumStates.existsUnique_isState_traceRepr`, quoted not
re-proven) cannot state. -/

/-- The Bell-state quantum-net system on the two-qubit fragment. -/
noncomputable def bellQNet :
    QNetSystem (Mink ℝ) (Fin 2 × Fin 2) (Fin 2) ℝ (Fin 2 × Fin 2) where
  frag := isingQubitFragment
  state := bell
  state_isState := bell_isState
  row := fun ik => if ik.1 = ik.2 then 1 / 2 else 0
  row_spec := fun ik => by
    show _ = recordShadow zzRecord bell ik
    rw [recordShadow_zz_bell]
    split <;> norm_num

/-- The maximally-mixed quantum-net system on the two-qubit
fragment. -/
noncomputable def mixedQNet :
    QNetSystem (Mink ℝ) (Fin 2 × Fin 2) (Fin 2) ℝ (Fin 2 × Fin 2) where
  frag := isingQubitFragment
  state := mixed
  state_isState := mixed_isState
  row := fun _ => 1 / 4
  row_spec := fun ik => by
    show _ = recordShadow zzRecord mixed ik
    rw [recordShadow_zz_mixed]
    norm_num

/-- The instance's left edge is the landed Bell shadow. -/
theorem bellQNet_shadowPMF : bellQNet.shadowPMF = bellShadowPMF :=
  FinPMF.ext fun _ => rfl

/-- The instance's left edge is the landed mixed shadow. -/
theorem mixedQNet_shadowPMF : mixedQNet.shadowPMF = mixedShadowPMF :=
  FinPMF.ext fun _ => rfl

/-- **Partiality, exercised**: the three-projector subfamily of the zz
record family at the maximally mixed state spends mass `3/4 < 1` — an
incomplete record family denotes a genuine subprobability law.  The
target stratum's mass-loss allowance, unexercised by every stochastic
former, is exercised naturally by a quantum presentation. -/
theorem exists_incomplete_mass_lt_one :
    ∃ (P : QNetSystem (Mink ℝ) (Fin 2 × Fin 2) (Fin 2) ℝ
        (Fin 2 × Fin 2)) (J : Finset (Fin 2 × Fin 2)),
      (QNet.rowsLaw (QNet.compileSub P J)
        (QNet.compileSub_wf P J)).mass < 1 := by
  refine ⟨mixedQNet, Finset.univ.erase ((0 : Fin 2), (0 : Fin 2)), ?_⟩
  rw [QNet.compileSub_mass]
  have hrow : ∀ ik : Fin 2 × Fin 2, mixedQNet.row ik = 1 / 4 :=
    fun _ => rfl
  rw [Finset.sum_congr rfl fun ik _ => hrow ik, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _)]
  norm_num [Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul]

/-! ### The negative witnesses -/

/-- The Bell/mixed pair, as a declared state set — deliberately NOT
mixture-closed. -/
def bellMixedSet : Set {ρ : TwoQubits // IsState ρ} :=
  {x | x = ⟨bell, bell_isState⟩ ∨ x = ⟨mixed, mixed_isState⟩}

/-- The Bell member of the pair set. -/
noncomputable def bellMember :
    QNet.RatShadowMember isingQubitFragment bellMixedSet where
  state := ⟨bell, bell_isState⟩
  mem := Or.inl rfl
  row := fun ik => if ik.1 = ik.2 then 1 / 2 else 0
  row_spec := fun ik => by
    show _ = recordShadow zzRecord bell ik
    rw [recordShadow_zz_bell]
    split <;> norm_num

/-- The maximally-mixed member of the pair set. -/
noncomputable def mixedMember :
    QNet.RatShadowMember isingQubitFragment bellMixedSet where
  state := ⟨mixed, mixed_isState⟩
  mem := Or.inr rfl
  row := fun _ => 1 / 4
  row_spec := fun ik => by
    show _ = recordShadow zzRecord mixed ik
    rw [recordShadow_zz_mixed]
    norm_num

/-- **The mixture-closure hypothesis is load-bearing**: over the
two-element Bell/mixed set — not mixture-closed — the midpoint of the
members' Born rows is NOT in the law-set: its `(0,0)` entry is `3/8`,
while the members' rows are pinned by their witnesses to `1/2` and
`1/4`.  (Contrast `quantumLaws_mix`, whose conclusion this refutes
once its hypothesis is dropped.) -/
theorem mixLaw_not_mem_pair :
    ¬ QNet.quantumLaws isingQubitFragment bellMixedSet
        (FinPMF.mix bellMember.pmf mixedMember.pmf (1 / 2)
          (by norm_num) (by norm_num)).toSubPMF := by
  rintro ⟨w, hw⟩
  have heq : (FinPMF.mix bellMember.pmf mixedMember.pmf (1 / 2)
      (by norm_num) (by norm_num)).toSubPMF = w.law :=
    (singletonC_iff _ _).mp hw
  have hwt := congrArg
    (fun μ : SubPMF (Fin 2 × Fin 2) => μ.wt ((0 : Fin 2), (0 : Fin 2)))
    heq
  simp only [Qtsl.Imprecise.FinPMF.toSubPMF_wt, FinPMF.mix_prob,
    QNet.RatShadowMember.pmf_prob, QNet.RatShadowMember.law_wt] at hwt
  have hb : bellMember.row ((0 : Fin 2), (0 : Fin 2)) = 1 / 2 := by
    show (if ((0 : Fin 2), (0 : Fin 2)).1 = ((0 : Fin 2), (0 : Fin 2)).2
        then (1 / 2 : ℚ) else 0) = 1 / 2
    exact if_pos rfl
  have hm : mixedMember.row ((0 : Fin 2), (0 : Fin 2)) = 1 / 4 := rfl
  rw [hb, hm] at hwt
  have hpin : w.row ((0 : Fin 2), (0 : Fin 2)) = 1 / 2 ∨
      w.row ((0 : Fin 2), (0 : Fin 2)) = 1 / 4 := by
    have hspec := w.row_spec ((0 : Fin 2), (0 : Fin 2))
    rcases w.mem with hb' | hm'
    · left
      rw [hb'] at hspec
      have h2 : (w.row ((0 : Fin 2), (0 : Fin 2)) : ℝ) =
          ((1 / 2 : ℚ) : ℝ) := by
        rw [hspec]
        show recordShadow zzRecord bell _ = _
        rw [recordShadow_zz_bell]
        norm_num
      exact_mod_cast h2
    · right
      rw [hm'] at hspec
      have h2 : (w.row ((0 : Fin 2), (0 : Fin 2)) : ℝ) =
          ((1 / 4 : ℚ) : ℝ) := by
        rw [hspec]
        show recordShadow zzRecord mixed _ = _
        rw [recordShadow_zz_mixed]
        norm_num
      exact_mod_cast h2
  rcases hpin with hp | hp <;> rw [hp] at hwt <;> norm_num at hwt

/-- **Record positivity is load-bearing**: a Hermitian family summing
to one but not positive-semidefinite prices an outcome negatively —
the kernel-visible reason the compiled rows' nonnegativity spends
`records_posSemidef`. -/
theorem exists_nonPSD_family_negative_shadow :
    ∃ (R : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ)
      (ρ : Matrix (Fin 1) (Fin 1) ℂ),
      IsState ρ ∧ (∑ α, R α = 1) ∧ ∃ α, recordShadow R ρ α < 0 := by
  have hone : (1 : Matrix (Fin 1) (Fin 1) ℂ) =
      Matrix.vecMulVec ![1] (star ![1]) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.vecMulVec_apply]
  refine ⟨![1 + 1, -1], 1, ⟨?_, ?_⟩, ?_, 1, ?_⟩
  · rw [hone]
    exact posSemidef_vecMulVec_star_self _
  · rw [Matrix.trace_one]
    simp
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    abel
  · show ((((1 : Matrix (Fin 1) (Fin 1) ℂ) *
      (![1 + 1, -1] (1 : Fin 2))).trace).re) < 0
    rw [one_mul]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [Matrix.trace_neg, Matrix.trace_one]
    norm_num [Fintype.card_fin, Complex.neg_re, Complex.natCast_re]

/-! ## The fibre reading: the square over the record interface

The wiring pattern of the assignment interface, reused verbatim: the
single-window record space embeds into the states of a one-wire
interface, laws and constraints push forward along the embedding, and
the transported judgment runs through the generic bridge. -/

section QuantumWire

open CategoryTheory.WireSpan

variable {κ : Type} [Fintype κ]

/-- The record interface: one wire, carrying the record outcome. -/
abbrev recWire (κ : Type) : WireSpan κ := ⟨Fin 1⟩

/-- A record outcome, read as a state of the record interface. -/
def recState : κ → states (recWire κ) := fun a _ => a

omit [Fintype κ] in
theorem recState_injective :
    Function.Injective (recState (κ := κ)) := fun _ _ h =>
  congrFun h 0

/-- The compiled quantum-net presentation at the record interface: the
pushed constraint diagram, as a citizen of the semantic universe's
fibre — by type. -/
noncomputable def qnetSpecW (R : QNet.QNetRows κ) :
    DnfSpec (recWire κ) :=
  diagramDnf ((QNet.atoms R).map (cmap recState))

/-- The rows-grain wiring at the record interface: the pushed ideal
point models the pushed presentation exactly when the intrinsic law is
the rows' law. -/
theorem su_qnet_wiring {R : QNet.QNetRows κ} (hR : R.WF)
    (μ : SubPMF κ) :
    idealPoint (μ.map recState) ∈ (qnetSpecW R).modelClass
      ↔ μ = QNet.rowsLaw R hR :=
  (idealPoint_map_mem_diagramDnf_iff recState_injective
      (QNet.atoms R) μ).trans (QNet.satAtoms_iff R hR μ)

variable {X : Type*} [PartialOrder X]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι T : Type*}

/-- **The quantum square, in the fibre over the record interface**:
the pushed ideal point of a law models the compiled system's pushed
presentation exactly when the law is the Born row. -/
theorem su_qnet_adequacy (P : QNetSystem X n ι T κ) (μ : SubPMF κ) :
    idealPoint (μ.map recState)
        ∈ (qnetSpecW (QNet.compile P)).modelClass
      ↔ μ = P.shadowLaw := by
  rw [su_qnet_wiring (QNet.compile_wf P) μ, QNet.compile_rowsLaw]

/-- The positive face at the quantum corner, in the fibre. -/
theorem su_qnet_shadowLaw_mem (P : QNetSystem X n ι T κ) :
    idealPoint (P.shadowLaw.map recState)
      ∈ (qnetSpecW (QNet.compile P)).modelClass :=
  (su_qnet_adequacy P P.shadowLaw).mpr rfl

/-- Ex falso at the quantum corner, in the fibre. -/
theorem su_qnet_bottom (R : QNet.QNetRows κ) :
    (⊤ : Plain.Pen (states (recWire κ))) ∉ (qnetSpecW R).modelClass :=
  top_notMem_diagramDnf _

end QuantumWire

end Adequacy
end SuFunctor

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.Imprecise.FinPMF.toSubPMF_mass
#print axioms Qtsl.Imprecise.FinPMF.toSubPMF_injective
#print axioms SuFunctor.Adequacy.QNetSystem.shadowLaw_mass
#print axioms SuFunctor.Adequacy.QNetSystem.shadowPMF_prob_eq_born
#print axioms SuFunctor.Adequacy.QNetSystem.shadowPMF_eq_fragment_shadow
#print axioms SuFunctor.Adequacy.shadowPMF_class_invariant
#print axioms SuFunctor.Adequacy.QNet.compile_complete
#print axioms SuFunctor.Adequacy.QNet.compile_wf
#print axioms SuFunctor.Adequacy.QNet.rowsLaw_mass
#print axioms SuFunctor.Adequacy.QNet.rowsLaw_mass_of_complete
#print axioms SuFunctor.Adequacy.QNet.satAtoms_unpack
#print axioms SuFunctor.Adequacy.QNet.satAtoms_iff
#print axioms SuFunctor.Adequacy.QNet.compile_rowsLaw
#print axioms SuFunctor.Adequacy.QNet.compileSub_wf
#print axioms SuFunctor.Adequacy.QNet.compileSub_mass
#print axioms SuFunctor.Adequacy.quantum_net_adequacy
#print axioms SuFunctor.Adequacy.QNet.RatShadowMember.law_mass
#print axioms SuFunctor.Adequacy.QNet.compileMember_rowsLaw
#print axioms SuFunctor.Adequacy.QNet.qnetCredalC_iff
#print axioms SuFunctor.Adequacy.quantum_credal_adequacy
#print axioms SuFunctor.Adequacy.quantum_maxSlice
#print axioms SuFunctor.Adequacy.quantum_ray_singleton_reconciliation
#print axioms SuFunctor.Adequacy.satCredal_lower_quantumCredal
#print axioms SuFunctor.Adequacy.satCredal_upper_quantumCredal
#print axioms SuFunctor.Adequacy.satCredal_lower_quantumLaws
#print axioms SuFunctor.Adequacy.satCredal_upper_quantumLaws
#print axioms SuFunctor.Adequacy.not_satCredal_upper_quantumCredal_geC
#print axioms SuFunctor.Adequacy.satCredal_quantum_of_isEmpty
#print axioms SuFunctor.Adequacy.QNet.quantumLaws_mix
#print axioms SuFunctor.Adequacy.bellQNet_shadowPMF
#print axioms SuFunctor.Adequacy.mixedQNet_shadowPMF
#print axioms SuFunctor.Adequacy.exists_incomplete_mass_lt_one
#print axioms SuFunctor.Adequacy.mixLaw_not_mem_pair
#print axioms SuFunctor.Adequacy.exists_nonPSD_family_negative_shadow
#print axioms SuFunctor.Adequacy.su_qnet_wiring
#print axioms SuFunctor.Adequacy.su_qnet_adequacy
#print axioms SuFunctor.Adequacy.su_qnet_shadowLaw_mem
#print axioms SuFunctor.Adequacy.su_qnet_bottom
