import SuFunctor.StateSpace.Limits
import Mathlib.Topology.Category.LightProfinite.Sequence

/-! # Citizens: the discrete-mode state spaces, with their lcsc receipts

The motivating members of the ω-semialgebraic class, mechanized as
objects together with exactly the topological structure the
semantic-universe carrier consumes of a state space — local compactness
(with second countability and Hausdorffness automatic for subspaces of
`ℝⁿ`):

* **`natSet`** — `ℕ ⊆ ℝ`: one degree-1 rational piece per point
  (`natSet_isOmegaSA`), closed in the ambient (`natSet_isClosed`), hence
  locally compact.  This is the citizen that is definable in no o-minimal
  structure and drives the countability axis.
* **`counterSet`** — the compactified counter `{0} ∪ {1/(k+1) : k ∈ ℕ}`:
  one rational piece per point (`counterSet_isOmegaSA`), compact
  (`counterSet_isCompact`), and homeomorphic to the one-point
  compactification `ℕ∞ = OnePoint ℕ` (`counterHomeo`).  A citizen
  receipt, not a closure obligation: the class owes no cemetery
  closure — compactification is an *operation* performed downstream of
  the class (mathlib's `OnePoint`, packaged for arbitrary ambients at
  the hyperspace tier by `SuFunctor.Universe.FellOnePoint`, and as the
  promotion chart at the valuation tier), and every downstream consumer
  of a fibre consumes local compactness only.  This citizen shows the
  wedge pattern is expressible in-class; nothing demands it.
* **`intervalNatObj`** — `[0,1] × ℕ`: a hybrid product citizen, locally
  closed via the product bridge (`isLocallyClosed_prodObj`).

The lcsc bridge is deliberately thin: the citizenship demand is local
compactness (with second countability and Hausdorffness automatic for
subspaces), *certified* at adoption time by local closedness of the
carved set — `ℚ ⊆ ℝ` is in the carving class and fails it — and
mathlib's `IsLocallyClosed.locallyCompactSpace` turns the certificate
into the subspace structure the carrier's record/Fell tier wants.
Nothing here consumes the carving beyond producing it.
-/

namespace SuFunctor.StateSpace

open MvPolynomial Set Topology OnePoint

noncomputable section

/-! ## The lcsc bridge -/

/-- The citizenship bridge: a locally closed subset of the ambient is a
locally compact space — with `T2Space` and `SecondCountableTopology`
instances automatic for subspaces — i.e. exactly the "lcsc state space"
interface the record layer consumes. -/
theorem locallyCompactSpace_of_isLocallyClosed {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : IsLocallyClosed S) : LocallyCompactSpace S :=
  h.locallyCompactSpace

/-- Products of locally closed citizens are locally closed (the product
carrier is an intersection of preimages under the continuous block
projections). -/
theorem isLocallyClosed_prodObj {V W : OmegaSA}
    (hV : IsLocallyClosed V.carrier) (hW : IsLocallyClosed W.carrier) :
    IsLocallyClosed (prodObj V W).carrier := by
  have h1 : Continuous fun (z : Fin (V.dim + W.dim) → ℝ) =>
      (fun i => z (Fin.castAdd W.dim i)) :=
    continuous_pi fun i => continuous_apply _
  have h2 : Continuous fun (z : Fin (V.dim + W.dim) → ℝ) =>
      (fun j => z (Fin.natAdd V.dim j)) :=
    continuous_pi fun j => continuous_apply _
  exact (hV.preimage h1).inter (hW.preimage h2)

/-! ## ℕ, the counter -/

/-- `ℕ` inside `ℝ¹`. -/
def natSet : Set (Fin 1 → ℝ) := {x | ∃ k : ℕ, x 0 = (k : ℝ)}

/-- The carving of `ℕ`: one degree-1 rational piece per point. -/
theorem natSet_isOmegaSA : IsOmegaSA natSet := by
  refine ⟨fun k => eqConds (X 0 - C (k : ℚ)), ?_⟩
  ext x
  simp only [natSet, mem_setOf_eq, mem_iUnion]
  refine exists_congr fun k => ?_
  rw [mem_basicSet_eqConds]
  simp [sub_eq_zero, map_natCast]

/-- The counter object. -/
def natObj : OmegaSA := ⟨1, natSet, natSet_isOmegaSA⟩

theorem natSet_isClosed : IsClosed natSet := by
  have h : natSet = (fun x : Fin 1 → ℝ => x 0) ⁻¹' (Set.range ((↑) : ℕ → ℝ)) := by
    ext x
    simp [natSet, eq_comm, Set.mem_range]
  rw [h]
  exact (Nat.isClosedEmbedding_coe_real.isClosed_range).preimage (continuous_apply 0)

/-- `ℕ` is a locally compact (second-countable, Hausdorff) state space:
the closed-citizenship pattern. -/
instance : LocallyCompactSpace natSet :=
  natSet_isClosed.isLocallyClosed.locallyCompactSpace

/-! ## The compactified counter `ℕ∞` -/

/-- The compactified counter `{0} ∪ {1/(k+1) : k ∈ ℕ}` inside `ℝ¹`:
the one-point compactification of the counter, realized with one
rational piece per mode. -/
def counterSet : Set (Fin 1 → ℝ) :=
  {x | x 0 = 0 ∨ ∃ k : ℕ, ((k : ℝ) + 1) * x 0 = 1}

/-- The carving of the compactified counter: the wedge point `0` and one
degree-1 rational piece per mode. -/
theorem counterSet_isOmegaSA : IsOmegaSA counterSet := by
  refine ⟨fun k => match k with
    | 0 => eqConds (X 0)
    | (k + 1) => eqConds ((C (k : ℚ) + 1) * X 0 - 1), ?_⟩
  ext x
  simp only [counterSet, mem_setOf_eq, mem_iUnion]
  constructor
  · rintro (h0 | ⟨k, hk⟩)
    · exact ⟨0, by rw [mem_basicSet_eqConds]; simpa using h0⟩
    · refine ⟨k + 1, ?_⟩
      rw [mem_basicSet_eqConds]
      simpa [sub_eq_zero, map_natCast] using hk
  · rintro ⟨k, hk⟩
    match k with
    | 0 =>
        rw [mem_basicSet_eqConds] at hk
        exact Or.inl (by simpa using hk)
    | (k + 1) =>
        rw [mem_basicSet_eqConds] at hk
        refine Or.inr ⟨k, ?_⟩
        simpa [sub_eq_zero, map_natCast] using hk

/-- The compactified counter object — a citizen receipt with no
downstream consumers (see `counterHomeo` for the design position). -/
def counterObj : OmegaSA := ⟨1, counterSet, counterSet_isOmegaSA⟩

/-- The realization map `ℕ∞ → ℝ¹`, `k ↦ 1/(k+1)`, `∞ ↦ 0` (the
mathlib convergent-sequence embedding, pushed into the one-dimensional
ambient). -/
def counterMap : OnePoint ℕ → (Fin 1 → ℝ) :=
  fun p _ => LightProfinite.natUnionInftyEmbedding p

theorem counterMap_isClosedEmbedding :
    Topology.IsClosedEmbedding counterMap := by
  have h : counterMap =
      ((Homeomorph.funUnique (Fin 1) ℝ).symm ∘
        LightProfinite.natUnionInftyEmbedding) := by
    funext p i
    rfl
  rw [h]
  exact (Homeomorph.funUnique (Fin 1) ℝ).symm.isClosedEmbedding.comp
    LightProfinite.isClosedEmbedding_natUnionInftyEmbedding

lemma counterMap_infty_apply (i : Fin 1) : counterMap ∞ i = 0 := rfl

lemma counterMap_some_apply (k : ℕ) (i : Fin 1) :
    counterMap (OnePoint.some k) i = 1 / ((k : ℝ) + 1) := rfl

theorem range_counterMap : Set.range counterMap = counterSet := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    rcases p with - | k
    · exact Or.inl rfl
    · refine Or.inr ⟨k, ?_⟩
      show ((k : ℝ) + 1) * (1 / ((k : ℝ) + 1)) = 1
      rw [mul_one_div, div_self (by positivity)]
  · rintro (h0 | ⟨k, hk⟩)
    · refine ⟨∞, ?_⟩
      funext i
      have h : i = 0 := Subsingleton.elim i 0
      subst h
      show (0 : ℝ) = x 0
      exact h0.symm
    · refine ⟨OnePoint.some k, ?_⟩
      funext i
      have h : i = 0 := Subsingleton.elim i 0
      subst h
      show 1 / ((k : ℝ) + 1) = x 0
      have hpos : ((k : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      linarith [hk]

/-- The compactified counter is compact. -/
theorem counterSet_isCompact : IsCompact counterSet := by
  rw [← range_counterMap]
  exact isCompact_range counterMap_isClosedEmbedding.continuous

instance : CompactSpace counterSet :=
  isCompact_iff_compactSpace.mp counterSet_isCompact

/-- The compactified counter in the class is homeomorphic to the
one-point compactification of `ℕ` — `ℕ∞` realizes as `{0} ∪ {1/(k+1)}`,
one constant rational piece per mode, the wedge point at the origin.

Retired belt-and-braces: this produces a carved compactification that no
consumer demands.  The state-space commitments ask fibres to be locally
compact — certified by locally closed carved pieces — and the operative
cemetery is the one-point compactification as an *operation* at the
record-carrier tier (mathlib's `OnePoint`, packaged for arbitrary
ambients by `SuFunctor.Universe.FellOnePoint`) and at the valuation tier
(the pointfree promotion chart), never a closure demand on the carving
class.  Kept as a true, green, zero-maintenance citizen receipt: the
wedge realization is expressible in-class, and nothing mandates it. -/
def counterHomeo : OnePoint ℕ ≃ₜ counterSet :=
  (counterMap_isClosedEmbedding.isEmbedding.toHomeomorph).trans
    (Homeomorph.setCongr range_counterMap)

/-- The compactified counter is a locally compact state space (compact ⇒
closed ⇒ locally closed citizenship). -/
instance : LocallyCompactSpace counterSet :=
  (counterSet_isCompact.isClosed.isLocallyClosed).locallyCompactSpace

/-! ## A hybrid product citizen: `[0,1] × ℕ` -/

/-- The unit interval in `ℝ¹`: a single basic piece `-x ≤ 0 ∧ x - 1 ≤ 0`. -/
def unitIntervalObj : OmegaSA :=
  ⟨1, BasicSet [⟨-(X 0), .le⟩, ⟨X 0 - 1, .le⟩], IsOmegaSA.of_basic _⟩

theorem unitIntervalObj_isLocallyClosed :
    IsLocallyClosed (unitIntervalObj.carrier) :=
  isLocallyClosed_basicSet _

/-- The hybrid citizen `[0,1] × ℕ`: a continuous factor and a discrete
countable factor, in one ω-semialgebraic object. -/
def intervalNatObj : OmegaSA := prodObj unitIntervalObj natObj

/-- `[0,1] × ℕ` is a locally compact state space: the product bridge on
locally closed citizens. -/
instance : LocallyCompactSpace (intervalNatObj.carrier) :=
  (isLocallyClosed_prodObj unitIntervalObj_isLocallyClosed
    natSet_isClosed.isLocallyClosed).locallyCompactSpace

/-- Second countability and Hausdorffness, recorded once: automatic for
every subspace of the ambient (the other two thirds of "lcsc"). -/
example : T2Space (natSet) ∧ T2Space (counterSet) := ⟨inferInstance, inferInstance⟩

example : SecondCountableTopology (natSet) ∧ SecondCountableTopology (counterSet) :=
  ⟨inferInstance, inferInstance⟩

end

end SuFunctor.StateSpace
