import SuFunctor.Adequacy.StochasticPetriColouredComposed
import SuFunctor.Adequacy.StochasticPetriColouredDemonic

/-! # Adequacy: coloured flattening, demonic and angelic directed faces

The flatten-facing transfer forms at colour — the faces the coloured
demonic module's scope fence named as "the coloured composed square's
to instantiate once its constructed flattening lands".  Both parents
have landed; this module is the first importer of both, and every
statement is a template instantiation: the uncoloured directed faces
(`SuFunctor.Adequacy.StochasticPetriFlatten`,
`SuFunctor.Adequacy.StochasticPetriAngelic`,
`SuFunctor.Adequacy.StochasticPetriComposed`) with the coloured
membership machinery
(`SuFunctor.Adequacy.StochasticPetriColouredDemonic`) spent at the
final step, through the coloured composed module's interface sockets.

**What is claimed.**  Agreement in, verdicts out, at the coloured
grain, in four tiers:

* the interface tier (`flatten_demonic_directed_of_agree`,
  `flatten_angelic_directed_of_agree`, `flatten_angelic_of_agree`,
  `flatten_demonic_verdict_of_agree`): a flat presentation on an
  abstract mode carrier, agreeing with the scheduler-closed coloured
  net off-diagonally and initially at some enabling-respecting
  adversary, transfers verdicts against the coloured demonic reading —
  the flattened law is that adversary's law, so universally certified
  demonic claims restrict to it, and claims established on it are
  angelic witnesses;
* the composed tier (`flatten_composed_demonic_directed_of_agree`,
  `flatten_composed_angelic_directed_of_agree`): the same faces read
  at the community grain, pasted through the flattened object's own
  jump-chain square;
* the discharged tier (`flatten_composed_demonic_directed`,
  `flatten_composed_angelic_directed`): the composed faces at the
  constructed coloured flattening, agreement receipts consumed from
  the composed module, no agreement hypothesis;
* the premise-bundle tier (`…_of_premises`): the community's premise
  set consumed whole, the scheduler taken bare with its
  enabling-respecting certificate.

**Sound directions only.**  Every cell here is directed: the demonic
set quantifies over adversaries the flattening never sees, and the
slice contains every adversary's law, so no envelope equality is
stated anywhere in this module — exactly the uncoloured faces'
grading, unchanged at colour.

**Scope fences.**  Everything the parents fence stays fenced:
kernel-valued firing measures beyond the Dirac slice,
boundary-hitting guards, the colour-vector carrier identification
with its padding obligations (the hybrid-grain residue), the
exponential time-law stratum, and law-level plurality of the coloured
arena.  No certificate rows are minted. -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Finset

variable {P T U : Type} [Fintype P] [DecidableEq P] [Fintype T]
  [Fintype U] [DecidableEq U] {K : P → Type} [∀ p, Fintype (K p)]
  [∀ p, DecidableEq (K p)] {B : ℕ}

/- The demonic reading's scheduler-row machinery keys rows by
(marking, pair); its consumers need the same Σ/Π-instance headroom the
coloured demonic module's own decidability instances needed. -/
set_option synthInstance.maxHeartbeats 400000

namespace FinCISPN

variable (N : FinCISPN P T U K B)

/-! ## The interface tier: agreement in, verdicts out -/

/-- **The demonic directed face at colour, packaged from agreement**:
the transported flat presentation's compiled reading *entails* the
compiled coloured demonic reading — the flattened law is one arena
member's law (the declared enabling-respecting adversary's, token
selections included), so every universally-quantified demonic verdict
transfers to it.  A directed cell, sound direction only; the reverse
entailment is not claimed (the demonic set quantifies over adversaries
the flattening never sees). -/
theorem flatten_demonic_directed_of_agree {r : N.Vanishing → ℕ}
    (hrk : N.CascadeRank r) (σ : N.RespScheduler)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).rate s s')
    (hinit : (flat.relabel e).init
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).init)
    (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ _α : Cell
        (looseConj (atoms (jumpRows (compileCtmc (flat.relabel e))) k) :
          Loose a a)
        (N.cispnDemonicC (absFuel r) k) (𝟙 a) (𝟙 a), True := by
  refine ⟨Crd.cellOfEntails fun μ hμ => ?_, trivial⟩
  rw [compile_jump_comm (flat.relabel e),
    satAtoms_iff (compile_wf (flat.relabel e).jumpChain) μ] at hμ
  have hμ' : μ = (flat.relabel e).jumpLaw k := hμ
  have hlaw : (flat.relabel e).jumpLaw k
      = N.tangiblePathLaw σ.1 r (N.respZenoFree hrk σ) k :=
    FinCTMC.jumpLaw_diag_blind _ _ hoff hinit k
  rw [hμ', hlaw]
  exact (N.cispnDemonicC_iff hrk k _).mpr ⟨σ, singletonC_self _⟩

/-- **The angelic directed face at colour**: the flatten-compiled
reading entails the radially maximal slice of the coloured demonic
credal set — the object the angelic verdict reads.  A directed cell,
sound direction only, packaged from the same membership fact as the
demonic directed face; the reverse entailment is not claimed (the
slice contains every adversary's law, most of which the flattening
never sees). -/
theorem flatten_angelic_directed_of_agree {r : N.Vanishing → ℕ}
    (hrk : N.CascadeRank r) (σ : N.RespScheduler)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).rate s s')
    (hinit : (flat.relabel e).init
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).init)
    (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ _α : Cell
        (looseConj (atoms (jumpRows (compileCtmc (flat.relabel e))) k) :
          Loose a a)
        (maxSlice (N.demonicTangibleCredal hrk k)) (𝟙 a) (𝟙 a), True := by
  refine ⟨Crd.cellOfEntails fun μ hμ => ?_, trivial⟩
  rw [compile_jump_comm (flat.relabel e),
    satAtoms_iff (compile_wf (flat.relabel e).jumpChain) μ] at hμ
  have hμ' : μ = (flat.relabel e).jumpLaw k := hμ
  have hlaw : (flat.relabel e).jumpLaw k
      = N.tangiblePathLaw σ.1 r (N.respZenoFree hrk σ) k :=
    FinCTMC.jumpLaw_diag_blind _ _ hoff hinit k
  rw [hμ', hlaw]
  exact (N.cispn_demonic_maxSlice hrk k _).mpr ⟨σ, singletonC_self _⟩

/-- **The angelic witness transfer at the coloured flattening**: under
the atom-transport agreement, a claim established on the transported
flat presentation's jump law transfers to the coloured net's angelic
reading — the flattened law is the exhibited resolution, token
selections included.  The sense-opposition to the demonic transfer
lives in the verdict flow (member → set), not in any reversed cell. -/
theorem flatten_angelic_of_agree {r : N.Vanishing → ℕ}
    (hrk : N.CascadeRank r) (σ : N.RespScheduler)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).rate s s')
    (hinit : (flat.relabel e).init
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).init)
    (k : ℕ) {c : SubPMF (Traj N.Tangible k) → Prop}
    (hc : c ((flat.relabel e).jumpLaw k)) :
    SatAngelic (N.demonicTangibleCredal hrk k) c := by
  have hlaw : (flat.relabel e).jumpLaw k
      = N.tangiblePathLaw σ.1 r (N.respZenoFree hrk σ) k :=
    FinCTMC.jumpLaw_diag_blind _ _ hoff hinit k
  exact N.cispn_angelic_of_member hrk σ k (hlaw ▸ hc)

/-- **The demonic restriction transfer at the coloured flattening**: a
claim certified universally against the coloured net's demonic credal
set holds of the transported flat presentation's jump law — the
flattened law is one adversary's, and the universal restricts to
it. -/
theorem flatten_demonic_verdict_of_agree {r : N.Vanishing → ℕ}
    (hrk : N.CascadeRank r) (σ : N.RespScheduler)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).rate s s')
    (hinit : (flat.relabel e).init
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).init)
    (k : ℕ) {c : SubPMF (Traj N.Tangible k) → Prop}
    (h : SatCredal .lower (N.demonicTangibleCredal hrk k) c) :
    c ((flat.relabel e).jumpLaw k) := by
  have hlaw : (flat.relabel e).jumpLaw k
      = N.tangiblePathLaw σ.1 r (N.respZenoFree hrk σ) k :=
    FinCTMC.jumpLaw_diag_blind _ _ hoff hinit k
  rw [hlaw]
  exact N.cispn_demonic_verdict_to_member hrk σ k h

/-! ## The composed directed faces: the community grain -/

/-- **The composed demonic directed face at colour**: the
flattened-execution community object entails the compiled coloured
demonic reading, read at the community grain through the flattened
object's own square.  A directed cell, sound direction only; the
coloured arena quantifies over adversaries — token selections
included — that the flattening never sees, so no envelope equality is
stated. -/
theorem flatten_composed_demonic_directed_of_agree
    {r : N.Vanishing → ℕ} (hrk : N.CascadeRank r) (σ : N.RespScheduler)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).rate s s')
    (hinit : (flat.relabel e).init
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).init)
    (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ _α : Cell
        (singletonC ((flat.relabel e).jumpLaw k) : Loose a a)
        (N.cispnDemonicC (absFuel r) k) (𝟙 a) (𝟙 a), True := by
  obtain ⟨-, β₃, -, -⟩ := ctmc_jump_adequacy (flat.relabel e) k (a := a)
  obtain ⟨αd, -⟩ :=
    N.flatten_demonic_directed_of_agree hrk σ e flat hoff hinit k (a := a)
  exact ⟨Crd.cellOfEntails fun μ h =>
    Crd.entailsOfCell αd μ (Crd.entailsOfCell β₃ μ h), trivial⟩

/-- **The composed angelic directed face at colour**: the
flattened-execution community object entails the radially maximal
slice the angelic verdict reads — a claim established on the flattened
execution law is an angelic witness for the coloured net, packaged at
the community grain.  The same membership fact as the demonic face,
opposite verdict sense; sound direction only. -/
theorem flatten_composed_angelic_directed_of_agree
    {r : N.Vanishing → ℕ} (hrk : N.CascadeRank r) (σ : N.RespScheduler)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).rate s s')
    (hinit : (flat.relabel e).init
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).init)
    (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ _α : Cell
        (singletonC ((flat.relabel e).jumpLaw k) : Loose a a)
        (maxSlice (N.demonicTangibleCredal hrk k)) (𝟙 a) (𝟙 a), True := by
  obtain ⟨-, β₃, -, -⟩ := ctmc_jump_adequacy (flat.relabel e) k (a := a)
  obtain ⟨αa, -⟩ :=
    N.flatten_angelic_directed_of_agree hrk σ e flat hoff hinit k (a := a)
  exact ⟨Crd.cellOfEntails fun μ h =>
    Crd.entailsOfCell αa μ (Crd.entailsOfCell β₃ μ h), trivial⟩

/-! ## The discharged tier: the constructed flattening

The composed directed faces at the coloured composed module's
constructed flattening — the carrier identification is the identity
enumeration, transport along it definitionally invisible, and the
agreement receipts are that module's own. -/

/-- **The composed demonic directed face, kernel-checked outright**:
the constructed coloured flattening's community object entails the
compiled coloured demonic reading — no agreement hypothesis. -/
theorem flatten_composed_demonic_directed {r : N.Vanishing → ℕ}
    (hrk : N.CascadeRank r) (σ : N.RespScheduler)
    (hti : N.TangibleInit) (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ _α : Cell
        (singletonC ((N.flattenChain σ.1 r hti).jumpLaw k) : Loose a a)
        (N.cispnDemonicC (absFuel r) k) (𝟙 a) (𝟙 a), True :=
  N.flatten_composed_demonic_directed_of_agree hrk σ (Equiv.refl _)
    (N.flattenChain σ.1 r hti)
    (N.flattenChain_agree_off σ.1 r (N.respZenoFree hrk σ) hti)
    (N.flattenChain_agree_init σ.1 r (N.respZenoFree hrk σ) hti) k

/-- **The composed angelic directed face, kernel-checked outright**:
the constructed coloured flattening's community object entails the
radially maximal slice the angelic verdict reads — no agreement
hypothesis. -/
theorem flatten_composed_angelic_directed {r : N.Vanishing → ℕ}
    (hrk : N.CascadeRank r) (σ : N.RespScheduler)
    (hti : N.TangibleInit) (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ _α : Cell
        (singletonC ((N.flattenChain σ.1 r hti).jumpLaw k) : Loose a a)
        (maxSlice (N.demonicTangibleCredal hrk k)) (𝟙 a) (𝟙 a), True :=
  N.flatten_composed_angelic_directed_of_agree hrk σ (Equiv.refl _)
    (N.flattenChain σ.1 r hti)
    (N.flattenChain_agree_off σ.1 r (N.respZenoFree hrk σ) hti)
    (N.flattenChain_agree_init σ.1 r (N.respZenoFree hrk σ) hti) k

/-! ## The premise-bundle entry points

The community's premise set, consumed whole; the enabling-respecting
hypothesis taken bare and packaged into the coloured demonic arena's
scheduler subtype at the call. -/

/-- The composed demonic directed face from the premise bundle. -/
theorem flatten_composed_demonic_directed_of_premises
    (prem : N.FlattenPremises) (σ : Policy N.Vanishing N.IAct)
    (hσ : N.RespectsEnabling σ) (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ _α : Cell
        (singletonC ((N.flattenChain σ prem.rank
          prem.init_tangible).jumpLaw k) : Loose a a)
        (N.cispnDemonicC (absFuel prem.rank) k) (𝟙 a) (𝟙 a), True :=
  N.flatten_composed_demonic_directed prem.cascade ⟨σ, hσ⟩
    prem.init_tangible k

/-- The composed angelic directed face from the premise bundle. -/
theorem flatten_composed_angelic_directed_of_premises
    (prem : N.FlattenPremises) (σ : Policy N.Vanishing N.IAct)
    (hσ : N.RespectsEnabling σ) (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ _α : Cell
        (singletonC ((N.flattenChain σ prem.rank
          prem.init_tangible).jumpLaw k) : Loose a a)
        (maxSlice (N.demonicTangibleCredal prem.cascade k)) (𝟙 a) (𝟙 a),
      True :=
  N.flatten_composed_angelic_directed prem.cascade ⟨σ, hσ⟩
    prem.init_tangible k

end FinCISPN

end Adequacy
end SuFunctor
