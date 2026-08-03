import Qtsl.Plate.Syntax

/-!
# Plates: T-PLATE — schematic well-formedness

**T-PLATE**: a well-formed plated hypernet instantiates to a
well-formed *ordinary* core hypernet at every extent assignment
σ : Plates → ℕ. Proof shape: instantiation
is a homomorphism on extents; every typing clause is a conjunction of
syntactic extent equalities and extent-free conditions; syntactic
equality is preserved by substitution; linearity/acyclicity are
verbatim (they never read extents).

The packaged form is `PlatedHypernet.inst : (Nat → Nat) →
PlatedHypernet → Hypernet` — a *total function into the core record*,
so "instances are ordinary hypernets; the evaluator and the checker are
untouched" is not a slogan but the type of the definition. The per-box
content is `SPrimApp.TypeConsistentS.inst`, generalizing a standalone
probe development's broadcast-corner lemma to all ten boxes.
-/

namespace PPLC
namespace Plate

/-- Instantiation of a symbolic wire typing. -/
def instW (σ : Nat → Nat) (swt : Wire → Option STensorType) :
    Wire → Option TensorType :=
  fun w => (swt w).map (STensorType.inst σ)

@[simp] theorem instW_eq_some {σ : Nat → Nat}
    {swt : Wire → Option STensorType} {w : Wire} {τ : STensorType}
    (h : swt w = some τ) : instW σ swt w = some (τ.inst σ) := by
  simp [instW, h]

/-- T-PLATE, per application (S6): each lifted typing clause
instantiates to the core clause at every σ. -/
theorem SPrimApp.TypeConsistentS.inst
    {swt : Wire → Option STensorType} {a : SPrimApp}
    (h : a.TypeConsistentS swt) (σ : Nat → Nat) :
    (a.inst σ).TypeConsistent (instW σ swt) := by
  cases a with
  | const ty c out =>
      simp only [SPrimApp.TypeConsistentS] at h
      simp only [SPrimApp.inst, PrimApp.TypeConsistent, instW, h,
        Option.map_some, STensorType.lift_inst]
  | contract δ r inputs output inputRanks outputRank pat =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      refine ⟨h1, ?_, ?_, ?_, ?_⟩
      · intro p hp
        obtain ⟨τ, hτ, hd, hr⟩ := h2 p hp
        exact ⟨τ.inst σ, instW_eq_some hτ, by simpa using hd,
          by simpa [Shape.rank] using hr⟩
      · obtain ⟨τ, hτ, hd, hr⟩ := h3
        exact ⟨τ.inst σ, instW_eq_some hτ, by simpa using hd,
          by simpa [Shape.rank] using hr⟩
      · intro i a
        obtain ⟨τ, hτ, hax⟩ := h4 i a
        refine ⟨τ.inst σ, instW_eq_some hτ, ?_⟩
        show (τ.shape.inst σ).getD a.val 0
          = (pat.indexExtent (pat.inputBinding i a)).inst σ
        rw [← hax]
        exact getD_map_comm (SExtent.inst σ) τ.shape a.val (.lit 0)
      · intro a
        obtain ⟨τ, hτ, hax⟩ := h5 a
        refine ⟨τ.inst σ, instW_eq_some hτ, ?_⟩
        show (τ.shape.inst σ).getD a.val 0
          = (pat.indexExtent (pat.outputBinding a)).inst σ
        rw [← hax]
        exact getD_map_comm (SExtent.inst σ) τ.shape a.val (.lit 0)
  | cast δf δt r shape i o =>
      obtain ⟨hin, hout⟩ := h
      exact ⟨instW_eq_some hin, instW_eq_some hout⟩
  | cell schema i outs =>
      obtain ⟨⟨δ, hin⟩, hlen, houts⟩ := h
      refine ⟨⟨δ, ?_⟩, hlen, ?_⟩
      · simpa [STensorType.inst] using instW_eq_some hin
      · intro o ho
        simpa [STensorType.inst] using instW_eq_some (houts o ho)
  | reshape ns i o =>
      obtain ⟨s, δ, hin, hsz, hout⟩ := h
      refine ⟨⟨s, δ⟩, ?_, by simpa using hsz, ?_⟩
      · simpa [STensorType.inst] using instW_eq_some hin
      · simpa [STensorType.inst] using instW_eq_some hout
  | broadcast ts i o =>
      obtain ⟨τ, hin, hbc, hout⟩ := h
      exact ⟨τ.inst σ, instW_eq_some hin,
        SShape.broadcastsToS_inst σ hbc,
        by simpa [STensorType.inst] using instW_eq_some hout⟩
  | copy k i outs =>
      obtain ⟨hlen, τ, hin, houts⟩ := h
      exact ⟨hlen, τ.inst σ, instW_eq_some hin,
        fun o ho => instW_eq_some (houts o ho)⟩
  | delete i =>
      simp only [SPrimApp.TypeConsistentS] at h
      simpa [SPrimApp.inst, PrimApp.TypeConsistent, instW] using h
  | swap a b c d =>
      obtain ⟨h1, h2, h3, h4⟩ := h
      refine ⟨by simpa [instW] using h1, by simpa [instW] using h2,
        ?_, ?_⟩
      · simp only [instW, h3]
      · simp only [instW, h4]
  | stack k shape ins o =>
      obtain ⟨hlen, τ, hout, hsh, hins⟩ := h
      refine ⟨hlen, τ.inst σ, instW_eq_some hout, ?_, ?_⟩
      · simp [STensorType.inst, hsh]
      · intro w hw
        simpa [STensorType.inst] using instW_eq_some (hins w hw)

/-- flatMap through a map, given a pointwise description. -/
private theorem flatMap_map_eq {α β γ : Type} (f : α → β)
    (g : β → List γ) (g' : α → List γ)
    (hgg : ∀ a, g (f a) = g' a) (l : List α) :
    (l.map f).flatMap g = l.flatMap g' := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [hgg, ih]

/-- S5: linearity transports along instantiation. -/
theorem linearity_inst (σ : Nat → Nat) {apps : List SPrimApp}
    (h : LinearityS apps) :
    Linearity (apps.map (SPrimApp.inst σ)) := by
  obtain ⟨hin, hout⟩ := h
  constructor
  · rw [flatMap_map_eq (SPrimApp.inst σ) PrimApp.inputWires
      SPrimApp.inputWiresS (fun a => SPrimApp.inst_inputWires σ a)]
    exact hin
  · rw [flatMap_map_eq (SPrimApp.inst σ) PrimApp.outputWires
      SPrimApp.outputWiresS (fun a => SPrimApp.inst_outputWires σ a)]
    exact hout

/-- S5: acyclicity transports along instantiation. -/
theorem acyclic_inst (σ : Nat → Nat) {apps : List SPrimApp}
    (h : AcyclicS apps) :
    Acyclic (apps.map (SPrimApp.inst σ)) := by
  intro i w hw j hj
  have hil : i.val < apps.length := by simpa using i.isLt
  have hjl : j.val < apps.length := by simpa using j.isLt
  have hgi : (apps.map (SPrimApp.inst σ))[i] = (apps[i.val]'hil).inst σ := by
    simp
  have hgj : (apps.map (SPrimApp.inst σ))[j] = (apps[j.val]'hjl).inst σ := by
    simp
  rw [hgi, SPrimApp.inst_inputWires] at hw
  rw [hgj, SPrimApp.inst_outputWires] at hj
  exact h ⟨i.val, hil⟩ w hw ⟨j.val, hjl⟩ hj

/-- **T-PLATE, packaged (S7)**: instantiation of a well-formed plated
hypernet is a well-formed ordinary core hypernet, at every σ — as a
total function into the core record. Everything downstream (evaluator,
canonical serialization of instances, the certified checker stack)
consumes instances and only instances. -/
def PlatedHypernet.inst (σ : Nat → Nat) (P : PlatedHypernet) : Hypernet where
  wireType       := instW σ P.wireTypeS
  applications   := P.applications.map (SPrimApp.inst σ)
  linearity      := linearity_inst σ P.linearity
  acyclic        := acyclic_inst σ P.acyclic
  typeConsistent := by
    intro app happ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp happ
    exact (P.typeConsistent a ha).inst σ

@[simp] theorem PlatedHypernet.inst_wireType (σ : Nat → Nat)
    (P : PlatedHypernet) :
    (P.inst σ).wireType = instW σ P.wireTypeS := rfl

@[simp] theorem PlatedHypernet.inst_applications (σ : Nat → Nat)
    (P : PlatedHypernet) :
    (P.inst σ).applications = P.applications.map (SPrimApp.inst σ) := rfl

end Plate
end PPLC
