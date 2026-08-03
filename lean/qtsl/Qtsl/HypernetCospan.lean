import Qtsl.Catalogue
import Qtsl.Substitution

/-!
# Open hypernets: the decorated-cospan composition layer, aligned stratum

A hypernet with a declared interface is a decorated cospan: the
decoration is the wiring diagram (the application list over the wire
context), and the cospan legs label the input and output wires. This
module mechanizes the loose-composition core of that reading at the
**aligned stratum** — the pushout-normal form in which the seam wires
of two composable open hypernets are literally shared names and the
off-seam wires are disjoint, which is the form every chosen-pushout
composite reduces to.

Contents:

* `OpenHypernet` — the core `Hypernet` (`Qtsl.Core.Catalogue`) plus an
  interface, with the well-formedness boundary clauses of the
  monogamous genre: inputs unproduced, consumed-unproduced wires
  covered by the inputs, outputs unconsumed (exposure is the
  consumption), outputs grounded (produced or passed through).
* `PrimApp.TypeConsistent.mono` — typing transports along wire-type
  extensions (the merge-compatibility engine).
* `OpenHypernet.glue` — loose composition at the aligned stratum, with
  the composite's linearity, acyclicity, type-consistency, and all
  boundary clauses **proved**: the wf-closure theorem. No seam repairs
  appear; under the boundary clauses the seam has capacity exactly one
  on each side.
* `glue_admissible_iff` — a valuation of the composite is admissible
  iff every application of each part holds: the relational composition
  law at the aligned stratum, with no determinism hypothesis (`cell`
  passes through the conjunction untouched).
* `unitOpen`, `glue_unit_left`, `glue_unit_right`, `glue_assoc` — the
  loose unit and the on-the-nose unit/associativity laws of the
  aligned stratum (the Lean shadow of the substitution laws' clause
  (iii) in pushout-normal form).

The general (non-aligned) cospan composition, the rename transport of
`SemOk`, and the double-categorical packaging through `DoubleCat` are
deliberate successors to this module.
-/

namespace PPLC

/-! ## Wire-type merges and typing transport -/

/-- Left-biased merge of two wire typings. -/
def mergeWt (f g : Wire → Option TensorType) : Wire → Option TensorType :=
  fun w =>
    match f w with
    | some τ => some τ
    | none => g w

theorem mergeWt_left {f g : Wire → Option TensorType} {w : Wire}
    {τ : TensorType} (h : f w = some τ) : mergeWt f g w = some τ := by
  simp [mergeWt, h]

theorem mergeWt_right {f g : Wire → Option TensorType}
    (hcompat : ∀ w τ τ', f w = some τ → g w = some τ' → τ = τ')
    {w : Wire} {τ : TensorType} (h : g w = some τ) :
    mergeWt f g w = some τ := by
  unfold mergeWt
  cases hf : f w with
  | none => simpa using h
  | some τ' => rw [hcompat w τ' τ hf h]

/-- Two hypernets with the same data are equal (the well-formedness
fields are propositions). -/
theorem Hypernet.ext' {H₁ H₂ : Hypernet}
    (hw : H₁.wireType = H₂.wireType)
    (ha : H₁.applications = H₂.applications) : H₁ = H₂ := by
  obtain ⟨w₁, a₁, l₁, c₁, t₁⟩ := H₁
  obtain ⟨w₂, a₂, l₂, c₂, t₂⟩ := H₂
  subst hw
  subst ha
  rfl

/-- Typing is monotone under extension of the wire typing: every clause
of `TypeConsistent` constrains `wt` only positively (`wt x = some τ`
under conjunction, existentials, and bounded universals), so enlarging
the domain of definition preserves it.  The one clause equating `wt` at
two wires (`swap`) is guarded by `isSome` on both sides. -/
theorem PrimApp.TypeConsistent.mono
    {wt wt' : Wire → Option TensorType}
    (hext : ∀ w τ, wt w = some τ → wt' w = some τ)
    {a : PrimApp} (h : a.TypeConsistent wt) : a.TypeConsistent wt' := by
  cases a with
  | const ty c out => exact hext _ _ h
  | contract δ r ins out ir orr pat =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨h1, ?_, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨τ, hτ, hδ, hrk⟩ := h2 p hp
      exact ⟨τ, hext _ _ hτ, hδ, hrk⟩
    · obtain ⟨τ, hτ, hδ, hr⟩ := h3
      exact ⟨τ, hext _ _ hτ, hδ, hr⟩
    · intro i aIdx
      obtain ⟨τ, hτ, he⟩ := h4 i aIdx
      exact ⟨τ, hext _ _ hτ, he⟩
    · intro aIdx
      obtain ⟨τ, hτ, he⟩ := h5 aIdx
      exact ⟨τ, hext _ _ hτ, he⟩
  | cast δf δt r s i o =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨hext _ _ h1, hext _ _ h2⟩
  | cell schema i outs =>
    obtain ⟨⟨δ, hδ⟩, hlen, houts⟩ := h
    exact ⟨⟨δ, hext _ _ hδ⟩, hlen, fun o ho => hext _ _ (houts o ho)⟩
  | reshape s i o =>
    obtain ⟨τ, h1, h2, h3⟩ := h
    exact ⟨τ, hext _ _ h1, h2, hext _ _ h3⟩
  | broadcast s i o =>
    obtain ⟨τ, h1, h2, h3⟩ := h
    exact ⟨τ, hext _ _ h1, h2, hext _ _ h3⟩
  | copy k i outs =>
    obtain ⟨hlen, τ, hτ, houts⟩ := h
    exact ⟨hlen, τ, hext _ _ hτ, fun o ho => hext _ _ (houts o ho)⟩
  | delete i =>
    obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp h
    exact Option.isSome_iff_exists.mpr ⟨τ, hext _ _ hτ⟩
  | swap i1 i2 o1 o2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨τ1, hτ1⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨τ2, hτ2⟩ := Option.isSome_iff_exists.mp h2
    refine ⟨Option.isSome_iff_exists.mpr ⟨τ1, hext _ _ hτ1⟩,
            Option.isSome_iff_exists.mpr ⟨τ2, hext _ _ hτ2⟩, ?_, ?_⟩
    · rw [hext _ _ (h3.trans hτ2), hext _ _ hτ2]
    · rw [hext _ _ (h4.trans hτ1), hext _ _ hτ1]
  | stack k s ins o =>
    obtain ⟨hlen, τ, hτ, hsh, hins⟩ := h
    exact ⟨hlen, τ, hext _ _ hτ, hsh, fun w hw => hext _ _ (hins w hw)⟩
  | relu s i o =>
    obtain ⟨τ, h1, h2, h3⟩ := h
    exact ⟨τ, hext _ _ h1, hext _ _ h2, h3⟩
  | ppoly n q ins o =>
    obtain ⟨hlen, hins, ho⟩ := h
    exact ⟨hlen, fun w hw => hext _ _ (hins w hw), hext _ _ ho⟩
  | pderiv s ax i o =>
    obtain ⟨τ, h1, h2, h3⟩ := h
    exact ⟨τ, hext _ _ h1, hext _ _ h2, h3⟩
  | facet s ax hi i o =>
    obtain ⟨τ, h1, h2, h3⟩ := h
    exact ⟨τ, hext _ _ h1, h2, hext _ _ h3⟩

/-! ## Concatenation lemmas for the application-list combinatorics -/

theorem consumedW_append (l₁ l₂ : List PrimApp) :
    consumedW (l₁ ++ l₂) = consumedW l₁ ++ consumedW l₂ :=
  List.flatMap_append ..

theorem producedW_append (l₁ l₂ : List PrimApp) :
    producedW (l₁ ++ l₂) = producedW l₁ ++ producedW l₂ :=
  List.flatMap_append ..

theorem mem_consumedW {apps : List PrimApp} {w : Wire} :
    w ∈ consumedW apps ↔ ∃ a ∈ apps, w ∈ a.inputWires :=
  List.mem_flatMap

theorem mem_producedW {apps : List PrimApp} {w : Wire} :
    w ∈ producedW apps ↔ ∃ a ∈ apps, w ∈ a.outputWires :=
  List.mem_flatMap

/-- Concatenating two acyclic application lists is acyclic provided no
wire consumed in the first block is produced in the second — the seam
flows one way. -/
theorem Acyclic.append {l₁ l₂ : List PrimApp}
    (h₁ : Acyclic l₁) (h₂ : Acyclic l₂)
    (hcross : ∀ w, w ∈ consumedW l₁ → w ∈ producedW l₂ → False) :
    Acyclic (l₁ ++ l₂) := by
  intro i w hw j hj
  show j.val < i.val
  have hw' : w ∈ ((l₁ ++ l₂)[i.val]'i.isLt).inputWires := hw
  have hj' : w ∈ ((l₁ ++ l₂)[j.val]'j.isLt).outputWires := hj
  clear hw hj
  rcases Nat.lt_or_ge i.val l₁.length with hi | hi
  · -- the consumer sits in the first block
    rw [List.getElem_append_left hi] at hw'
    rcases Nat.lt_or_ge j.val l₁.length with hjl | hjl
    · rw [List.getElem_append_left hjl] at hj'
      exact h₁ ⟨i.val, hi⟩ w hw' ⟨j.val, hjl⟩ hj'
    · -- the producer would sit in the second block: contradicts the seam
      exfalso
      have hjlt : j.val - l₁.length < l₂.length := by
        have h1 := j.isLt
        have h2 : (l₁ ++ l₂).length = l₁.length + l₂.length := by simp
        omega
      rw [List.getElem_append_right hjl] at hj'
      exact hcross w
        (mem_consumedW.mpr ⟨_, List.getElem_mem hi, hw'⟩)
        (mem_producedW.mpr ⟨_, List.getElem_mem hjlt, hj'⟩)
  · rcases Nat.lt_or_ge j.val l₁.length with hjl | hjl
    · -- producer in the first block, consumer in the second: earlier
      omega
    · -- both in the second block
      have hilt : i.val - l₁.length < l₂.length := by
        have h1 := i.isLt
        have h2 : (l₁ ++ l₂).length = l₁.length + l₂.length := by simp
        omega
      have hjlt : j.val - l₁.length < l₂.length := by
        have h1 := j.isLt
        have h2 : (l₁ ++ l₂).length = l₁.length + l₂.length := by simp
        omega
      rw [List.getElem_append_right hi] at hw'
      rw [List.getElem_append_right hjl] at hj'
      have hlt : (⟨j.val - l₁.length, hjlt⟩ : Fin l₂.length)
          < (⟨i.val - l₁.length, hilt⟩ : Fin l₂.length) :=
        h₂ ⟨i.val - l₁.length, hilt⟩ w hw' ⟨j.val - l₁.length, hjlt⟩ hj'
      have : j.val - l₁.length < i.val - l₁.length := hlt
      omega

/-! ## Open hypernets -/

/-- A hypernet with a declared interface: the decoration side of a
decorated cospan, at the aligned stratum.  The boundary clauses are the
monogamous genre's well-formedness: inputs are produced by no
application; every consumed-but-unproduced wire is an input; outputs
are consumed by no application (exposure is the consumption — the
strict reading of the interface discipline, matching the reference
implementation's seam-capacity refusal); outputs are produced or pass
through from the inputs. -/
structure OpenHypernet where
  net : Hypernet
  inputs : List Wire
  outputs : List Wire
  inputs_nodup : inputs.Nodup
  outputs_nodup : outputs.Nodup
  inputs_unproduced : ∀ w ∈ inputs, w ∉ producedW net.applications
  consumed_covered : ∀ w ∈ consumedW net.applications,
    w ∉ producedW net.applications → w ∈ inputs
  outputs_unconsumed : ∀ w ∈ outputs, w ∉ consumedW net.applications
  outputs_grounded : ∀ w ∈ outputs,
    w ∈ producedW net.applications ∨ w ∈ inputs

namespace OpenHypernet

/-- Two open hypernets with the same data are equal. -/
theorem ext' {H₁ H₂ : OpenHypernet}
    (hn : H₁.net = H₂.net) (hi : H₁.inputs = H₂.inputs)
    (ho : H₁.outputs = H₂.outputs) : H₁ = H₂ := by
  obtain ⟨n₁, i₁, o₁, _, _, _, _, _, _⟩ := H₁
  obtain ⟨n₂, i₂, o₂, _, _, _, _, _, _⟩ := H₂
  subst hn
  subst hi
  subst ho
  rfl

/-- Every wire an open hypernet touches: application ports and the
interface. -/
def wires (H : OpenHypernet) : List Wire :=
  consumedW H.net.applications ++ producedW H.net.applications ++
    H.inputs ++ H.outputs

theorem mem_wires_of_consumed {H : OpenHypernet} {w : Wire}
    (h : w ∈ consumedW H.net.applications) : w ∈ H.wires := by
  unfold wires
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ h))

theorem mem_wires_of_produced {H : OpenHypernet} {w : Wire}
    (h : w ∈ producedW H.net.applications) : w ∈ H.wires := by
  unfold wires
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ h))

theorem mem_wires_of_input {H : OpenHypernet} {w : Wire}
    (h : w ∈ H.inputs) : w ∈ H.wires := by
  unfold wires
  exact List.mem_append_left _ (List.mem_append_right _ h)

theorem mem_wires_of_output {H : OpenHypernet} {w : Wire}
    (h : w ∈ H.outputs) : w ∈ H.wires := by
  unfold wires
  exact List.mem_append_right _ h

/-! ## Gluing: loose composition at the aligned stratum -/

/-- The aligned-composition hypotheses: the seam is literal name
sharing (`G.inputs = H.outputs`), the two typings agree wherever both
are defined, and the two nets share wires only on the seam. -/
structure Aligned (H G : OpenHypernet) : Prop where
  seam : G.inputs = H.outputs
  compat : ∀ w τ τ', H.net.wireType w = some τ →
    G.net.wireType w = some τ' → τ = τ'
  disj : ∀ w, w ∈ H.wires → w ∈ G.wires → w ∈ H.outputs

section Glue

variable {H G : OpenHypernet}

/-- Wires consumed on both sides would have to sit on the seam, where
`H` exposes them unconsumed. -/
theorem consumed_disjoint (hA : Aligned H G) :
    ∀ w ∈ consumedW H.net.applications,
      w ∈ consumedW G.net.applications → False := by
  intro w hwH hwG
  have hseam : w ∈ H.outputs :=
    hA.disj w (mem_wires_of_consumed hwH) (mem_wires_of_consumed hwG)
  exact H.outputs_unconsumed w hseam hwH

/-- Wires produced on both sides would have to sit on the seam, where
`G` declares them unproduced inputs. -/
theorem produced_disjoint (hA : Aligned H G) :
    ∀ w ∈ producedW H.net.applications,
      w ∈ producedW G.net.applications → False := by
  intro w hwH hwG
  have hseam : w ∈ H.outputs :=
    hA.disj w (mem_wires_of_produced hwH) (mem_wires_of_produced hwG)
  have hin : w ∈ G.inputs := by rw [hA.seam]; exact hseam
  exact G.inputs_unproduced w hin hwG

/-- No wire consumed by `H` is produced by `G`: the seam flows from `H`
to `G`. -/
theorem cross_flow (hA : Aligned H G) :
    ∀ w, w ∈ consumedW H.net.applications →
      w ∈ producedW G.net.applications → False := by
  intro w hwH hwG
  have hseam : w ∈ H.outputs :=
    hA.disj w (mem_wires_of_consumed hwH) (mem_wires_of_produced hwG)
  exact H.outputs_unconsumed w hseam hwH

variable (hA : Aligned H G)

/-- The merged hypernet of an aligned pair: merged typing, concatenated
applications, with linearity, acyclicity, and type-consistency proved —
the core of the wf-closure theorem. -/
def glueNet : Hypernet where
  wireType := mergeWt H.net.wireType G.net.wireType
  applications := H.net.applications ++ G.net.applications
  linearity := by
    constructor
    · show ((H.net.applications ++ G.net.applications).flatMap
        PrimApp.inputWires).Nodup
      have h : (H.net.applications ++ G.net.applications).flatMap
          PrimApp.inputWires
          = consumedW H.net.applications ++ consumedW G.net.applications :=
        consumedW_append ..
      rw [h]
      exact List.nodup_append.mpr
        ⟨H.net.linearity.1, G.net.linearity.1,
         fun a ha b hb heq => consumed_disjoint hA a ha (heq ▸ hb)⟩
    · show ((H.net.applications ++ G.net.applications).flatMap
        PrimApp.outputWires).Nodup
      have h : (H.net.applications ++ G.net.applications).flatMap
          PrimApp.outputWires
          = producedW H.net.applications ++ producedW G.net.applications :=
        producedW_append ..
      rw [h]
      exact List.nodup_append.mpr
        ⟨H.net.linearity.2, G.net.linearity.2,
         fun a ha b hb heq => produced_disjoint hA a ha (heq ▸ hb)⟩
  acyclic := Acyclic.append H.net.acyclic G.net.acyclic (cross_flow hA)
  typeConsistent := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact PrimApp.TypeConsistent.mono
        (fun w τ hw => mergeWt_left hw) (H.net.typeConsistent a h)
    · exact PrimApp.TypeConsistent.mono
        (fun w τ hw => mergeWt_right hA.compat hw)
        (G.net.typeConsistent a h)

@[simp] theorem glueNet_applications :
    (glueNet hA).applications
      = H.net.applications ++ G.net.applications := rfl

@[simp] theorem glueNet_wireType :
    (glueNet hA).wireType = mergeWt H.net.wireType G.net.wireType := rfl

/-- **The wf-closure theorem, aligned stratum.**  Gluing two
well-formed open hypernets along their shared seam yields a well-formed
open hypernet: every boundary clause of the monogamous genre is
re-established.  No seam repair is inserted — under the boundary
clauses the seam has capacity exactly one on each side. -/
def glue : OpenHypernet where
  net := glueNet hA
  inputs := H.inputs
  outputs := G.outputs
  inputs_nodup := H.inputs_nodup
  outputs_nodup := G.outputs_nodup
  inputs_unproduced := by
    intro w hw
    show w ∉ producedW (H.net.applications ++ G.net.applications)
    rw [producedW_append]
    intro hmem
    rcases List.mem_append.mp hmem with h | h
    · exact H.inputs_unproduced w hw h
    · have hseam : w ∈ H.outputs :=
        hA.disj w (mem_wires_of_input hw) (mem_wires_of_produced h)
      have hin : w ∈ G.inputs := by rw [hA.seam]; exact hseam
      exact G.inputs_unproduced w hin h
  consumed_covered := by
    intro w hw hnp
    replace hw : w ∈ consumedW (H.net.applications ++ G.net.applications) :=
      hw
    replace hnp : w ∉ producedW (H.net.applications ++ G.net.applications) :=
      hnp
    rw [consumedW_append] at hw
    rw [producedW_append] at hnp
    have hnpH : w ∉ producedW H.net.applications :=
      fun h => hnp (List.mem_append_left _ h)
    have hnpG : w ∉ producedW G.net.applications :=
      fun h => hnp (List.mem_append_right _ h)
    rcases List.mem_append.mp hw with h | h
    · exact H.consumed_covered w h hnpH
    · have hin : w ∈ G.inputs := G.consumed_covered w h hnpG
      have hout : w ∈ H.outputs := by rw [hA.seam] at hin; exact hin
      rcases H.outputs_grounded w hout with hp | hi
      · exact absurd hp hnpH
      · exact hi
  outputs_unconsumed := by
    intro w hw
    show w ∉ consumedW (H.net.applications ++ G.net.applications)
    rw [consumedW_append]
    intro hmem
    rcases List.mem_append.mp hmem with h | h
    · have hseam : w ∈ H.outputs :=
        hA.disj w (mem_wires_of_consumed h) (mem_wires_of_output hw)
      exact H.outputs_unconsumed w hseam h
    · exact G.outputs_unconsumed w hw h
  outputs_grounded := by
    intro w hw
    show w ∈ producedW (H.net.applications ++ G.net.applications)
      ∨ w ∈ H.inputs
    rw [producedW_append]
    rcases G.outputs_grounded w hw with hp | hi
    · exact Or.inl (List.mem_append_right _ hp)
    · have hout : w ∈ H.outputs := by rw [hA.seam] at hi; exact hi
      rcases H.outputs_grounded w hout with hp' | hi'
      · exact Or.inl (List.mem_append_left _ hp')
      · exact Or.inr hi'

@[simp] theorem glue_net : (glue hA).net = glueNet hA := rfl
@[simp] theorem glue_inputs : (glue hA).inputs = H.inputs := rfl
@[simp] theorem glue_outputs : (glue hA).outputs = G.outputs := rfl

/-! ## The relational composition law, aligned stratum -/

/-- A valuation of the glued net is admissible iff every application of
each part holds under it.  No determinism hypothesis: `cell`'s one-hot
disjunction passes through the conjunction untouched.  This is the
semantic engine of the decorated-cospan inclusion's `β = 1` coherence
(the possibilistic penalty of the composite is the sum of the parts'
pushforwards). -/
theorem glue_admissible_iff (σ : (glueNet hA).Valuation) :
    σ.Admissible ↔
      (∀ a ∈ H.net.applications, a.SemOk σ) ∧
      (∀ a ∈ G.net.applications, a.SemOk σ) := by
  unfold Hypernet.Valuation.Admissible
  rw [glueNet_applications]
  constructor
  · intro h
    exact ⟨fun a ha => h a (List.mem_append_left _ ha),
           fun a ha => h a (List.mem_append_right _ ha)⟩
  · rintro ⟨h₁, h₂⟩ a ha
    rcases List.mem_append.mp ha with h | h
    · exact h₁ a h
    · exact h₂ a h

end Glue

/-! ## Units and associativity, on the nose -/

/-- The loose identity at a wire context: no applications, the context
passed straight through. -/
def unitOpen (X : List Wire) (wt₀ : Wire → Option TensorType)
    (hX : X.Nodup) : OpenHypernet where
  net :=
    { wireType := wt₀
      applications := []
      linearity := ⟨List.nodup_nil, List.nodup_nil⟩
      acyclic := fun i => i.elim0
      typeConsistent := fun _ ha => nomatch ha }
  inputs := X
  outputs := X
  inputs_nodup := hX
  outputs_nodup := hX
  inputs_unproduced := fun _ _ h => nomatch h
  consumed_covered := fun _ hw _ => nomatch hw
  outputs_unconsumed := fun _ _ h => nomatch h
  outputs_grounded := fun _ hw => Or.inr hw

/-- The aligned hypotheses for a canonical left-unit gluing hold
whenever the unit's typing is a restriction of `H`'s. -/
theorem aligned_unit_left (H : OpenHypernet)
    (wt₀ : Wire → Option TensorType)
    (hsub : ∀ w τ, wt₀ w = some τ → H.net.wireType w = some τ) :
    Aligned (unitOpen H.inputs wt₀ H.inputs_nodup) H := by
  refine ⟨rfl, ?_, ?_⟩
  · intro w τ τ' h h'
    have hH := hsub w τ h
    rw [hH] at h'
    exact Option.some.inj h'
  · intro w hw _
    show w ∈ H.inputs
    have : w ∈ H.inputs ∨ w ∈ H.inputs := by
      simpa [wires, unitOpen, consumedW, producedW] using hw
    exact this.elim id id

/-- The aligned hypotheses for a canonical right-unit gluing. -/
theorem aligned_unit_right (H : OpenHypernet)
    (wt₀ : Wire → Option TensorType)
    (hsub : ∀ w τ, wt₀ w = some τ → H.net.wireType w = some τ) :
    Aligned H (unitOpen H.outputs wt₀ H.outputs_nodup) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro w τ τ' h h'
    have hH := hsub w τ' h'
    rw [hH] at h
    exact (Option.some.inj h).symm
  · intro w _ hw
    show w ∈ H.outputs
    have : w ∈ H.outputs ∨ w ∈ H.outputs := by
      simpa [wires, unitOpen, consumedW, producedW] using hw
    exact this.elim id id

/-- Left unit law, on the nose: gluing the unit (as inner part) onto
`H` returns `H` — data equal, proofs irrelevant. -/
theorem glue_unit_left (H : OpenHypernet)
    (wt₀ : Wire → Option TensorType)
    (hsub : ∀ w τ, wt₀ w = some τ → H.net.wireType w = some τ)
    (hA : Aligned (unitOpen H.inputs wt₀ H.inputs_nodup) H) :
    glue hA = H := by
  refine ext' ?_ rfl rfl
  refine Hypernet.ext' ?_ rfl
  funext w
  show mergeWt wt₀ H.net.wireType w = H.net.wireType w
  unfold mergeWt
  cases h : wt₀ w with
  | none => rfl
  | some τ => exact (hsub w τ h).symm

/-- Right unit law, on the nose. -/
theorem glue_unit_right (H : OpenHypernet)
    (wt₀ : Wire → Option TensorType)
    (hsub : ∀ w τ, wt₀ w = some τ → H.net.wireType w = some τ)
    (hA : Aligned H (unitOpen H.outputs wt₀ H.outputs_nodup)) :
    glue hA = H := by
  refine ext' ?_ rfl rfl
  refine Hypernet.ext' ?_ (List.append_nil _)
  funext w
  show mergeWt H.net.wireType wt₀ w = H.net.wireType w
  unfold mergeWt
  cases h : H.net.wireType w with
  | some τ => rfl
  | none =>
    cases h₀ : wt₀ w with
    | none => rfl
    | some τ =>
      exfalso
      have := hsub w τ h₀
      rw [h] at this
      exact nomatch this

/-- Associativity of gluing, on the nose: both associations produce the
same open hypernet (list-append associativity + merge associativity +
proof irrelevance).  The aligned hypotheses of the two nestings are
supplied as arguments; deriving them from pairwise data is the general
(non-aligned) successor's bookkeeping. -/
theorem glue_assoc {H G K : OpenHypernet}
    (hHG : Aligned H G) (hGK : Aligned G K)
    (hL : Aligned (glue hHG) K) (hR : Aligned H (glue hGK)) :
    glue hL = glue hR := by
  refine ext' ?_ rfl rfl
  refine Hypernet.ext' ?_ ?_
  · funext w
    show mergeWt (mergeWt H.net.wireType G.net.wireType) K.net.wireType w
       = mergeWt H.net.wireType (mergeWt G.net.wireType K.net.wireType) w
    unfold mergeWt
    cases hH : H.net.wireType w with
    | some τ => rfl
    | none =>
      cases hG : G.net.wireType w with
      | some τ => rfl
      | none => rfl
  · show (H.net.applications ++ G.net.applications) ++ K.net.applications
       = H.net.applications ++ (G.net.applications ++ K.net.applications)
    exact List.append_assoc ..

end OpenHypernet

end PPLC
