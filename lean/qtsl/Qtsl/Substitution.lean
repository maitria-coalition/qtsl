import Qtsl.Core.Catalogue
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

/-!
# Graph substitution over the presentation IR

The substitution calculus at the presentation stratum: `HypernetP` — a
hypernet presentation with a wire-type table, application list, and
graph inputs/outputs — with renumbering and substitution, and the
theorem ledger relating substitution to well-typedness and semantics.
The core `Hypernet` deliberately carries no interface; this module
introduces the presentation the substitution calculus needs.
-/

namespace PPLC

def PrimApp.remapWires (ρ : Wire → Wire) : PrimApp → PrimApp
  | .const ty c out => .const ty c (ρ out)
  | .contract δ r ins out ir orr pat =>
      .contract δ r (ins.map ρ) (ρ out) ir orr pat
  | .cast δf δt r s i o => .cast δf δt r s (ρ i) (ρ o)
  | .cell schema i outs => .cell schema (ρ i) (outs.map ρ)
  | .reshape s i o => .reshape s (ρ i) (ρ o)
  | .broadcast s i o => .broadcast s (ρ i) (ρ o)
  | .copy k i outs => .copy k (ρ i) (outs.map ρ)
  | .delete i => .delete (ρ i)
  | .swap i1 i2 o1 o2 => .swap (ρ i1) (ρ i2) (ρ o1) (ρ o2)
  | .stack k s ins o => .stack k s (ins.map ρ) (ρ o)
  | .relu s i o => .relu s (ρ i) (ρ o)
  | .ppoly n q ins o => .ppoly n q (ins.map ρ) (ρ o)
  | .pderiv s ax i o => .pderiv s ax (ρ i) (ρ o)
  | .facet s ax hi i o => .facet s ax hi (ρ i) (ρ o)

@[simp] theorem PrimApp.inputWires_remapWires (ρ : Wire → Wire) (a : PrimApp) :
    (a.remapWires ρ).inputWires = a.inputWires.map ρ := by
  cases a <;> simp [remapWires, inputWires]

@[simp] theorem PrimApp.outputWires_remapWires (ρ : Wire → Wire) (a : PrimApp) :
    (a.remapWires ρ).outputWires = a.outputWires.map ρ := by
  cases a <;> simp [remapWires, outputWires]

theorem PrimApp.remapWires_remapWires (ρ σ : Wire → Wire) (a : PrimApp) :
    (a.remapWires ρ).remapWires σ = a.remapWires (σ ∘ ρ) := by
  cases a <;> simp [remapWires]

@[simp] theorem PrimApp.remapWires_id (a : PrimApp) :
    a.remapWires id = a := by
  cases a <;> simp [remapWires]

theorem PrimApp.remapWires_congr {ρ σ : Wire → Wire} (a : PrimApp)
    (hin : ∀ w ∈ a.inputWires, ρ w = σ w)
    (hout : ∀ w ∈ a.outputWires, ρ w = σ w) :
    a.remapWires ρ = a.remapWires σ := by
  cases a <;>
    simp only [remapWires, inputWires, outputWires, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq] at hin hout ⊢
  case const ty c out => rw [hout]
  case contract δ r ins out ir orr pat =>
    rw [List.map_congr_left hin, hout]
  case cast δf δt r s i o => rw [hin, hout]
  case cell schema i outs => rw [hin, List.map_congr_left hout]
  case reshape s i o => rw [hin, hout]
  case broadcast s i o => rw [hin, hout]
  case copy k i outs => rw [hin, List.map_congr_left hout]
  case delete i => rw [hin]
  case swap i1 i2 o1 o2 =>
    rw [hin i1 (Or.inl rfl), hin i2 (Or.inr rfl),
        hout o1 (Or.inl rfl), hout o2 (Or.inr rfl)]
  case stack k s ins o => rw [List.map_congr_left hin, hout]
  case relu s i o => rw [hin, hout]
  case ppoly n q ins o => rw [List.map_congr_left hin, hout]
  case pderiv s ax i o => rw [hin, hout]
  case facet s ax hi i o => rw [hin, hout]

theorem getD_map_lt {l : List Wire} {ρ : Wire → Wire} {i : Nat}
    (h : i < l.length) (d : Wire) :
    (l.map ρ).getD i d = ρ (l.getD i d) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem h]

theorem getD_mem_lt {l : List Wire} {i : Nat} (h : i < l.length) (d : Wire) :
    l.getD i d ∈ l := by
  have : l.getD i d = l[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rw [this]
  exact List.getElem_mem h

theorem PrimApp.TypeConsistent.remapWires
    {wt wt' : Wire → Option TensorType} {ρ : Wire → Wire} {a : PrimApp}
    (hin : ∀ w ∈ a.inputWires, wt' (ρ w) = wt w)
    (hout : ∀ w ∈ a.outputWires, wt' (ρ w) = wt w)
    (h : a.TypeConsistent wt) : (a.remapWires ρ).TypeConsistent wt' := by
  cases a with
  | const ty c out =>
    simp only [PrimApp.remapWires, PrimApp.TypeConsistent,
      PrimApp.outputWires, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq] at h hout ⊢
    rw [hout]; exact h
  | contract δ r ins out ir orr pat =>
    simp only [PrimApp.inputWires, PrimApp.outputWires, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq] at hin hout
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨by simpa using h1, ?_, ?_, ?_, ?_⟩
    · intro p hp
      rw [List.zip_map_left] at hp
      obtain ⟨⟨w, rk⟩, hmem, rfl⟩ := List.mem_map.mp hp
      obtain ⟨τ, hτ, hδ, hrk⟩ := h2 (w, rk) hmem
      exact ⟨τ, by
        show wt' (ρ w) = some τ
        rw [hin w (List.of_mem_zip hmem).1]; exact hτ, hδ, hrk⟩
    · obtain ⟨τ, hτ, hδ, hr⟩ := h3
      exact ⟨τ, by rw [hout]; exact hτ, hδ, hr⟩
    · intro i aIdx
      obtain ⟨τ, hτ, hext⟩ := h4 i aIdx
      have hlt : i.val < ins.length := by
        rw [h1]; exact i.isLt
      refine ⟨τ, ?_, hext⟩
      rw [getD_map_lt hlt, hin (ins.getD i.val 0) (getD_mem_lt hlt 0)]
      exact hτ
    · intro aIdx
      obtain ⟨τ, hτ, hext⟩ := h5 aIdx
      exact ⟨τ, by rw [hout]; exact hτ, hext⟩
  | cast δf δt r s i o =>
    simp only [PrimApp.remapWires, PrimApp.TypeConsistent,
      PrimApp.inputWires, PrimApp.outputWires, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq] at h hin hout ⊢
    rw [hin, hout]; exact h
  | cell schema i outs =>
    simp only [PrimApp.inputWires, PrimApp.outputWires, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq] at hin
    obtain ⟨⟨δ, hδ⟩, hlen, houts⟩ := h
    refine ⟨⟨δ, by rw [hin]; exact hδ⟩, by simpa using hlen, ?_⟩
    intro o ho
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ho
    rw [hout u hu]; exact houts u hu
  | reshape s i o =>
    simp only [PrimApp.inputWires, PrimApp.outputWires, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq] at hin hout
    obtain ⟨τ, hτ, hsz, ho⟩ := h
    exact ⟨τ, by rw [hin]; exact hτ, hsz, by rw [hout]; exact ho⟩
  | broadcast s i o =>
    simp only [PrimApp.inputWires, PrimApp.outputWires, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq] at hin hout
    obtain ⟨τ, hτ, hb, ho⟩ := h
    exact ⟨τ, by rw [hin]; exact hτ, hb, by rw [hout]; exact ho⟩
  | copy k i outs =>
    simp only [PrimApp.inputWires, PrimApp.outputWires, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq] at hin
    obtain ⟨hlen, τ, hτ, houts⟩ := h
    refine ⟨by simpa using hlen, τ, by rw [hin]; exact hτ, ?_⟩
    intro o ho
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ho
    rw [hout u hu]; exact houts u hu
  | delete i =>
    simp only [PrimApp.remapWires, PrimApp.TypeConsistent,
      PrimApp.inputWires, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq] at h hin ⊢
    rw [hin]; exact h
  | swap i1 i2 o1 o2 =>
    simp only [PrimApp.remapWires, PrimApp.TypeConsistent,
      PrimApp.inputWires, PrimApp.outputWires, List.mem_cons,
      List.not_mem_nil, or_false] at h hin hout ⊢
    obtain ⟨hi1, hi2, ho1, ho2⟩ := h
    exact ⟨by rw [hin i1 (Or.inl rfl)]; exact hi1,
           by rw [hin i2 (Or.inr rfl)]; exact hi2,
           by rw [hout o1 (Or.inl rfl), hin i2 (Or.inr rfl)]; exact ho1,
           by rw [hout o2 (Or.inr rfl), hin i1 (Or.inl rfl)]; exact ho2⟩
  | stack k s ins o =>
    simp only [PrimApp.outputWires, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq] at hout
    obtain ⟨hlen, τ, hτ, hsh, hins⟩ := h
    refine ⟨by simpa using hlen, τ, by rw [hout]; exact hτ, hsh, ?_⟩
    intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    rw [hin u (by simpa [PrimApp.inputWires] using hu)]
    exact hins u hu
  | relu s i o =>
    simp only [PrimApp.inputWires, PrimApp.outputWires, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq] at hin hout
    obtain ⟨τ, hτi, hτo, hs⟩ := h
    exact ⟨τ, by rw [hin]; exact hτi, by rw [hout]; exact hτo, hs⟩
  | ppoly n q ins o =>
    simp only [PrimApp.outputWires, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq] at hout
    obtain ⟨hlen, hins, ho⟩ := h
    refine ⟨by simpa using hlen, ?_, by rw [hout]; exact ho⟩
    intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    rw [hin u (by simpa [PrimApp.inputWires] using hu)]
    exact hins u hu
  | pderiv s ax i o =>
    simp only [PrimApp.inputWires, PrimApp.outputWires, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq] at hin hout
    obtain ⟨τ, hτi, hτo, hs⟩ := h
    exact ⟨τ, by rw [hin]; exact hτi, by rw [hout]; exact hτo, hs⟩
  | facet s ax hi i o =>
    simp only [PrimApp.inputWires, PrimApp.outputWires, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq] at hin hout
    obtain ⟨τ, hτi, hs, hτo⟩ := h
    exact ⟨τ, by rw [hin]; exact hτi, hs, by rw [hout]; exact hτo⟩

structure HypernetP where
  wireTypes : List TensorType
  apps : List PrimApp
  ins : List Wire
  outs : List Wire

def producedW (apps : List PrimApp) : List Wire :=
  apps.flatMap PrimApp.outputWires

def consumedW (apps : List PrimApp) : List Wire :=
  apps.flatMap PrimApp.inputWires

namespace HypernetP

def wt (h : HypernetP) : Wire → Option TensorType := fun w => h.wireTypes[w]?

def wireOrder (h : HypernetP) : List Wire := h.ins ++ producedW h.apps

end HypernetP

def SSA (ins : List Wire) (apps : List PrimApp) : Prop :=
  ∀ i (hi : i < apps.length), ∀ w ∈ (apps[i]'hi).inputWires,
    w ∈ ins ∨ ∃ j, ∃ (hj : j < apps.length), j < i ∧
      w ∈ (apps[j]'hj).outputWires

structure WFP (h : HypernetP) : Prop where
  linCons : (consumedW h.apps).Nodup
  linProd : (producedW h.apps).Nodup
  insNodup : h.ins.Nodup
  insNotProduced : ∀ w ∈ h.ins, w ∉ producedW h.apps
  ssa : SSA h.ins h.apps
  outsNodup : h.outs.Nodup
  outsKnown : ∀ w ∈ h.outs, w ∈ h.wireOrder
  wiresBound : ∀ w ∈ h.wireOrder, w < h.wireTypes.length
  tc : TypeConsistentAll h.wt h.apps

theorem producedW_disjoint {apps : List PrimApp}
    (hnd : (producedW apps).Nodup) {i j : Fin apps.length} (hne : i ≠ j)
    {w : Wire} (hwi : w ∈ apps[i].outputWires) (hwj : w ∈ apps[j].outputWires) :
    False := by
  have hjoin : (producedW apps) = (apps.map PrimApp.outputWires).flatten := by
    simp [producedW, List.flatMap_def]
  rw [hjoin] at hnd
  have hpw := (List.nodup_flatten.mp hnd).2
  have hget := List.pairwise_iff_getElem.mp hpw
  rcases Nat.lt_or_ge i.val j.val with hlt | hge
  · have hd := hget i.val j.val (by simp [i.isLt]) (by simp [j.isLt]) hlt
    simp only [List.getElem_map] at hd
    exact hd hwi hwj
  · have hlt' : j.val < i.val := by
      cases Nat.eq_or_lt_of_le hge with
      | inl heq => exact absurd (Fin.ext heq.symm) hne
      | inr h => exact h
    have hd := hget j.val i.val (by simp [j.isLt]) (by simp [i.isLt]) hlt'
    simp only [List.getElem_map] at hd
    exact hd hwj hwi

namespace WFP

theorem wireOrder_nodup {h : HypernetP} (hwf : WFP h) : h.wireOrder.Nodup :=
  List.Nodup.append hwf.insNodup hwf.linProd
    (fun w hins hprod => hwf.insNotProduced w hins hprod)

theorem produced_mem_wireOrder {h : HypernetP}
    {w : Wire} (hw : w ∈ producedW h.apps) : w ∈ h.wireOrder :=
  List.mem_append.mpr (Or.inr hw)

theorem consumed_mem_wireOrder {h : HypernetP} (hwf : WFP h)
    {w : Wire} (hw : w ∈ consumedW h.apps) : w ∈ h.wireOrder := by
  simp only [consumedW, List.mem_flatMap] at hw
  obtain ⟨a, ha, hwa⟩ := hw
  obtain ⟨i, hilt, hi⟩ := List.mem_iff_getElem.mp ha
  rcases hwf.ssa i hilt w (by simpa [hi]) with hins | ⟨j, hj, _, hjw⟩
  · exact List.mem_append.mpr (Or.inl hins)
  · exact List.mem_append.mpr (Or.inr (by
      simp only [producedW, List.mem_flatMap]
      exact ⟨h.apps[j], List.getElem_mem _, hjw⟩))

theorem acyclic {h : HypernetP} (hwf : WFP h) : Acyclic h.apps := by
  intro i w hwi j hwj
  rcases hwf.ssa i.val i.isLt w hwi with hins | ⟨j', hj', hj'lt, hj'w⟩
  · exact absurd (by
      simp only [producedW, List.mem_flatMap]
      exact ⟨h.apps[j], List.getElem_mem _, hwj⟩)
      (hwf.insNotProduced w hins)
  · rcases eq_or_ne j ⟨j', hj'⟩ with rfl | hne
    · exact hj'lt
    · exact (producedW_disjoint hwf.linProd hne hwj hj'w).elim

def toCore {h : HypernetP} (hwf : WFP h) : Hypernet where
  wireType := h.wt
  applications := h.apps
  linearity := ⟨hwf.linCons, hwf.linProd⟩
  acyclic := hwf.acyclic
  typeConsistent := hwf.tc

theorem app_input_mem_wireOrder {h : HypernetP} (hwf : WFP h)
    {a : PrimApp} (ha : a ∈ h.apps) {w : Wire} (hw : w ∈ a.inputWires) :
    w ∈ h.wireOrder :=
  hwf.consumed_mem_wireOrder (by
    simp only [consumedW, List.mem_flatMap]; exact ⟨a, ha, hw⟩)

theorem app_output_mem_wireOrder {h : HypernetP}
    {a : PrimApp} (ha : a ∈ h.apps) {w : Wire} (hw : w ∈ a.outputWires) :
    w ∈ h.wireOrder :=
  List.mem_append.mpr (Or.inr (by
    simp only [producedW, List.mem_flatMap]; exact ⟨a, ha, hw⟩))

end WFP

namespace HypernetP

def ren (h : HypernetP) : Wire → Wire := fun w => h.wireOrder.idxOf w

def applyRen (h : HypernetP) (ρ : Wire → Wire) (tys : List TensorType) :
    HypernetP where
  wireTypes := tys
  apps := h.apps.map (PrimApp.remapWires ρ)
  ins := h.ins.map ρ
  outs := h.outs.map ρ

def renumber (h : HypernetP) : HypernetP :=
  h.applyRen h.ren (h.wireOrder.map (fun w => (h.wt w).getD ⟨[], Dtype.Q⟩))

@[simp] theorem producedW_map_remapWires (ρ : Wire → Wire) (apps : List PrimApp) :
    producedW (apps.map (PrimApp.remapWires ρ)) = (producedW apps).map ρ := by
  simp [producedW, List.flatMap_map, List.map_flatMap]

@[simp] theorem consumedW_map_remapWires (ρ : Wire → Wire) (apps : List PrimApp) :
    consumedW (apps.map (PrimApp.remapWires ρ)) = (consumedW apps).map ρ := by
  simp [consumedW, List.flatMap_map, List.map_flatMap]

@[simp] theorem wireOrder_applyRen (h : HypernetP) (ρ : Wire → Wire)
    (tys : List TensorType) :
    (h.applyRen ρ tys).wireOrder = h.wireOrder.map ρ := by
  simp [wireOrder, applyRen]

protected theorem ext {h₁ h₂ : HypernetP}
    (hty : h₁.wireTypes = h₂.wireTypes) (happs : h₁.apps = h₂.apps)
    (hins : h₁.ins = h₂.ins) (houts : h₁.outs = h₂.outs) : h₁ = h₂ := by
  cases h₁; cases h₂; simp_all

theorem idxOf_map_of_inj {l : List Wire} {ρ : Wire → Wire} {w : Wire}
    (hinj : ∀ x ∈ l, ρ x = ρ w → x = w) :
    (l.map ρ).idxOf (ρ w) = l.idxOf w := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.idxOf_cons, cond_eq_ite, beq_iff_eq]
    by_cases haw : a = w
    · subst haw; simp
    · rw [if_neg (fun he => haw (hinj a (by simp) he)), if_neg haw,
        ih (fun x hx he => hinj x (List.mem_cons_of_mem a hx) he)]

theorem ren_inj {h : HypernetP} {w₁ w₂ : Wire}
    (h₁ : w₁ ∈ h.wireOrder) (_h₂ : w₂ ∈ h.wireOrder)
    (he : h.ren w₁ = h.ren w₂) : w₁ = w₂ :=
  (List.idxOf_inj h₁).mp he

theorem wt_renumber_ren {h : HypernetP} (hwf : WFP h)
    {w : Wire} (hw : w ∈ h.wireOrder) :
    (h.wireOrder.map (fun v => (h.wt v).getD ⟨[], Dtype.Q⟩))[h.ren w]? = h.wt w := by
  have hsome : (h.wt w).isSome := by
    have hlt := hwf.wiresBound w hw
    simp [wt, List.getElem?_eq_getElem hlt]
  rw [List.getElem?_map, ren, List.getElem?_idxOf hw]
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hsome
  simp [hτ]

theorem renumber_applyRen {h : HypernetP} (hwf : WFP h)
    {ρ : Wire → Wire} {tys : List TensorType}
    (hinj : ∀ w₁ ∈ h.wireOrder, ∀ w₂ ∈ h.wireOrder, ρ w₁ = ρ w₂ → w₁ = w₂)
    (hty : ∀ w ∈ h.wireOrder, tys[ρ w]? = h.wt w) :
    (h.applyRen ρ tys).renumber = h.renumber := by
  have hren : ∀ w ∈ h.wireOrder, (h.applyRen ρ tys).ren (ρ w) = h.ren w := by
    intro w hw
    show ((h.applyRen ρ tys).wireOrder).idxOf (ρ w) = h.wireOrder.idxOf w
    rw [wireOrder_applyRen]
    exact idxOf_map_of_inj (fun x hx he => hinj x hx w hw he)
  refine HypernetP.ext ?_ ?_ ?_ ?_
  · show ((h.applyRen ρ tys).wireOrder).map
        (fun v => ((h.applyRen ρ tys).wt v).getD ⟨[], Dtype.Q⟩)
      = h.wireOrder.map (fun v => (h.wt v).getD ⟨[], Dtype.Q⟩)
    rw [wireOrder_applyRen, List.map_map]
    exact List.map_congr_left (fun w hw => by
      show ((h.applyRen ρ tys).wt (ρ w)).getD _ = (h.wt w).getD _
      rw [show (h.applyRen ρ tys).wt (ρ w) = tys[ρ w]? from rfl, hty w hw])
  · show ((h.apps.map (PrimApp.remapWires ρ)).map
        (PrimApp.remapWires (h.applyRen ρ tys).ren))
      = h.apps.map (PrimApp.remapWires h.ren)
    rw [List.map_map]
    refine List.map_congr_left (fun a ha => ?_)
    show (a.remapWires ρ).remapWires ((h.applyRen ρ tys).ren)
      = a.remapWires h.ren
    rw [PrimApp.remapWires_remapWires]
    exact PrimApp.remapWires_congr a
      (fun w hw => hren w (WFP.app_input_mem_wireOrder hwf ha hw))
      (fun w hw => hren w (WFP.app_output_mem_wireOrder ha hw))
  · show (h.ins.map ρ).map ((h.applyRen ρ tys).ren) = h.ins.map h.ren
    rw [List.map_map]
    exact List.map_congr_left (fun w hw => hren w
      (List.mem_append.mpr (Or.inl hw)))
  · show (h.outs.map ρ).map ((h.applyRen ρ tys).ren) = h.outs.map h.ren
    rw [List.map_map]
    exact List.map_congr_left (fun w hw => hren w (hwf.outsKnown w hw))

theorem renumber_idem {h : HypernetP} (hwf : WFP h) :
    h.renumber.renumber = h.renumber :=
  renumber_applyRen hwf
    (fun _ h₁ _ h₂ he => ren_inj h₁ h₂ he)
    (fun _ hw => wt_renumber_ren hwf hw)

end HypernetP

namespace WFP

theorem applyRen {h : HypernetP} (hwf : WFP h)
    {ρ : Wire → Wire} {tys : List TensorType}
    (hinj : ∀ w₁ ∈ h.wireOrder, ∀ w₂ ∈ h.wireOrder, ρ w₁ = ρ w₂ → w₁ = w₂)
    (hty : ∀ w ∈ h.wireOrder, tys[ρ w]? = h.wt w) :
    WFP (h.applyRen ρ tys) := by
  have hACapps : (h.applyRen ρ tys).apps = h.apps.map (PrimApp.remapWires ρ) := rfl
  have hACins : (h.applyRen ρ tys).ins = h.ins.map ρ := rfl
  have hACouts : (h.applyRen ρ tys).outs = h.outs.map ρ := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hACapps, HypernetP.consumedW_map_remapWires]
    exact hwf.linCons.map_on (fun w₁ h₁ w₂ h₂ he =>
      hinj w₁ (hwf.consumed_mem_wireOrder h₁)
        w₂ (hwf.consumed_mem_wireOrder h₂) he)
  ·
    rw [hACapps, HypernetP.producedW_map_remapWires]
    exact hwf.linProd.map_on (fun w₁ h₁ w₂ h₂ he =>
      hinj w₁ (produced_mem_wireOrder h₁) w₂ (produced_mem_wireOrder h₂) he)
  ·
    rw [hACins]
    exact hwf.insNodup.map_on (fun w₁ h₁ w₂ h₂ he =>
      hinj w₁ (List.mem_append.mpr (Or.inl h₁))
        w₂ (List.mem_append.mpr (Or.inl h₂)) he)
  ·
    rw [hACins, hACapps, HypernetP.producedW_map_remapWires]
    intro w' hw' hcontra
    obtain ⟨w, hwins, rfl⟩ := List.mem_map.mp hw'
    obtain ⟨u, huprod, hu⟩ := List.mem_map.mp hcontra
    have huw : u = w := hinj u (produced_mem_wireOrder huprod)
      w (List.mem_append.mpr (Or.inl hwins)) hu
    exact hwf.insNotProduced w hwins (huw ▸ huprod)
  ·
    rw [hACapps, hACins]
    intro i hi w' hw'
    have hilen : i < h.apps.length := by simpa using hi
    simp only [List.getElem_map, PrimApp.inputWires_remapWires,
      List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    rcases hwf.ssa i hilen w hw with hins | ⟨j, hj, hjlt, hjout⟩
    · exact Or.inl (List.mem_map.mpr ⟨w, hins, rfl⟩)
    · refine Or.inr ⟨j, by simpa using hj, hjlt, ?_⟩
      simp only [List.getElem_map, PrimApp.outputWires_remapWires,
        List.mem_map]
      exact ⟨w, hjout, rfl⟩
  ·
    rw [hACouts]
    exact hwf.outsNodup.map_on (fun w₁ h₁ w₂ h₂ he =>
      hinj w₁ (hwf.outsKnown w₁ h₁) w₂ (hwf.outsKnown w₂ h₂) he)
  ·
    rw [hACouts, HypernetP.wireOrder_applyRen]
    intro w' hw'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hw'
    exact List.mem_map.mpr ⟨w, hwf.outsKnown w hw, rfl⟩
  ·
    rw [HypernetP.wireOrder_applyRen]
    intro w' hw'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hw'
    have hlt := hwf.wiresBound w hw
    have hsome : tys[ρ w]? = some (h.wireTypes[w]) := by
      rw [hty w hw]
      simp [HypernetP.wt, List.getElem?_eq_getElem hlt]
    obtain ⟨hlt', -⟩ := List.getElem?_eq_some_iff.mp hsome
    exact hlt'
  ·
    rw [hACapps]
    intro a' ha'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    refine PrimApp.TypeConsistent.remapWires
      (fun w hw => hty w (app_input_mem_wireOrder hwf ha hw))
      (fun w hw => hty w (app_output_mem_wireOrder ha hw))
      (hwf.tc a ha)

theorem renumber {h : HypernetP} (hwf : WFP h) : WFP h.renumber :=
  hwf.applyRen
    (fun _ h₁ _ h₂ he => HypernetP.ren_inj h₁ h₂ he)
    (fun _ hw => HypernetP.wt_renumber_ren hwf hw)

end WFP

structure SeamOut where
  repairs : List PrimApp
  redirect : List (Wire × Wire)
  exposeMap : List (Wire × Wire)
  freshTys : List TensorType

def seamN (portsOf : Wire → List Wire) (isExp : Wire → Bool) (v : Wire) : Nat :=
  (portsOf v).length + (if isExp v then 1 else 0)

def seamStep (innerConsumed : Wire → Bool) (wtv : Wire → Option TensorType)
    (portsOf : Wire → List Wire) (isExp : Wire → Bool)
    (v : Wire) (fresh : Nat) : SeamOut :=
  if innerConsumed v then ⟨[], [], [], []⟩
  else
    let ports := portsOf v
    let n := seamN portsOf isExp v
    if n = 0 then ⟨[.delete v], [], [], []⟩
    else if n = 1 then
      match ports with
      | [k] => ⟨[], [(k, v)], [], []⟩
      | _ => ⟨[], [], [], []⟩
    else
      let nExp := if isExp v then 1 else 0
      ⟨[.copy n v (List.range' fresh n)],
       ports.zip (List.range' (fresh + nExp) ports.length),
       (if isExp v then [(v, fresh)] else []),
       (List.range' fresh n).map (fun _ => (wtv v).getD ⟨[], Dtype.Q⟩)⟩

def seamGo (innerConsumed : Wire → Bool) (wtv : Wire → Option TensorType)
    (portsOf : Wire → List Wire) (isExp : Wire → Bool) :
    List Wire → Nat → SeamOut
  | [], _ => ⟨[], [], [], []⟩
  | v :: vs, fresh =>
    let s₁ := seamStep innerConsumed wtv portsOf isExp v fresh
    let rest := seamGo innerConsumed wtv portsOf isExp vs
      (fresh + s₁.freshTys.length)
    ⟨s₁.repairs ++ rest.repairs, s₁.redirect ++ rest.redirect,
     s₁.exposeMap ++ rest.exposeMap, s₁.freshTys ++ rest.freshTys⟩

structure PortOk (outer : HypernetP) (φ : List (Wire × Wire)) (E : List Wire)
    (inner : HypernetP) : Prop where
  keysNodup : (φ.map Prod.fst).Nodup
  keysIns : ∀ p ∈ φ, p.1 ∈ outer.ins
  valsOuts : ∀ p ∈ φ, p.2 ∈ inner.outs
  typeExact : ∀ p ∈ φ, outer.wt p.1 = inner.wt p.2
  expOuts : ∀ v ∈ E, v ∈ inner.outs
  seamCap : ∀ v ∈ inner.outs, v ∈ consumedW inner.apps →
    (∀ p ∈ φ, p.2 ≠ v) ∧ v ∉ E

def substPortsOf (φ : List (Wire × Wire)) (v : Wire) : List Wire :=
  ((φ.filter (fun p => p.2 = v)).map Prod.fst).mergeSort
    (fun a b => Nat.ble a b)

def substSeam (outer : HypernetP) (φ : List (Wire × Wire)) (E : List Wire)
    (inner : HypernetP) : SeamOut :=
  seamGo (fun w => decide (w ∈ consumedW inner.apps)) inner.wt
    (substPortsOf φ) (fun v => decide (v ∈ E)) inner.outs
    (inner.wireTypes.length + outer.wireTypes.length)

def substOuterWire (outer : HypernetP) (φ : List (Wire × Wire))
    (E : List Wire) (inner : HypernetP) (w : Wire) : Wire :=
  (((substSeam outer φ E inner).redirect.lookup w).getD
    (w + inner.wireTypes.length))

def substituteRaw (outer : HypernetP) (φ : List (Wire × Wire)) (E : List Wire)
    (inner : HypernetP) : HypernetP :=
  { wireTypes := inner.wireTypes ++ outer.wireTypes
      ++ (substSeam outer φ E inner).freshTys
    apps := inner.apps ++ (substSeam outer φ E inner).repairs
      ++ outer.apps.map (PrimApp.remapWires (substOuterWire outer φ E inner))
    ins := inner.ins
      ++ (outer.ins.filter (fun w => decide (w ∉ φ.map Prod.fst))).map
          (· + inner.wireTypes.length)
    outs := outer.outs.map (substOuterWire outer φ E inner)
      ++ (inner.outs.filter (fun v => decide (v ∈ E))).map
          (fun v => ((substSeam outer φ E inner).exposeMap.lookup v).getD v) }

def substitute (outer : HypernetP) (φ : List (Wire × Wire)) (E : List Wire)
    (inner : HypernetP) : HypernetP :=
  (substituteRaw outer φ E inner).renumber

namespace SeamFacts

variable {ic isExp : Wire → Bool} {wtv : Wire → Option TensorType}
  {portsOf : Wire → List Wire}

theorem range'_append_simple : ∀ (s m n : Nat),
    List.range' s m ++ List.range' (s + m) n = List.range' s (m + n) := by
  intro s m
  induction m generalizing s with
  | zero => intro n; simp
  | succ m ih =>
    intro n
    rw [List.range'_succ, List.cons_append,
      show s + (m + 1) = (s + 1) + m by omega, ih (s + 1),
      show m + 1 + n = (m + n) + 1 by omega, List.range'_succ]

theorem step_produced (v : Wire) (fresh : Nat) :
    producedW (seamStep ic wtv portsOf isExp v fresh).repairs
      = List.range' fresh
          (seamStep ic wtv portsOf isExp v fresh).freshTys.length := by
  unfold seamStep
  by_cases hic : ic v
  · simp [hic, producedW]
  · by_cases h0 : seamN portsOf isExp v = 0
    · simp [hic, h0, producedW, PrimApp.outputWires]
    · by_cases h1 : seamN portsOf isExp v = 1
      · rcases hports : portsOf v with _ | ⟨k, _ | ⟨k₂, ps⟩⟩ <;>
          simp [hic, h0, h1, hports, producedW]
      · simp [hic, h0, h1, producedW, PrimApp.outputWires]

theorem step_consumed (v : Wire) (fresh : Nat) :
    consumedW (seamStep ic wtv portsOf isExp v fresh).repairs
      = if ic v then [] else if seamN portsOf isExp v = 1 then []
        else [v] := by
  unfold seamStep
  by_cases hic : ic v
  · simp [hic, consumedW]
  · by_cases h0 : seamN portsOf isExp v = 0
    · simp [hic, h0, consumedW, PrimApp.inputWires]
    · by_cases h1 : seamN portsOf isExp v = 1
      · rcases hports : portsOf v with _ | ⟨k, _ | ⟨k₂, ps⟩⟩ <;>
          simp [hic, h0, h1, hports, consumedW]
      · simp [hic, h0, h1, consumedW, PrimApp.inputWires]

theorem go_produced :
    ∀ (vs : List Wire) (fresh : Nat),
      producedW (seamGo ic wtv portsOf isExp vs fresh).repairs
        = List.range' fresh
            (seamGo ic wtv portsOf isExp vs fresh).freshTys.length := by
  intro vs
  induction vs with
  | nil => intro fresh; rfl
  | cons v vs ih =>
    intro fresh
    show producedW ((seamStep ic wtv portsOf isExp v fresh).repairs
        ++ (seamGo ic wtv portsOf isExp vs _).repairs) = _
    rw [show producedW ((seamStep ic wtv portsOf isExp v fresh).repairs
        ++ (seamGo ic wtv portsOf isExp vs
          (fresh + (seamStep ic wtv portsOf isExp v fresh).freshTys.length)).repairs)
      = producedW (seamStep ic wtv portsOf isExp v fresh).repairs
        ++ producedW (seamGo ic wtv portsOf isExp vs
          (fresh + (seamStep ic wtv portsOf isExp v fresh).freshTys.length)).repairs
      from List.flatMap_append]
    rw [step_produced, ih]
    show List.range' fresh _ ++ List.range' (fresh + _) _
      = List.range' fresh (List.length (_ ++ _))
    rw [List.length_append, range'_append_simple]

theorem go_consumed :
    ∀ (vs : List Wire) (fresh : Nat),
      consumedW (seamGo ic wtv portsOf isExp vs fresh).repairs
        = vs.filter (fun v => !ic v && !(seamN portsOf isExp v == 1)) := by
  intro vs
  induction vs with
  | nil => intro fresh; rfl
  | cons v vs ih =>
    intro fresh
    show consumedW ((seamStep ic wtv portsOf isExp v fresh).repairs
        ++ (seamGo ic wtv portsOf isExp vs _).repairs) = _
    rw [show consumedW ((seamStep ic wtv portsOf isExp v fresh).repairs
        ++ (seamGo ic wtv portsOf isExp vs
          (fresh + (seamStep ic wtv portsOf isExp v fresh).freshTys.length)).repairs)
      = consumedW (seamStep ic wtv portsOf isExp v fresh).repairs
        ++ consumedW (seamGo ic wtv portsOf isExp vs
          (fresh + (seamStep ic wtv portsOf isExp v fresh).freshTys.length)).repairs
      from List.flatMap_append]
    rw [step_consumed, ih, List.filter_cons]
    by_cases hic : ic v
    · simp [hic]
    · by_cases h1 : seamN portsOf isExp v = 1
      · simp [hic, h1]
      · simp [hic, h1]

theorem mem_range'_bounds {s n a : Nat} (h : a ∈ List.range' s n) :
    s ≤ a ∧ a < s + n := by
  induction n generalizing s with
  | zero => cases h
  | succ n ih =>
    rw [List.range'_succ] at h
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h
      omega

theorem nodup_range'_simple : ∀ (s n : Nat), (List.range' s n).Nodup := by
  intro s n
  induction n generalizing s with
  | zero => exact List.nodup_nil
  | succ n ih =>
    rw [List.range'_succ]
    exact List.nodup_cons.mpr
      ⟨fun hmem => by have := mem_range'_bounds hmem; omega, ih (s + 1)⟩

theorem step_redirect_keys {v : Wire} {fresh : Nat} {p : Wire × Wire}
    (hp : p ∈ (seamStep ic wtv portsOf isExp v fresh).redirect) :
    p.1 ∈ portsOf v := by
  unfold seamStep at hp
  by_cases hic : ic v
  · simp [hic] at hp
  · by_cases h0 : seamN portsOf isExp v = 0
    · simp [hic, h0] at hp
    · by_cases h1 : seamN portsOf isExp v = 1
      · rcases hports : portsOf v with _ | ⟨k, _ | ⟨k₂, ps⟩⟩ <;>
          simp [hic, h0, h1, hports] at hp ⊢
        subst hp
        rfl
      · simp only [hic, h0, h1, if_neg, if_false, Bool.false_eq_true,
          not_false_eq_true, ite_false] at hp
        have hp' : p ∈ (portsOf v).zip
            (List.range' (fresh + (if isExp v then 1 else 0))
              (portsOf v).length) := by
          simpa [hic, h0, h1] using hp
        rcases p with ⟨k, b⟩
        exact (List.of_mem_zip hp').1

theorem go_redirect_keys : ∀ (vs : List Wire) (fresh : Nat)
    {p : Wire × Wire},
    p ∈ (seamGo ic wtv portsOf isExp vs fresh).redirect →
    ∃ v ∈ vs, p.1 ∈ portsOf v := by
  intro vs
  induction vs with
  | nil => intro fresh p hp; cases hp
  | cons v vs ih =>
    intro fresh p hp
    have hp' : p ∈ (seamStep ic wtv portsOf isExp v fresh).redirect
        ++ (seamGo ic wtv portsOf isExp vs
          (fresh + (seamStep ic wtv portsOf isExp v fresh).freshTys.length)).redirect := hp
    rcases List.mem_append.mp hp' with h | h
    · exact ⟨v, List.mem_cons_self, step_redirect_keys h⟩
    · obtain ⟨v', hv', hk⟩ := ih _ h
      exact ⟨v', List.mem_cons_of_mem _ hv', hk⟩

end SeamFacts

theorem substPortsOf_mem {φ : List (Wire × Wire)} {v k : Wire}
    (hk : k ∈ substPortsOf φ v) : (k, v) ∈ φ := by
  unfold substPortsOf at hk
  rw [List.mem_mergeSort] at hk
  obtain ⟨⟨k', v'⟩, hmem, rfl⟩ := List.mem_map.mp hk
  obtain ⟨hφ, heq⟩ := List.mem_filter.mp hmem
  have hv : v' = v := by simpa using heq
  subst hv
  exact hφ

theorem substituteRaw_linProd {outer inner : HypernetP}
    {φ : List (Wire × Wire)} {E : List Wire}
    (hwfO : WFP outer) (hwfI : WFP inner)
    (hpo : PortOk outer φ E inner) :
    (producedW (substituteRaw outer φ E inner).apps).Nodup := by
  have hsplit : producedW (substituteRaw outer φ E inner).apps
      = producedW inner.apps
        ++ producedW (substSeam outer φ E inner).repairs
        ++ producedW (outer.apps.map
            (PrimApp.remapWires (substOuterWire outer φ E inner))) := by
    show producedW (inner.apps ++ (substSeam outer φ E inner).repairs
      ++ outer.apps.map (PrimApp.remapWires (substOuterWire outer φ E inner)))
      = _
    simp [producedW, List.flatMap_append]
  rw [hsplit]

  have hrep : producedW (substSeam outer φ E inner).repairs
      = List.range' (inner.wireTypes.length + outer.wireTypes.length)
          (substSeam outer φ E inner).freshTys.length :=
    SeamFacts.go_produced inner.outs _

  have houter : producedW (outer.apps.map
      (PrimApp.remapWires (substOuterWire outer φ E inner)))
      = (producedW outer.apps).map (· + inner.wireTypes.length) := by
    rw [HypernetP.producedW_map_remapWires]
    refine List.map_congr_left (fun w hw => ?_)
    unfold substOuterWire
    cases hlk : (substSeam outer φ E inner).redirect.lookup w with
    | none => rfl
    | some t =>
      exfalso
      obtain ⟨l₁, l₂, hsplit', -⟩ := List.lookup_eq_some_iff.mp hlk
      have hwmem : (w, t) ∈ (substSeam outer φ E inner).redirect := by
        rw [hsplit']
        exact List.mem_append.mpr (Or.inr (List.mem_cons_self))
      obtain ⟨v, -, hkport⟩ := SeamFacts.go_redirect_keys inner.outs _ hwmem
      have hφmem : (w, v) ∈ φ := substPortsOf_mem hkport
      have hins : w ∈ outer.ins := hpo.keysIns _ hφmem
      exact hwfO.insNotProduced w hins hw
  rw [hrep, houter]

  have hb1 : ∀ w ∈ producedW inner.apps, w < inner.wireTypes.length :=
    fun w hw => hwfI.wiresBound w (WFP.produced_mem_wireOrder hw)

  refine List.Nodup.append (List.Nodup.append hwfI.linProd
      (SeamFacts.nodup_range'_simple _ _) ?_)
    (hwfO.linProd.map_on (fun w₁ _ w₂ _ he => by simpa using he)) ?_
  ·
    intro w hw hcontra
    have h1 : w < inner.wireTypes.length := hb1 w hw
    have h2 : inner.wireTypes.length + outer.wireTypes.length ≤ w :=
      (SeamFacts.mem_range'_bounds hcontra).1
    exact Nat.lt_irrefl w (Nat.lt_of_lt_of_le h1
      (Nat.le_trans (Nat.le_add_right _ _) h2))
  ·
    intro w hw hcontra
    obtain ⟨w', hw', heq⟩ := List.mem_map.mp hcontra
    have heq' : w' + inner.wireTypes.length = w := heq
    have h2 : w' < outer.wireTypes.length :=
      hwfO.wiresBound w' (WFP.produced_mem_wireOrder hw')
    rcases List.mem_append.mp hw with h | h
    · have h1 : w < inner.wireTypes.length := hb1 w h
      have hge : inner.wireTypes.length ≤ w :=
        Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq heq')
      exact Nat.lt_irrefl w (Nat.lt_of_lt_of_le h1 hge)
    · have h1 : inner.wireTypes.length + outer.wireTypes.length ≤ w :=
        (SeamFacts.mem_range'_bounds h).1
      have hlt : w < outer.wireTypes.length + inner.wireTypes.length :=
        heq' ▸ Nat.add_lt_add_right h2 inner.wireTypes.length
      rw [Nat.add_comm] at hlt
      exact Nat.lt_irrefl w (Nat.lt_of_lt_of_le hlt h1)

end PPLC

namespace PPLC

theorem substitute_determined {A A' B B' : HypernetP}
    {φ φ' : List (Wire × Wire)} {E E' : List Wire}
    (hA : A = A') (hφ : φ = φ') (hE : E = E') (hB : B = B') :
    substitute A φ E B = substitute A' φ' E' B' := by
  subst hA; subst hφ; subst hE; subst hB; rfl

#print axioms HypernetP.renumber_applyRen
#print axioms HypernetP.renumber_idem
#print axioms WFP.renumber
#print axioms WFP.toCore
#print axioms substituteRaw_linProd
#print axioms substitute_determined

end PPLC
