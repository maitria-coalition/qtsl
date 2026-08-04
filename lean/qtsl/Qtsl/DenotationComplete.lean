import Qtsl.DenotationClass
import Qtsl.DenotationCompile

/-!
# The generation direction of the completion theorem

The primitive basis generates the piecewise-polynomial denotation
class: every finite union of rational-polynomial graphs over basic
closed pieces is the interface denotation of an exact-⟨B,Q⟩ ten-box
hypernet (`primitiveBasisComplete`).

The witness net for a list of pieces is assembled from four blocks:

* **ports** — the `d` input wires, free;
* **bit gadgets** — one per selector bit: a constant origin fed
  through the σ± cell schema and an exact Boolean-to-rational cast,
  producing a wire that an admissible valuation may set to `0` or `1`,
  freely, and to nothing else;
* **combs** — one `copy` per source (port or bit), fanning its value
  to the tap blocks of the compiled expressions;
* **stations** — the compiled expressions (`PolyExpr.compileMany`):
  for each piece and each of its carving conditions, the masked
  polynomial `selector · condition`, and for each output coordinate
  the selected sum `Σ_I selector_I · value_I`;
* **guards** — one `reshape`+`cell sigmaNN` pair per masked condition,
  admissible exactly on the nonnegative ray.

The first-match selector polynomials `c_I = β_I·Π_{j<I}(1−β_j)` are
inlined into the station expressions, so that for Boolean bit values
the selector vector ranges over exactly the standard basis vectors —
selection is total and exclusive without any additional constraint.
-/

namespace PPLC

namespace BasisGen

open PolyExpr
open ReluExpansion (pat0 sigmaPM cNeg cPos qelem belem qv0 qv1 bv)

variable (d nb : ℕ) (Es : List PolyExpr) (K : ℕ)

/-! ## Wire layout -/

/-- First wire of the station region. -/
def eB : ℕ := d + 5 * nb

/-- The compiled stations. -/
def M : ManyCompiled := PolyExpr.compileMany Es (eB d nb)

/-- First wire of the guard region. -/
def gB : ℕ := (M d nb Es).next

/-- The wire carrying source `s`: a port, or a bit gadget's cast. -/
def srcW (s : ℕ) : ℕ := if s < d then s else d + 5 * (s - d) + 4

/-! ## The four application blocks -/

def bitApps : List PrimApp :=
  (List.range nb).flatMap (fun i =>
    [.const ⟨[], Dtype.Q⟩ (qv0 0) (d + 5 * i),
     .reshape [1] (d + 5 * i) (d + 5 * i + 1),
     .cell sigmaPM (d + 5 * i + 1) [d + 5 * i + 2, d + 5 * i + 3],
     .cast Dtype.B Dtype.Q .exact [] (d + 5 * i + 3) (d + 5 * i + 4)])

def combApps : List PrimApp :=
  (List.range (d + nb)).map (fun s =>
    .copy ((M d nb Es).tapOf s).length (srcW d s) ((M d nb Es).tapOf s))

def guardApps : List PrimApp :=
  (List.range K).flatMap (fun r =>
    [.reshape [1] ((M d nb Es).outs.getD r 0) (gB d nb Es + 2 * r),
     .cell sigmaNN (gB d nb Es + 2 * r) [gB d nb Es + 2 * r + 1]])

def masterApps : List PrimApp :=
  bitApps d nb ++ combApps d nb Es ++ (M d nb Es).apps ++
    guardApps d nb Es K

/-! ## The wire typing -/

def bitTy (w : ℕ) : Option TensorType :=
  if (w - d) % 5 = 1 then some ⟨[1], Dtype.Q⟩
  else if (w - d) % 5 = 2 then some ⟨[], Dtype.B⟩
  else if (w - d) % 5 = 3 then some ⟨[], Dtype.B⟩
  else some ⟨[], Dtype.Q⟩

def guardTy (w : ℕ) : Option TensorType :=
  if gB d nb Es ≤ w ∧ w < gB d nb Es + 2 * K then
    (if (w - gB d nb Es) % 2 = 0 then some ⟨[1], Dtype.Q⟩
     else some ⟨[], Dtype.B⟩)
  else none

def masterTy : ℕ → Option TensorType := fun w =>
  if w < d then some ⟨[], Dtype.Q⟩
  else if w < eB d nb then bitTy d w
  else mergeWt (M d nb Es).ty (guardTy d nb Es K) w

/-! ## Typing facts -/

theorem ty_port {w : ℕ} (h : w < d) :
    masterTy d nb Es K w = some ⟨[], Dtype.Q⟩ := by
  unfold masterTy
  rw [if_pos h]

theorem ty_z {i : ℕ} (h : i < nb) :
    masterTy d nb Es K (d + 5 * i) = some ⟨[], Dtype.Q⟩ := by
  unfold masterTy bitTy
  rw [if_neg (by omega), if_pos (by unfold eB; omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem ty_z' {i : ℕ} (h : i < nb) :
    masterTy d nb Es K (d + 5 * i + 1) = some ⟨[1], Dtype.Q⟩ := by
  unfold masterTy bitTy
  rw [if_neg (by omega), if_pos (by unfold eB; omega),
    if_pos (by omega)]

theorem ty_b0 {i : ℕ} (h : i < nb) :
    masterTy d nb Es K (d + 5 * i + 2) = some ⟨[], Dtype.B⟩ := by
  unfold masterTy bitTy
  rw [if_neg (by omega), if_pos (by unfold eB; omega),
    if_neg (by omega), if_pos (by omega)]

theorem ty_b1 {i : ℕ} (h : i < nb) :
    masterTy d nb Es K (d + 5 * i + 3) = some ⟨[], Dtype.B⟩ := by
  unfold masterTy bitTy
  rw [if_neg (by omega), if_pos (by unfold eB; omega),
    if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem ty_b {i : ℕ} (h : i < nb) :
    masterTy d nb Es K (d + 5 * i + 4) = some ⟨[], Dtype.Q⟩ := by
  unfold masterTy bitTy
  rw [if_neg (by omega), if_pos (by unfold eB; omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem ty_srcW {s : ℕ} (h : s < d + nb) :
    masterTy d nb Es K (srcW d s) = some ⟨[], Dtype.Q⟩ := by
  unfold srcW
  by_cases hs : s < d
  · rw [if_pos hs]
    exact ty_port d nb Es K hs
  · rw [if_neg hs]
    exact ty_b d nb Es K (by omega)

theorem ty_M {w : ℕ} {τ : TensorType} (h : (M d nb Es).ty w = some τ) :
    masterTy d nb Es K w = some τ := by
  obtain ⟨h1, h2⟩ := many_ty_domain Es (eB d nb) h
  unfold masterTy
  rw [if_neg (by unfold eB at h1; omega), if_neg (by omega)]
  exact mergeWt_left h

theorem ty_guard_s {r : ℕ} (h : r < K) :
    masterTy d nb Es K (gB d nb Es + 2 * r) = some ⟨[1], Dtype.Q⟩ := by
  have hge : eB d nb ≤ gB d nb Es := many_le Es (eB d nb)
  have hd : d ≤ eB d nb := by unfold eB; omega
  unfold masterTy
  rw [if_neg (by omega), if_neg (by omega),
    mergeWt_of_left_none (show (M d nb Es).ty (gB d nb Es + 2 * r) = none
      from many_ty_none Es (eB d nb) (Or.inr (by
        show gB d nb Es ≤ gB d nb Es + 2 * r
        omega)))]
  unfold guardTy
  rw [if_pos ⟨by omega, by omega⟩,
    if_pos (show (gB d nb Es + 2 * r - gB d nb Es) % 2 = 0 by omega)]

theorem ty_guard_g {r : ℕ} (h : r < K) :
    masterTy d nb Es K (gB d nb Es + 2 * r + 1) = some ⟨[], Dtype.B⟩ := by
  have hge : eB d nb ≤ gB d nb Es := many_le Es (eB d nb)
  have hd : d ≤ eB d nb := by unfold eB; omega
  unfold masterTy
  rw [if_neg (by omega), if_neg (by omega),
    mergeWt_of_left_none (show (M d nb Es).ty (gB d nb Es + 2 * r + 1) = none
      from many_ty_none Es (eB d nb) (Or.inr (by
        show gB d nb Es ≤ gB d nb Es + 2 * r + 1
        omega)))]
  unfold guardTy
  rw [if_pos ⟨by omega, by omega⟩,
    if_neg (show ¬((gB d nb Es + 2 * r + 1 - gB d nb Es) % 2 = 0) by
      omega)]

theorem ty_tapOf {s w : ℕ} (h : w ∈ (M d nb Es).tapOf s) :
    masterTy d nb Es K w = some ⟨[], Dtype.Q⟩ :=
  ty_M d nb Es K (many_ty_tapOf Es (eB d nb) s w h)

/-! ## Fragment membership of every emitted application -/

theorem compile_fragment (e : PolyExpr) (base : ℕ) :
    ∀ a ∈ (e.compile base).apps,
      a.isTenBox = true ∧ a.exactBQ = true := by
  induction e generalizing base with
  | tap w => intro a ha; exact nomatch ha
  | qconst q =>
    intro a ha
    have ha' := List.mem_singleton.mp ha
    subst ha'
    exact ⟨rfl, rfl⟩
  | add e₁ e₂ ih₁ ih₂ =>
    intro a ha
    rw [compile_add_apps] at ha
    rcases List.mem_append.mp ha with ha' | ha'
    · rcases List.mem_append.mp ha' with ha'' | ha''
      · exact ih₁ base a ha''
      · exact ih₂ (e₁.compile base).next a ha''
    · rcases List.mem_cons.mp ha' with ha'' | ha''
      · subst ha''
        exact ⟨rfl, rfl⟩
      · have ha₃ := List.mem_singleton.mp ha''
        subst ha₃
        exact ⟨rfl, rfl⟩
  | mul e₁ e₂ ih₁ ih₂ =>
    intro a ha
    rw [compile_mul_apps] at ha
    rcases List.mem_append.mp ha with ha' | ha'
    · rcases List.mem_append.mp ha' with ha'' | ha''
      · exact ih₁ base a ha''
      · exact ih₂ (e₁.compile base).next a ha''
    · have ha₃ := List.mem_singleton.mp ha'
      subst ha₃
      exact ⟨rfl, rfl⟩

theorem many_fragment (Es' : List PolyExpr) (start : ℕ) :
    ∀ a ∈ (PolyExpr.compileMany Es' start).apps,
      a.isTenBox = true ∧ a.exactBQ = true := by
  induction Es' generalizing start with
  | nil => intro a ha; exact nomatch ha
  | cons E rest ih =>
    intro a ha
    rw [many_cons_apps] at ha
    rcases List.mem_append.mp ha with ha' | ha'
    · exact compile_fragment _ _ a ha'
    · exact ih _ a ha'

theorem master_fragment :
    ∀ a ∈ masterApps d nb Es K,
      a.isTenBox = true ∧ a.exactBQ = true := by
  intro a ha
  unfold masterApps at ha
  rcases List.mem_append.mp ha with ha' | ha'
  · rcases List.mem_append.mp ha' with ha'' | ha''
    · rcases List.mem_append.mp ha'' with hb | hb
      · unfold bitApps at hb
        rw [List.mem_flatMap] at hb
        obtain ⟨i, -, hmem⟩ := hb
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact ⟨rfl, rfl⟩
        · rcases List.mem_cons.mp hmem with rfl | hmem
          · exact ⟨rfl, rfl⟩
          · rcases List.mem_cons.mp hmem with rfl | hmem
            · exact ⟨rfl, rfl⟩
            · have h4 := List.mem_singleton.mp hmem
              subst h4
              exact ⟨rfl, rfl⟩
      · unfold combApps at hb
        rw [List.mem_map] at hb
        obtain ⟨s, -, rfl⟩ := hb
        exact ⟨rfl, rfl⟩
    · exact many_fragment Es (eB d nb) a ha''
  · unfold guardApps at ha'
    rw [List.mem_flatMap] at ha'
    obtain ⟨r, -, hmem⟩ := ha'
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ⟨rfl, rfl⟩
    · have h2 := List.mem_singleton.mp hmem
      subst h2
      exact ⟨rfl, rfl⟩


/-! ## List helpers for block assembly -/

theorem producedW_flatMap (l : List ℕ) (f : ℕ → List PrimApp) :
    producedW (l.flatMap f) = l.flatMap (fun a => producedW (f a)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show producedW (f a ++ l.flatMap f) = _
    rw [producedW_append, ih]
    rfl

theorem consumedW_flatMap (l : List ℕ) (f : ℕ → List PrimApp) :
    consumedW (l.flatMap f) = l.flatMap (fun a => consumedW (f a)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show consumedW (f a ++ l.flatMap f) = _
    rw [consumedW_append, ih]
    rfl

theorem map_eq_flatMap_single (l : List ℕ) (f : ℕ → PrimApp) :
    l.map f = l.flatMap (fun a => [f a]) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show f a :: l.map f = f a :: l.flatMap (fun a => [f a])
    rw [ih]

theorem nodup_flatMap_nat {l : List ℕ} {f : ℕ → List ℕ}
    (hl : l.Nodup)
    (hf : ∀ a ∈ l, (f a).Nodup)
    (hdisj : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ w ∈ f a, w ∉ f b) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    obtain ⟨hna, hnl⟩ := List.nodup_cons.mp hl
    show ((f a) ++ l.flatMap f).Nodup
    refine nodup_append_nat (hf a List.mem_cons_self)
      (ih hnl (fun b hb => hf b (List.mem_cons_of_mem _ hb))
        (fun b hb c hc => hdisj b (List.mem_cons_of_mem _ hb)
          c (List.mem_cons_of_mem _ hc))) ?_
    intro w hw w' hw' he
    subst he
    obtain ⟨b, hb, hwb⟩ := List.mem_flatMap.mp hw'
    exact hdisj a List.mem_cons_self b (List.mem_cons_of_mem _ hb)
      (fun hab => hna (hab ▸ hb)) w hw hwb

theorem acyclic_flatMap_nat {l : List ℕ} (hl : l.Nodup)
    {f : ℕ → List PrimApp}
    (hf : ∀ a ∈ l, Acyclic (f a))
    (hdisj : ∀ a ∈ l, ∀ b ∈ l, a ≠ b →
      ∀ w : ℕ, w ∈ consumedW (f a) → w ∈ producedW (f b) → False) :
    Acyclic (l.flatMap f) := by
  induction l with
  | nil => exact acyclic_nil
  | cons a l ih =>
    obtain ⟨hna, hnl⟩ := List.nodup_cons.mp hl
    show Acyclic ((f a) ++ l.flatMap f)
    refine acyclic_append_nat (hf a List.mem_cons_self)
      (ih hnl (fun b hb => hf b (List.mem_cons_of_mem _ hb))
        (fun b hb c hc => hdisj b (List.mem_cons_of_mem _ hb)
          c (List.mem_cons_of_mem _ hc))) ?_
    intro w hw hw'
    rw [producedW_flatMap] at hw'
    obtain ⟨b, hb, hwb⟩ := List.mem_flatMap.mp hw'
    exact hdisj a List.mem_cons_self b (List.mem_cons_of_mem _ hb)
      (fun hab => hna (hab ▸ hb)) w hw hwb

/-! ## The block wire inventories -/

theorem bit_produced :
    producedW (bitApps d nb)
      = (List.range nb).flatMap (fun i =>
          [d + 5 * i, d + 5 * i + 1, d + 5 * i + 2, d + 5 * i + 3,
           d + 5 * i + 4]) := by
  unfold bitApps
  rw [producedW_flatMap]
  simp [producedW, PrimApp.outputWires]

theorem bit_consumed :
    consumedW (bitApps d nb)
      = (List.range nb).flatMap (fun i =>
          [d + 5 * i, d + 5 * i + 1, d + 5 * i + 3]) := by
  unfold bitApps
  rw [consumedW_flatMap]
  simp [consumedW, PrimApp.inputWires]

theorem comb_produced :
    producedW (combApps d nb Es)
      = (List.range (d + nb)).flatMap (fun s => (M d nb Es).tapOf s) := by
  unfold combApps
  rw [map_eq_flatMap_single, producedW_flatMap]
  simp [producedW, PrimApp.outputWires]

theorem comb_consumed :
    consumedW (combApps d nb Es)
      = (List.range (d + nb)).flatMap (fun s => [srcW d s]) := by
  unfold combApps
  rw [map_eq_flatMap_single, consumedW_flatMap]
  simp [consumedW, PrimApp.inputWires]

theorem guard_produced :
    producedW (guardApps d nb Es K)
      = (List.range K).flatMap (fun r =>
          [gB d nb Es + 2 * r, gB d nb Es + 2 * r + 1]) := by
  unfold guardApps
  rw [producedW_flatMap]
  simp [producedW, PrimApp.outputWires]

theorem guard_consumed :
    consumedW (guardApps d nb Es K)
      = (List.range K).flatMap (fun r =>
          [(M d nb Es).outs.getD r 0, gB d nb Es + 2 * r]) := by
  unfold guardApps
  rw [consumedW_flatMap]
  simp [consumedW, PrimApp.inputWires]

/-! ## Range bounds for the blocks -/

theorem bit_produced_bounds {w : ℕ} (h : w ∈ producedW (bitApps d nb)) :
    d ≤ w ∧ w < eB d nb := by
  rw [bit_produced] at h
  obtain ⟨i, hi, hw⟩ := List.mem_flatMap.mp h
  have hi' := List.mem_range.mp hi
  unfold eB
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  omega

theorem bit_consumed_bounds {w : ℕ} (h : w ∈ consumedW (bitApps d nb)) :
    d ≤ w ∧ w < eB d nb := by
  rw [bit_consumed] at h
  obtain ⟨i, hi, hw⟩ := List.mem_flatMap.mp h
  have hi' := List.mem_range.mp hi
  unfold eB
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  omega

theorem comb_produced_bounds {w : ℕ}
    (h : w ∈ producedW (combApps d nb Es)) :
    eB d nb ≤ w ∧ w < gB d nb Es := by
  rw [comb_produced] at h
  obtain ⟨s, hs, hw⟩ := List.mem_flatMap.mp h
  have hb := many_tapOf_bounds Es (eB d nb) s w hw
  exact hb

theorem comb_consumed_bounds {w : ℕ}
    (h : w ∈ consumedW (combApps d nb Es)) :
    w < eB d nb := by
  rw [comb_consumed] at h
  obtain ⟨s, hs, hw⟩ := List.mem_flatMap.mp h
  have hw' := List.mem_singleton.mp hw
  subst hw'
  have hs' := List.mem_range.mp hs
  unfold srcW eB
  by_cases hlt : s < d
  · rw [if_pos hlt]; omega
  · rw [if_neg hlt]; omega

theorem station_produced_bounds {w : ℕ}
    (h : w ∈ producedW (M d nb Es).apps) :
    eB d nb ≤ w ∧ w < gB d nb Es :=
  many_produced_bounds Es (eB d nb) w h

theorem station_consumed_bounds {w : ℕ}
    (h : w ∈ consumedW (M d nb Es).apps) :
    eB d nb ≤ w ∧ w < gB d nb Es :=
  many_consumed_bounds Es (eB d nb) w h

theorem guard_produced_bounds {w : ℕ}
    (h : w ∈ producedW (guardApps d nb Es K)) :
    gB d nb Es ≤ w ∧ w < gB d nb Es + 2 * K := by
  rw [guard_produced] at h
  obtain ⟨r, hr, hw⟩ := List.mem_flatMap.mp h
  have hr' := List.mem_range.mp hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  omega

theorem guard_consumed_bounds (hK : K ≤ Es.length) {w : ℕ}
    (h : w ∈ consumedW (guardApps d nb Es K)) :
    (w ∈ (M d nb Es).outs ∧ eB d nb ≤ w ∧ w < gB d nb Es) ∨
      (gB d nb Es ≤ w ∧ w < gB d nb Es + 2 * K ∧
       (w - gB d nb Es) % 2 = 0) := by
  rw [guard_consumed] at h
  obtain ⟨r, hr, hw⟩ := List.mem_flatMap.mp h
  have hr' := List.mem_range.mp hr
  rcases List.mem_cons.mp hw with rfl | hw'
  · left
    have hlen : r < (M d nb Es).outs.length := by
      unfold M
      rw [many_outs_length]; omega
    have hget : (M d nb Es).outs.getD r 0 = (M d nb Es).outs[r]'hlen := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
      rfl
    rw [hget]
    refine ⟨List.getElem_mem _, ?_⟩
    exact many_outs_bounds Es (eB d nb) _ (List.getElem_mem _)
  · have hw'' := List.mem_singleton.mp hw'
    subst hw''
    right
    refine ⟨by omega, by omega, by omega⟩

/-! ## Linearity -/

theorem master_produced_nodup :
    (producedW (masterApps d nb Es K)).Nodup := by
  have hgeB : eB d nb ≤ gB d nb Es := many_le Es (eB d nb)
  have hgBeq : gB d nb Es = (compileMany Es (eB d nb)).next := rfl
  have heBeq : eB d nb = d + 5 * nb := rfl
  unfold masterApps
  rw [producedW_append, producedW_append, producedW_append]
  refine nodup_append_nat (nodup_append_nat (nodup_append_nat
    ?bits ?combs ?bc) ?station ?bcs) ?guards ?all
  case bits =>
    rw [bit_produced]
    refine nodup_flatMap_nat (List.nodup_range) ?_ ?_
    · intro i hi
      refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
        List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
          List.nodup_singleton _⟩⟩⟩⟩ <;>
        · intro hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          omega
    · intro a ha b hb hne w hw hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw hw'
      omega
  case combs =>
    rw [comb_produced]
    refine nodup_flatMap_nat (List.nodup_range)
      (fun s hs => many_tapOf_nodup Es (eB d nb) s) ?_
    intro a ha b hb hne w hw
    exact many_tapOf_src_ne Es (eB d nb) hne w hw
  case bc =>
    intro w hw w' hw' he
    subst he
    obtain ⟨h1, h2⟩ := bit_produced_bounds d nb hw
    obtain ⟨h3, h4⟩ := comb_produced_bounds d nb Es hw'
    omega
  case station => exact many_produced_nodup Es (eB d nb)
  case bcs =>
    intro w hw w' hw' he
    subst he
    rcases List.mem_append.mp hw with hm | hm
    · obtain ⟨h1, h2⟩ := bit_produced_bounds d nb hm
      obtain ⟨h3, h4⟩ := station_produced_bounds d nb Es hw'
      omega
    · -- a comb output is a tap wire, never produced by a station
      rw [comb_produced] at hm
      obtain ⟨s, hs, hwm⟩ := List.mem_flatMap.mp hm
      exact many_tapOf_not_produced Es (eB d nb) s w hwm hw'
  case guards =>
    rw [guard_produced]
    refine nodup_flatMap_nat (List.nodup_range) ?_ ?_
    · intro r hr
      refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
      intro hmem
      have := List.mem_singleton.mp hmem
      omega
    · intro a ha b hb hne w hw hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw hw'
      omega
  case all =>
    intro w hw w' hw' he
    subst he
    obtain ⟨h1, h2⟩ := guard_produced_bounds d nb Es K hw'
    rcases List.mem_append.mp hw with hm | hm
    · rcases List.mem_append.mp hm with hm' | hm'
      · obtain ⟨h3, h4⟩ := bit_produced_bounds d nb hm'
        omega
      · obtain ⟨h3, h4⟩ := comb_produced_bounds d nb Es hm'
        omega
    · obtain ⟨h3, h4⟩ := station_produced_bounds d nb Es hm
      omega

theorem srcW_inj {s s' : ℕ} (hs : s < d + nb) (hs' : s' < d + nb)
    (hne : s ≠ s') : srcW d s ≠ srcW d s' := by
  unfold srcW
  by_cases h1 : s < d <;> by_cases h2 : s' < d
  · rw [if_pos h1, if_pos h2]; omega
  · rw [if_pos h1, if_neg h2]; omega
  · rw [if_neg h1, if_pos h2]; omega
  · rw [if_neg h1, if_neg h2]; omega

theorem master_consumed_nodup (hK : K ≤ Es.length) :
    (consumedW (masterApps d nb Es K)).Nodup := by
  have hgeB : eB d nb ≤ gB d nb Es := many_le Es (eB d nb)
  have houtnd := many_outs_nodup Es (eB d nb)
  have hgBeq : gB d nb Es = (compileMany Es (eB d nb)).next := rfl
  have heBeq : eB d nb = d + 5 * nb := rfl
  unfold masterApps
  rw [consumedW_append, consumedW_append, consumedW_append]
  refine nodup_append_nat (nodup_append_nat (nodup_append_nat
    ?bits ?combs ?bc) ?station ?bcs) ?guards ?all
  case bits =>
    rw [bit_consumed]
    refine nodup_flatMap_nat (List.nodup_range) ?_ ?_
    · intro i hi
      refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
        List.nodup_singleton _⟩⟩ <;>
        · intro hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          omega
    · intro a ha b hb hne w hw hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw hw'
      omega
  case combs =>
    rw [comb_consumed]
    refine nodup_flatMap_nat (List.nodup_range) ?_ ?_
    · intro s hs
      exact List.nodup_singleton _
    · intro a ha b hb hne w hw hw'
      have h1 := List.mem_singleton.mp hw
      have h2 := List.mem_singleton.mp hw'
      subst h1
      exact srcW_inj d nb (List.mem_range.mp ha) (List.mem_range.mp hb)
        hne h2
  case bc =>
    intro w hw w' hw' he
    subst he
    rw [comb_consumed] at hw'
    obtain ⟨s, hs, hww⟩ := List.mem_flatMap.mp hw'
    have hww' := List.mem_singleton.mp hww
    have hs' := List.mem_range.mp hs
    rw [bit_consumed] at hw
    obtain ⟨i, hi, hwm⟩ := List.mem_flatMap.mp hw
    have hi' := List.mem_range.mp hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
    unfold srcW at hww'
    by_cases hlt : s < d
    · rw [if_pos hlt] at hww'
      omega
    · rw [if_neg hlt] at hww'
      omega
  case station => exact many_consumed_nodup Es (eB d nb)
  case bcs =>
    intro w hw w' hw' he
    subst he
    obtain ⟨h3, h4⟩ := station_consumed_bounds d nb Es hw'
    rcases List.mem_append.mp hw with hm | hm
    · obtain ⟨h1, h2⟩ := bit_consumed_bounds d nb hm
      omega
    · have h1 := comb_consumed_bounds d nb Es hm
      omega
  case guards =>
    rw [guard_consumed]
    refine nodup_flatMap_nat (List.nodup_range) ?_ ?_
    · intro r hr
      refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
      intro hmem
      have hh := List.mem_singleton.mp hmem
      have hr' := List.mem_range.mp hr
      have hlen : r < (M d nb Es).outs.length := by
        unfold M
        rw [many_outs_length]; omega
      have hget : (M d nb Es).outs.getD r 0
          = (M d nb Es).outs[r]'hlen := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
        rfl
      rw [hget] at hh
      obtain ⟨h5, h6⟩ := many_outs_bounds Es (eB d nb) _
        (hh ▸ List.getElem_mem hlen)
      omega
    · intro a ha b hb hne w hw hw'
      have ha' := List.mem_range.mp ha
      have hb' := List.mem_range.mp hb
      have hla : a < (M d nb Es).outs.length := by
        unfold M
        rw [many_outs_length]; omega
      have hlb : b < (M d nb Es).outs.length := by
        unfold M
        rw [many_outs_length]; omega
      have hgeta : (M d nb Es).outs.getD a 0
          = (M d nb Es).outs[a]'hla := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hla]
        rfl
      have hgetb : (M d nb Es).outs.getD b 0
          = (M d nb Es).outs[b]'hlb := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlb]
        rfl
      rcases List.mem_cons.mp hw with rfl | hw₂
      · rcases List.mem_cons.mp hw' with he | hmem'
        · rw [hgeta, hgetb] at he
          exact hne (List.Nodup.getElem_inj_iff houtnd |>.mp he)
        · have hh := List.mem_singleton.mp hmem'
          rw [hgeta] at hh
          obtain ⟨h5, h6⟩ := many_outs_bounds Es (eB d nb) _
            (hh ▸ List.getElem_mem hla)
          omega
      · have hw₃ := List.mem_singleton.mp hw₂
        subst hw₃
        rcases List.mem_cons.mp hw' with he | hmem'
        · rw [hgetb] at he
          obtain ⟨h5, h6⟩ := many_outs_bounds Es (eB d nb) _
            (he.symm ▸ List.getElem_mem hlb)
          omega
        · have hh := List.mem_singleton.mp hmem'
          omega
  case all =>
    intro w hw w' hw' he
    subst he
    rcases guard_consumed_bounds d nb Es K hK hw' with
        ⟨hmem, h1, h2⟩ | ⟨h1, h2, h3⟩
    · rcases List.mem_append.mp hw with hm | hm
      · rcases List.mem_append.mp hm with hm' | hm'
        · obtain ⟨h3, h4⟩ := bit_consumed_bounds d nb hm'
          omega
        · have h3 := comb_consumed_bounds d nb Es hm'
          omega
      · exact many_outs_not_consumed Es (eB d nb) w hmem hm
    · rcases List.mem_append.mp hw with hm | hm
      · rcases List.mem_append.mp hm with hm' | hm'
        · obtain ⟨h4, h5⟩ := bit_consumed_bounds d nb hm'
          omega
        · have h4 := comb_consumed_bounds d nb Es hm'
          omega
      · obtain ⟨h4, h5⟩ := station_consumed_bounds d nb Es hm
        omega


/-! ## Output access -/

theorem outs_getD_bounds {r : ℕ} (h : r < Es.length) :
    eB d nb ≤ (M d nb Es).outs.getD r 0 ∧
      (M d nb Es).outs.getD r 0 < gB d nb Es ∧
      (M d nb Es).outs.getD r 0 ∈ (M d nb Es).outs := by
  have hlen : r < (M d nb Es).outs.length := by
    unfold M
    rw [many_outs_length]
    exact h
  have hget : (M d nb Es).outs.getD r 0 = (M d nb Es).outs[r]'hlen := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    rfl
  rw [hget]
  have hb := many_outs_bounds Es (eB d nb) _ (List.getElem_mem hlen)
  exact ⟨hb.1, hb.2, List.getElem_mem _⟩

theorem ty_out_getD {r : ℕ} (h : r < Es.length) :
    masterTy d nb Es K ((M d nb Es).outs.getD r 0)
      = some ⟨[], Dtype.Q⟩ := by
  have hlen : r < (M d nb Es).outs.length := by
    unfold M
    rw [many_outs_length]
    exact h
  have hget : (M d nb Es).outs.getD r 0 = (M d nb Es).outs[r]'hlen := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    rfl
  rw [hget]
  exact ty_M d nb Es K
    (many_ty_out Es (eB d nb) _ (List.getElem_mem hlen))

theorem M_outs_length : (M d nb Es).outs.length = Es.length :=
  many_outs_length Es (eB d nb)

theorem M_ty_out {o : ℕ} (h : o ∈ (M d nb Es).outs) :
    (M d nb Es).ty o = some ⟨[], Dtype.Q⟩ :=
  many_ty_out Es (eB d nb) o h

theorem M_mdl_out (vals : ℕ → ℚ) {i : ℕ} (hi : i < Es.length) :
    (M d nb Es).mdl vals ((M d nb Es).outs[i]'(by
      rw [M_outs_length]; exact hi))
      = [(Es[i]'hi).evalE vals] :=
  many_mdl_out Es (eB d nb) vals i hi

/-! ## Acyclicity -/

theorem bit_gadget_acyclic (i : ℕ) :
    Acyclic [PrimApp.const ⟨[], Dtype.Q⟩ (qv0 0) (d + 5 * i),
      .reshape [1] (d + 5 * i) (d + 5 * i + 1),
      .cell sigmaPM (d + 5 * i + 1) [d + 5 * i + 2, d + 5 * i + 3],
      .cast Dtype.B Dtype.Q .exact [] (d + 5 * i + 3) (d + 5 * i + 4)] := by
  show Acyclic ([PrimApp.const ⟨[], Dtype.Q⟩ (qv0 0) (d + 5 * i)] ++
    ([.reshape [1] (d + 5 * i) (d + 5 * i + 1)] ++
      ([.cell sigmaPM (d + 5 * i + 1) [d + 5 * i + 2, d + 5 * i + 3]] ++
        [.cast Dtype.B Dtype.Q .exact [] (d + 5 * i + 3)
          (d + 5 * i + 4)])))
  refine acyclic_append_nat (acyclic_single (fun w hw => nomatch hw)) ?_ ?_
  · refine acyclic_append_nat (acyclic_single ?_) ?_ ?_
    · intro w hw hmem
      have h1 := List.mem_singleton.mp hw
      have h2 := List.mem_singleton.mp hmem
      omega
    · refine acyclic_append_nat (acyclic_single ?_) (acyclic_single ?_) ?_
      · intro w hw hmem
        have h1 := List.mem_singleton.mp hw
        rcases List.mem_cons.mp hmem with h2 | h2
        · omega
        · have h3 := List.mem_singleton.mp h2
          omega
      · intro w hw hmem
        have h1 := List.mem_singleton.mp hw
        have h2 := List.mem_singleton.mp hmem
        omega
      · intro w hw hw'
        have h1 := List.mem_singleton.mp (mem_consumedW_single.mp hw)
        have h2 := List.mem_singleton.mp (mem_producedW_single.mp hw')
        omega
    · intro w hw hw'
      have h1 := List.mem_singleton.mp (mem_consumedW_single.mp hw)
      rw [producedW_append] at hw'
      rcases List.mem_append.mp hw' with hm | hm
      · rcases List.mem_cons.mp (mem_producedW_single.mp hm) with h2 | h2
        · omega
        · have h3 := List.mem_singleton.mp h2
          omega
      · have h2 := List.mem_singleton.mp (mem_producedW_single.mp hm)
        omega
  · intro w hw hw'
    exact nomatch hw

theorem master_acyclic (hK : K ≤ Es.length) :
    Acyclic (masterApps d nb Es K) := by
  have hgeB : eB d nb ≤ gB d nb Es := many_le Es (eB d nb)
  have hgBeq : gB d nb Es = (compileMany Es (eB d nb)).next := rfl
  have heBeq : eB d nb = d + 5 * nb := rfl
  unfold masterApps
  refine acyclic_append_nat (acyclic_append_nat (acyclic_append_nat
    ?bits ?combs ?crossBC) ?station ?crossBCM) ?guards ?crossAll
  case bits =>
    unfold bitApps
    refine acyclic_flatMap_nat (List.nodup_range)
      (fun i _ => bit_gadget_acyclic d i) ?_
    intro a ha b hb hne w hw hw'
    have ha' := List.mem_range.mp ha
    have hb' := List.mem_range.mp hb
    have hcw : consumedW [PrimApp.const ⟨[], Dtype.Q⟩ (qv0 0) (d + 5 * a),
        .reshape [1] (d + 5 * a) (d + 5 * a + 1),
        .cell sigmaPM (d + 5 * a + 1) [d + 5 * a + 2, d + 5 * a + 3],
        .cast Dtype.B Dtype.Q .exact [] (d + 5 * a + 3) (d + 5 * a + 4)]
        = [d + 5 * a, d + 5 * a + 1, d + 5 * a + 3] := rfl
    have hpw : producedW [PrimApp.const ⟨[], Dtype.Q⟩ (qv0 0) (d + 5 * b),
        .reshape [1] (d + 5 * b) (d + 5 * b + 1),
        .cell sigmaPM (d + 5 * b + 1) [d + 5 * b + 2, d + 5 * b + 3],
        .cast Dtype.B Dtype.Q .exact [] (d + 5 * b + 3) (d + 5 * b + 4)]
        = [d + 5 * b, d + 5 * b + 1, d + 5 * b + 2, d + 5 * b + 3,
           d + 5 * b + 4] := rfl
    rw [hcw] at hw
    rw [hpw] at hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw hw'
    omega
  case combs =>
    unfold combApps
    rw [map_eq_flatMap_single]
    refine acyclic_flatMap_nat (List.nodup_range) ?_ ?_
    · intro s hs
      refine acyclic_single ?_
      intro w hw hmem
      have h1 := List.mem_singleton.mp hw
      subst h1
      have hb := many_tapOf_bounds Es (eB d nb) s _ hmem
      unfold srcW at hb
      by_cases hlt : s < d
      · rw [if_pos hlt] at hb
        omega
      · rw [if_neg hlt] at hb
        have hs' := List.mem_range.mp hs
        omega
    · intro a ha b hb hne w hw hw'
      have h1 := List.mem_singleton.mp (mem_consumedW_single.mp hw)
      subst h1
      have h2 := mem_producedW_single.mp hw'
      have hbnd := many_tapOf_bounds Es (eB d nb) b _ h2
      unfold srcW at hbnd
      by_cases hlt : a < d
      · rw [if_pos hlt] at hbnd
        omega
      · rw [if_neg hlt] at hbnd
        have ha' := List.mem_range.mp ha
        omega
  case crossBC =>
    intro w hw hw'
    have h1 := bit_consumed_bounds d nb hw
    have h2 := comb_produced_bounds d nb Es hw'
    omega
  case station => exact many_acyclic Es (eB d nb)
  case crossBCM =>
    intro w hw hw'
    have h2 := station_produced_bounds d nb Es hw'
    rw [consumedW_append] at hw
    rcases List.mem_append.mp hw with hm | hm
    · have h1 := bit_consumed_bounds d nb hm
      omega
    · have h1 := comb_consumed_bounds d nb Es hm
      omega
  case guards =>
    unfold guardApps
    refine acyclic_flatMap_nat (List.nodup_range) ?_ ?_
    · intro r hr
      have hr' := List.mem_range.mp hr
      obtain ⟨ho1, ho2, ho3⟩ := outs_getD_bounds d nb Es
        (show r < Es.length by omega)
      show Acyclic ([PrimApp.reshape [1] ((M d nb Es).outs.getD r 0)
          (gB d nb Es + 2 * r)] ++
        [.cell sigmaNN (gB d nb Es + 2 * r) [gB d nb Es + 2 * r + 1]])
      refine acyclic_append_nat (acyclic_single ?_) (acyclic_single ?_) ?_
      · intro w hw hmem
        have h1 := List.mem_singleton.mp hw
        have h2 := List.mem_singleton.mp hmem
        omega
      · intro w hw hmem
        have h1 := List.mem_singleton.mp hw
        have h2 := List.mem_singleton.mp hmem
        omega
      · intro w hw hw'
        have h1 := List.mem_singleton.mp (mem_consumedW_single.mp hw)
        have h2 := List.mem_singleton.mp (mem_producedW_single.mp hw')
        omega
    · intro a ha b hb hne w hw hw'
      have ha' := List.mem_range.mp ha
      have hb' := List.mem_range.mp hb
      obtain ⟨hoa1, hoa2, hoa3⟩ := outs_getD_bounds d nb Es
        (show a < Es.length by omega)
      have hcw : consumedW [PrimApp.reshape [1]
          ((M d nb Es).outs.getD a 0) (gB d nb Es + 2 * a),
          .cell sigmaNN (gB d nb Es + 2 * a) [gB d nb Es + 2 * a + 1]]
          = [(M d nb Es).outs.getD a 0, gB d nb Es + 2 * a] := rfl
      have hpw : producedW [PrimApp.reshape [1]
          ((M d nb Es).outs.getD b 0) (gB d nb Es + 2 * b),
          .cell sigmaNN (gB d nb Es + 2 * b) [gB d nb Es + 2 * b + 1]]
          = [gB d nb Es + 2 * b, gB d nb Es + 2 * b + 1] := rfl
      rw [hcw] at hw
      rw [hpw] at hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw hw'
      omega
  case crossAll =>
    intro w hw hw'
    have h2 := guard_produced_bounds d nb Es K hw'
    rw [consumedW_append, consumedW_append] at hw
    rcases List.mem_append.mp hw with hm | hm
    · rcases List.mem_append.mp hm with hm' | hm'
      · have h1 := bit_consumed_bounds d nb hm'
        omega
      · have h1 := comb_consumed_bounds d nb Es hm'
        omega
    · have h1 := station_consumed_bounds d nb Es hm
      omega

/-! ## Type consistency -/

theorem master_tc (hK : K ≤ Es.length) :
    TypeConsistentAll (masterTy d nb Es K) (masterApps d nb Es K) := by
  intro a ha
  unfold masterApps at ha
  rcases List.mem_append.mp ha with h1 | hguard
  · rcases List.mem_append.mp h1 with h2 | hM
    · rcases List.mem_append.mp h2 with hbit | hcomb
      · unfold bitApps at hbit
        rw [List.mem_flatMap] at hbit
        obtain ⟨i, hi, hmem⟩ := hbit
        have hi' := List.mem_range.mp hi
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact tcConstQ 0 (ty_z d nb Es K hi')
        · rcases List.mem_cons.mp hmem with rfl | hmem
          · exact tcReshape01 (ty_z d nb Es K hi') (ty_z' d nb Es K hi')
          · rcases List.mem_cons.mp hmem with rfl | hmem
            · exact tcCellPM (ty_z' d nb Es K hi') (ty_b0 d nb Es K hi')
                (ty_b1 d nb Es K hi')
            · have h4 := List.mem_singleton.mp hmem
              subst h4
              exact tcCastBQ (ty_b1 d nb Es K hi') (ty_b d nb Es K hi')
      · unfold combApps at hcomb
        rw [List.mem_map] at hcomb
        obtain ⟨s, hs, rfl⟩ := hcomb
        have hs' := List.mem_range.mp hs
        exact tcCopyQ (ty_srcW d nb Es K hs')
          (fun o ho => ty_tapOf d nb Es K ho)
    · exact many_tc Es (eB d nb)
        (fun w τ h => ty_M d nb Es K h) a hM
  · unfold guardApps at hguard
    rw [List.mem_flatMap] at hguard
    obtain ⟨r, hr, hmem⟩ := hguard
    have hr' := List.mem_range.mp hr
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact tcReshape01 (ty_out_getD d nb Es K (by omega))
        (ty_guard_s d nb Es K hr')
    · have h2 := List.mem_singleton.mp hmem
      subst h2
      exact tcCellNN (ty_guard_s d nb Es K hr') (ty_guard_g d nb Es K hr')

/-! ## The master hypernet -/

def masterH (hK : K ≤ Es.length) : Hypernet where
  wireType := masterTy d nb Es K
  applications := masterApps d nb Es K
  linearity := ⟨master_consumed_nodup d nb Es K hK,
    master_produced_nodup d nb Es K⟩
  acyclic := master_acyclic d nb Es K hK
  typeConsistent := master_tc d nb Es K hK

theorem masterH_tenBox (hK : K ≤ Es.length) :
    (masterH d nb Es K hK).TenBoxOnly :=
  fun a ha => (master_fragment d nb Es K a ha).1

theorem masterH_exactBQ (hK : K ≤ Es.length) :
    (masterH d nb Es K hK).ExactBQ :=
  fun a ha => (master_fragment d nb Es K a ha).2

theorem masterH_port_in (hK : K ≤ Es.length) {w : ℕ} (h : w < d) :
    (masterH d nb Es K hK).ScalarQPort w :=
  ⟨⟨[], Dtype.Q⟩, ty_port d nb Es K h, rfl, rfl⟩

theorem masterH_port_out (hK : K ≤ Es.length) {r : ℕ}
    (h : r < Es.length) :
    (masterH d nb Es K hK).ScalarQPort ((M d nb Es).outs.getD r 0) :=
  ⟨⟨[], Dtype.Q⟩, ty_out_getD d nb Es K h, rfl, rfl⟩


/-! ## Table valuations -/

theorem valueSet_fin {δ : Dtype} {q : ℚ}
    (h1 : δ.kind.MemK q) (h2 : δ.sign = .nn → 0 ≤ q) :
    δ.ValueSet (.fin q) := by
  simp only [Dtype.ValueSet]
  exact ⟨h1, h2⟩

/-- Build a valuation from a table of rational entry lists. -/
def mkVal (H : Hypernet) (g : ℕ → List ℚ)
    (hg : ∀ w τ, H.wireType w = some τ →
      (g w).length = τ.shape.totalSize ∧
      ∀ q ∈ g w, τ.dtype.kind.MemK q ∧ (τ.dtype.sign = .nn → 0 ≤ q)) :
    H.Valuation := fun w τ h =>
  ⟨(g w).attach.map (fun p =>
      (⟨.fin p.val, valueSet_fin ((hg w τ h).2 p.val p.property).1
        ((hg w τ h).2 p.val p.property).2⟩ : τ.dtype.carrier)),
   by rw [List.length_map, List.length_attach]; exact (hg w τ h).1⟩

theorem mkVal_reads (H : Hypernet) (g : ℕ → List ℚ)
    (hg : ∀ w τ, H.wireType w = some τ →
      (g w).length = τ.shape.totalSize ∧
      ∀ q ∈ g w, τ.dtype.kind.MemK q ∧ (τ.dtype.sign = .nn → 0 ≤ q))
    {w : ℕ} {τ : TensorType} (h : H.wireType w = some τ) (i : ℕ) :
    (mkVal H g hg).entryFlat w i = ((g w)[i]?).map ERat.fin := by
  rw [Hypernet.Valuation.entryFlat_some _ h]
  show ((((g w).attach.map _)[i]?).map Subtype.val) = _
  rcases Nat.lt_or_ge i (g w).length with hi | hi
  · rw [List.getElem?_eq_getElem (by
      rw [List.length_map, List.length_attach]; exact hi),
      List.getElem?_eq_getElem hi]
    rw [List.getElem_map]
    simp [List.getElem_attach]
  · rw [List.getElem?_eq_none (by
      rw [List.length_map, List.length_attach]; exact hi),
      List.getElem?_eq_none hi]
    rfl

/-! ## The master model -/

/-- Source values from port values and bit values. -/
def valsOfXB (x : Fin d → ℚ) (bv : ℕ → ℚ) : ℕ → ℚ :=
  fun s => if h : s < d then x ⟨s, h⟩ else bv (s - d)

/-- The master model: entries of every wire under given port and bit
values.  Bits follow the indicator pattern; stations carry the station
model; guards carry the guarded value and the fired indicator. -/
def gm (x : Fin d → ℚ) (bv : ℕ → ℚ) : ℕ → List ℚ := fun w =>
  if h : w < d then [x ⟨w, h⟩]
  else if w < eB d nb then
    (if (w - d) % 5 = 1 then [0]
     else if (w - d) % 5 = 2 then [1 - bv ((w - d) / 5)]
     else if (w - d) % 5 = 3 then [bv ((w - d) / 5)]
     else if (w - d) % 5 = 4 then [bv ((w - d) / 5)]
     else [0])
  else if ((M d nb Es).ty w).isSome then
    (M d nb Es).mdl (valsOfXB d x bv) w
  else if (w - gB d nb Es) % 2 = 0 then
    [(Es.getD ((w - gB d nb Es) / 2) (.qconst 0)).evalE
      (valsOfXB d x bv)]
  else [1]

theorem gm_wf (x : Fin d → ℚ) (bv : ℕ → ℚ)
    (hbv : ∀ i, bv i = 0 ∨ bv i = 1) :
    ∀ w τ, masterTy d nb Es K w = some τ →
      (gm d nb Es x bv w).length = τ.shape.totalSize ∧
      ∀ q ∈ gm d nb Es x bv w, τ.dtype.kind.MemK q ∧
        (τ.dtype.sign = .nn → 0 ≤ q) := by
  intro w τ hτ
  unfold masterTy at hτ
  unfold gm
  by_cases h1 : w < d
  · rw [if_pos h1] at hτ
    obtain rfl : (⟨[], Dtype.Q⟩ : TensorType) = τ := Option.some.inj hτ
    rw [dif_pos h1]
    refine ⟨rfl, ?_⟩
    intro q hq
    exact ⟨trivial, fun h => nomatch h⟩
  · rw [if_neg h1] at hτ
    rw [dif_neg h1]
    by_cases h2 : w < eB d nb
    · rw [if_pos h2] at hτ
      rw [if_pos h2]
      unfold bitTy at hτ
      by_cases h3 : (w - d) % 5 = 1
      · rw [if_pos h3] at hτ ⊢
        obtain rfl : (⟨[1], Dtype.Q⟩ : TensorType) = τ := Option.some.inj hτ
        refine ⟨rfl, ?_⟩
        intro q hq
        exact ⟨trivial, fun h => nomatch h⟩
      · rw [if_neg h3] at hτ ⊢
        by_cases h4 : (w - d) % 5 = 2
        · rw [if_pos h4] at hτ ⊢
          obtain rfl : (⟨[], Dtype.B⟩ : TensorType) = τ :=
            Option.some.inj hτ
          refine ⟨rfl, ?_⟩
          intro q hq
          have hq' := List.mem_singleton.mp hq
          subst hq'
          rcases hbv ((w - d) / 5) with hb | hb <;> rw [hb]
          · exact ⟨Or.inr (by norm_num), fun _ => by norm_num⟩
          · exact ⟨Or.inl (by norm_num), fun _ => by norm_num⟩
        · rw [if_neg h4] at hτ ⊢
          by_cases h5 : (w - d) % 5 = 3
          · rw [if_pos h5] at hτ ⊢
            obtain rfl : (⟨[], Dtype.B⟩ : TensorType) = τ :=
              Option.some.inj hτ
            refine ⟨rfl, ?_⟩
            intro q hq
            have hq' := List.mem_singleton.mp hq
            subst hq'
            rcases hbv ((w - d) / 5) with hb | hb <;> rw [hb]
            · exact ⟨Or.inl rfl, fun _ => by norm_num⟩
            · exact ⟨Or.inr rfl, fun _ => by norm_num⟩
          · rw [if_neg h5] at hτ ⊢
            obtain rfl : (⟨[], Dtype.Q⟩ : TensorType) = τ :=
              Option.some.inj hτ
            by_cases h6 : (w - d) % 5 = 4
            · rw [if_pos h6]
              refine ⟨rfl, ?_⟩
              intro q hq
              exact ⟨trivial, fun h => nomatch h⟩
            · rw [if_neg h6]
              refine ⟨rfl, ?_⟩
              intro q hq
              exact ⟨trivial, fun h => nomatch h⟩
    · rw [if_neg h2] at hτ
      rw [if_neg h2]
      rcases mergeWt_cases hτ with hM | hG
      · rw [if_pos (by rw [hM]; rfl)]
        obtain ⟨hdt, hlen⟩ := many_mdl_wf Es (eB d nb)
          (valsOfXB d x bv) hM
        refine ⟨hlen, ?_⟩
        intro q hq
        rw [hdt]
        exact ⟨trivial, fun h => nomatch h⟩
      · unfold guardTy at hG
        by_cases h3 : gB d nb Es ≤ w ∧ w < gB d nb Es + 2 * K
        · rw [if_pos h3] at hG
          have hMnone : (M d nb Es).ty w = none :=
            many_ty_none Es (eB d nb) (Or.inr h3.1)
          rw [if_neg (by rw [hMnone]; simp)]
          by_cases h4 : (w - gB d nb Es) % 2 = 0
          · rw [if_pos h4] at hG ⊢
            obtain rfl : (⟨[1], Dtype.Q⟩ : TensorType) = τ :=
              Option.some.inj hG
            refine ⟨rfl, ?_⟩
            intro q hq
            exact ⟨trivial, fun h => nomatch h⟩
          · rw [if_neg h4] at hG ⊢
            obtain rfl : (⟨[], Dtype.B⟩ : TensorType) = τ :=
              Option.some.inj hG
            refine ⟨rfl, ?_⟩
            intro q hq
            have hq' := List.mem_singleton.mp hq
            subst hq'
            exact ⟨Or.inr rfl, fun _ => by norm_num⟩
        · rw [if_neg h3] at hG
          exact nomatch hG

/-! ## Membership of the block applications -/

theorem mem_master_bit {a : PrimApp} (h : a ∈ bitApps d nb) :
    a ∈ masterApps d nb Es K := by
  unfold masterApps
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ h))

theorem mem_master_comb {a : PrimApp} (h : a ∈ combApps d nb Es) :
    a ∈ masterApps d nb Es K := by
  unfold masterApps
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ h))

theorem mem_master_M {a : PrimApp} (h : a ∈ (M d nb Es).apps) :
    a ∈ masterApps d nb Es K := by
  unfold masterApps
  exact List.mem_append_left _ (List.mem_append_right _ h)

theorem mem_master_guard {a : PrimApp} (h : a ∈ guardApps d nb Es K) :
    a ∈ masterApps d nb Es K := by
  unfold masterApps
  exact List.mem_append_right _ h

theorem mem_bit_const {i : ℕ} (h : i < nb) :
    PrimApp.const ⟨[], Dtype.Q⟩ (qv0 0) (d + 5 * i) ∈ bitApps d nb := by
  unfold bitApps
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr h,
    List.mem_cons_self⟩

theorem mem_bit_reshape {i : ℕ} (h : i < nb) :
    PrimApp.reshape [1] (d + 5 * i) (d + 5 * i + 1) ∈ bitApps d nb := by
  unfold bitApps
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr h,
    List.mem_cons_of_mem _ List.mem_cons_self⟩

theorem mem_bit_cell {i : ℕ} (h : i < nb) :
    PrimApp.cell sigmaPM (d + 5 * i + 1)
      [d + 5 * i + 2, d + 5 * i + 3] ∈ bitApps d nb := by
  unfold bitApps
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr h,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

theorem mem_bit_cast {i : ℕ} (h : i < nb) :
    PrimApp.cast Dtype.B Dtype.Q .exact [] (d + 5 * i + 3)
      (d + 5 * i + 4) ∈ bitApps d nb := by
  unfold bitApps
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr h,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))⟩

theorem mem_comb {s : ℕ} (h : s < d + nb) :
    PrimApp.copy ((M d nb Es).tapOf s).length (srcW d s)
      ((M d nb Es).tapOf s) ∈ combApps d nb Es := by
  unfold combApps
  exact List.mem_map.mpr ⟨s, List.mem_range.mpr h, rfl⟩

theorem mem_guard_reshape {r : ℕ} (h : r < K) :
    PrimApp.reshape [1] ((M d nb Es).outs.getD r 0)
      (gB d nb Es + 2 * r) ∈ guardApps d nb Es K := by
  unfold guardApps
  exact List.mem_flatMap.mpr ⟨r, List.mem_range.mpr h,
    List.mem_cons_self⟩

theorem mem_guard_cell {r : ℕ} (h : r < K) :
    PrimApp.cell sigmaNN (gB d nb Es + 2 * r)
      [gB d nb Es + 2 * r + 1] ∈ guardApps d nb Es K := by
  unfold guardApps
  exact List.mem_flatMap.mpr ⟨r, List.mem_range.mpr h,
    List.mem_cons_of_mem _ List.mem_cons_self⟩


/-! ## Model entry values -/

section GmValues

variable (x : Fin d → ℚ) (bv : ℕ → ℚ)

theorem gm_port {w : ℕ} (h : w < d) :
    gm d nb Es x bv w = [x ⟨w, h⟩] := by
  unfold gm
  rw [dif_pos h]

theorem gm_z {i : ℕ} (h : i < nb) :
    gm d nb Es x bv (d + 5 * i) = [0] := by
  unfold gm
  rw [dif_neg (by omega), if_pos (show d + 5 * i < eB d nb by
      unfold eB; omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

theorem gm_z' {i : ℕ} (h : i < nb) :
    gm d nb Es x bv (d + 5 * i + 1) = [0] := by
  unfold gm
  rw [dif_neg (by omega), if_pos (show d + 5 * i + 1 < eB d nb by
      unfold eB; omega),
    if_pos (by omega)]

theorem gm_b0 {i : ℕ} (h : i < nb) :
    gm d nb Es x bv (d + 5 * i + 2) = [1 - bv i] := by
  unfold gm
  rw [dif_neg (by omega), if_pos (show d + 5 * i + 2 < eB d nb by
      unfold eB; omega),
    if_neg (by omega), if_pos (by omega),
    show (d + 5 * i + 2 - d) / 5 = i by omega]

theorem gm_b1 {i : ℕ} (h : i < nb) :
    gm d nb Es x bv (d + 5 * i + 3) = [bv i] := by
  unfold gm
  rw [dif_neg (by omega), if_pos (show d + 5 * i + 3 < eB d nb by
      unfold eB; omega),
    if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show (d + 5 * i + 3 - d) / 5 = i by omega]

theorem gm_b {i : ℕ} (h : i < nb) :
    gm d nb Es x bv (d + 5 * i + 4) = [bv i] := by
  unfold gm
  rw [dif_neg (by omega), if_pos (show d + 5 * i + 4 < eB d nb by
      unfold eB; omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega),
    show (d + 5 * i + 4 - d) / 5 = i by omega]

theorem gm_station {w : ℕ} (hs : ((M d nb Es).ty w).isSome = true) :
    gm d nb Es x bv w = (M d nb Es).mdl (valsOfXB d x bv) w := by
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨h1, h2⟩ := many_ty_domain Es (eB d nb) hτ
  have heB : eB d nb = d + 5 * nb := rfl
  unfold gm
  rw [dif_neg (by omega), if_neg (by omega), if_pos hs]

theorem gm_guard_s {r : ℕ} (h : r < K) (hK : K ≤ Es.length) :
    gm d nb Es x bv (gB d nb Es + 2 * r)
      = [(Es.getD r (.qconst 0)).evalE (valsOfXB d x bv)] := by
  have hgeB : eB d nb ≤ gB d nb Es := many_le Es (eB d nb)
  have heB : eB d nb = d + 5 * nb := rfl
  have hMnone : (M d nb Es).ty (gB d nb Es + 2 * r) = none :=
    many_ty_none Es (eB d nb) (Or.inr (by
      show gB d nb Es ≤ gB d nb Es + 2 * r
      omega))
  unfold gm
  rw [dif_neg (by omega), if_neg (by omega),
    if_neg (by rw [hMnone]; simp),
    if_pos (show (gB d nb Es + 2 * r - gB d nb Es) % 2 = 0 by omega),
    show (gB d nb Es + 2 * r - gB d nb Es) / 2 = r by omega]

theorem gm_guard_g {r : ℕ} (h : r < K) (hK : K ≤ Es.length) :
    gm d nb Es x bv (gB d nb Es + 2 * r + 1) = [1] := by
  have hgeB : eB d nb ≤ gB d nb Es := many_le Es (eB d nb)
  have heB : eB d nb = d + 5 * nb := rfl
  have hMnone : (M d nb Es).ty (gB d nb Es + 2 * r + 1) = none :=
    many_ty_none Es (eB d nb) (Or.inr (by
      show gB d nb Es ≤ gB d nb Es + 2 * r + 1
      omega))
  unfold gm
  rw [dif_neg (by omega), if_neg (by omega),
    if_neg (by rw [hMnone]; simp),
    if_neg (show ¬((gB d nb Es + 2 * r + 1 - gB d nb Es) % 2 = 0) by
      omega)]

end GmValues

/-! ## The interface denotation of the master net -/

theorem master_denot_mp (hK : K ≤ Es.length) {m : ℕ}
    (hm : K + m = Es.length)
    (hsrcb : ∀ E ∈ Es, ∀ s ∈ E.taps, s < d + nb)
    (x : Fin d → ℚ) (y : Fin m → ℚ)
    (σ : (masterH d nb Es K hK).Valuation)
    (hadm : σ.Admissible)
    (hin : ∀ i : Fin d, σ.entryFlat i.val 0 = some (.fin (x i)))
    (hout : ∀ j : Fin m,
      σ.entryFlat ((M d nb Es).outs.getD (K + j.val) 0) 0
        = some (.fin (y j))) :
    ∃ bv : ℕ → ℚ, (∀ i, bv i = 0 ∨ bv i = 1) ∧
      (∀ r, (hr : r < K) →
        0 ≤ (Es[r]'(by omega)).evalE (valsOfXB d x bv)) ∧
      (∀ j : Fin m,
        y j = (Es[K + j.val]'(by omega)).evalE (valsOfXB d x bv)) := by
  classical
  have hbit : ∀ i : ℕ, i < nb → ∃ b : ℚ, (b = 0 ∨ b = 1) ∧
      σ.entryFlat (d + 5 * i + 4) 0 = some (.fin b) := by
    intro i hi
    have hz := (const_scalarQ_semOk_iff σ (ty_z d nb Es K hi) 0).mp
      (hadm _ (mem_master_bit d nb Es K (mem_bit_const d nb hi)))
    have hz' := (reshape_scalar_semOk_iff σ (ty_z d nb Es K hi)
      (ty_z' d nb Es K hi) hz).mp
      (hadm _ (mem_master_bit d nb Es K (mem_bit_reshape d nb hi)))
    have hcell := (cell_freeBit_semOk_iff σ (ty_z' d nb Es K hi) hz').mp
      (hadm _ (mem_master_bit d nb Es K (mem_bit_cell d nb hi)))
    rcases hcell with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact ⟨0, Or.inl rfl, (cast_BQ_semOk_iff σ h1).mp
        (hadm _ (mem_master_bit d nb Es K (mem_bit_cast d nb hi)))⟩
    · exact ⟨1, Or.inr rfl, (cast_BQ_semOk_iff σ h1).mp
        (hadm _ (mem_master_bit d nb Es K (mem_bit_cast d nb hi)))⟩
  have hbvex : ∃ bv : ℕ → ℚ, ∀ i : ℕ, (i < nb →
      (bv i = 0 ∨ bv i = 1) ∧
      σ.entryFlat (d + 5 * i + 4) 0 = some (.fin (bv i))) ∧
      (¬(i < nb) → bv i = 0) := by
    refine ⟨fun i => if h : i < nb then (hbit i h).choose else 0, ?_⟩
    intro i
    constructor
    · intro h
      simp only [dif_pos h]
      exact ⟨(hbit i h).choose_spec.1, (hbit i h).choose_spec.2⟩
    · intro h
      simp only [dif_neg h]
  obtain ⟨bv, hbvspec⟩ := hbvex
  have hbv : ∀ i, bv i = 0 ∨ bv i = 1 := by
    intro i
    by_cases h : i < nb
    · exact ((hbvspec i).1 h).1
    · exact Or.inl ((hbvspec i).2 h)
  have hbread : ∀ i : ℕ, i < nb →
      σ.entryFlat (d + 5 * i + 4) 0 = some (.fin (bv i)) :=
    fun i h => ((hbvspec i).1 h).2
  have hsrcread : ∀ s : ℕ, s < d + nb →
      σ.entryFlat (srcW d s) 0 = some (.fin (valsOfXB d x bv s)) := by
    intro s hs
    unfold srcW valsOfXB
    by_cases h : s < d
    · rw [if_pos h, dif_pos h]
      exact hin ⟨s, h⟩
    · rw [if_neg h, dif_neg h]
      exact hbread (s - d) (by omega)
  have htaps : ∀ s : ℕ, ∀ w ∈ (M d nb Es).tapOf s,
      σ.entryFlat w 0 = some (.fin (valsOfXB d x bv s)) := by
    intro s w hw
    by_cases hs : s < d + nb
    · exact (copy_scalarQ_semOk_iff σ ((M d nb Es).tapOf s).length
        (ty_srcW d nb Es K hs) (fun o ho => ty_tapOf d nb Es K ho)
        (hsrcread s hs)).mp
        (hadm _ (mem_master_comb d nb Es K (mem_comb d nb Es hs))) w hw
    · have hw' : w ∈ (PolyExpr.compileMany Es (eB d nb)).tapOf s := hw
      rw [many_tapOf_empty Es (eB d nb) hsrcb (show d + nb ≤ s by omega)]
        at hw'
      exact nomatch hw'
  have houtread := many_reads σ Es (eB d nb) (valsOfXB d x bv)
    (fun w τ h => ty_M d nb Es K h) htaps
    (fun a ha => hadm _ (mem_master_M d nb Es K ha))
  have hguard : ∀ r, (hr : r < K) →
      0 ≤ (Es[r]'(by omega)).evalE (valsOfXB d x bv) := by
    intro r hr
    have hlen : r < (M d nb Es).outs.length := by
      unfold M
      rw [many_outs_length]
      omega
    have hget : (M d nb Es).outs.getD r 0
        = (M d nb Es).outs[r]'hlen := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
      rfl
    have hor := houtread r (by omega)
    have hs' := (reshape_scalar_semOk_iff σ
      (ty_out_getD d nb Es K (by omega)) (ty_guard_s d nb Es K hr)
      (by rw [hget]; exact hor)).mp
      (hadm _ (mem_master_guard d nb Es K (mem_guard_reshape d nb Es K hr)))
    exact ((cell_guard_semOk_iff σ (ty_guard_s d nb Es K hr) hs').mp
      (hadm _ (mem_master_guard d nb Es K
        (mem_guard_cell d nb Es K hr)))).1
  refine ⟨bv, hbv, hguard, ?_⟩
  intro j
  have hlen : K + j.val < (M d nb Es).outs.length := by
    unfold M
    rw [many_outs_length]
    omega
  have hget : (M d nb Es).outs.getD (K + j.val) 0
      = (M d nb Es).outs[K + j.val]'hlen := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    rfl
  have hor := houtread (K + j.val) (by omega)
  have hyj := hout j
  rw [hget] at hyj
  exact ERat.fin.inj (Option.some.inj (hyj.symm.trans hor))

theorem master_denot_mpr (hK : K ≤ Es.length) {m : ℕ}
    (hm : K + m = Es.length)
    (x : Fin d → ℚ) (y : Fin m → ℚ) (bv : ℕ → ℚ)
    (hbv : ∀ i, bv i = 0 ∨ bv i = 1)
    (hg : ∀ r, (hr : r < K) →
      0 ≤ (Es[r]'(by omega)).evalE (valsOfXB d x bv))
    (hy : ∀ j : Fin m,
      y j = (Es[K + j.val]'(by omega)).evalE (valsOfXB d x bv)) :
    ∃ σ : (masterH d nb Es K hK).Valuation, σ.Admissible ∧
      (∀ i : Fin d, σ.entryFlat i.val 0 = some (.fin (x i))) ∧
      (∀ j : Fin m,
        σ.entryFlat ((M d nb Es).outs.getD (K + j.val) 0) 0
          = some (.fin (y j))) := by
  refine ⟨mkVal (masterH d nb Es K hK) (gm d nb Es x bv) (gm_wf d nb Es K x bv hbv), ?_, ?_, ?_⟩
  case refine_2 =>
    intro i
    rw [mkVal_reads _ _ _ (ty_port d nb Es K i.isLt) 0,
      gm_port d nb Es x bv i.isLt]
    rfl
  case refine_3 =>
    intro j
    have hlen : K + j.val < (M d nb Es).outs.length := by
      unfold M
      rw [many_outs_length]
      omega
    have hget : (M d nb Es).outs.getD (K + j.val) 0
        = (M d nb Es).outs[K + j.val]'hlen := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
      rfl
    rw [mkVal_reads _ _ _ (ty_out_getD d nb Es K (by omega)) 0]
    rw [gm_station d nb Es x bv (by
      rw [hget, M_ty_out d nb Es (List.getElem_mem hlen)]
      rfl)]
    rw [hget, M_mdl_out d nb Es (valsOfXB d x bv)
      (show K + j.val < Es.length by omega)]
    rw [hy j]
    rfl
  case refine_1 =>
    intro a ha
    replace ha : a ∈ masterApps d nb Es K := ha
    unfold masterApps at ha
    rcases List.mem_append.mp ha with h1 | hguard
    · rcases List.mem_append.mp h1 with h2 | hM
      · rcases List.mem_append.mp h2 with hbit | hcomb
        · -- bit gadgets
          unfold bitApps at hbit
          rw [List.mem_flatMap] at hbit
          obtain ⟨i, hi, hmem⟩ := hbit
          have hi' := List.mem_range.mp hi
          have hz : (mkVal (masterH d nb Es K hK) (gm d nb Es x bv)
              (gm_wf d nb Es K x bv hbv)).entryFlat (d + 5 * i) 0
              = some (.fin 0) := by
            rw [mkVal_reads _ _ _ (ty_z d nb Es K hi') 0,
              gm_z d nb Es x bv hi']
            rfl
          have hz' : (mkVal (masterH d nb Es K hK) (gm d nb Es x bv)
              (gm_wf d nb Es K x bv hbv)).entryFlat (d + 5 * i + 1) 0
              = some (.fin 0) := by
            rw [mkVal_reads _ _ _ (ty_z' d nb Es K hi') 0,
              gm_z' d nb Es x bv hi']
            rfl
          have hb0 : (mkVal (masterH d nb Es K hK) (gm d nb Es x bv)
              (gm_wf d nb Es K x bv hbv)).entryFlat (d + 5 * i + 2) 0
              = some (.fin (1 - bv i)) := by
            rw [mkVal_reads _ _ _ (ty_b0 d nb Es K hi') 0,
              gm_b0 d nb Es x bv hi']
            rfl
          have hb1 : (mkVal (masterH d nb Es K hK) (gm d nb Es x bv)
              (gm_wf d nb Es K x bv hbv)).entryFlat (d + 5 * i + 3) 0
              = some (.fin (bv i)) := by
            rw [mkVal_reads _ _ _ (ty_b1 d nb Es K hi') 0,
              gm_b1 d nb Es x bv hi']
            rfl
          have hb : (mkVal (masterH d nb Es K hK) (gm d nb Es x bv)
              (gm_wf d nb Es K x bv hbv)).entryFlat (d + 5 * i + 4) 0
              = some (.fin (bv i)) := by
            rw [mkVal_reads _ _ _ (ty_b d nb Es K hi') 0,
              gm_b d nb Es x bv hi']
            rfl
          rcases List.mem_cons.mp hmem with rfl | hmem
          · exact (const_scalarQ_semOk_iff _ (ty_z d nb Es K hi') 0).mpr hz
          · rcases List.mem_cons.mp hmem with rfl | hmem
            · exact (reshape_scalar_semOk_iff _ (ty_z d nb Es K hi')
                (ty_z' d nb Es K hi') hz).mpr hz'
            · rcases List.mem_cons.mp hmem with rfl | hmem
              · refine (cell_freeBit_semOk_iff _ (ty_z' d nb Es K hi')
                  hz').mpr ?_
                rcases hbv i with hbi | hbi
                · left
                  rw [hbi] at hb0 hb1
                  norm_num at hb0
                  exact ⟨hb0, hb1⟩
                · right
                  rw [hbi] at hb0 hb1
                  norm_num at hb0
                  exact ⟨hb0, hb1⟩
              · have h4 := List.mem_singleton.mp hmem
                subst h4
                exact (cast_BQ_semOk_iff _ hb1).mpr hb
        · -- combs
          unfold combApps at hcomb
          rw [List.mem_map] at hcomb
          obtain ⟨s, hs, rfl⟩ := hcomb
          have hs' := List.mem_range.mp hs
          have hsrcv : (mkVal (masterH d nb Es K hK) (gm d nb Es x bv)
              (gm_wf d nb Es K x bv hbv)).entryFlat (srcW d s) 0
              = some (.fin (valsOfXB d x bv s)) := by
            rw [mkVal_reads _ _ _ (ty_srcW d nb Es K hs') 0]
            unfold srcW valsOfXB
            by_cases h : s < d
            · rw [if_pos h, dif_pos h, gm_port d nb Es x bv h]
              rfl
            · rw [if_neg h, dif_neg h,
                gm_b d nb Es x bv (show s - d < nb by omega)]
              rfl
          refine (copy_scalarQ_semOk_iff _ ((M d nb Es).tapOf s).length
            (ty_srcW d nb Es K hs')
            (fun o ho => ty_tapOf d nb Es K ho) hsrcv).mpr ?_
          intro o ho
          rw [mkVal_reads _ _ _ (ty_tapOf d nb Es K ho) 0,
            gm_station d nb Es x bv (show
              ((PolyExpr.compileMany Es (eB d nb)).ty o).isSome = true by
              rw [many_ty_tapOf Es (eB d nb) s o ho]
              rfl)]
          rw [show (M d nb Es).mdl (valsOfXB d x bv) o
            = [valsOfXB d x bv s] from
            many_mdl_tapOf Es (eB d nb) (valsOfXB d x bv) s o ho]
          rfl
      · -- stations
        refine many_semOk _ Es (eB d nb) (valsOfXB d x bv)
          (fun w τ h => ty_M d nb Es K h) ?_ a hM
        intro w hs i
        rw [mkVal_reads _ _ _ (ty_M d nb Es K
          (Option.isSome_iff_exists.mp hs).choose_spec) i]
        rw [gm_station d nb Es x bv hs]
        rfl
    · -- guards
      unfold guardApps at hguard
      rw [List.mem_flatMap] at hguard
      obtain ⟨r, hr, hmem⟩ := hguard
      have hr' := List.mem_range.mp hr
      have hlen : r < (M d nb Es).outs.length := by
        unfold M
        rw [many_outs_length]
        omega
      have hget : (M d nb Es).outs.getD r 0
          = (M d nb Es).outs[r]'hlen := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
        rfl
      have hEget : Es.getD r (.qconst 0) = Es[r]'(by omega) := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show r < Es.length by omega)]
        rfl
      have hov : (mkVal (masterH d nb Es K hK) (gm d nb Es x bv)
          (gm_wf d nb Es K x bv hbv)).entryFlat
          ((M d nb Es).outs.getD r 0) 0
          = some (.fin ((Es[r]'(by omega)).evalE (valsOfXB d x bv))) := by
        rw [mkVal_reads _ _ _ (ty_out_getD d nb Es K (by omega)) 0]
        rw [gm_station d nb Es x bv (by
          rw [hget, M_ty_out d nb Es (List.getElem_mem hlen)]
          rfl)]
        rw [hget, M_mdl_out d nb Es (valsOfXB d x bv)
          (show r < Es.length by omega)]
        rfl
      have hsv : (mkVal (masterH d nb Es K hK) (gm d nb Es x bv)
          (gm_wf d nb Es K x bv hbv)).entryFlat (gB d nb Es + 2 * r) 0
          = some (.fin ((Es[r]'(by omega)).evalE (valsOfXB d x bv))) := by
        rw [mkVal_reads _ _ _ (ty_guard_s d nb Es K hr') 0,
          gm_guard_s d nb Es K x bv hr' hK, hEget]
        rfl
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact (reshape_scalar_semOk_iff _
          (ty_out_getD d nb Es K (by omega))
          (ty_guard_s d nb Es K hr') hov).mpr hsv
      · have h2 := List.mem_singleton.mp hmem
        subst h2
        refine (cell_guard_semOk_iff _ (ty_guard_s d nb Es K hr')
          hsv).mpr ⟨hg r hr', ?_⟩
        rw [mkVal_reads _ _ _ (ty_guard_g d nb Es K hr') 0,
          gm_guard_g d nb Es K x bv hr' hK]
        rfl


/-! ## The first-match selector trees -/

/-- `1 − tap s`. -/
def oneMinus (s : ℕ) : PolyExpr :=
  .add (.qconst 1) (.mul (.qconst (-1)) (.tap s))

/-- `Π_{j<t} (1 − tap (d+j))`. -/
def prefProd (dd : ℕ) : ℕ → PolyExpr
  | 0 => .qconst 1
  | t + 1 => .mul (oneMinus (dd + t)) (prefProd dd t)

/-- The `I`-th selector among `n`, bits at sources `dd..`:
`tap (dd+I) · Π_{j<I} (1 − tap (dd+j))`, with the last selector the
bare prefix product. -/
def selE (dd n I : ℕ) : PolyExpr :=
  if I + 1 < n then .mul (.tap (dd + I)) (prefProd dd I)
  else prefProd dd I

/-- Sum of `f I` over `I < k`. -/
def sumSel (f : ℕ → PolyExpr) : ℕ → PolyExpr
  | 0 => .qconst 0
  | k + 1 => .add (f k) (sumSel f k)

theorem prefProd_taps (dd : ℕ) : ∀ t : ℕ,
    ∀ s ∈ (prefProd dd t).taps, dd ≤ s ∧ s < dd + t := by
  intro t
  induction t with
  | zero => intro s hs; exact nomatch hs
  | succ t ih =>
    intro s hs
    rcases List.mem_append.mp hs with hm | hm
    · have : s = dd + t := by
        rcases List.mem_append.mp hm with h | h
        · exact nomatch h
        · rcases List.mem_append.mp h with h' | h'
          · exact nomatch h'
          · exact List.mem_singleton.mp h'
      omega
    · have := ih s hm
      omega

theorem selE_taps (dd n I : ℕ) (hI : I < n) :
    ∀ s ∈ (selE dd n I).taps, dd ≤ s ∧ s < dd + (n - 1) := by
  intro s hs
  unfold selE at hs
  by_cases h : I + 1 < n
  · rw [if_pos h] at hs
    rcases List.mem_append.mp hs with hm | hm
    · have := List.mem_singleton.mp hm
      omega
    · have := prefProd_taps dd I s hm
      omega
  · rw [if_neg h] at hs
    have := prefProd_taps dd I s hs
    omega

theorem sumSel_taps (f : ℕ → PolyExpr) : ∀ k : ℕ,
    ∀ s ∈ (sumSel f k).taps, ∃ I, I < k ∧ s ∈ (f I).taps := by
  intro k
  induction k with
  | zero => intro s hs; exact nomatch hs
  | succ k ih =>
    intro s hs
    rcases List.mem_append.mp hs with hm | hm
    · exact ⟨k, by omega, hm⟩
    · obtain ⟨I, hI, hm'⟩ := ih s hm
      exact ⟨I, by omega, hm'⟩

/-! ## Selector values at Boolean bits -/

theorem prefProd_eval_one (dd : ℕ) (vals : ℕ → ℚ) : ∀ t : ℕ,
    (∀ j, j < t → vals (dd + j) = 0) →
    (prefProd dd t).evalE vals = 1 := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro hz
    show ((1 : ℚ) + (-1) * vals (dd + t))
        * (prefProd dd t).evalE vals = 1
    rw [hz t (by omega), ih (fun j hj => hz j (by omega))]
    ring

theorem prefProd_eval_zero (dd : ℕ) (vals : ℕ → ℚ) : ∀ t j : ℕ,
    j < t → vals (dd + j) = 1 →
    (prefProd dd t).evalE vals = 0 := by
  intro t
  induction t with
  | zero => intro j hj; omega
  | succ t ih =>
    intro j hj hone
    show ((1 : ℚ) + (-1) * vals (dd + t))
        * (prefProd dd t).evalE vals = 0
    by_cases hjt : j = t
    · subst hjt
      rw [hone]
      ring
    · rw [ih j (by omega) hone]
      ring

theorem selE_eval_one (dd n I₀ : ℕ) (vals : ℕ → ℚ) (hI₀ : I₀ < n)
    (hzero : ∀ j, j < I₀ → vals (dd + j) = 0)
    (hone : I₀ + 1 < n → vals (dd + I₀) = 1) :
    (selE dd n I₀).evalE vals = 1 := by
  unfold selE
  by_cases h : I₀ + 1 < n
  · rw [if_pos h]
    show vals (dd + I₀) * (prefProd dd I₀).evalE vals = 1
    rw [hone h, prefProd_eval_one dd vals I₀ hzero]
    ring
  · rw [if_neg h]
    exact prefProd_eval_one dd vals I₀ hzero

theorem selE_eval_zero (dd n I I₀ : ℕ) (vals : ℕ → ℚ)
    (hI : I < n) (hI₀ : I₀ < n) (hne : I ≠ I₀)
    (hzero : ∀ j, j < I₀ → vals (dd + j) = 0)
    (hone : I₀ + 1 < n → vals (dd + I₀) = 1) :
    (selE dd n I).evalE vals = 0 := by
  unfold selE
  rcases Nat.lt_or_ge I I₀ with hlt | hge
  · -- an earlier selector: its own bit is zero
    have hb := hzero I hlt
    rw [if_pos (by omega)]
    show vals (dd + I) * (prefProd dd I).evalE vals = 0
    rw [hb]
    ring
  · -- a later selector: the prefix product contains the fired bit
    have hgt : I₀ < I := by omega
    have hone' : vals (dd + I₀) = 1 := hone (by omega)
    by_cases h : I + 1 < n
    · rw [if_pos h]
      show vals (dd + I) * (prefProd dd I).evalE vals = 0
      rw [prefProd_eval_zero dd vals I I₀ hgt hone']
      ring
    · rw [if_neg h]
      exact prefProd_eval_zero dd vals I I₀ hgt hone'

/-- Boolean bits fire exactly one selector. -/
theorem exists_selector (dd n : ℕ) (hn : 0 < n) (vals : ℕ → ℚ)
    (hb : ∀ j, vals (dd + j) = 0 ∨ vals (dd + j) = 1) :
    ∃ I₀, I₀ < n ∧ (selE dd n I₀).evalE vals = 1 ∧
      ∀ I, I < n → I ≠ I₀ → (selE dd n I).evalE vals = 0 := by
  classical
  by_cases hex : ∃ j, j < n - 1 ∧ vals (dd + j) = 1
  · have hfind := Nat.find_spec hex
    set I₀ := Nat.find hex with hI₀def
    have hzero : ∀ j, j < I₀ → vals (dd + j) = 0 := by
      intro j hj
      have hnot := Nat.find_min hex hj
      rcases hb j with h | h
      · exact h
      · exact absurd ⟨by omega, h⟩ hnot
    have hone : I₀ + 1 < n → vals (dd + I₀) = 1 := fun _ => hfind.2
    refine ⟨I₀, by omega, selE_eval_one dd n I₀ vals (by omega)
      hzero hone, ?_⟩
    intro I hI hne
    exact selE_eval_zero dd n I I₀ vals hI (by omega) hne hzero hone
  · refine ⟨n - 1, by omega, ?_, ?_⟩
    · refine selE_eval_one dd n (n - 1) vals (by omega) ?_ ?_
      · intro j hj
        rcases hb j with h | h
        · exact h
        · exact absurd (show ∃ j, j < n - 1 ∧ vals (dd + j) = 1 from
            ⟨j, by omega, h⟩) hex
      · intro h
        omega
    · intro I hI hne
      refine selE_eval_zero dd n I (n - 1) vals hI (by omega) hne ?_ ?_
      · intro j hj
        rcases hb j with h | h
        · exact h
        · exact absurd (show ∃ j, j < n - 1 ∧ vals (dd + j) = 1 from
            ⟨j, by omega, h⟩) hex
      · intro h
        omega

/-! ## Sum collapse at a fired selector -/

theorem sumSel_eval_zero (f : ℕ → PolyExpr) (vals : ℕ → ℚ) : ∀ k : ℕ,
    (∀ I, I < k → (f I).evalE vals = 0) →
    (sumSel f k).evalE vals = 0 := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hz
    show (f k).evalE vals + (sumSel f k).evalE vals = 0
    rw [hz k (by omega), ih (fun I hI => hz I (by omega))]
    ring

theorem sumSel_eval_collapse (f : ℕ → PolyExpr) (vals : ℕ → ℚ)
    (I₀ : ℕ) : ∀ k : ℕ, I₀ < k →
    (∀ I, I < k → I ≠ I₀ → (f I).evalE vals = 0) →
    (sumSel f k).evalE vals = (f I₀).evalE vals := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hI₀ hz
    show (f k).evalE vals + (sumSel f k).evalE vals = _
    by_cases hk : I₀ = k
    · subst hk
      rw [sumSel_eval_zero f vals I₀ (fun I hI => hz I (by omega)
        (by omega))]
      ring
    · rw [hz k (by omega) (fun h => hk h.symm),
        ih (by omega) (fun I hI hne => hz I (by omega) hne)]
      ring

/-! ## The rational-polynomial bridge -/

theorem exists_polyExpr (dd : ℕ) (p : MvPolynomial (Fin dd) ℚ) :
    ∃ E : PolyExpr, (∀ s ∈ E.taps, s < dd) ∧
      ∀ vals : ℕ → ℚ,
        E.evalE vals
          = MvPolynomial.eval (fun i : Fin dd => vals i.val) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨.qconst a, ?_, ?_⟩
    · intro s hs
      exact nomatch hs
    · intro vals
      simp [PolyExpr.evalE]
  | add p q ihp ihq =>
    obtain ⟨E₁, h₁, hev₁⟩ := ihp
    obtain ⟨E₂, h₂, hev₂⟩ := ihq
    refine ⟨.add E₁ E₂, ?_, ?_⟩
    · intro s hs
      rcases List.mem_append.mp hs with hm | hm
      · exact h₁ s hm
      · exact h₂ s hm
    · intro vals
      show E₁.evalE vals + E₂.evalE vals = _
      rw [hev₁ vals, hev₂ vals]
      simp
  | mul_X p i ihp =>
    obtain ⟨E₁, h₁, hev₁⟩ := ihp
    refine ⟨.mul E₁ (.tap i.val), ?_, ?_⟩
    · intro s hs
      rcases List.mem_append.mp hs with hm | hm
      · exact h₁ s hm
      · have := List.mem_singleton.mp hm
        subst this
        exact i.isLt
    · intro vals
      show E₁.evalE vals * vals i.val = _
      rw [hev₁ vals]
      simp

/-- Bridge a list of polynomials, indexwise. -/
theorem exists_polyExpr_list (dd : ℕ)
    (l : List (MvPolynomial (Fin dd) ℚ)) :
    ∃ Bs : List PolyExpr, ∃ _ : Bs.length = l.length,
      ∀ k, (hk : k < l.length) →
        (∀ s ∈ (Bs[k]'(by omega)).taps, s < dd) ∧
        ∀ vals : ℕ → ℚ,
          (Bs[k]'(by omega)).evalE vals
            = MvPolynomial.eval (fun i : Fin dd => vals i.val)
                (l[k]'hk) := by
  induction l with
  | nil => exact ⟨[], rfl, fun k hk => absurd hk (by simp)⟩
  | cons q l ih =>
    obtain ⟨Bs, hlen, hspec⟩ := ih
    obtain ⟨E, hE, hEev⟩ := exists_polyExpr dd q
    refine ⟨E :: Bs, by simp [hlen], ?_⟩
    intro k hk
    match k with
    | 0 => exact ⟨hE, hEev⟩
    | k + 1 =>
      have hk' : k < l.length := by
        have := hk
        simp only [List.length_cons] at this
        omega
      exact hspec k hk'


/-! ## Source-value plumbing -/

theorem valsOfXB_x (x : Fin d → ℚ) (bv : ℕ → ℚ) (i : Fin d) :
    valsOfXB d x bv i.val = x i := by
  unfold valsOfXB
  rw [dif_pos i.isLt]

theorem valsOfXB_fun (x : Fin d → ℚ) (bv : ℕ → ℚ) :
    (fun i : Fin d => valsOfXB d x bv i.val) = x :=
  funext (fun i => valsOfXB_x d x bv i)

theorem valsOfXB_bit (x : Fin d → ℚ) (bv : ℕ → ℚ) (j : ℕ) :
    valsOfXB d x bv (d + j) = bv j := by
  unfold valsOfXB
  rw [dif_neg (by omega)]
  congr 1
  omega

end BasisGen

/-! ## The generation direction

The final assembly deliberately avoids `set`-style local definitions:
every list built for the master net is introduced as an *opaque*
variable together with the facts the proof consumes (a membership
characterization, a length, an indexed read).  Local `set` bindings
would leave the context with the same list at several unfolding
stages, and `getElem` bound proofs then block the rewrite motives. -/

/-- Transport a `getElem` read along a list equation. -/
private theorem getElem_list_congr {α : Type _} {l l' : List α}
    (h : l = l') (i : ℕ) (hi : i < l.length) :
    l[i]'hi = l'[i]'(h ▸ hi) := by
  cases h
  rfl

/-- Transport a `getElem` read along an index equation. -/
private theorem getElem_idx_congr {α : Type _} (l : List α) {i i' : ℕ}
    (h : i = i') (hi : i < l.length) :
    l[i]'hi = l[i']'(h ▸ hi) := by
  cases h
  rfl

/-- Reading the `j`-th element of the right part of an append. -/
private theorem getElem_append_add {α : Type _} (as bs : List α) (j : ℕ)
    (hj : j < bs.length) (hb : as.length + j < (as ++ bs).length) :
    (as ++ bs)[as.length + j]'hb = bs[j]'hj := by
  rw [List.getElem_append_right (by omega : as.length ≤ as.length + j),
    getElem_idx_congr bs (by omega : as.length + j - as.length = j)]

open BasisGen in
/-- Any nonempty finite family of pieces is realized: the master net's
interface denotation equals the union of the family's graphs. -/
theorem exists_hypernet_denotRel_eq_union (d m : ℕ)
    (l : List (PieceData d m)) (hn0 : 0 < l.length) :
    ∃ (H : Hypernet) (ins : Fin d → Wire) (outs : Fin m → Wire),
      H.TenBoxOnly ∧ H.ExactBQ ∧
      (∀ i, H.ScalarQPort (ins i)) ∧ (∀ j, H.ScalarQPort (outs j)) ∧
      H.DenotRel d m ins outs = ⋃ P ∈ l, P.graph := by
  classical
  -- per-piece condition expressions and output expressions
  have hG : ∀ I : Fin l.length, ∃ Bs : List PolyExpr,
      ∃ _ : Bs.length = (l[I]).conds.length,
      ∀ k, (hk : k < (l[I]).conds.length) →
        (∀ s ∈ (Bs[k]'(by omega)).taps, s < d) ∧
        ∀ vals : ℕ → ℚ, (Bs[k]'(by omega)).evalE vals
          = MvPolynomial.eval (fun i : Fin d => vals i.val)
              ((l[I]).conds[k]'hk) :=
    fun I => exists_polyExpr_list d (l[I]).conds
  choose G hGlen hGspec using hG
  have hF : ∀ I : Fin l.length, ∀ j : Fin m, ∃ E : PolyExpr,
      (∀ s ∈ E.taps, s < d) ∧
      ∀ vals : ℕ → ℚ, E.evalE vals
        = MvPolynomial.eval (fun i : Fin d => vals i.val)
            ((l[I]).val j) :=
    fun I j => exists_polyExpr d ((l[I]).val j)
  choose F hFt hFev using hF
  -- the guard list, opaque, with its membership characterization
  obtain ⟨gEs, hgEs⟩ : ∃ x : List PolyExpr,
      x = (List.finRange l.length).flatMap (fun I =>
        (G I).map (fun B => PolyExpr.mul (selE d l.length I.val) B)) :=
    ⟨_, rfl⟩
  have hgMem : ∀ E : PolyExpr, E ∈ gEs ↔
      ∃ I : Fin l.length, ∃ B ∈ G I,
        E = PolyExpr.mul (selE d l.length I.val) B := by
    intro E
    rw [hgEs]
    constructor
    · intro hE
      obtain ⟨I, -, hmem⟩ := List.mem_flatMap.mp hE
      obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hmem
      exact ⟨I, B, hB, rfl⟩
    · rintro ⟨I, B, hB, rfl⟩
      exact List.mem_flatMap.mpr ⟨I, List.mem_finRange _,
        List.mem_map.mpr ⟨B, hB, rfl⟩⟩
  -- the masked output summands, opaque, read pointwise
  obtain ⟨fsum, hfsum⟩ : ∃ fs : Fin m → ℕ → PolyExpr,
      ∀ (j : Fin m) (I : ℕ) (h : I < l.length),
        fs j I = PolyExpr.mul (selE d l.length I) (F ⟨I, h⟩ j) :=
    ⟨fun j I => if h : I < l.length then
        PolyExpr.mul (selE d l.length I) (F ⟨I, h⟩ j)
      else .qconst 0,
     fun _ _ h => dif_pos h⟩
  -- the output list, opaque, with its length and indexed read
  obtain ⟨oEs, hoEs⟩ : ∃ x : List PolyExpr,
      x = (List.finRange m).map (fun j => sumSel (fsum j) l.length) :=
    ⟨_, rfl⟩
  have holen : oEs.length = m := by
    rw [hoEs]
    simp
  have hK : gEs.length ≤ (gEs ++ oEs).length := by
    rw [List.length_append]
    omega
  have hmm : gEs.length + m = (gEs ++ oEs).length := by
    rw [List.length_append, holen]
  have hoGet : ∀ (j : Fin m)
      (hb : gEs.length + j.val < (gEs ++ oEs).length),
      (gEs ++ oEs)[gEs.length + j.val]'hb = sumSel (fsum j) l.length := by
    intro j hb
    have hj : j.val < oEs.length := by
      rw [holen]
      exact j.isLt
    rw [getElem_append_add gEs oEs j.val hj hb,
      getElem_list_congr hoEs j.val hj]
    simp only [List.getElem_map, List.getElem_finRange]
    rfl
  have hsrcb : ∀ E ∈ gEs ++ oEs, ∀ s ∈ E.taps,
      s < d + (l.length - 1) := by
    intro E hE s hs
    rcases List.mem_append.mp hE with hE' | hE'
    · obtain ⟨I, B, hB, rfl⟩ := (hgMem E).mp hE'
      rcases List.mem_append.mp hs with hm' | hm'
      · have := selE_taps d l.length I.val I.isLt s hm'
        omega
      · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hB
        have hk' : k < (l[I]).conds.length := by
          rw [← hGlen I]
          exact hk
        have := (hGspec I k hk').1 s hm'
        omega
    · rw [hoEs] at hE'
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hE'
      obtain ⟨I, hI, hm'⟩ := sumSel_taps (fsum j) l.length s hs
      rw [hfsum j I hI] at hm'
      rcases List.mem_append.mp hm' with hm'' | hm''
      · have := selE_taps d l.length I hI s hm''
        omega
      · have := hFt ⟨I, hI⟩ j s hm''
        omega
  refine ⟨masterH d (l.length - 1) (gEs ++ oEs) gEs.length hK,
    fun i => i.val,
    fun j => (M d (l.length - 1) (gEs ++ oEs)).outs.getD
      (gEs.length + j.val) 0,
    masterH_tenBox _ _ _ _ _, masterH_exactBQ _ _ _ _ _,
    fun i => masterH_port_in _ _ _ _ _ i.isLt,
    fun j => masterH_port_out _ _ _ _ _ (by
      have := j.isLt
      omega), ?_⟩
  ext xy
  simp only [Hypernet.DenotRel, Set.mem_setOf_eq]
  constructor
  · rintro ⟨σ, hadm, hin, hout⟩
    obtain ⟨bv, hbv, hguard, hy⟩ := master_denot_mp d (l.length - 1)
      (gEs ++ oEs) gEs.length hK hmm hsrcb xy.1 xy.2 σ hadm hin hout
    obtain ⟨I₀, hI₀, hone, hzero⟩ := exists_selector d l.length hn0
      (valsOfXB d xy.1 bv)
      (fun j => by rw [valsOfXB_bit]; exact hbv j)
    have hvx : (fun i : Fin d => valsOfXB d xy.1 bv i.val) = xy.1 :=
      valsOfXB_fun d xy.1 bv
    have hguard' : ∀ E ∈ gEs, 0 ≤ E.evalE (valsOfXB d xy.1 bv) := by
      intro E hE
      obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hE
      have h0 := hguard r hr
      rwa [List.getElem_append_left hr] at h0
    refine Set.mem_iUnion₂.mpr ⟨l[I₀]'hI₀, List.getElem_mem _, ?_⟩
    refine Set.mem_setOf_eq ▸ ⟨?_, ?_⟩
    · intro q hq
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq
      have hkG : k < (G ⟨I₀, hI₀⟩).length := by
        rw [hGlen ⟨I₀, hI₀⟩]
        exact hk
      have hmemg : PolyExpr.mul (selE d l.length I₀)
          ((G ⟨I₀, hI₀⟩)[k]'hkG) ∈ gEs :=
        (hgMem _).mpr ⟨⟨I₀, hI₀⟩, (G ⟨I₀, hI₀⟩)[k]'hkG,
          List.getElem_mem _, rfl⟩
      have h0 := hguard' _ hmemg
      have heval : (PolyExpr.mul (selE d l.length I₀)
          ((G ⟨I₀, hI₀⟩)[k]'hkG)).evalE (valsOfXB d xy.1 bv)
          = MvPolynomial.eval xy.1
              ((l[(⟨I₀, hI₀⟩ : Fin l.length)]).conds[k]'hk) := by
        show (selE d l.length I₀).evalE (valsOfXB d xy.1 bv)
            * ((G ⟨I₀, hI₀⟩)[k]'hkG).evalE (valsOfXB d xy.1 bv) = _
        rw [hone, one_mul,
          (hGspec ⟨I₀, hI₀⟩ k hk).2 (valsOfXB d xy.1 bv), hvx]
      rw [heval] at h0
      exact h0
    · intro j
      have hyj := hy j
      rw [hoGet j] at hyj
      have hcol : (sumSel (fsum j) l.length).evalE (valsOfXB d xy.1 bv)
          = (fsum j I₀).evalE (valsOfXB d xy.1 bv) := by
        refine sumSel_eval_collapse (fsum j) (valsOfXB d xy.1 bv) I₀
          l.length hI₀ ?_
        intro I hI hne
        rw [hfsum j I hI]
        show (selE d l.length I).evalE (valsOfXB d xy.1 bv)
            * (F ⟨I, hI⟩ j).evalE (valsOfXB d xy.1 bv) = 0
        rw [hzero I hI hne, zero_mul]
      rw [hcol, hfsum j I₀ hI₀] at hyj
      have hfin : (PolyExpr.mul (selE d l.length I₀)
          (F ⟨I₀, hI₀⟩ j)).evalE (valsOfXB d xy.1 bv)
          = MvPolynomial.eval xy.1
              ((l[(⟨I₀, hI₀⟩ : Fin l.length)]).val j) := by
        show (selE d l.length I₀).evalE (valsOfXB d xy.1 bv)
            * (F ⟨I₀, hI₀⟩ j).evalE (valsOfXB d xy.1 bv) = _
        rw [hone, one_mul, hFev ⟨I₀, hI₀⟩ j (valsOfXB d xy.1 bv), hvx]
      rw [hfin] at hyj
      exact hyj
  · intro hmem
    obtain ⟨P, hP, hxy⟩ := Set.mem_iUnion₂.mp hmem
    obtain ⟨I₀, hI₀, rfl⟩ := List.mem_iff_getElem.mp hP
    obtain ⟨hconds, hvals⟩ := hxy
    obtain ⟨bv, hbvI, hbv0, hbv⟩ :
        ∃ bv : ℕ → ℚ, bv I₀ = 1 ∧ (∀ i, i ≠ I₀ → bv i = 0) ∧
          ∀ i, bv i = 0 ∨ bv i = 1 :=
      ⟨fun i => if i = I₀ then 1 else 0, if_pos rfl,
        fun _ hi => if_neg hi,
        fun i => by
          by_cases h : i = I₀
          · exact Or.inr (if_pos h)
          · exact Or.inl (if_neg h)⟩
    have hbits : ∀ j, valsOfXB d xy.1 bv (d + j) = bv j :=
      fun j => valsOfXB_bit d xy.1 bv j
    have hone : (selE d l.length I₀).evalE (valsOfXB d xy.1 bv) = 1 := by
      refine selE_eval_one d l.length I₀ (valsOfXB d xy.1 bv) hI₀ ?_ ?_
      · intro j hj
        rw [hbits j]
        exact hbv0 j (by omega)
      · intro _
        rw [hbits I₀]
        exact hbvI
    have hzero : ∀ I, I < l.length → I ≠ I₀ →
        (selE d l.length I).evalE (valsOfXB d xy.1 bv) = 0 := by
      intro I hI hne
      refine selE_eval_zero d l.length I I₀ (valsOfXB d xy.1 bv)
        hI hI₀ hne ?_ ?_
      · intro j hj
        rw [hbits j]
        exact hbv0 j (by omega)
      · intro _
        rw [hbits I₀]
        exact hbvI
    have hvx : (fun i : Fin d => valsOfXB d xy.1 bv i.val) = xy.1 :=
      valsOfXB_fun d xy.1 bv
    have hgmem : ∀ E ∈ gEs, 0 ≤ E.evalE (valsOfXB d xy.1 bv) := by
      intro E hE
      obtain ⟨I, B, hB, rfl⟩ := (hgMem E).mp hE
      obtain ⟨k, hkG, rfl⟩ := List.mem_iff_getElem.mp hB
      have hk' : k < (l[I]).conds.length := by
        rw [← hGlen I]
        exact hkG
      show 0 ≤ (selE d l.length I.val).evalE (valsOfXB d xy.1 bv)
          * ((G I)[k]'hkG).evalE (valsOfXB d xy.1 bv)
      by_cases hII : I.val = I₀
      · have hIeq : I = ⟨I₀, hI₀⟩ := Fin.ext hII
        subst hIeq
        have hone' : (selE d l.length
            (⟨I₀, hI₀⟩ : Fin l.length).val).evalE
            (valsOfXB d xy.1 bv) = 1 := hone
        rw [hone', one_mul,
          (hGspec ⟨I₀, hI₀⟩ k hk').2 (valsOfXB d xy.1 bv), hvx]
        exact hconds _ (List.getElem_mem hk')
      · have h0 : (selE d l.length I.val).evalE (valsOfXB d xy.1 bv)
            * ((G I)[k]'hkG).evalE (valsOfXB d xy.1 bv) = 0 := by
          rw [hzero I.val I.isLt hII, zero_mul]
        exact h0.ge
    have hg : ∀ r, (hr : r < gEs.length) →
        0 ≤ ((gEs ++ oEs)[r]'(by
          rw [List.length_append]
          omega)).evalE (valsOfXB d xy.1 bv) := by
      intro r hr
      rw [List.getElem_append_left hr]
      exact hgmem _ (List.getElem_mem hr)
    have hy : ∀ j : Fin m,
        xy.2 j = ((gEs ++ oEs)[gEs.length + j.val]'(by
          rw [List.length_append, holen]
          omega)).evalE (valsOfXB d xy.1 bv) := by
      intro j
      rw [hoGet j]
      have hcol : (sumSel (fsum j) l.length).evalE (valsOfXB d xy.1 bv)
          = (fsum j I₀).evalE (valsOfXB d xy.1 bv) := by
        refine sumSel_eval_collapse (fsum j) (valsOfXB d xy.1 bv) I₀
          l.length hI₀ ?_
        intro I hI hne
        rw [hfsum j I hI]
        show (selE d l.length I).evalE (valsOfXB d xy.1 bv)
            * (F ⟨I, hI⟩ j).evalE (valsOfXB d xy.1 bv) = 0
        rw [hzero I hI hne, zero_mul]
      rw [hcol, hfsum j I₀ hI₀]
      show xy.2 j = (selE d l.length I₀).evalE (valsOfXB d xy.1 bv)
          * (F ⟨I₀, hI₀⟩ j).evalE (valsOfXB d xy.1 bv)
      rw [hone, one_mul, hFev ⟨I₀, hI₀⟩ j (valsOfXB d xy.1 bv), hvx]
      exact hvals j
    obtain ⟨σ, hadm, hin, hout⟩ := master_denot_mpr d (l.length - 1)
      (gEs ++ oEs) gEs.length hK hmm xy.1 xy.2 bv hbv hg hy
    exact ⟨σ, hadm, hin, hout⟩

open BasisGen in
/-- **Completeness of the primitive basis**: every finite union of
rational-polynomial graphs over basic closed pieces is the interface
denotation of an exact-⟨B,Q⟩ ten-box hypernet. -/
theorem primitiveBasisComplete : PrimitiveBasisComplete := by
  intro d m Ps
  classical
  cases Ps with
  | nil =>
    refine ⟨masterH d 0 (.qconst (-1) :: List.replicate m (.qconst 0)) 1
        (by simp), fun i => i.val,
      fun j => (M d 0 (.qconst (-1) ::
        List.replicate m (.qconst 0))).outs.getD (1 + j.val) 0,
      masterH_tenBox _ _ _ _ _, masterH_exactBQ _ _ _ _ _,
      fun i => masterH_port_in _ _ _ _ _ i.isLt,
      fun j => masterH_port_out _ _ _ _ _ (by
        have := j.isLt
        simp only [List.length_cons, List.length_replicate]
        omega), ?_⟩
    ext xy
    simp only [Hypernet.DenotRel, Set.mem_setOf_eq]
    constructor
    · rintro ⟨σ, hadm, hin, hout⟩
      obtain ⟨bv, hbv, hguard, -⟩ := master_denot_mp d 0 _ 1 (by simp)
        (by simp only [List.length_cons, List.length_replicate]; omega)
        (by
          intro E hE s hs
          rcases List.mem_cons.mp hE with rfl | hE'
          · exact nomatch hs
          · rw [List.eq_of_mem_replicate hE'] at hs
            exact nomatch hs)
        xy.1 xy.2 σ hadm hin hout
      have h0 := hguard 0 (by omega)
      have hcon : (0 : ℚ) ≤ -1 := h0
      norm_num at hcon
    · intro hmem
      obtain ⟨P, hP, -⟩ := Set.mem_iUnion₂.mp hmem
      exact nomatch hP
  | cons P₀ Ps' =>
    exact exists_hypernet_denotRel_eq_union d m (P₀ :: Ps') (by simp)

#print axioms primitiveBasisComplete

end PPLC
