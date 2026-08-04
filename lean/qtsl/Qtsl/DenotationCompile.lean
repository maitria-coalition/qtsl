import Qtsl.DenotationGadgets
import Qtsl.HypernetCospan

/-!
# Compiling rational expressions into core-primitive nets

The generation direction of the completion theorem needs, for every
piece of denotation-class data, a ten-box hypernet — and the working
part of every such net is rational arithmetic.  This module compiles
binary expression trees over named *taps* (wires supplied by the
surrounding net) into application lists over the core primitives:

* `qconst q` — one `const` application;
* `mul` — one `contract` at the index-free pattern (scalar product);
* `add` — a pair `stack` followed by a `contract` over one index of
  extent two (scalar sum);
* `tap w` — no applications; the expression reads the wire `w`.

`PolyExpr.compile` allocates its wires in `[base, next)` and returns,
besides the applications and the output wire, the wire typing of its
allocation and a *model*: the entry table every wire takes when the
taps carry a given environment.  The lemma pack proves the structural
invariants (allocation bounds, linearity of the produced and consumed
wire lists, acyclicity, type consistency) and the two semantic
directions: an admissible valuation reads the expression's value at
the output (`compile_reads`), and any valuation agreeing with the
model is admissible on the compiled applications (`compile_semOk`).

`PolyExpr.inst` turns an expression over *source names* into an
expression over a contiguous block of tap wires, one per occurrence —
the form whose taps a `copy` comb can feed.
-/

namespace PPLC

open ReluExpansion (pat0 qv0)

/-- Rational expression trees over named taps. -/
inductive PolyExpr where
  | tap (w : ℕ)
  | qconst (q : ℚ)
  | add (e₁ e₂ : PolyExpr)
  | mul (e₁ e₂ : PolyExpr)

namespace PolyExpr

/-- Evaluation against an environment of tap values. -/
def evalE (env : ℕ → ℚ) : PolyExpr → ℚ
  | tap w => env w
  | qconst q => q
  | add e₁ e₂ => e₁.evalE env + e₂.evalE env
  | mul e₁ e₂ => e₁.evalE env * e₂.evalE env

/-- The taps of an expression, in evaluation order, with multiplicity. -/
def taps : PolyExpr → List ℕ
  | tap w => [w]
  | qconst _ => []
  | add e₁ e₂ => e₁.taps ++ e₂.taps
  | mul e₁ e₂ => e₁.taps ++ e₂.taps

/-- The result of compiling an expression at a wire base: the emitted
applications, the output wire, the next free wire, the typing of the
allocated wires, and the model entry table under a tap environment. -/
structure Compiled where
  apps : List PrimApp
  out : ℕ
  next : ℕ
  ty : ℕ → Option TensorType
  mdl : (ℕ → ℚ) → ℕ → List ℚ

/-- Compile an expression at a wire base. -/
def compile : PolyExpr → ℕ → Compiled
  | tap w, base =>
      { apps := [], out := w, next := base,
        ty := fun _ => none, mdl := fun _ _ => [] }
  | qconst q, base =>
      { apps := [.const ⟨[], Dtype.Q⟩ (qv0 q) base],
        out := base, next := base + 1,
        ty := fun w => if w = base then some ⟨[], Dtype.Q⟩ else none,
        mdl := fun _ w => if w = base then [q] else [] }
  | add e₁ e₂, base =>
      let c₁ := e₁.compile base
      let c₂ := e₂.compile c₁.next
      { apps := c₁.apps ++ c₂.apps ++
          [.stack 2 [] [c₁.out, c₂.out] c₂.next,
           .contract Dtype.Q .exact [c₂.next] (c₂.next + 1) [1] 0
             patSum1],
        out := c₂.next + 1, next := c₂.next + 2,
        ty := fun w =>
          if w = c₂.next then some ⟨[2], Dtype.Q⟩
          else if w = c₂.next + 1 then some ⟨[], Dtype.Q⟩
          else mergeWt c₁.ty c₂.ty w,
        mdl := fun env w =>
          if w = c₂.next then [e₁.evalE env, e₂.evalE env]
          else if w = c₂.next + 1 then [e₁.evalE env + e₂.evalE env]
          else if (c₁.ty w).isSome then c₁.mdl env w else c₂.mdl env w }
  | mul e₁ e₂, base =>
      let c₁ := e₁.compile base
      let c₂ := e₂.compile c₁.next
      { apps := c₁.apps ++ c₂.apps ++
          [.contract Dtype.Q .exact [c₁.out, c₂.out] c₂.next [0, 0] 0 pat0],
        out := c₂.next, next := c₂.next + 1,
        ty := fun w =>
          if w = c₂.next then some ⟨[], Dtype.Q⟩
          else mergeWt c₁.ty c₂.ty w,
        mdl := fun env w =>
          if w = c₂.next then [e₁.evalE env * e₂.evalE env]
          else if (c₁.ty w).isSome then c₁.mdl env w else c₂.mdl env w }

/-! ## Structural invariants -/

theorem mergeWt_of_left_none {f g : ℕ → Option TensorType} {w : ℕ}
    (h : f w = none) : mergeWt f g w = g w := by
  simp [mergeWt, h]

theorem mergeWt_cases {f g : ℕ → Option TensorType} {w : ℕ}
    {τ : TensorType} (h : mergeWt f g w = some τ) :
    f w = some τ ∨ g w = some τ := by
  cases hf : f w with
  | none => exact Or.inr ((mergeWt_of_left_none hf).symm.trans h)
  | some τ' => exact Or.inl ((mergeWt_left hf).symm.trans h)

/-! ### Projection equations (all definitional) -/

section ProjEq

variable (e₁ e₂ : PolyExpr) (base base' : ℕ)

theorem compile_add_apps :
    ((add e₁ e₂).compile base).apps
      = (e₁.compile base).apps ++ (e₂.compile (e₁.compile base).next).apps ++
        [.stack 2 [] [(e₁.compile base).out
            , (e₂.compile (e₁.compile base).next).out]
            (e₂.compile (e₁.compile base).next).next,
         .contract Dtype.Q .exact [(e₂.compile (e₁.compile base).next).next]
            ((e₂.compile (e₁.compile base).next).next + 1) [1] 0 patSum1] :=
  rfl

theorem compile_add_out :
    ((add e₁ e₂).compile base).out
      = (e₂.compile (e₁.compile base).next).next + 1 := rfl

theorem compile_add_next :
    ((add e₁ e₂).compile base).next
      = (e₂.compile (e₁.compile base).next).next + 2 := rfl

theorem compile_add_ty (w : ℕ) :
    ((add e₁ e₂).compile base).ty w
      = if w = (e₂.compile (e₁.compile base).next).next
          then some ⟨[2], Dtype.Q⟩
        else if w = (e₂.compile (e₁.compile base).next).next + 1
          then some ⟨[], Dtype.Q⟩
        else mergeWt (e₁.compile base).ty
          (e₂.compile (e₁.compile base).next).ty w := rfl

theorem compile_add_mdl (env : ℕ → ℚ) (w : ℕ) :
    ((add e₁ e₂).compile base).mdl env w
      = if w = (e₂.compile (e₁.compile base).next).next
          then [e₁.evalE env, e₂.evalE env]
        else if w = (e₂.compile (e₁.compile base).next).next + 1
          then [e₁.evalE env + e₂.evalE env]
        else if ((e₁.compile base).ty w).isSome
          then (e₁.compile base).mdl env w
          else (e₂.compile (e₁.compile base).next).mdl env w := rfl

theorem compile_mul_apps :
    ((mul e₁ e₂).compile base).apps
      = (e₁.compile base).apps ++ (e₂.compile (e₁.compile base).next).apps ++
        [.contract Dtype.Q .exact [(e₁.compile base).out
            , (e₂.compile (e₁.compile base).next).out]
            (e₂.compile (e₁.compile base).next).next [0, 0] 0 pat0] := rfl

theorem compile_mul_out :
    ((mul e₁ e₂).compile base).out
      = (e₂.compile (e₁.compile base).next).next := rfl

theorem compile_mul_next :
    ((mul e₁ e₂).compile base).next
      = (e₂.compile (e₁.compile base).next).next + 1 := rfl

theorem compile_mul_ty (w : ℕ) :
    ((mul e₁ e₂).compile base).ty w
      = if w = (e₂.compile (e₁.compile base).next).next
          then some ⟨[], Dtype.Q⟩
        else mergeWt (e₁.compile base).ty
          (e₂.compile (e₁.compile base).next).ty w := rfl

theorem compile_mul_mdl (env : ℕ → ℚ) (w : ℕ) :
    ((mul e₁ e₂).compile base).mdl env w
      = if w = (e₂.compile (e₁.compile base).next).next
          then [e₁.evalE env * e₂.evalE env]
        else if ((e₁.compile base).ty w).isSome
          then (e₁.compile base).mdl env w
          else (e₂.compile (e₁.compile base).next).mdl env w := rfl

theorem compile_tap_next (w : ℕ) :
    ((tap w).compile base').next = base' := rfl

theorem compile_qconst_apps (q : ℚ) :
    ((qconst q).compile base').apps
      = [.const ⟨[], Dtype.Q⟩ (qv0 q) base'] := rfl

theorem compile_qconst_out (q : ℚ) :
    ((qconst q).compile base').out = base' := rfl

theorem compile_qconst_next (q : ℚ) :
    ((qconst q).compile base').next = base' + 1 := rfl

theorem compile_qconst_ty (q : ℚ) (w : ℕ) :
    ((qconst q).compile base').ty w
      = if w = base' then some ⟨[], Dtype.Q⟩ else none := rfl

theorem compile_qconst_mdl (q : ℚ) (env : ℕ → ℚ) (w : ℕ) :
    ((qconst q).compile base').mdl env w
      = if w = base' then [q] else [] := rfl

end ProjEq

/-! ### Wire-list equations for the emitted applications -/

theorem mem_producedW_pair {w : ℕ} {a b : PrimApp} :
    w ∈ producedW [a, b] ↔ w ∈ a.outputWires ∨ w ∈ b.outputWires := by
  simp [producedW]

theorem mem_producedW_single {w : ℕ} {a : PrimApp} :
    w ∈ producedW [a] ↔ w ∈ a.outputWires := by
  simp [producedW]

theorem mem_consumedW_pair {w : ℕ} {a b : PrimApp} :
    w ∈ consumedW [a, b] ↔ w ∈ a.inputWires ∨ w ∈ b.inputWires := by
  simp [consumedW]

theorem mem_consumedW_single {w : ℕ} {a : PrimApp} :
    w ∈ consumedW [a] ↔ w ∈ a.inputWires := by
  simp [consumedW]

/-- `List.nodup_append`, with the disjointness clause bound at `ℕ` (the
`Wire` abbreviation is opaque to the arithmetic automation). -/
theorem nodup_append_nat {l₁ l₂ : List Wire} (h₁ : l₁.Nodup)
    (h₂ : l₂.Nodup)
    (hd : ∀ a : ℕ, a ∈ l₁ → ∀ b : ℕ, b ∈ l₂ → a ≠ b) :
    (l₁ ++ l₂).Nodup :=
  List.nodup_append.mpr ⟨h₁, h₂, fun a ha b hb => hd a ha b hb⟩

/-- `Acyclic.append`, with the seam clause bound at `ℕ`. -/
theorem acyclic_append_nat {l₁ l₂ : List PrimApp}
    (h₁ : Acyclic l₁) (h₂ : Acyclic l₂)
    (hcross : ∀ w : ℕ, w ∈ consumedW l₁ → w ∈ producedW l₂ → False) :
    Acyclic (l₁ ++ l₂) :=
  Acyclic.append h₁ h₂ (fun w hw₁ hw₂ => hcross w hw₁ hw₂)

/-! ### Allocation bounds -/

theorem compile_le (e : PolyExpr) (base : ℕ) :
    base ≤ (e.compile base).next := by
  induction e generalizing base with
  | tap w => exact Nat.le_refl _
  | qconst q => exact Nat.le_succ _
  | add e₁ e₂ ih₁ ih₂ =>
    have h₁ := ih₁ base
    have h₂ := ih₂ (e₁.compile base).next
    rw [compile_add_next]
    omega
  | mul e₁ e₂ ih₁ ih₂ =>
    have h₁ := ih₁ base
    have h₂ := ih₂ (e₁.compile base).next
    rw [compile_mul_next]
    omega

/-- Outside the allocation, the compiled typing is empty. -/
theorem compile_ty_none (e : PolyExpr) (base : ℕ) {w : ℕ}
    (h : w < base ∨ (e.compile base).next ≤ w) :
    (e.compile base).ty w = none := by
  induction e generalizing base with
  | tap w' => rfl
  | qconst q =>
    rw [compile_qconst_next] at h
    have hn : ¬(w = base) := by rcases h with h | h <;> omega
    show (if w = base then some (⟨[], Dtype.Q⟩ : TensorType) else none)
      = none
    rw [if_neg hn]
  | add e₁ e₂ ih₁ ih₂ =>
    have hle₁ := compile_le e₁ base
    have hle₂ := compile_le e₂ (e₁.compile base).next
    rw [compile_add_next] at h
    have hn1 : ¬(w = (e₂.compile (e₁.compile base).next).next) := by
      rcases h with h | h <;> omega
    have hn2 : ¬(w = (e₂.compile (e₁.compile base).next).next + 1) := by
      rcases h with h | h <;> omega
    have hty₁ : (e₁.compile base).ty w = none := by
      refine ih₁ base ?_
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hty₂ : (e₂.compile (e₁.compile base).next).ty w = none := by
      refine ih₂ (e₁.compile base).next ?_
      rcases h with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rw [compile_add_ty, if_neg hn1, if_neg hn2,
      mergeWt_of_left_none hty₁]
    exact hty₂
  | mul e₁ e₂ ih₁ ih₂ =>
    have hle₁ := compile_le e₁ base
    have hle₂ := compile_le e₂ (e₁.compile base).next
    rw [compile_mul_next] at h
    have hn1 : ¬(w = (e₂.compile (e₁.compile base).next).next) := by
      rcases h with h | h <;> omega
    have hty₁ : (e₁.compile base).ty w = none := by
      refine ih₁ base ?_
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hty₂ : (e₂.compile (e₁.compile base).next).ty w = none := by
      refine ih₂ (e₁.compile base).next ?_
      rcases h with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rw [compile_mul_ty, if_neg hn1,
      mergeWt_of_left_none hty₁]
    exact hty₂

theorem compile_ty_domain (e : PolyExpr) (base : ℕ) {w : ℕ}
    {τ : TensorType} (h : (e.compile base).ty w = some τ) :
    base ≤ w ∧ w < (e.compile base).next := by
  rcases Nat.lt_or_ge w base with h' | h'
  · rw [compile_ty_none e base (Or.inl h')] at h
    exact nomatch h
  · rcases Nat.lt_or_ge w (e.compile base).next with h'' | h''
    · exact ⟨h', h''⟩
    · rw [compile_ty_none e base (Or.inr h'')] at h
      exact nomatch h

/-! ### The output wire -/

theorem compile_add_ty_v (e₁ e₂ : PolyExpr) (base : ℕ) :
    ((add e₁ e₂).compile base).ty (e₂.compile (e₁.compile base).next).next
      = some ⟨[2], Dtype.Q⟩ := by
  rw [compile_add_ty, if_pos rfl]

theorem compile_add_ty_out (e₁ e₂ : PolyExpr) (base : ℕ) :
    ((add e₁ e₂).compile base).ty
        ((e₂.compile (e₁.compile base).next).next + 1)
      = some ⟨[], Dtype.Q⟩ := by
  have hn : ¬((e₂.compile (e₁.compile base).next).next + 1
      = (e₂.compile (e₁.compile base).next).next) := by omega
  rw [compile_add_ty, if_neg hn, if_pos rfl]

theorem compile_mul_ty_out (e₁ e₂ : PolyExpr) (base : ℕ) :
    ((mul e₁ e₂).compile base).ty (e₂.compile (e₁.compile base).next).next
      = some ⟨[], Dtype.Q⟩ := by
  rw [compile_mul_ty, if_pos rfl]

/-- The output wire is a tap or a freshly allocated scalar. -/
theorem compile_out (e : PolyExpr) (base : ℕ) :
    (e.compile base).out ∈ e.taps ∨
      ((e.compile base).ty (e.compile base).out = some ⟨[], Dtype.Q⟩ ∧
       base ≤ (e.compile base).out ∧
       (e.compile base).out < (e.compile base).next) := by
  induction e generalizing base with
  | tap w => exact Or.inl (List.mem_singleton.mpr rfl)
  | qconst q =>
    refine Or.inr ⟨?_, Nat.le_refl _, Nat.lt_succ_self _⟩
    show (if base = base then some (⟨[], Dtype.Q⟩ : TensorType)
        else none)
      = some (⟨[], Dtype.Q⟩ : TensorType)
    rw [if_pos rfl]
  | add e₁ e₂ ih₁ ih₂ =>
    have hle₁ := compile_le e₁ base
    have hle₂ := compile_le e₂ (e₁.compile base).next
    refine Or.inr ⟨?_, ?_, ?_⟩
    · rw [compile_add_out]
      exact compile_add_ty_out e₁ e₂ base
    · rw [compile_add_out]
      omega
    · rw [compile_add_out, compile_add_next]
      omega
  | mul e₁ e₂ ih₁ ih₂ =>
    have hle₁ := compile_le e₁ base
    have hle₂ := compile_le e₂ (e₁.compile base).next
    refine Or.inr ⟨?_, ?_, ?_⟩
    · rw [compile_mul_out]
      exact compile_mul_ty_out e₁ e₂ base
    · rw [compile_mul_out]
      omega
    · rw [compile_mul_out, compile_mul_next]
      omega

theorem compile_out_cases (e : PolyExpr) (base : ℕ) :
    (e.compile base).out ∈ e.taps ∨
      (base ≤ (e.compile base).out ∧
       (e.compile base).out < (e.compile base).next) := by
  rcases compile_out e base with h | ⟨-, h₁, h₂⟩
  · exact Or.inl h
  · exact Or.inr ⟨h₁, h₂⟩

/-! ### Produced wires: bounds and linearity -/

theorem compile_produced_bounds (e : PolyExpr) (base : ℕ) :
    ∀ w : ℕ, w ∈ producedW (e.compile base).apps →
      base ≤ w ∧ w < (e.compile base).next := by
  induction e generalizing base with
  | tap w' => intro w hw; exact nomatch hw
  | qconst q =>
    intro w hw
    have hw' : w = base := List.mem_singleton.mp (mem_producedW_single.mp hw)
    subst hw'
    exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
  | add e₁ e₂ ih₁ ih₂ =>
    intro w hw
    have hle₁ := compile_le e₁ base
    have hle₂ := compile_le e₂ (e₁.compile base).next
    rw [compile_add_apps, producedW_append, producedW_append] at hw
    rw [compile_add_next]
    rcases List.mem_append.mp hw with hw' | hw'
    · rcases List.mem_append.mp hw' with hw'' | hw''
      · obtain ⟨h1, h2⟩ := ih₁ base w hw''
        omega
      · obtain ⟨h1, h2⟩ := ih₂ (e₁.compile base).next w hw''
        omega
    · rcases mem_producedW_pair.mp hw' with h | h
      · have h' := List.mem_singleton.mp h
        omega
      · have h' := List.mem_singleton.mp h
        omega
  | mul e₁ e₂ ih₁ ih₂ =>
    intro w hw
    have hle₁ := compile_le e₁ base
    have hle₂ := compile_le e₂ (e₁.compile base).next
    rw [compile_mul_apps, producedW_append, producedW_append] at hw
    rw [compile_mul_next]
    rcases List.mem_append.mp hw with hw' | hw'
    · rcases List.mem_append.mp hw' with hw'' | hw''
      · obtain ⟨h1, h2⟩ := ih₁ base w hw''
        omega
      · obtain ⟨h1, h2⟩ := ih₂ (e₁.compile base).next w hw''
        omega
    · have h' := List.mem_singleton.mp (mem_producedW_single.mp hw')
      omega

theorem compile_produced_nodup (e : PolyExpr) (base : ℕ) :
    (producedW (e.compile base).apps).Nodup := by
  induction e generalizing base with
  | tap w => exact List.nodup_nil
  | qconst q =>
    show (producedW [PrimApp.const ⟨[], Dtype.Q⟩ (qv0 q) base]).Nodup
    simp [producedW, PrimApp.outputWires]
  | add e₁ e₂ ih₁ ih₂ =>
    have hb₁ := compile_produced_bounds e₁ base
    have hb₂ := compile_produced_bounds e₂ (e₁.compile base).next
    have hle₁ := compile_le e₁ base
    have hle₂ := compile_le e₂ (e₁.compile base).next
    rw [compile_add_apps, producedW_append, producedW_append]
    refine nodup_append_nat (nodup_append_nat
      (ih₁ base) (ih₂ (e₁.compile base).next) ?_) ?_ ?_
    · intro w hw₁ w' hw₂ he
      subst he
      obtain ⟨h1, h2⟩ := hb₁ w hw₁
      obtain ⟨h3, h4⟩ := hb₂ w hw₂
      omega
    · show ((e₂.compile (e₁.compile base).next).next ::
        [(e₂.compile (e₁.compile base).next).next + 1]).Nodup
      refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
      intro hmem
      have h := List.mem_singleton.mp hmem
      omega
    · intro w hw₁ w' hw₂ he
      subst he
      have hwb : base ≤ w ∧ w < (e₂.compile (e₁.compile base).next).next := by
        rcases List.mem_append.mp hw₁ with hm | hm
        · obtain ⟨h1, h2⟩ := hb₁ w hm
          omega
        · obtain ⟨h1, h2⟩ := hb₂ w hm
          omega
      obtain ⟨hwb1, hwb2⟩ := hwb
      rcases mem_producedW_pair.mp hw₂ with h | h
      · have h' := List.mem_singleton.mp h
        omega
      · have h' := List.mem_singleton.mp h
        omega
  | mul e₁ e₂ ih₁ ih₂ =>
    have hb₁ := compile_produced_bounds e₁ base
    have hb₂ := compile_produced_bounds e₂ (e₁.compile base).next
    have hle₁ := compile_le e₁ base
    have hle₂ := compile_le e₂ (e₁.compile base).next
    rw [compile_mul_apps, producedW_append, producedW_append]
    refine nodup_append_nat (nodup_append_nat
      (ih₁ base) (ih₂ (e₁.compile base).next) ?_) ?_ ?_
    · intro w hw₁ w' hw₂ he
      subst he
      obtain ⟨h1, h2⟩ := hb₁ w hw₁
      obtain ⟨h3, h4⟩ := hb₂ w hw₂
      omega
    · show ([(e₂.compile (e₁.compile base).next).next] : List ℕ).Nodup
      exact List.nodup_singleton _
    · intro w hw₁ w' hw₂ he
      subst he
      have h' := List.mem_singleton.mp (mem_producedW_single.mp hw₂)
      rcases List.mem_append.mp hw₁ with hm | hm
      · obtain ⟨h1, h2⟩ := hb₁ w hm
        omega
      · obtain ⟨h1, h2⟩ := hb₂ w hm
        omega

/-! ### Consumed wires: bounds and linearity -/

theorem compile_consumed_bounds (e : PolyExpr) (base : ℕ) :
    ∀ w : ℕ, w ∈ consumedW (e.compile base).apps →
      w ∈ e.taps ∨ (base ≤ w ∧ w < (e.compile base).next) := by
  induction e generalizing base with
  | tap w' => intro w hw; exact nomatch hw
  | qconst q =>
    intro w hw
    exact nomatch mem_consumedW_single.mp hw
  | add e₁ e₂ ih₁ ih₂ =>
    intro w hw
    have hle₁ := compile_le e₁ base
    have hle₂ := compile_le e₂ (e₁.compile base).next
    have ho₁ := compile_out_cases e₁ base
    have ho₂ := compile_out_cases e₂ (e₁.compile base).next
    rw [compile_add_apps, consumedW_append, consumedW_append] at hw
    rw [compile_add_next]
    show w ∈ e₁.taps ++ e₂.taps ∨ _
    rcases List.mem_append.mp hw with hw' | hw'
    · rcases List.mem_append.mp hw' with hw'' | hw''
      · rcases ih₁ base w hw'' with h | ⟨h1, h2⟩
        · exact Or.inl (List.mem_append_left _ h)
        · exact Or.inr ⟨h1, by omega⟩
      · rcases ih₂ (e₁.compile base).next w hw'' with h | ⟨h1, h2⟩
        · exact Or.inl (List.mem_append_right _ h)
        · exact Or.inr ⟨by omega, by omega⟩
    · rcases mem_consumedW_pair.mp hw' with h | h
      · rcases List.mem_cons.mp h with h' | h'
        · subst h'
          rcases ho₁ with h'' | ⟨h1, h2⟩
          · exact Or.inl (List.mem_append_left _ h'')
          · exact Or.inr ⟨h1, by omega⟩
        · have h'' := List.mem_singleton.mp h'
          subst h''
          rcases ho₂ with h'' | ⟨h1, h2⟩
          · exact Or.inl (List.mem_append_right _ h'')
          · exact Or.inr ⟨by omega, by omega⟩
      · have h' := List.mem_singleton.mp h
        subst h'
        exact Or.inr ⟨by omega, by omega⟩
  | mul e₁ e₂ ih₁ ih₂ =>
    intro w hw
    have hle₁ := compile_le e₁ base
    have hle₂ := compile_le e₂ (e₁.compile base).next
    have ho₁ := compile_out_cases e₁ base
    have ho₂ := compile_out_cases e₂ (e₁.compile base).next
    rw [compile_mul_apps, consumedW_append, consumedW_append] at hw
    rw [compile_mul_next]
    show w ∈ e₁.taps ++ e₂.taps ∨ _
    rcases List.mem_append.mp hw with hw' | hw'
    · rcases List.mem_append.mp hw' with hw'' | hw''
      · rcases ih₁ base w hw'' with h | ⟨h1, h2⟩
        · exact Or.inl (List.mem_append_left _ h)
        · exact Or.inr ⟨h1, by omega⟩
      · rcases ih₂ (e₁.compile base).next w hw'' with h | ⟨h1, h2⟩
        · exact Or.inl (List.mem_append_right _ h)
        · exact Or.inr ⟨by omega, by omega⟩
    · rcases List.mem_cons.mp (mem_consumedW_single.mp hw') with h' | h'
      · subst h'
        rcases ho₁ with h'' | ⟨h1, h2⟩
        · exact Or.inl (List.mem_append_left _ h'')
        · exact Or.inr ⟨h1, by omega⟩
      · have h'' := List.mem_singleton.mp h'
        subst h''
        rcases ho₂ with h'' | ⟨h1, h2⟩
        · exact Or.inl (List.mem_append_right _ h'')
        · exact Or.inr ⟨by omega, by omega⟩

/-- The output wire is never consumed inside its own compilation. -/
theorem compile_out_not_consumed (e : PolyExpr) (base : ℕ)
    (htb : ∀ w ∈ e.taps, w < base) :
    (e.compile base).out ∉ consumedW (e.compile base).apps := by
  induction e generalizing base with
  | tap w => exact fun h => nomatch h
  | qconst q => exact fun h => nomatch mem_consumedW_single.mp h
  | add e₁ e₂ ih₁ ih₂ =>
    intro hmem
    have hle₁ := compile_le e₁ base
    have hle₂ := compile_le e₂ (e₁.compile base).next
    have hcb₁ := compile_consumed_bounds e₁ base
    have hcb₂ := compile_consumed_bounds e₂ (e₁.compile base).next
    have ho₁ := compile_out_cases e₁ base
    have ho₂ := compile_out_cases e₂ (e₁.compile base).next
    have htb₁ : ∀ w ∈ e₁.taps, w < base :=
      fun w hw => htb w (List.mem_append_left _ hw)
    have htb₂ : ∀ w ∈ e₂.taps, w < base :=
      fun w hw => htb w (List.mem_append_right _ hw)
    rw [compile_add_out] at hmem
    rw [compile_add_apps, consumedW_append, consumedW_append] at hmem
    rcases List.mem_append.mp hmem with hm | hm
    · rcases List.mem_append.mp hm with hm' | hm'
      · rcases hcb₁ _ hm' with h | ⟨h1, h2⟩
        · have := htb₁ _ h; omega
        · omega
      · rcases hcb₂ _ hm' with h | ⟨h1, h2⟩
        · have := htb₂ _ h; omega
        · omega
    · rcases mem_consumedW_pair.mp hm with h | h
      · rcases List.mem_cons.mp h with h' | h'
        · rcases ho₁ with h'' | ⟨h1, h2⟩
          · have := htb₁ _ h''; omega
          · omega
        · have h'' := List.mem_singleton.mp h'
          rcases ho₂ with h₃ | ⟨h1, h2⟩
          · have h₄ := htb₂ _ h₃; omega
          · omega
      · have h' := List.mem_singleton.mp h
        omega
  | mul e₁ e₂ ih₁ ih₂ =>
    intro hmem
    have hle₁ := compile_le e₁ base
    have hle₂ := compile_le e₂ (e₁.compile base).next
    have hcb₁ := compile_consumed_bounds e₁ base
    have hcb₂ := compile_consumed_bounds e₂ (e₁.compile base).next
    have ho₁ := compile_out_cases e₁ base
    have ho₂ := compile_out_cases e₂ (e₁.compile base).next
    have htb₁ : ∀ w ∈ e₁.taps, w < base :=
      fun w hw => htb w (List.mem_append_left _ hw)
    have htb₂ : ∀ w ∈ e₂.taps, w < base :=
      fun w hw => htb w (List.mem_append_right _ hw)
    rw [compile_mul_out] at hmem
    rw [compile_mul_apps, consumedW_append, consumedW_append] at hmem
    rcases List.mem_append.mp hmem with hm | hm
    · rcases List.mem_append.mp hm with hm' | hm'
      · rcases hcb₁ _ hm' with h | ⟨h1, h2⟩
        · have := htb₁ _ h; omega
        · omega
      · rcases hcb₂ _ hm' with h | ⟨h1, h2⟩
        · have := htb₂ _ h; omega
        · omega
    · rcases List.mem_cons.mp (mem_consumedW_single.mp hm) with h' | h'
      · rcases ho₁ with h'' | ⟨h1, h2⟩
        · have := htb₁ _ h''; omega
        · omega
      · have h'' := List.mem_singleton.mp h'
        rcases ho₂ with h₃ | ⟨h1, h2⟩
        · have h₄ := htb₂ _ h₃; omega
        · omega

theorem compile_consumed_nodup (e : PolyExpr) (base : ℕ)
    (htn : e.taps.Nodup) (htb : ∀ w ∈ e.taps, w < base) :
    (consumedW (e.compile base).apps).Nodup := by
  induction e generalizing base with
  | tap w => exact List.nodup_nil
  | qconst q =>
    show (consumedW [PrimApp.const ⟨[], Dtype.Q⟩ (qv0 q) base]).Nodup
    exact List.nodup_nil
  | add e₁ e₂ ih₁ ih₂ =>
    obtain ⟨htn₁, htn₂, hdisj⟩ := List.nodup_append.mp htn
    have htb₁ : ∀ w ∈ e₁.taps, w < base :=
      fun w hw => htb w (List.mem_append_left _ hw)
    have htb₂' : ∀ w ∈ e₂.taps, w < base :=
      fun w hw => htb w (List.mem_append_right _ hw)
    have hle₁ := compile_le e₁ base
    have hle₂ := compile_le e₂ (e₁.compile base).next
    have hcb₁ := compile_consumed_bounds e₁ base
    have hcb₂ := compile_consumed_bounds e₂ (e₁.compile base).next
    have ho₁ := compile_out_cases e₁ base
    have ho₂ := compile_out_cases e₂ (e₁.compile base).next
    have htb₂ : ∀ w ∈ e₂.taps, w < (e₁.compile base).next :=
      fun w hw => by have := htb₂' w hw; omega
    have hnc₁ := compile_out_not_consumed e₁ base htb₁
    have hnc₂ := compile_out_not_consumed e₂ (e₁.compile base).next htb₂
    have hne : ¬((e₁.compile base).out
        = (e₂.compile (e₁.compile base).next).out) := by
      intro he
      rcases ho₁ with h1 | ⟨h1a, h1b⟩ <;> rcases ho₂ with h2 | ⟨h2a, h2b⟩
      · exact hdisj _ h1 _ (he ▸ h2) rfl
      · have := htb₁ _ h1; omega
      · have := htb₂' _ h2; omega
      · omega
    rw [compile_add_apps, consumedW_append, consumedW_append]
    refine nodup_append_nat (nodup_append_nat
      (ih₁ base htn₁ htb₁) (ih₂ (e₁.compile base).next htn₂ htb₂) ?_)
      ?_ ?_
    · intro w hw₁ w' hw₂ he
      subst he
      rcases hcb₁ w hw₁ with h1 | ⟨h1a, h1b⟩ <;>
        rcases hcb₂ w hw₂ with h2 | ⟨h2a, h2b⟩
      · exact hdisj _ h1 _ h2 rfl
      · have := htb₁ w h1; omega
      · have := htb₂' w h2; omega
      · omega
    · show ((e₁.compile base).out ::
        [(e₂.compile (e₁.compile base).next).out] ++
        [(e₂.compile (e₁.compile base).next).next]).Nodup
      have hno₁ : ¬((e₁.compile base).out
          = (e₂.compile (e₁.compile base).next).next) := by
        rcases ho₁ with h1 | ⟨h1a, h1b⟩
        · have := htb₁ _ h1; omega
        · omega
      have hno₂ : ¬((e₂.compile (e₁.compile base).next).out
          = (e₂.compile (e₁.compile base).next).next) := by
        rcases ho₂ with h2 | ⟨h2a, h2b⟩
        · have := htb₂' _ h2; omega
        · omega
      refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr
        ⟨?_, List.nodup_singleton _⟩⟩
      · intro hmem
        rcases List.mem_cons.mp hmem with h | h
        · exact hne h
        · exact hno₁ (List.mem_singleton.mp h)
      · intro hmem
        exact hno₂ (List.mem_singleton.mp hmem)
    · intro w hw₁ w' hw₂ he
      subst he
      rcases mem_consumedW_pair.mp hw₂ with h | h
      · rcases List.mem_cons.mp h with h' | h'
        · subst h'
          rcases List.mem_append.mp hw₁ with hm | hm
          · exact hnc₁ hm
          · rcases hcb₂ _ hm with h2 | ⟨h2a, h2b⟩
            · rcases ho₁ with h1 | ⟨h1a, h1b⟩
              · exact hdisj _ h1 _ h2 rfl
              · have := htb₂' _ h2; omega
            · rcases ho₁ with h1 | ⟨h1a, h1b⟩
              · have := htb₁ _ h1; omega
              · omega
        · have h'' := List.mem_singleton.mp h'
          subst h''
          rcases List.mem_append.mp hw₁ with hm | hm
          · rcases hcb₁ _ hm with h1 | ⟨h1a, h1b⟩
            · rcases ho₂ with h2 | ⟨h2a, h2b⟩
              · exact hdisj _ h1 _ h2 rfl
              · have := htb₁ _ h1; omega
            · rcases ho₂ with h2 | ⟨h2a, h2b⟩
              · have := htb₂' _ h2; omega
              · omega
          · exact hnc₂ hm
      · have h' := List.mem_singleton.mp h
        subst h'
        rcases List.mem_append.mp hw₁ with hm | hm
        · rcases hcb₁ _ hm with h1 | ⟨h1a, h1b⟩
          · have := htb₁ _ h1; omega
          · omega
        · rcases hcb₂ _ hm with h2 | ⟨h2a, h2b⟩
          · have := htb₂' _ h2; omega
          · omega
  | mul e₁ e₂ ih₁ ih₂ =>
    obtain ⟨htn₁, htn₂, hdisj⟩ := List.nodup_append.mp htn
    have htb₁ : ∀ w ∈ e₁.taps, w < base :=
      fun w hw => htb w (List.mem_append_left _ hw)
    have htb₂' : ∀ w ∈ e₂.taps, w < base :=
      fun w hw => htb w (List.mem_append_right _ hw)
    have hle₁ := compile_le e₁ base
    have hle₂ := compile_le e₂ (e₁.compile base).next
    have hcb₁ := compile_consumed_bounds e₁ base
    have hcb₂ := compile_consumed_bounds e₂ (e₁.compile base).next
    have ho₁ := compile_out_cases e₁ base
    have ho₂ := compile_out_cases e₂ (e₁.compile base).next
    have htb₂ : ∀ w ∈ e₂.taps, w < (e₁.compile base).next :=
      fun w hw => by have := htb₂' w hw; omega
    have hnc₁ := compile_out_not_consumed e₁ base htb₁
    have hnc₂ := compile_out_not_consumed e₂ (e₁.compile base).next htb₂
    have hne : ¬((e₁.compile base).out
        = (e₂.compile (e₁.compile base).next).out) := by
      intro he
      rcases ho₁ with h1 | ⟨h1a, h1b⟩ <;> rcases ho₂ with h2 | ⟨h2a, h2b⟩
      · exact hdisj _ h1 _ (he ▸ h2) rfl
      · have := htb₁ _ h1; omega
      · have := htb₂' _ h2; omega
      · omega
    rw [compile_mul_apps, consumedW_append, consumedW_append]
    refine nodup_append_nat (nodup_append_nat
      (ih₁ base htn₁ htb₁) (ih₂ (e₁.compile base).next htn₂ htb₂) ?_)
      ?_ ?_
    · intro w hw₁ w' hw₂ he
      subst he
      rcases hcb₁ w hw₁ with h1 | ⟨h1a, h1b⟩ <;>
        rcases hcb₂ w hw₂ with h2 | ⟨h2a, h2b⟩
      · exact hdisj _ h1 _ h2 rfl
      · have := htb₁ w h1; omega
      · have := htb₂' w h2; omega
      · omega
    · show ((e₁.compile base).out ::
        [(e₂.compile (e₁.compile base).next).out]).Nodup
      refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
      intro hmem
      exact hne (List.mem_singleton.mp hmem)
    · intro w hw₁ w' hw₂ he
      subst he
      rcases List.mem_cons.mp (mem_consumedW_single.mp hw₂) with h' | h'
      · subst h'
        rcases List.mem_append.mp hw₁ with hm | hm
        · exact hnc₁ hm
        · rcases hcb₂ _ hm with h2 | ⟨h2a, h2b⟩
          · rcases ho₁ with h1 | ⟨h1a, h1b⟩
            · exact hdisj _ h1 _ h2 rfl
            · have := htb₂' _ h2; omega
          · rcases ho₁ with h1 | ⟨h1a, h1b⟩
            · have := htb₁ _ h1; omega
            · omega
      · have h'' := List.mem_singleton.mp h'
        subst h''
        rcases List.mem_append.mp hw₁ with hm | hm
        · rcases hcb₁ _ hm with h1 | ⟨h1a, h1b⟩
          · rcases ho₂ with h2 | ⟨h2a, h2b⟩
            · exact hdisj _ h1 _ h2 rfl
            · have := htb₁ _ h1; omega
          · rcases ho₂ with h2 | ⟨h2a, h2b⟩
            · have := htb₂' _ h2; omega
            · omega
        · exact hnc₂ hm

/-! ### Acyclicity -/

theorem acyclic_nil : Acyclic ([] : List PrimApp) :=
  fun i => i.elim0

theorem acyclic_single {a : PrimApp}
    (h : ∀ w : ℕ, w ∈ a.inputWires → w ∉ a.outputWires) : Acyclic [a] := by
  intro i w hw j hj
  have hieq : i = ⟨0, by simp⟩ := Fin.ext (Nat.lt_one_iff.mp i.isLt)
  have hjeq : j = ⟨0, by simp⟩ := Fin.ext (Nat.lt_one_iff.mp j.isLt)
  subst hieq
  subst hjeq
  exact absurd hj (h w hw)

theorem compile_acyclic (e : PolyExpr) (base : ℕ)
    (htb : ∀ w ∈ e.taps, w < base) :
    Acyclic (e.compile base).apps := by
  induction e generalizing base with
  | tap w => exact acyclic_nil
  | qconst q =>
    exact acyclic_single (fun w hw => nomatch hw)
  | add e₁ e₂ ih₁ ih₂ =>
    have htb₁ : ∀ w ∈ e₁.taps, w < base :=
      fun w hw => htb w (List.mem_append_left _ hw)
    have htb₂' : ∀ w ∈ e₂.taps, w < base :=
      fun w hw => htb w (List.mem_append_right _ hw)
    have hle₁ := compile_le e₁ base
    have hle₂ := compile_le e₂ (e₁.compile base).next
    have hcb₁ := compile_consumed_bounds e₁ base
    have hcb₂ := compile_consumed_bounds e₂ (e₁.compile base).next
    have hpb₂ := compile_produced_bounds e₂ (e₁.compile base).next
    have ho₁ := compile_out_cases e₁ base
    have ho₂ := compile_out_cases e₂ (e₁.compile base).next
    have htb₂ : ∀ w ∈ e₂.taps, w < (e₁.compile base).next :=
      fun w hw => by have := htb₂' w hw; omega
    rw [compile_add_apps]
    refine acyclic_append_nat (acyclic_append_nat (ih₁ base htb₁)
      (ih₂ (e₁.compile base).next htb₂) ?_) ?_ ?_
    · intro w hw₁ hw₂
      obtain ⟨h2a, h2b⟩ := hpb₂ w hw₂
      rcases hcb₁ w hw₁ with h1 | ⟨h1a, h1b⟩
      · have := htb₁ w h1; omega
      · omega
    · refine acyclic_append_nat (acyclic_single ?_) (acyclic_single ?_) ?_
      · intro w hw hmem
        have hv := List.mem_singleton.mp hmem
        rcases List.mem_cons.mp hw with h' | h'
        · subst h'
          rcases ho₁ with h1 | ⟨h1a, h1b⟩
          · have := htb₁ _ h1; omega
          · omega
        · have h'' := List.mem_singleton.mp h'
          subst h''
          rcases ho₂ with h2 | ⟨h2a, h2b⟩
          · have := htb₂' _ h2; omega
          · omega
      · intro w hw hmem
        have hv := List.mem_singleton.mp hmem
        have hw' := List.mem_singleton.mp hw
        omega
      · intro w hw₁ hw₂
        have hv := List.mem_singleton.mp (mem_producedW_single.mp hw₂)
        rcases List.mem_cons.mp (mem_consumedW_single.mp hw₁) with h' | h'
        · subst h'
          rcases ho₁ with h1 | ⟨h1a, h1b⟩
          · have := htb₁ _ h1; omega
          · omega
        · have h'' := List.mem_singleton.mp h'
          subst h''
          rcases ho₂ with h2 | ⟨h2a, h2b⟩
          · have := htb₂' _ h2; omega
          · omega
    · intro w hw₁ hw₂
      have hwb : w ∈ e₁.taps ∨ w ∈ e₂.taps ∨
          (base ≤ w ∧ w < (e₂.compile (e₁.compile base).next).next) := by
        rw [consumedW_append] at hw₁
        rcases List.mem_append.mp hw₁ with hm | hm
        · rcases hcb₁ w hm with h | ⟨ha', hb'⟩
          · exact Or.inl h
          · exact Or.inr (Or.inr ⟨ha', by omega⟩)
        · rcases hcb₂ w hm with h | ⟨ha', hb'⟩
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ⟨by omega, hb'⟩)
      rcases mem_producedW_pair.mp hw₂ with h | h
      · have hv := List.mem_singleton.mp h
        rcases hwb with h' | h' | ⟨h'a, h'b⟩
        · have := htb₁ w h'; omega
        · have := htb₂' w h'; omega
        · omega
      · have hv := List.mem_singleton.mp h
        rcases hwb with h' | h' | ⟨h'a, h'b⟩
        · have := htb₁ w h'; omega
        · have := htb₂' w h'; omega
        · omega
  | mul e₁ e₂ ih₁ ih₂ =>
    have htb₁ : ∀ w ∈ e₁.taps, w < base :=
      fun w hw => htb w (List.mem_append_left _ hw)
    have htb₂' : ∀ w ∈ e₂.taps, w < base :=
      fun w hw => htb w (List.mem_append_right _ hw)
    have hle₁ := compile_le e₁ base
    have hle₂ := compile_le e₂ (e₁.compile base).next
    have hcb₁ := compile_consumed_bounds e₁ base
    have hcb₂ := compile_consumed_bounds e₂ (e₁.compile base).next
    have hpb₂ := compile_produced_bounds e₂ (e₁.compile base).next
    have ho₁ := compile_out_cases e₁ base
    have ho₂ := compile_out_cases e₂ (e₁.compile base).next
    have htb₂ : ∀ w ∈ e₂.taps, w < (e₁.compile base).next :=
      fun w hw => by have := htb₂' w hw; omega
    rw [compile_mul_apps]
    refine acyclic_append_nat (acyclic_append_nat (ih₁ base htb₁)
      (ih₂ (e₁.compile base).next htb₂) ?_) (acyclic_single ?_) ?_
    · intro w hw₁ hw₂
      obtain ⟨h2a, h2b⟩ := hpb₂ w hw₂
      rcases hcb₁ w hw₁ with h1 | ⟨h1a, h1b⟩
      · have := htb₁ w h1; omega
      · omega
    · intro w hw hmem
      have hv := List.mem_singleton.mp hmem
      rcases List.mem_cons.mp hw with h' | h'
      · subst h'
        rcases ho₁ with h1 | ⟨h1a, h1b⟩
        · have := htb₁ _ h1; omega
        · omega
      · have h'' := List.mem_singleton.mp h'
        subst h''
        rcases ho₂ with h2 | ⟨h2a, h2b⟩
        · have := htb₂' _ h2; omega
        · omega
    · intro w hw₁ hw₂
      have hv := List.mem_singleton.mp (mem_producedW_single.mp hw₂)
      rw [consumedW_append] at hw₁
      rcases List.mem_append.mp hw₁ with hm | hm
      · rcases hcb₁ w hm with h | ⟨ha', hb'⟩
        · have := htb₁ w h; omega
        · omega
      · rcases hcb₂ w hm with h | ⟨ha', hb'⟩
        · have := htb₂' w h; omega
        · omega


/-! ### Typing transport into the composite -/

theorem compile_add_ty_left (e₁ e₂ : PolyExpr) (base : ℕ) {w : ℕ}
    {τ : TensorType} (h : (e₁.compile base).ty w = some τ) :
    ((add e₁ e₂).compile base).ty w = some τ := by
  obtain ⟨h1, h2⟩ := compile_ty_domain e₁ base h
  have hle₂ := compile_le e₂ (e₁.compile base).next
  have hn1 : ¬(w = (e₂.compile (e₁.compile base).next).next) := by omega
  have hn2 : ¬(w = (e₂.compile (e₁.compile base).next).next + 1) := by
    omega
  rw [compile_add_ty, if_neg hn1, if_neg hn2]
  exact mergeWt_left h

theorem compile_add_ty_right (e₁ e₂ : PolyExpr) (base : ℕ) {w : ℕ}
    {τ : TensorType}
    (h : (e₂.compile (e₁.compile base).next).ty w = some τ) :
    ((add e₁ e₂).compile base).ty w = some τ := by
  obtain ⟨h1, h2⟩ := compile_ty_domain e₂ (e₁.compile base).next h
  have hle₁ := compile_le e₁ base
  have hn1 : ¬(w = (e₂.compile (e₁.compile base).next).next) := by omega
  have hn2 : ¬(w = (e₂.compile (e₁.compile base).next).next + 1) := by
    omega
  rw [compile_add_ty, if_neg hn1, if_neg hn2,
    mergeWt_of_left_none (compile_ty_none e₁ base (Or.inr h1))]
  exact h

theorem compile_mul_ty_left (e₁ e₂ : PolyExpr) (base : ℕ) {w : ℕ}
    {τ : TensorType} (h : (e₁.compile base).ty w = some τ) :
    ((mul e₁ e₂).compile base).ty w = some τ := by
  obtain ⟨h1, h2⟩ := compile_ty_domain e₁ base h
  have hle₂ := compile_le e₂ (e₁.compile base).next
  have hn1 : ¬(w = (e₂.compile (e₁.compile base).next).next) := by omega
  rw [compile_mul_ty, if_neg hn1]
  exact mergeWt_left h

theorem compile_mul_ty_right (e₁ e₂ : PolyExpr) (base : ℕ) {w : ℕ}
    {τ : TensorType}
    (h : (e₂.compile (e₁.compile base).next).ty w = some τ) :
    ((mul e₁ e₂).compile base).ty w = some τ := by
  obtain ⟨h1, h2⟩ := compile_ty_domain e₂ (e₁.compile base).next h
  have hle₁ := compile_le e₁ base
  have hn1 : ¬(w = (e₂.compile (e₁.compile base).next).next) := by omega
  rw [compile_mul_ty, if_neg hn1,
    mergeWt_of_left_none (compile_ty_none e₁ base (Or.inr h1))]
  exact h

/-- The composite model restricted to the left part. -/
theorem compile_add_mdl_left (e₁ e₂ : PolyExpr) (base : ℕ) (env : ℕ → ℚ)
    {w : ℕ} (hs : ((e₁.compile base).ty w).isSome = true) :
    ((add e₁ e₂).compile base).mdl env w = (e₁.compile base).mdl env w := by
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨h1, h2⟩ := compile_ty_domain e₁ base hτ
  have hle₂ := compile_le e₂ (e₁.compile base).next
  have hn1 : ¬(w = (e₂.compile (e₁.compile base).next).next) := by omega
  have hn2 : ¬(w = (e₂.compile (e₁.compile base).next).next + 1) := by
    omega
  rw [compile_add_mdl, if_neg hn1, if_neg hn2, if_pos hs]

theorem compile_add_mdl_right (e₁ e₂ : PolyExpr) (base : ℕ) (env : ℕ → ℚ)
    {w : ℕ}
    (hs : ((e₂.compile (e₁.compile base).next).ty w).isSome = true) :
    ((add e₁ e₂).compile base).mdl env w
      = (e₂.compile (e₁.compile base).next).mdl env w := by
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨h1, h2⟩ := compile_ty_domain e₂ (e₁.compile base).next hτ
  have hle₁ := compile_le e₁ base
  have hn1 : ¬(w = (e₂.compile (e₁.compile base).next).next) := by omega
  have hn2 : ¬(w = (e₂.compile (e₁.compile base).next).next + 1) := by
    omega
  have hnone : (e₁.compile base).ty w = none :=
    compile_ty_none e₁ base (Or.inr h1)
  rw [compile_add_mdl, if_neg hn1, if_neg hn2,
    if_neg (by rw [hnone]; simp)]

theorem compile_mul_mdl_left (e₁ e₂ : PolyExpr) (base : ℕ) (env : ℕ → ℚ)
    {w : ℕ} (hs : ((e₁.compile base).ty w).isSome = true) :
    ((mul e₁ e₂).compile base).mdl env w = (e₁.compile base).mdl env w := by
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨h1, h2⟩ := compile_ty_domain e₁ base hτ
  have hle₂ := compile_le e₂ (e₁.compile base).next
  have hn1 : ¬(w = (e₂.compile (e₁.compile base).next).next) := by omega
  rw [compile_mul_mdl, if_neg hn1, if_pos hs]

theorem compile_mul_mdl_right (e₁ e₂ : PolyExpr) (base : ℕ) (env : ℕ → ℚ)
    {w : ℕ}
    (hs : ((e₂.compile (e₁.compile base).next).ty w).isSome = true) :
    ((mul e₁ e₂).compile base).mdl env w
      = (e₂.compile (e₁.compile base).next).mdl env w := by
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨h1, h2⟩ := compile_ty_domain e₂ (e₁.compile base).next hτ
  have hle₁ := compile_le e₁ base
  have hn1 : ¬(w = (e₂.compile (e₁.compile base).next).next) := by omega
  have hnone : (e₁.compile base).ty w = none :=
    compile_ty_none e₁ base (Or.inr h1)
  rw [compile_mul_mdl, if_neg hn1, if_neg (by rw [hnone]; simp)]

/-! ### Type consistency of the emitted applications -/

theorem compile_out_wt {wt : ℕ → Option TensorType} (e : PolyExpr)
    (base : ℕ)
    (hagr : ∀ w τ, (e.compile base).ty w = some τ → wt w = some τ)
    (htyt : ∀ w ∈ e.taps, wt w = some ⟨[], Dtype.Q⟩) :
    wt (e.compile base).out = some ⟨[], Dtype.Q⟩ := by
  rcases compile_out e base with h | ⟨hty, -, -⟩
  · exact htyt _ h
  · exact hagr _ _ hty

theorem compile_tc {wt : ℕ → Option TensorType} (e : PolyExpr) (base : ℕ)
    (hagr : ∀ w τ, (e.compile base).ty w = some τ → wt w = some τ)
    (htyt : ∀ w ∈ e.taps, wt w = some ⟨[], Dtype.Q⟩) :
    ∀ a ∈ (e.compile base).apps, a.TypeConsistent wt := by
  induction e generalizing base with
  | tap w => intro a ha; exact nomatch ha
  | qconst q =>
    intro a ha
    have ha' := List.mem_singleton.mp ha
    subst ha'
    exact tcConstQ q
      (hagr base _ (by rw [compile_qconst_ty, if_pos rfl]))
  | add e₁ e₂ ih₁ ih₂ =>
    have hagr₁ : ∀ w τ, (e₁.compile base).ty w = some τ → wt w = some τ :=
      fun w τ h => hagr w τ (compile_add_ty_left e₁ e₂ base h)
    have hagr₂ : ∀ w τ,
        (e₂.compile (e₁.compile base).next).ty w = some τ →
          wt w = some τ :=
      fun w τ h => hagr w τ (compile_add_ty_right e₁ e₂ base h)
    have htyt₁ : ∀ w ∈ e₁.taps, wt w = some ⟨[], Dtype.Q⟩ :=
      fun w hw => htyt w (List.mem_append_left _ hw)
    have htyt₂ : ∀ w ∈ e₂.taps, wt w = some ⟨[], Dtype.Q⟩ :=
      fun w hw => htyt w (List.mem_append_right _ hw)
    intro a ha
    rw [compile_add_apps] at ha
    rcases List.mem_append.mp ha with ha' | ha'
    · rcases List.mem_append.mp ha' with ha'' | ha''
      · exact ih₁ base hagr₁ htyt₁ a ha''
      · exact ih₂ (e₁.compile base).next hagr₂ htyt₂ a ha''
    · have hov₁ := compile_out_wt e₁ base hagr₁ htyt₁
      have hov₂ := compile_out_wt e₂ (e₁.compile base).next hagr₂ htyt₂
      have hv := hagr _ _ (compile_add_ty_v e₁ e₂ base)
      have hout := hagr _ _ (compile_add_ty_out e₁ e₂ base)
      rcases List.mem_cons.mp ha' with ha'' | ha''
      · subst ha''
        exact tcStackPair hov₁ hov₂ hv
      · have ha₃ := List.mem_singleton.mp ha''
        subst ha₃
        exact tcSumPair hv hout
  | mul e₁ e₂ ih₁ ih₂ =>
    have hagr₁ : ∀ w τ, (e₁.compile base).ty w = some τ → wt w = some τ :=
      fun w τ h => hagr w τ (compile_mul_ty_left e₁ e₂ base h)
    have hagr₂ : ∀ w τ,
        (e₂.compile (e₁.compile base).next).ty w = some τ →
          wt w = some τ :=
      fun w τ h => hagr w τ (compile_mul_ty_right e₁ e₂ base h)
    have htyt₁ : ∀ w ∈ e₁.taps, wt w = some ⟨[], Dtype.Q⟩ :=
      fun w hw => htyt w (List.mem_append_left _ hw)
    have htyt₂ : ∀ w ∈ e₂.taps, wt w = some ⟨[], Dtype.Q⟩ :=
      fun w hw => htyt w (List.mem_append_right _ hw)
    intro a ha
    rw [compile_mul_apps] at ha
    rcases List.mem_append.mp ha with ha' | ha'
    · rcases List.mem_append.mp ha' with ha'' | ha''
      · exact ih₁ base hagr₁ htyt₁ a ha''
      · exact ih₂ (e₁.compile base).next hagr₂ htyt₂ a ha''
    · have ha₃ := List.mem_singleton.mp ha'
      subst ha₃
      exact tcMul (compile_out_wt e₁ base hagr₁ htyt₁)
        (compile_out_wt e₂ (e₁.compile base).next hagr₂ htyt₂)
        (hagr _ _ (compile_mul_ty_out e₁ e₂ base))

/-! ### The semantic interface of a compilation -/

/-- Admissible reads evaluate the expression at the output wire. -/
theorem compile_reads {H : Hypernet} (σ : H.Valuation) (e : PolyExpr)
    (base : ℕ) (env : ℕ → ℚ)
    (hagr : ∀ w τ, (e.compile base).ty w = some τ → H.wireType w = some τ)
    (htyt : ∀ w ∈ e.taps, H.wireType w = some ⟨[], Dtype.Q⟩)
    (htaps : ∀ w ∈ e.taps, σ.entryFlat w 0 = some (.fin (env w)))
    (hsem : ∀ a ∈ (e.compile base).apps, a.SemOk σ) :
    σ.entryFlat (e.compile base).out 0 = some (.fin (e.evalE env)) := by
  induction e generalizing base with
  | tap w => exact htaps w (List.mem_singleton.mpr rfl)
  | qconst q =>
    have hw : H.wireType base = some ⟨[], Dtype.Q⟩ :=
      hagr base _ (by rw [compile_qconst_ty, if_pos rfl])
    exact (const_scalarQ_semOk_iff σ hw q).mp
      (hsem _ (List.mem_singleton.mpr rfl))
  | add e₁ e₂ ih₁ ih₂ =>
    have hagr₁ : ∀ w τ, (e₁.compile base).ty w = some τ →
        H.wireType w = some τ :=
      fun w τ h => hagr w τ (compile_add_ty_left e₁ e₂ base h)
    have hagr₂ : ∀ w τ,
        (e₂.compile (e₁.compile base).next).ty w = some τ →
          H.wireType w = some τ :=
      fun w τ h => hagr w τ (compile_add_ty_right e₁ e₂ base h)
    have htyt₁ : ∀ w ∈ e₁.taps, H.wireType w = some ⟨[], Dtype.Q⟩ :=
      fun w hw => htyt w (List.mem_append_left _ hw)
    have htyt₂ : ∀ w ∈ e₂.taps, H.wireType w = some ⟨[], Dtype.Q⟩ :=
      fun w hw => htyt w (List.mem_append_right _ hw)
    have htaps₁ : ∀ w ∈ e₁.taps, σ.entryFlat w 0 = some (.fin (env w)) :=
      fun w hw => htaps w (List.mem_append_left _ hw)
    have htaps₂ : ∀ w ∈ e₂.taps, σ.entryFlat w 0 = some (.fin (env w)) :=
      fun w hw => htaps w (List.mem_append_right _ hw)
    have hsem₁ : ∀ a ∈ (e₁.compile base).apps, a.SemOk σ := fun a ha =>
      hsem a (by
        rw [compile_add_apps]
        exact List.mem_append_left _ (List.mem_append_left _ ha))
    have hsem₂ : ∀ a ∈ (e₂.compile (e₁.compile base).next).apps,
        a.SemOk σ := fun a ha =>
      hsem a (by
        rw [compile_add_apps]
        exact List.mem_append_left _ (List.mem_append_right _ ha))
    have r₁ := ih₁ base hagr₁ htyt₁ htaps₁ hsem₁
    have r₂ := ih₂ (e₁.compile base).next hagr₂ htyt₂ htaps₂ hsem₂
    have hsemStack := hsem _ (by
      rw [compile_add_apps]
      exact List.mem_append_right _ (List.mem_cons_self ..))
    have hsemSum := hsem _ (by
      rw [compile_add_apps]
      exact List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)))
    obtain ⟨hv0, hv1⟩ := (stack_pair_semOk_iff σ r₁ r₂).mp hsemStack
    have hres := (contract_sumPair_semOk_iff σ
      (hagr _ _ (compile_add_ty_v e₁ e₂ base))
      (hagr _ _ (compile_add_ty_out e₁ e₂ base)) hv0 hv1).mp hsemSum
    rw [compile_add_out]
    exact hres
  | mul e₁ e₂ ih₁ ih₂ =>
    have hagr₁ : ∀ w τ, (e₁.compile base).ty w = some τ →
        H.wireType w = some τ :=
      fun w τ h => hagr w τ (compile_mul_ty_left e₁ e₂ base h)
    have hagr₂ : ∀ w τ,
        (e₂.compile (e₁.compile base).next).ty w = some τ →
          H.wireType w = some τ :=
      fun w τ h => hagr w τ (compile_mul_ty_right e₁ e₂ base h)
    have htyt₁ : ∀ w ∈ e₁.taps, H.wireType w = some ⟨[], Dtype.Q⟩ :=
      fun w hw => htyt w (List.mem_append_left _ hw)
    have htyt₂ : ∀ w ∈ e₂.taps, H.wireType w = some ⟨[], Dtype.Q⟩ :=
      fun w hw => htyt w (List.mem_append_right _ hw)
    have htaps₁ : ∀ w ∈ e₁.taps, σ.entryFlat w 0 = some (.fin (env w)) :=
      fun w hw => htaps w (List.mem_append_left _ hw)
    have htaps₂ : ∀ w ∈ e₂.taps, σ.entryFlat w 0 = some (.fin (env w)) :=
      fun w hw => htaps w (List.mem_append_right _ hw)
    have hsem₁ : ∀ a ∈ (e₁.compile base).apps, a.SemOk σ := fun a ha =>
      hsem a (by
        rw [compile_mul_apps]
        exact List.mem_append_left _ (List.mem_append_left _ ha))
    have hsem₂ : ∀ a ∈ (e₂.compile (e₁.compile base).next).apps,
        a.SemOk σ := fun a ha =>
      hsem a (by
        rw [compile_mul_apps]
        exact List.mem_append_left _ (List.mem_append_right _ ha))
    have r₁ := ih₁ base hagr₁ htyt₁ htaps₁ hsem₁
    have r₂ := ih₂ (e₁.compile base).next hagr₂ htyt₂ htaps₂ hsem₂
    have hsemMul := hsem _ (by
      rw [compile_mul_apps]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl))
    have hres := (contract_mul_semOk_iff σ
      (compile_out_wt e₁ base hagr₁ htyt₁)
      (compile_out_wt e₂ (e₁.compile base).next hagr₂ htyt₂)
      (hagr _ _ (compile_mul_ty_out e₁ e₂ base)) r₁ r₂).mp hsemMul
    rw [compile_mul_out]
    exact hres

/-- A valuation carrying the model is admissible on the compilation. -/
theorem compile_semOk {H : Hypernet} (σ : H.Valuation) (e : PolyExpr)
    (base : ℕ) (env : ℕ → ℚ)
    (hagr : ∀ w τ, (e.compile base).ty w = some τ → H.wireType w = some τ)
    (htyt : ∀ w ∈ e.taps, H.wireType w = some ⟨[], Dtype.Q⟩)
    (htaps : ∀ w ∈ e.taps, σ.entryFlat w 0 = some (.fin (env w)))
    (hmdl : ∀ w : ℕ, ((e.compile base).ty w).isSome = true →
      ∀ i : ℕ, σ.entryFlat w i =
        (((e.compile base).mdl env w)[i]?).map ERat.fin) :
    ∀ a ∈ (e.compile base).apps, a.SemOk σ := by
  induction e generalizing base with
  | tap w => intro a ha; exact nomatch ha
  | qconst q =>
    intro a ha
    have ha' := List.mem_singleton.mp ha
    subst ha'
    have hw : H.wireType base = some ⟨[], Dtype.Q⟩ :=
      hagr base _ (by rw [compile_qconst_ty, if_pos rfl])
    refine (const_scalarQ_semOk_iff σ hw q).mpr ?_
    have hrd := hmdl base
      (by rw [compile_qconst_ty, if_pos rfl]; rfl) 0
    rw [hrd, compile_qconst_mdl, if_pos rfl]
    rfl
  | add e₁ e₂ ih₁ ih₂ =>
    have hagr₁ : ∀ w τ, (e₁.compile base).ty w = some τ →
        H.wireType w = some τ :=
      fun w τ h => hagr w τ (compile_add_ty_left e₁ e₂ base h)
    have hagr₂ : ∀ w τ,
        (e₂.compile (e₁.compile base).next).ty w = some τ →
          H.wireType w = some τ :=
      fun w τ h => hagr w τ (compile_add_ty_right e₁ e₂ base h)
    have htyt₁ : ∀ w ∈ e₁.taps, H.wireType w = some ⟨[], Dtype.Q⟩ :=
      fun w hw => htyt w (List.mem_append_left _ hw)
    have htyt₂ : ∀ w ∈ e₂.taps, H.wireType w = some ⟨[], Dtype.Q⟩ :=
      fun w hw => htyt w (List.mem_append_right _ hw)
    have htaps₁ : ∀ w ∈ e₁.taps, σ.entryFlat w 0 = some (.fin (env w)) :=
      fun w hw => htaps w (List.mem_append_left _ hw)
    have htaps₂ : ∀ w ∈ e₂.taps, σ.entryFlat w 0 = some (.fin (env w)) :=
      fun w hw => htaps w (List.mem_append_right _ hw)
    have hmdl₁ : ∀ w : ℕ, ((e₁.compile base).ty w).isSome = true →
        ∀ i : ℕ, σ.entryFlat w i =
          (((e₁.compile base).mdl env w)[i]?).map ERat.fin := by
      intro w hs i
      obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hs
      have hcomp := hmdl w
        (by rw [compile_add_ty_left e₁ e₂ base hτ]; rfl) i
      rw [hcomp, compile_add_mdl_left e₁ e₂ base env hs]
    have hmdl₂ : ∀ w : ℕ,
        ((e₂.compile (e₁.compile base).next).ty w).isSome = true →
        ∀ i : ℕ, σ.entryFlat w i =
          ((((e₂.compile (e₁.compile base).next)).mdl env w)[i]?).map
            ERat.fin := by
      intro w hs i
      obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hs
      have hcomp := hmdl w
        (by rw [compile_add_ty_right e₁ e₂ base hτ]; rfl) i
      rw [hcomp, compile_add_mdl_right e₁ e₂ base env hs]
    have hsem₁ := ih₁ base hagr₁ htyt₁ htaps₁ hmdl₁
    have hsem₂ := ih₂ (e₁.compile base).next hagr₂ htyt₂ htaps₂ hmdl₂
    have r₁ := compile_reads σ e₁ base env hagr₁ htyt₁ htaps₁ hsem₁
    have r₂ := compile_reads σ e₂ (e₁.compile base).next env hagr₂ htyt₂
      htaps₂ hsem₂
    have hvrd0 : σ.entryFlat (e₂.compile (e₁.compile base).next).next 0
        = some (.fin (e₁.evalE env)) := by
      have hrd := hmdl (e₂.compile (e₁.compile base).next).next
        (by rw [compile_add_ty_v e₁ e₂ base]; rfl) 0
      rw [hrd, compile_add_mdl, if_pos rfl]
      rfl
    have hvrd1 : σ.entryFlat (e₂.compile (e₁.compile base).next).next 1
        = some (.fin (e₂.evalE env)) := by
      have hrd := hmdl (e₂.compile (e₁.compile base).next).next
        (by rw [compile_add_ty_v e₁ e₂ base]; rfl) 1
      rw [hrd, compile_add_mdl, if_pos rfl]
      rfl
    have hord : σ.entryFlat ((e₂.compile (e₁.compile base).next).next + 1) 0
        = some (.fin (e₁.evalE env + e₂.evalE env)) := by
      have hn1 : ¬((e₂.compile (e₁.compile base).next).next + 1
          = (e₂.compile (e₁.compile base).next).next) := by omega
      have hrd := hmdl ((e₂.compile (e₁.compile base).next).next + 1)
        (by rw [compile_add_ty_out e₁ e₂ base]; rfl) 0
      rw [hrd, compile_add_mdl, if_neg hn1, if_pos rfl]
      rfl
    intro a ha
    rw [compile_add_apps] at ha
    rcases List.mem_append.mp ha with ha' | ha'
    · rcases List.mem_append.mp ha' with ha'' | ha''
      · exact hsem₁ a ha''
      · exact hsem₂ a ha''
    · rcases List.mem_cons.mp ha' with ha'' | ha''
      · subst ha''
        exact (stack_pair_semOk_iff σ r₁ r₂).mpr ⟨hvrd0, hvrd1⟩
      · have ha₃ := List.mem_singleton.mp ha''
        subst ha₃
        exact (contract_sumPair_semOk_iff σ
          (hagr _ _ (compile_add_ty_v e₁ e₂ base))
          (hagr _ _ (compile_add_ty_out e₁ e₂ base)) hvrd0 hvrd1).mpr hord
  | mul e₁ e₂ ih₁ ih₂ =>
    have hagr₁ : ∀ w τ, (e₁.compile base).ty w = some τ →
        H.wireType w = some τ :=
      fun w τ h => hagr w τ (compile_mul_ty_left e₁ e₂ base h)
    have hagr₂ : ∀ w τ,
        (e₂.compile (e₁.compile base).next).ty w = some τ →
          H.wireType w = some τ :=
      fun w τ h => hagr w τ (compile_mul_ty_right e₁ e₂ base h)
    have htyt₁ : ∀ w ∈ e₁.taps, H.wireType w = some ⟨[], Dtype.Q⟩ :=
      fun w hw => htyt w (List.mem_append_left _ hw)
    have htyt₂ : ∀ w ∈ e₂.taps, H.wireType w = some ⟨[], Dtype.Q⟩ :=
      fun w hw => htyt w (List.mem_append_right _ hw)
    have htaps₁ : ∀ w ∈ e₁.taps, σ.entryFlat w 0 = some (.fin (env w)) :=
      fun w hw => htaps w (List.mem_append_left _ hw)
    have htaps₂ : ∀ w ∈ e₂.taps, σ.entryFlat w 0 = some (.fin (env w)) :=
      fun w hw => htaps w (List.mem_append_right _ hw)
    have hmdl₁ : ∀ w : ℕ, ((e₁.compile base).ty w).isSome = true →
        ∀ i : ℕ, σ.entryFlat w i =
          (((e₁.compile base).mdl env w)[i]?).map ERat.fin := by
      intro w hs i
      obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hs
      have hcomp := hmdl w
        (by rw [compile_mul_ty_left e₁ e₂ base hτ]; rfl) i
      rw [hcomp, compile_mul_mdl_left e₁ e₂ base env hs]
    have hmdl₂ : ∀ w : ℕ,
        ((e₂.compile (e₁.compile base).next).ty w).isSome = true →
        ∀ i : ℕ, σ.entryFlat w i =
          ((((e₂.compile (e₁.compile base).next)).mdl env w)[i]?).map
            ERat.fin := by
      intro w hs i
      obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hs
      have hcomp := hmdl w
        (by rw [compile_mul_ty_right e₁ e₂ base hτ]; rfl) i
      rw [hcomp, compile_mul_mdl_right e₁ e₂ base env hs]
    have hsem₁ := ih₁ base hagr₁ htyt₁ htaps₁ hmdl₁
    have hsem₂ := ih₂ (e₁.compile base).next hagr₂ htyt₂ htaps₂ hmdl₂
    have r₁ := compile_reads σ e₁ base env hagr₁ htyt₁ htaps₁ hsem₁
    have r₂ := compile_reads σ e₂ (e₁.compile base).next env hagr₂ htyt₂
      htaps₂ hsem₂
    have hord : σ.entryFlat (e₂.compile (e₁.compile base).next).next 0
        = some (.fin (e₁.evalE env * e₂.evalE env)) := by
      have hrd := hmdl (e₂.compile (e₁.compile base).next).next
        (by rw [compile_mul_ty_out e₁ e₂ base]; rfl) 0
      rw [hrd, compile_mul_mdl, if_pos rfl]
      rfl
    intro a ha
    rw [compile_mul_apps] at ha
    rcases List.mem_append.mp ha with ha' | ha'
    · rcases List.mem_append.mp ha' with ha'' | ha''
      · exact hsem₁ a ha''
      · exact hsem₂ a ha''
    · have ha₃ := List.mem_singleton.mp ha'
      subst ha₃
      exact (contract_mul_semOk_iff σ
        (compile_out_wt e₁ base hagr₁ htyt₁)
        (compile_out_wt e₂ (e₁.compile base).next hagr₂ htyt₂)
        (hagr _ _ (compile_mul_ty_out e₁ e₂ base)) r₁ r₂).mpr hord

#print axioms compile_tc
#print axioms compile_reads
#print axioms compile_semOk
#print axioms compile_consumed_nodup
#print axioms compile_produced_nodup
#print axioms compile_acyclic


/-! ### Instantiation: one tap wire per occurrence -/

/-- Rename an expression's taps to a contiguous block starting at
`tb`, one wire per occurrence, threading an occurrence counter.  The
original tap names become *sources*; the instantiated expression reads
the block wires, which a `copy` comb per source can feed. -/
def inst (tb : ℕ) : PolyExpr → ℕ → PolyExpr × ℕ
  | tap _, k => (tap (tb + k), k + 1)
  | qconst q, k => (qconst q, k)
  | add e₁ e₂, k =>
    let p₁ := e₁.inst tb k
    let p₂ := e₂.inst tb p₁.2
    (add p₁.1 p₂.1, p₂.2)
  | mul e₁ e₂, k =>
    let p₁ := e₁.inst tb k
    let p₂ := e₂.inst tb p₁.2
    (mul p₁.1 p₂.1, p₂.2)

theorem inst_counter (e : PolyExpr) (tb : ℕ) : ∀ k : ℕ,
    (e.inst tb k).2 = k + e.taps.length := by
  induction e with
  | tap w => intro k; rfl
  | qconst q => intro k; rfl
  | add e₁ e₂ ih₁ ih₂ =>
    intro k
    show (e₂.inst tb (e₁.inst tb k).2).2 = k + (e₁.taps ++ e₂.taps).length
    rw [ih₂, ih₁, List.length_append]
    omega
  | mul e₁ e₂ ih₁ ih₂ =>
    intro k
    show (e₂.inst tb (e₁.inst tb k).2).2 = k + (e₁.taps ++ e₂.taps).length
    rw [ih₂, ih₁, List.length_append]
    omega

theorem inst_taps (e : PolyExpr) (tb : ℕ) : ∀ k : ℕ,
    (e.inst tb k).1.taps = List.range' (tb + k) e.taps.length := by
  induction e with
  | tap w => intro k; rfl
  | qconst q => intro k; rfl
  | add e₁ e₂ ih₁ ih₂ =>
    intro k
    show (e₁.inst tb k).1.taps ++ (e₂.inst tb (e₁.inst tb k).2).1.taps
      = List.range' (tb + k) (e₁.taps ++ e₂.taps).length
    rw [ih₁, ih₂, inst_counter, List.length_append,
      show tb + (k + e₁.taps.length) = (tb + k) + e₁.taps.length by omega]
    exact SeamFacts.range'_append_simple (tb + k) e₁.taps.length
      e₂.taps.length
  | mul e₁ e₂ ih₁ ih₂ =>
    intro k
    show (e₁.inst tb k).1.taps ++ (e₂.inst tb (e₁.inst tb k).2).1.taps
      = List.range' (tb + k) (e₁.taps ++ e₂.taps).length
    rw [ih₁, ih₂, inst_counter, List.length_append,
      show tb + (k + e₁.taps.length) = (tb + k) + e₁.taps.length by omega]
    exact SeamFacts.range'_append_simple (tb + k) e₁.taps.length
      e₂.taps.length

theorem inst_evalE (e : PolyExpr) (tb : ℕ) (env vals : ℕ → ℚ) :
    ∀ k : ℕ,
    (∀ j : ℕ, (hj : j < e.taps.length) →
      env (tb + k + j) = vals (e.taps[j]'hj)) →
    (e.inst tb k).1.evalE env = e.evalE vals := by
  induction e with
  | tap w =>
    intro k h
    show env (tb + k) = vals w
    exact h 0 (by simp [taps])
  | qconst q => intro k h; rfl
  | add e₁ e₂ ih₁ ih₂ =>
    intro k h
    show (e₁.inst tb k).1.evalE env
        + (e₂.inst tb (e₁.inst tb k).2).1.evalE env
      = e₁.evalE vals + e₂.evalE vals
    have h₁ : ∀ j : ℕ, (hj : j < e₁.taps.length) →
        env (tb + k + j) = vals (e₁.taps[j]'hj) := by
      intro j hj
      have hlt : j < (add e₁ e₂).taps.length := by
        simp only [taps, List.length_append]; omega
      have hh := h j hlt
      simp only [taps] at hh
      rwa [List.getElem_append_left hj] at hh
    have h₂ : ∀ j : ℕ, (hj : j < e₂.taps.length) →
        env (tb + (e₁.inst tb k).2 + j) = vals (e₂.taps[j]'hj) := by
      intro j hj
      rw [inst_counter]
      have hlt : e₁.taps.length + j < (add e₁ e₂).taps.length := by
        simp only [taps, List.length_append]; omega
      have hh := h (e₁.taps.length + j) hlt
      simp only [taps] at hh
      rw [List.getElem_append_right (by omega)] at hh
      simp only [Nat.add_sub_cancel_left] at hh
      rw [show tb + (k + e₁.taps.length) + j
        = tb + k + (e₁.taps.length + j) by omega]
      exact hh
    rw [ih₁ k h₁, ih₂ (e₁.inst tb k).2 h₂]
  | mul e₁ e₂ ih₁ ih₂ =>
    intro k h
    show (e₁.inst tb k).1.evalE env
        * (e₂.inst tb (e₁.inst tb k).2).1.evalE env
      = e₁.evalE vals * e₂.evalE vals
    have h₁ : ∀ j : ℕ, (hj : j < e₁.taps.length) →
        env (tb + k + j) = vals (e₁.taps[j]'hj) := by
      intro j hj
      have hlt : j < (mul e₁ e₂).taps.length := by
        simp only [taps, List.length_append]; omega
      have hh := h j hlt
      simp only [taps] at hh
      rwa [List.getElem_append_left hj] at hh
    have h₂ : ∀ j : ℕ, (hj : j < e₂.taps.length) →
        env (tb + (e₁.inst tb k).2 + j) = vals (e₂.taps[j]'hj) := by
      intro j hj
      rw [inst_counter]
      have hlt : e₁.taps.length + j < (mul e₁ e₂).taps.length := by
        simp only [taps, List.length_append]; omega
      have hh := h (e₁.taps.length + j) hlt
      simp only [taps] at hh
      rw [List.getElem_append_right (by omega)] at hh
      simp only [Nat.add_sub_cancel_left] at hh
      rw [show tb + (k + e₁.taps.length) + j
        = tb + k + (e₁.taps.length + j) by omega]
      exact hh
    rw [ih₁ k h₁, ih₂ (e₁.inst tb k).2 h₂]

/-! ### The tap wires carrying a given source -/

/-- The tap-block wires of an instantiation at `tb` that carry source
`s`, in occurrence order. -/
def srcTaps (e : PolyExpr) (tb : ℕ) (s : ℕ) : List ℕ :=
  ((List.range e.taps.length).filter
    (fun j => decide (e.taps[j]? = some s))).map (fun j => tb + j)

theorem mem_srcTaps {e : PolyExpr} {tb s w : ℕ} :
    w ∈ srcTaps e tb s ↔
      ∃ j : ℕ, ∃ hj : j < e.taps.length,
        e.taps[j]'hj = s ∧ w = tb + j := by
  unfold srcTaps
  simp only [List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro ⟨j, ⟨hj, hget⟩, rfl⟩
    rw [List.getElem?_eq_getElem hj] at hget
    exact ⟨j, hj, Option.some.inj hget, rfl⟩
  · rintro ⟨j, hj, hget, rfl⟩
    refine ⟨j, ⟨hj, ?_⟩, rfl⟩
    rw [List.getElem?_eq_getElem hj, hget]

theorem srcTaps_nodup (e : PolyExpr) (tb s : ℕ) :
    (srcTaps e tb s).Nodup := by
  unfold srcTaps
  refine List.Nodup.map ?_ (List.Nodup.filter _ (List.nodup_range))
  intro a b hab
  have hab' : tb + a = tb + b := hab
  omega

theorem srcTaps_bounds {e : PolyExpr} {tb s w : ℕ}
    (h : w ∈ srcTaps e tb s) : tb ≤ w ∧ w < tb + e.taps.length := by
  obtain ⟨j, hj, -, rfl⟩ := mem_srcTaps.mp h
  omega

#print axioms inst_evalE
#print axioms mem_srcTaps
#print axioms srcTaps_nodup


/-! ### Compiling a list of expressions: tap blocks and stations -/

/-- The tap environment of a station: the tap-block wire `tb + j`
carries the value of the expression's `j`-th source occurrence. -/
def stEnv (E : PolyExpr) (tb : ℕ) (vals : ℕ → ℚ) : ℕ → ℚ :=
  fun w =>
    if h : tb ≤ w ∧ w - tb < E.taps.length then
      vals (E.taps[w - tb]'h.2)
    else 0

theorem stEnv_at (E : PolyExpr) (tb : ℕ) (vals : ℕ → ℚ) {j : ℕ}
    (hj : j < E.taps.length) :
    stEnv E tb vals (tb + j) = vals (E.taps[j]'hj) := by
  unfold stEnv
  rw [dif_pos ⟨by omega, by omega⟩]
  simp only [Nat.add_sub_cancel_left]

/-- The result of compiling a station list. -/
structure ManyCompiled where
  apps : List PrimApp
  outs : List ℕ
  next : ℕ
  ty : ℕ → Option TensorType
  mdl : (ℕ → ℚ) → ℕ → List ℚ
  tapOf : ℕ → List ℕ

/-- Compile a list of source-named expressions from a starting wire:
each station gets a tap block (one wire per occurrence, to be fed by
per-source combs) followed by its compilation. -/
def compileMany : List PolyExpr → ℕ → ManyCompiled
  | [], start =>
    { apps := [], outs := [], next := start,
      ty := fun _ => none, mdl := fun _ _ => [], tapOf := fun _ => [] }
  | E :: rest, start =>
    let T := E.taps.length
    let ie := (E.inst start 0).1
    let c := ie.compile (start + T)
    let r := compileMany rest c.next
    { apps := c.apps ++ r.apps,
      outs := c.out :: r.outs,
      next := r.next,
      ty := fun w =>
        if start ≤ w ∧ w < start + T then some ⟨[], Dtype.Q⟩
        else mergeWt c.ty r.ty w,
      mdl := fun vals w =>
        if h : start ≤ w ∧ w - start < T then [vals (E.taps[w - start]'h.2)]
        else if (c.ty w).isSome then c.mdl (stEnv E start vals) w
        else r.mdl vals w,
      tapOf := fun s => srcTaps E start s ++ r.tapOf s }

section ManyProj

variable (E : PolyExpr) (rest : List PolyExpr) (start : ℕ)

theorem many_cons_apps :
    (compileMany (E :: rest) start).apps
      = ((E.inst start 0).1.compile (start + E.taps.length)).apps ++
        (compileMany rest
          ((E.inst start 0).1.compile (start + E.taps.length)).next).apps :=
  rfl

theorem many_cons_outs :
    (compileMany (E :: rest) start).outs
      = ((E.inst start 0).1.compile (start + E.taps.length)).out ::
        (compileMany rest
          ((E.inst start 0).1.compile (start + E.taps.length)).next).outs :=
  rfl

theorem many_cons_next :
    (compileMany (E :: rest) start).next
      = (compileMany rest
          ((E.inst start 0).1.compile (start + E.taps.length)).next).next :=
  rfl

theorem many_cons_ty (w : ℕ) :
    (compileMany (E :: rest) start).ty w
      = if start ≤ w ∧ w < start + E.taps.length then some ⟨[], Dtype.Q⟩
        else mergeWt ((E.inst start 0).1.compile
            (start + E.taps.length)).ty
          (compileMany rest
            ((E.inst start 0).1.compile
              (start + E.taps.length)).next).ty w := rfl

theorem many_cons_mdl (vals : ℕ → ℚ) (w : ℕ) :
    (compileMany (E :: rest) start).mdl vals w
      = if h : start ≤ w ∧ w - start < E.taps.length then
          [vals (E.taps[w - start]'h.2)]
        else if (((E.inst start 0).1.compile
            (start + E.taps.length)).ty w).isSome then
          ((E.inst start 0).1.compile (start + E.taps.length)).mdl
            (stEnv E start vals) w
        else (compileMany rest
          ((E.inst start 0).1.compile
            (start + E.taps.length)).next).mdl vals w := rfl

theorem many_cons_tapOf (s : ℕ) :
    (compileMany (E :: rest) start).tapOf s
      = srcTaps E start s ++
        (compileMany rest
          ((E.inst start 0).1.compile
            (start + E.taps.length)).next).tapOf s := rfl

end ManyProj

/-- The instantiated taps of a station sit below its compile base. -/
theorem inst_taps_below (E : PolyExpr) (start : ℕ) :
    ∀ w ∈ (E.inst start 0).1.taps, w < start + E.taps.length := by
  intro w hw
  rw [inst_taps] at hw
  have := SeamFacts.mem_range'_bounds hw
  omega

theorem inst_taps_lower (E : PolyExpr) (start : ℕ) :
    ∀ w ∈ (E.inst start 0).1.taps, start ≤ w := by
  intro w hw
  rw [inst_taps] at hw
  have := SeamFacts.mem_range'_bounds hw
  omega

theorem many_le (Es : List PolyExpr) (start : ℕ) :
    start ≤ (compileMany Es start).next := by
  induction Es generalizing start with
  | nil => exact Nat.le_refl _
  | cons E rest ih =>
    have h1 := compile_le (E.inst start 0).1 (start + E.taps.length)
    have h2 := ih ((E.inst start 0).1.compile (start + E.taps.length)).next
    rw [many_cons_next]
    omega

theorem many_ty_none (Es : List PolyExpr) (start : ℕ) {w : ℕ}
    (h : w < start ∨ (compileMany Es start).next ≤ w) :
    (compileMany Es start).ty w = none := by
  induction Es generalizing start with
  | nil => rfl
  | cons E rest ih =>
    have h1 := compile_le (E.inst start 0).1 (start + E.taps.length)
    have h2 := many_le rest
      ((E.inst start 0).1.compile (start + E.taps.length)).next
    rw [many_cons_next] at h
    have hn : ¬(start ≤ w ∧ w < start + E.taps.length) := by
      rcases h with h | h <;> omega
    rw [many_cons_ty, if_neg hn,
      mergeWt_of_left_none (compile_ty_none _ _ (by
        rcases h with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)))]
    exact ih _ (by
      rcases h with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega))

theorem many_ty_domain (Es : List PolyExpr) (start : ℕ) {w : ℕ}
    {τ : TensorType} (h : (compileMany Es start).ty w = some τ) :
    start ≤ w ∧ w < (compileMany Es start).next := by
  rcases Nat.lt_or_ge w start with h' | h'
  · rw [many_ty_none Es start (Or.inl h')] at h
    exact nomatch h
  · rcases Nat.lt_or_ge w (compileMany Es start).next with h'' | h''
    · exact ⟨h', h''⟩
    · rw [many_ty_none Es start (Or.inr h'')] at h
      exact nomatch h

theorem many_produced_bounds (Es : List PolyExpr) (start : ℕ) :
    ∀ w : ℕ, w ∈ producedW (compileMany Es start).apps →
      start ≤ w ∧ w < (compileMany Es start).next := by
  induction Es generalizing start with
  | nil => intro w hw; exact nomatch hw
  | cons E rest ih =>
    intro w hw
    have h1 := compile_le (E.inst start 0).1 (start + E.taps.length)
    have h2 := many_le rest
      ((E.inst start 0).1.compile (start + E.taps.length)).next
    rw [many_cons_apps, producedW_append] at hw
    rw [many_cons_next]
    rcases List.mem_append.mp hw with hw' | hw'
    · obtain ⟨ha, hb⟩ := compile_produced_bounds _ _ w hw'
      omega
    · obtain ⟨ha, hb⟩ := ih _ w hw'
      omega

theorem many_consumed_bounds (Es : List PolyExpr) (start : ℕ) :
    ∀ w : ℕ, w ∈ consumedW (compileMany Es start).apps →
      start ≤ w ∧ w < (compileMany Es start).next := by
  induction Es generalizing start with
  | nil => intro w hw; exact nomatch hw
  | cons E rest ih =>
    intro w hw
    have h1 := compile_le (E.inst start 0).1 (start + E.taps.length)
    have h2 := many_le rest
      ((E.inst start 0).1.compile (start + E.taps.length)).next
    rw [many_cons_apps, consumedW_append] at hw
    rw [many_cons_next]
    rcases List.mem_append.mp hw with hw' | hw'
    · rcases compile_consumed_bounds _ _ w hw' with hm | ⟨ha, hb⟩
      · have hlo := inst_taps_lower E start w hm
        have hhi := inst_taps_below E start w hm
        omega
      · omega
    · obtain ⟨ha, hb⟩ := ih _ w hw'
      omega

theorem many_produced_nodup (Es : List PolyExpr) (start : ℕ) :
    (producedW (compileMany Es start).apps).Nodup := by
  induction Es generalizing start with
  | nil => exact List.nodup_nil
  | cons E rest ih =>
    have h1 := compile_le (E.inst start 0).1 (start + E.taps.length)
    rw [many_cons_apps, producedW_append]
    refine nodup_append_nat (compile_produced_nodup _ _) (ih _) ?_
    intro a ha b hb he
    subst he
    obtain ⟨h3, h4⟩ := compile_produced_bounds _ _ a ha
    obtain ⟨h5, h6⟩ := many_produced_bounds _ _ a hb
    omega

theorem many_consumed_nodup (Es : List PolyExpr) (start : ℕ) :
    (consumedW (compileMany Es start).apps).Nodup := by
  induction Es generalizing start with
  | nil => exact List.nodup_nil
  | cons E rest ih =>
    have h1 := compile_le (E.inst start 0).1 (start + E.taps.length)
    rw [many_cons_apps, consumedW_append]
    refine nodup_append_nat (compile_consumed_nodup _ _ ?_ ?_) (ih _) ?_
    · rw [inst_taps]
      exact SeamFacts.nodup_range'_simple _ _
    · exact inst_taps_below E start
    · intro a ha b hb he
      subst he
      have hbnd : start ≤ a ∧ a < ((E.inst start 0).1.compile
          (start + E.taps.length)).next := by
        rcases compile_consumed_bounds _ _ a ha with hm | ⟨h3, h4⟩
        · exact ⟨inst_taps_lower E start a hm, by
            have := inst_taps_below E start a hm
            omega⟩
        · exact ⟨by omega, h4⟩
      obtain ⟨h5, h6⟩ := many_consumed_bounds _ _ a hb
      omega

theorem many_acyclic (Es : List PolyExpr) (start : ℕ) :
    Acyclic (compileMany Es start).apps := by
  induction Es generalizing start with
  | nil => exact acyclic_nil
  | cons E rest ih =>
    have h1 := compile_le (E.inst start 0).1 (start + E.taps.length)
    rw [many_cons_apps]
    refine acyclic_append_nat
      (compile_acyclic _ _ (inst_taps_below E start)) (ih _) ?_
    intro w hw₁ hw₂
    have hbnd : w < ((E.inst start 0).1.compile
        (start + E.taps.length)).next := by
      rcases compile_consumed_bounds _ _ w hw₁ with hm | ⟨h3, h4⟩
      · have := inst_taps_below E start w hm
        omega
      · omega
    obtain ⟨h5, h6⟩ := many_produced_bounds _ _ w hw₂
    omega

theorem many_outs_length (Es : List PolyExpr) (start : ℕ) :
    (compileMany Es start).outs.length = Es.length := by
  induction Es generalizing start with
  | nil => rfl
  | cons E rest ih =>
    rw [many_cons_outs]
    show _ + 1 = _ + 1
    rw [ih]

theorem many_outs_bounds (Es : List PolyExpr) (start : ℕ) :
    ∀ o ∈ (compileMany Es start).outs,
      start ≤ o ∧ o < (compileMany Es start).next := by
  induction Es generalizing start with
  | nil => intro o ho; exact nomatch ho
  | cons E rest ih =>
    intro o ho
    have h1 := compile_le (E.inst start 0).1 (start + E.taps.length)
    have h2 := many_le rest
      ((E.inst start 0).1.compile (start + E.taps.length)).next
    rw [many_cons_outs] at ho
    rw [many_cons_next]
    rcases List.mem_cons.mp ho with ho' | ho'
    · subst ho'
      rcases compile_out_cases (E.inst start 0).1
          (start + E.taps.length) with hm | ⟨h3, h4⟩
      · have hlo := inst_taps_lower E start _ hm
        have hhi := inst_taps_below E start _ hm
        omega
      · omega
    · obtain ⟨h3, h4⟩ := ih _ o ho'
      omega

theorem many_outs_not_consumed (Es : List PolyExpr) (start : ℕ) :
    ∀ o ∈ (compileMany Es start).outs,
      o ∉ consumedW (compileMany Es start).apps := by
  induction Es generalizing start with
  | nil => intro o ho; exact nomatch ho
  | cons E rest ih =>
    intro o ho hmem
    have h1 := compile_le (E.inst start 0).1 (start + E.taps.length)
    rw [many_cons_outs] at ho
    rw [many_cons_apps, consumedW_append] at hmem
    rcases List.mem_cons.mp ho with ho' | ho'
    · subst ho'
      rcases List.mem_append.mp hmem with hm | hm
      · -- within the own station: a station's output is never consumed
        -- there; a tap output is consumed by nothing it emits either
        rcases compile_out_cases (E.inst start 0).1
            (start + E.taps.length) with hout | ⟨h3, h4⟩
        · -- the out is a tap: station apps consume taps at most once…
          -- for a bare-tap station there are no apps at all, and for a
          -- compound station the out is fresh, so this branch means the
          -- expression is a bare tap: apps = [] and hm is absurd — but
          -- we argue uniformly through out_not_consumed
          exact compile_out_not_consumed _ _ (inst_taps_below E start) hm
        · exact compile_out_not_consumed _ _ (inst_taps_below E start) hm
      · obtain ⟨h5, h6⟩ := many_consumed_bounds _ _ _ hm
        rcases compile_out_cases (E.inst start 0).1
            (start + E.taps.length) with hout | ⟨h3, h4⟩
        · have := inst_taps_below E start _ hout
          omega
        · omega
    · rcases List.mem_append.mp hmem with hm | hm
      · obtain ⟨h5, h6⟩ := many_outs_bounds _ _ o ho'
        have hbnd : o < ((E.inst start 0).1.compile
            (start + E.taps.length)).next := by
          rcases compile_consumed_bounds _ _ o hm with hm' | ⟨h7, h8⟩
          · have := inst_taps_below E start o hm'
            omega
          · omega
        omega
      · exact ih _ o ho' hm


/-! ### Station typing transport -/

theorem many_ty_tap (E : PolyExpr) (rest : List PolyExpr) (start : ℕ)
    {w : ℕ} (h : start ≤ w ∧ w < start + E.taps.length) :
    (compileMany (E :: rest) start).ty w = some ⟨[], Dtype.Q⟩ := by
  rw [many_cons_ty, if_pos h]

theorem many_ty_station (E : PolyExpr) (rest : List PolyExpr) (start : ℕ)
    {w : ℕ} {τ : TensorType}
    (h : ((E.inst start 0).1.compile (start + E.taps.length)).ty w
      = some τ) :
    (compileMany (E :: rest) start).ty w = some τ := by
  obtain ⟨h1, h2⟩ := compile_ty_domain _ _ h
  rw [many_cons_ty, if_neg (by omega)]
  exact mergeWt_left h

theorem many_ty_rest (E : PolyExpr) (rest : List PolyExpr) (start : ℕ)
    {w : ℕ} {τ : TensorType}
    (h : (compileMany rest
      ((E.inst start 0).1.compile (start + E.taps.length)).next).ty w
      = some τ) :
    (compileMany (E :: rest) start).ty w = some τ := by
  obtain ⟨h1, h2⟩ := many_ty_domain _ _ h
  have h3 := compile_le (E.inst start 0).1 (start + E.taps.length)
  rw [many_cons_ty, if_neg (by omega),
    mergeWt_of_left_none (compile_ty_none _ _ (Or.inr (by omega)))]
  exact h

/-! ### Station model dispatch -/

theorem many_mdl_tap (E : PolyExpr) (rest : List PolyExpr) (start : ℕ)
    (vals : ℕ → ℚ) {w : ℕ} (h : start ≤ w ∧ w - start < E.taps.length) :
    (compileMany (E :: rest) start).mdl vals w
      = [vals (E.taps[w - start]'h.2)] := by
  rw [many_cons_mdl, dif_pos h]

theorem many_mdl_station (E : PolyExpr) (rest : List PolyExpr) (start : ℕ)
    (vals : ℕ → ℚ) {w : ℕ}
    (hs : (((E.inst start 0).1.compile
      (start + E.taps.length)).ty w).isSome = true) :
    (compileMany (E :: rest) start).mdl vals w
      = ((E.inst start 0).1.compile (start + E.taps.length)).mdl
          (stEnv E start vals) w := by
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨h1, h2⟩ := compile_ty_domain _ _ hτ
  rw [many_cons_mdl, dif_neg (by omega), if_pos hs]

theorem many_mdl_rest (E : PolyExpr) (rest : List PolyExpr) (start : ℕ)
    (vals : ℕ → ℚ) {w : ℕ}
    (hs : ((compileMany rest
      ((E.inst start 0).1.compile
        (start + E.taps.length)).next).ty w).isSome = true) :
    (compileMany (E :: rest) start).mdl vals w
      = (compileMany rest
          ((E.inst start 0).1.compile
            (start + E.taps.length)).next).mdl vals w := by
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨h1, h2⟩ := many_ty_domain _ _ hτ
  have h3 := compile_le (E.inst start 0).1 (start + E.taps.length)
  rw [many_cons_mdl, dif_neg (by omega),
    if_neg (by rw [compile_ty_none _ _ (Or.inr (by omega))]; simp)]

/-! ### Per-source tap wires of a station list -/

theorem many_tapOf_bounds (Es : List PolyExpr) (start : ℕ) (s : ℕ) :
    ∀ w ∈ (compileMany Es start).tapOf s,
      start ≤ w ∧ w < (compileMany Es start).next := by
  induction Es generalizing start with
  | nil => intro w hw; exact nomatch hw
  | cons E rest ih =>
    intro w hw
    have h1 := compile_le (E.inst start 0).1 (start + E.taps.length)
    have h2 := many_le rest
      ((E.inst start 0).1.compile (start + E.taps.length)).next
    rw [many_cons_tapOf] at hw
    rw [many_cons_next]
    rcases List.mem_append.mp hw with hw' | hw'
    · obtain ⟨h3, h4⟩ := srcTaps_bounds hw'
      omega
    · obtain ⟨h3, h4⟩ := ih _ w hw'
      omega

theorem many_tapOf_nodup (Es : List PolyExpr) (start : ℕ) (s : ℕ) :
    ((compileMany Es start).tapOf s).Nodup := by
  induction Es generalizing start with
  | nil => exact List.nodup_nil
  | cons E rest ih =>
    have h1 := compile_le (E.inst start 0).1 (start + E.taps.length)
    rw [many_cons_tapOf]
    refine nodup_append_nat (srcTaps_nodup E start s) (ih _) ?_
    intro a ha b hb he
    subst he
    obtain ⟨h3, h4⟩ := srcTaps_bounds ha
    obtain ⟨h5, h6⟩ := many_tapOf_bounds _ _ s a hb
    omega

theorem many_tapOf_src_ne (Es : List PolyExpr) (start : ℕ) {s s' : ℕ}
    (hne : s ≠ s') :
    ∀ w ∈ (compileMany Es start).tapOf s,
      w ∉ (compileMany Es start).tapOf s' := by
  induction Es generalizing start with
  | nil => intro w hw; exact nomatch hw
  | cons E rest ih =>
    intro w hw hw'
    have h1 := compile_le (E.inst start 0).1 (start + E.taps.length)
    rw [many_cons_tapOf] at hw hw'
    rcases List.mem_append.mp hw with hm | hm <;>
      rcases List.mem_append.mp hw' with hm' | hm'
    · obtain ⟨j, hj, hsrc, rfl⟩ := mem_srcTaps.mp hm
      obtain ⟨j', hj', hsrc', heq⟩ := mem_srcTaps.mp hm'
      have hjj : j = j' := by omega
      subst hjj
      exact hne (hsrc.symm.trans hsrc')
    · obtain ⟨h3, h4⟩ := srcTaps_bounds hm
      obtain ⟨h5, h6⟩ := many_tapOf_bounds _ _ s' w hm'
      omega
    · obtain ⟨h3, h4⟩ := srcTaps_bounds hm'
      obtain ⟨h5, h6⟩ := many_tapOf_bounds _ _ s w hm
      omega
    · exact ih _ w hm hm'

theorem many_tapOf_empty (Es : List PolyExpr) (start : ℕ) {bound : ℕ}
    (hE : ∀ E ∈ Es, ∀ s ∈ E.taps, s < bound) {s : ℕ} (hs : bound ≤ s) :
    (compileMany Es start).tapOf s = [] := by
  induction Es generalizing start with
  | nil => rfl
  | cons E rest ih =>
    rw [many_cons_tapOf]
    have hsrc : srcTaps E start s = [] := by
      by_contra hne
      obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨j, hj, hsj, -⟩ := mem_srcTaps.mp hw
      have := hE E List.mem_cons_self (E.taps[j]'hj) (List.getElem_mem hj)
      omega
    rw [hsrc, List.nil_append]
    exact ih _ (fun E' hE' => hE E' (List.mem_cons_of_mem _ hE'))

theorem many_tapOf_not_produced (Es : List PolyExpr) (start : ℕ) (s : ℕ) :
    ∀ w ∈ (compileMany Es start).tapOf s,
      w ∉ producedW (compileMany Es start).apps := by
  induction Es generalizing start with
  | nil => intro w hw; exact nomatch hw
  | cons E rest ih =>
    intro w hw hmem
    have h1 := compile_le (E.inst start 0).1 (start + E.taps.length)
    rw [many_cons_tapOf] at hw
    rw [many_cons_apps, producedW_append] at hmem
    rcases List.mem_append.mp hw with hm | hm <;>
      rcases List.mem_append.mp hmem with hp | hp
    · obtain ⟨h3, h4⟩ := srcTaps_bounds hm
      obtain ⟨h5, h6⟩ := compile_produced_bounds _ _ w hp
      omega
    · obtain ⟨h3, h4⟩ := srcTaps_bounds hm
      obtain ⟨h5, h6⟩ := many_produced_bounds _ _ w hp
      omega
    · obtain ⟨h3, h4⟩ := many_tapOf_bounds _ _ s w hm
      obtain ⟨h5, h6⟩ := compile_produced_bounds _ _ w hp
      omega
    · exact ih _ w hm hp

/-- Every tap wire of a station list is combed by its own source. -/
theorem many_taps_mem_tapOf (E : PolyExpr) (rest : List PolyExpr)
    (start : ℕ) {w : ℕ} (hw : w ∈ (E.inst start 0).1.taps) :
    ∃ s : ℕ, (∃ hj : w - start < E.taps.length,
      E.taps[w - start]'hj = s) ∧
      w ∈ (compileMany (E :: rest) start).tapOf s := by
  rw [inst_taps] at hw
  obtain ⟨hlo, hhi⟩ := SeamFacts.mem_range'_bounds hw
  have hj : w - start < E.taps.length := by omega
  refine ⟨E.taps[w - start]'hj, ⟨hj, rfl⟩, ?_⟩
  rw [many_cons_tapOf]
  refine List.mem_append_left _ (mem_srcTaps.mpr ⟨w - start, hj, rfl, ?_⟩)
  omega

/-! ### The semantic interface of a station list -/

theorem many_tc {wt : ℕ → Option TensorType} (Es : List PolyExpr)
    (start : ℕ)
    (hagr : ∀ w τ, (compileMany Es start).ty w = some τ →
      wt w = some τ) :
    ∀ a ∈ (compileMany Es start).apps, a.TypeConsistent wt := by
  induction Es generalizing start with
  | nil => intro a ha; exact nomatch ha
  | cons E rest ih =>
    intro a ha
    rw [many_cons_apps] at ha
    rcases List.mem_append.mp ha with ha' | ha'
    · refine compile_tc _ _
        (fun w τ h => hagr w τ (many_ty_station E rest start h)) ?_ a ha'
      intro w hw
      exact hagr w _ (many_ty_tap E rest start
        ⟨inst_taps_lower E start w hw, inst_taps_below E start w hw⟩)
    · exact ih _ (fun w τ h => hagr w τ (many_ty_rest E rest start h)) a ha'

theorem many_reads {H : Hypernet} (σ : H.Valuation) (Es : List PolyExpr)
    (start : ℕ) (vals : ℕ → ℚ)
    (hagr : ∀ w τ, (compileMany Es start).ty w = some τ →
      H.wireType w = some τ)
    (htaps : ∀ s : ℕ, ∀ w ∈ (compileMany Es start).tapOf s,
      σ.entryFlat w 0 = some (.fin (vals s)))
    (hsem : ∀ a ∈ (compileMany Es start).apps, a.SemOk σ) :
    ∀ i : ℕ, (hi : i < Es.length) →
      σ.entryFlat ((compileMany Es start).outs[i]'(by
        rw [many_outs_length]; exact hi)) 0
        = some (.fin ((Es[i]'hi).evalE vals)) := by
  induction Es generalizing start with
  | nil => intro i hi; exact absurd hi (by simp)
  | cons E rest ih =>
    intro i hi
    match i with
    | 0 =>
      show σ.entryFlat ((E.inst start 0).1.compile
        (start + E.taps.length)).out 0 = some (.fin (E.evalE vals))
      have htyt : ∀ w ∈ (E.inst start 0).1.taps,
          H.wireType w = some ⟨[], Dtype.Q⟩ := by
        intro w hw
        exact hagr w _ (many_ty_tap E rest start
          ⟨inst_taps_lower E start w hw, inst_taps_below E start w hw⟩)
      have htapsSt : ∀ w ∈ (E.inst start 0).1.taps,
          σ.entryFlat w 0 = some (.fin (stEnv E start vals w)) := by
        intro w hw
        obtain ⟨s, ⟨hj, hsrc⟩, hmem⟩ := many_taps_mem_tapOf E rest start hw
        have hread := htaps s w hmem
        have hlo := inst_taps_lower E start w hw
        have hval : stEnv E start vals w = vals s := by
          unfold stEnv
          rw [dif_pos ⟨hlo, hj⟩, hsrc]
        rw [hval]
        exact hread
      have hsemSt : ∀ a ∈ ((E.inst start 0).1.compile
          (start + E.taps.length)).apps, a.SemOk σ := fun a ha =>
        hsem a (by rw [many_cons_apps]; exact List.mem_append_left _ ha)
      have hres := compile_reads σ (E.inst start 0).1
        (start + E.taps.length) (stEnv E start vals)
        (fun w τ h => hagr w τ (many_ty_station E rest start h))
        htyt htapsSt hsemSt
      have hev : (E.inst start 0).1.evalE (stEnv E start vals)
          = E.evalE vals := by
        refine inst_evalE E start (stEnv E start vals) vals 0 ?_
        intro j hj
        have := stEnv_at E start vals hj
        rw [show start + 0 + j = start + j by omega]
        exact this
      rw [← hev]
      exact hres
    | i + 1 =>
      have hi' : i < rest.length := by
        have := hi
        simp only [List.length_cons] at this
        omega
      have hres := ih ((E.inst start 0).1.compile
          (start + E.taps.length)).next
        (fun w τ h => hagr w τ (many_ty_rest E rest start h))
        (fun s w hw => htaps s w (by
          rw [many_cons_tapOf]
          exact List.mem_append_right _ hw))
        (fun a ha => hsem a (by
          rw [many_cons_apps]
          exact List.mem_append_right _ ha))
        i hi'
      exact hres

theorem many_semOk {H : Hypernet} (σ : H.Valuation) (Es : List PolyExpr)
    (start : ℕ) (vals : ℕ → ℚ)
    (hagr : ∀ w τ, (compileMany Es start).ty w = some τ →
      H.wireType w = some τ)
    (hmdl : ∀ w : ℕ, ((compileMany Es start).ty w).isSome = true →
      ∀ i : ℕ, σ.entryFlat w i =
        (((compileMany Es start).mdl vals w)[i]?).map ERat.fin) :
    ∀ a ∈ (compileMany Es start).apps, a.SemOk σ := by
  induction Es generalizing start with
  | nil => intro a ha; exact nomatch ha
  | cons E rest ih =>
    have htapread : ∀ w ∈ (E.inst start 0).1.taps,
        σ.entryFlat w 0 = some (.fin (stEnv E start vals w)) := by
      intro w hw
      have hlo := inst_taps_lower E start w hw
      have hhi := inst_taps_below E start w hw
      have hj : w - start < E.taps.length := by omega
      have hs : ((compileMany (E :: rest) start).ty w).isSome = true := by
        rw [many_ty_tap E rest start ⟨hlo, by omega⟩]
        rfl
      have hrd := hmdl w hs 0
      rw [many_mdl_tap E rest start vals ⟨hlo, hj⟩] at hrd
      have hval : stEnv E start vals w = vals (E.taps[w - start]'hj) := by
        unfold stEnv
        rw [dif_pos ⟨hlo, hj⟩]
      rw [hval]
      exact hrd
    intro a ha
    rw [many_cons_apps] at ha
    rcases List.mem_append.mp ha with ha' | ha'
    · refine compile_semOk σ (E.inst start 0).1 (start + E.taps.length)
        (stEnv E start vals)
        (fun w τ h => hagr w τ (many_ty_station E rest start h))
        (fun w hw => hagr w _ (many_ty_tap E rest start
          ⟨inst_taps_lower E start w hw, inst_taps_below E start w hw⟩))
        htapread ?_ a ha'
      intro w hs i
      have hcomp := hmdl w (by
        obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hs
        rw [many_ty_station E rest start hτ]; rfl) i
      rw [hcomp, many_mdl_station E rest start vals hs]
    · refine ih _ (fun w τ h => hagr w τ (many_ty_rest E rest start h))
        ?_ a ha'
      intro w hs i
      have hcomp := hmdl w (by
        obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hs
        rw [many_ty_rest E rest start hτ]; rfl) i
      rw [hcomp, many_mdl_rest E rest start vals hs]

#print axioms many_tc
#print axioms many_reads
#print axioms many_semOk


/-! ### Model well-formedness: lengths, dtypes, and output entries -/

theorem compile_mdl_wf (e : PolyExpr) (base : ℕ) (env : ℕ → ℚ) {w : ℕ}
    {τ : TensorType} (h : (e.compile base).ty w = some τ) :
    τ.dtype = Dtype.Q ∧
      ((e.compile base).mdl env w).length = τ.shape.totalSize := by
  induction e generalizing base with
  | tap w' => exact nomatch h
  | qconst q =>
    have hd : w = base := by
      by_contra hne
      rw [compile_qconst_ty, if_neg hne] at h
      exact nomatch h
    subst hd
    rw [compile_qconst_ty, if_pos rfl] at h
    obtain rfl : (⟨[], Dtype.Q⟩ : TensorType) = τ := Option.some.inj h
    rw [compile_qconst_mdl, if_pos rfl]
    exact ⟨rfl, rfl⟩
  | add e₁ e₂ ih₁ ih₂ =>
    rw [compile_add_ty] at h
    rw [compile_add_mdl]
    by_cases h1 : w = (e₂.compile (e₁.compile base).next).next
    · rw [if_pos h1] at h
      obtain rfl : (⟨[2], Dtype.Q⟩ : TensorType) = τ := Option.some.inj h
      rw [if_pos h1]
      exact ⟨rfl, rfl⟩
    · rw [if_neg h1] at h
      rw [if_neg h1]
      by_cases h2 : w = (e₂.compile (e₁.compile base).next).next + 1
      · rw [if_pos h2] at h
        obtain rfl : (⟨[], Dtype.Q⟩ : TensorType) = τ := Option.some.inj h
        rw [if_pos h2]
        exact ⟨rfl, rfl⟩
      · rw [if_neg h2] at h
        rw [if_neg h2]
        rcases mergeWt_cases h with h' | h'
        · rw [if_pos (by rw [h']; rfl)]
          exact ih₁ base h'
        · have hnone : (e₁.compile base).ty w = none := by
            obtain ⟨hd1, hd2⟩ := compile_ty_domain _ _ h'
            have := compile_le e₁ base
            exact compile_ty_none e₁ base (Or.inr (by omega))
          rw [if_neg (by rw [hnone]; simp)]
          exact ih₂ (e₁.compile base).next h'
  | mul e₁ e₂ ih₁ ih₂ =>
    rw [compile_mul_ty] at h
    rw [compile_mul_mdl]
    by_cases h1 : w = (e₂.compile (e₁.compile base).next).next
    · rw [if_pos h1] at h
      obtain rfl : (⟨[], Dtype.Q⟩ : TensorType) = τ := Option.some.inj h
      rw [if_pos h1]
      exact ⟨rfl, rfl⟩
    · rw [if_neg h1] at h
      rw [if_neg h1]
      rcases mergeWt_cases h with h' | h'
      · rw [if_pos (by rw [h']; rfl)]
        exact ih₁ base h'
      · have hnone : (e₁.compile base).ty w = none := by
          obtain ⟨hd1, hd2⟩ := compile_ty_domain _ _ h'
          have := compile_le e₁ base
          exact compile_ty_none e₁ base (Or.inr (by omega))
        rw [if_neg (by rw [hnone]; simp)]
        exact ih₂ (e₁.compile base).next h'

theorem many_mdl_wf (Es : List PolyExpr) (start : ℕ) (vals : ℕ → ℚ)
    {w : ℕ} {τ : TensorType}
    (h : (compileMany Es start).ty w = some τ) :
    τ.dtype = Dtype.Q ∧
      ((compileMany Es start).mdl vals w).length = τ.shape.totalSize := by
  induction Es generalizing start with
  | nil => exact nomatch h
  | cons E rest ih =>
    rw [many_cons_ty] at h
    by_cases h1 : start ≤ w ∧ w < start + E.taps.length
    · rw [if_pos h1] at h
      obtain rfl : (⟨[], Dtype.Q⟩ : TensorType) = τ := Option.some.inj h
      rw [many_mdl_tap E rest start vals ⟨h1.1, by omega⟩]
      exact ⟨rfl, rfl⟩
    · rw [if_neg h1] at h
      rcases mergeWt_cases h with h' | h'
      · rw [many_mdl_station E rest start vals (by rw [h']; rfl)]
        exact compile_mdl_wf _ _ _ h'
      · rw [many_mdl_rest E rest start vals (by rw [h']; rfl)]
        exact ih _ h'

/-! ### Output typing and output model entries -/

theorem compile_mdl_out_qconst (q : ℚ) (b : ℕ) (env : ℕ → ℚ) :
    ((qconst q).compile b).mdl env ((qconst q).compile b).out
      = [(qconst q).evalE env] := by
  rw [show ((qconst q).compile b).out = b from rfl, compile_qconst_mdl,
    if_pos rfl]
  rfl

theorem compile_mdl_out_add (e₁ e₂ : PolyExpr) (b : ℕ) (env : ℕ → ℚ) :
    ((add e₁ e₂).compile b).mdl env ((add e₁ e₂).compile b).out
      = [(add e₁ e₂).evalE env] := by
  rw [compile_add_out, compile_add_mdl, if_neg (by omega), if_pos rfl]
  rfl

theorem compile_mdl_out_mul (e₁ e₂ : PolyExpr) (b : ℕ) (env : ℕ → ℚ) :
    ((mul e₁ e₂).compile b).mdl env ((mul e₁ e₂).compile b).out
      = [(mul e₁ e₂).evalE env] := by
  rw [compile_mul_out, compile_mul_mdl, if_pos rfl]
  rfl

/-- Station outputs are typed scalar rationals in the composite. -/
theorem many_ty_out (Es : List PolyExpr) (start : ℕ) :
    ∀ o ∈ (compileMany Es start).outs,
      (compileMany Es start).ty o = some ⟨[], Dtype.Q⟩ := by
  induction Es generalizing start with
  | nil => intro o ho; exact nomatch ho
  | cons E rest ih =>
    intro o ho
    rw [many_cons_outs] at ho
    rcases List.mem_cons.mp ho with ho' | ho'
    · subst ho'
      rcases compile_out (E.inst start 0).1 (start + E.taps.length)
          with hm | ⟨hty, -, -⟩
      · exact many_ty_tap E rest start
          ⟨inst_taps_lower E start _ hm, inst_taps_below E start _ hm⟩
      · exact many_ty_station E rest start hty
    · exact many_ty_rest E rest start (ih _ o ho')

/-- The model's entry at a station output is the expression value. -/
theorem many_mdl_out (Es : List PolyExpr) (start : ℕ) (vals : ℕ → ℚ) :
    ∀ i : ℕ, (hi : i < Es.length) →
      (compileMany Es start).mdl vals
        ((compileMany Es start).outs[i]'(by
          rw [many_outs_length]; exact hi))
        = [(Es[i]'hi).evalE vals] := by
  induction Es generalizing start with
  | nil => intro i hi; exact absurd hi (by simp)
  | cons E rest ih =>
    intro i hi
    match i with
    | 0 =>
      show (compileMany (E :: rest) start).mdl vals
        ((E.inst start 0).1.compile (start + E.taps.length)).out
        = [E.evalE vals]
      have hev : ((E.inst start 0).1).evalE (stEnv E start vals)
          = E.evalE vals := by
        refine inst_evalE E start _ vals 0 ?_
        intro j hj
        rw [show start + 0 + j = start + j by omega]
        exact stEnv_at E start vals hj
      match E with
      | tap s =>
        show (compileMany (tap s :: rest) start).mdl vals (start + 0)
          = [vals s]
        rw [many_mdl_tap (tap s) rest start vals
          ⟨by omega, by simp [taps]⟩]
        simp only [taps, List.getElem_singleton]
      | qconst q =>
        rw [many_mdl_station (qconst q) rest start vals (by
          rw [show (((qconst q).inst start 0).1.compile
              (start + (qconst q).taps.length)).ty
              (((qconst q).inst start 0).1.compile
                (start + (qconst q).taps.length)).out
            = some ⟨[], Dtype.Q⟩ from by
              rw [show (((qconst q).inst start 0).1.compile
                (start + (qconst q).taps.length)).out
                = start + (qconst q).taps.length from rfl,
                show ((qconst q).inst start 0).1 = qconst q from rfl,
                compile_qconst_ty, if_pos rfl]]
          rfl)]
        exact compile_mdl_out_qconst q _ _
      | add e₁ e₂ =>
        rw [many_mdl_station (add e₁ e₂) rest start vals (by
          rw [show ((add e₁ e₂).inst start 0).1
            = add (e₁.inst start 0).1
                (e₂.inst start (e₁.inst start 0).2).1 from rfl,
            compile_add_out, compile_add_ty_out]
          rfl)]
        rw [show ((add e₁ e₂).inst start 0).1
          = add (e₁.inst start 0).1
              (e₂.inst start (e₁.inst start 0).2).1 from rfl] at hev ⊢
        rw [compile_mdl_out_add, hev]
      | mul e₁ e₂ =>
        rw [many_mdl_station (mul e₁ e₂) rest start vals (by
          rw [show ((mul e₁ e₂).inst start 0).1
            = mul (e₁.inst start 0).1
                (e₂.inst start (e₁.inst start 0).2).1 from rfl,
            compile_mul_out, compile_mul_ty_out]
          rfl)]
        rw [show ((mul e₁ e₂).inst start 0).1
          = mul (e₁.inst start 0).1
              (e₂.inst start (e₁.inst start 0).2).1 from rfl] at hev ⊢
        rw [compile_mdl_out_mul, hev]
    | i + 1 =>
      have hi' : i < rest.length := by
        have := hi
        simp only [List.length_cons] at this
        omega
      have hoo : (compileMany (E :: rest) start).outs[i + 1]'(by
          rw [many_outs_length]; exact hi)
          = (compileMany rest
              ((E.inst start 0).1.compile
                (start + E.taps.length)).next).outs[i]'(by
            rw [many_outs_length]; exact hi') := rfl
      rw [hoo]
      have hmem : (compileMany rest ((E.inst start 0).1.compile
          (start + E.taps.length)).next).outs[i]'(by
            rw [many_outs_length]; exact hi')
          ∈ (compileMany rest ((E.inst start 0).1.compile
            (start + E.taps.length)).next).outs :=
        List.getElem_mem _
      have htyo := many_ty_out rest
        ((E.inst start 0).1.compile (start + E.taps.length)).next _ hmem
      rw [many_mdl_rest E rest start vals (by rw [htyo]; rfl)]
      exact ih _ i hi'

#print axioms compile_mdl_wf
#print axioms many_mdl_wf
#print axioms many_ty_out
#print axioms many_mdl_out

/-- Tap wires are typed scalar rationals in the composite. -/
theorem many_ty_tapOf (Es : List PolyExpr) (start : ℕ) (s : ℕ) :
    ∀ w ∈ (compileMany Es start).tapOf s,
      (compileMany Es start).ty w = some ⟨[], Dtype.Q⟩ := by
  induction Es generalizing start with
  | nil => intro w hw; exact nomatch hw
  | cons E rest ih =>
    intro w hw
    rw [many_cons_tapOf] at hw
    rcases List.mem_append.mp hw with hm | hm
    · obtain ⟨h1, h2⟩ := srcTaps_bounds hm
      exact many_ty_tap E rest start ⟨h1, h2⟩
    · exact many_ty_rest E rest start (ih _ w hm)

/-- Station outputs are pairwise distinct. -/
theorem many_outs_nodup (Es : List PolyExpr) (start : ℕ) :
    (compileMany Es start).outs.Nodup := by
  induction Es generalizing start with
  | nil => exact List.nodup_nil
  | cons E rest ih =>
    have h1 := compile_le (E.inst start 0).1 (start + E.taps.length)
    rw [many_cons_outs]
    refine List.nodup_cons.mpr ⟨?_, ih _⟩
    intro hmem
    obtain ⟨h2, h3⟩ := many_outs_bounds rest
      ((E.inst start 0).1.compile (start + E.taps.length)).next _ hmem
    rcases compile_out_cases (E.inst start 0).1
        (start + E.taps.length) with hm | ⟨h4, h5⟩
    · have hlo := inst_taps_lower E start _ hm
      have hhi := inst_taps_below E start _ hm
      omega
    · omega

/-- The model reads a source's value at each of its tap wires. -/
theorem many_mdl_tapOf (Es : List PolyExpr) (start : ℕ) (vals : ℕ → ℚ)
    (s : ℕ) : ∀ w ∈ (compileMany Es start).tapOf s,
      (compileMany Es start).mdl vals w = [vals s] := by
  induction Es generalizing start with
  | nil => intro w hw; exact nomatch hw
  | cons E rest ih =>
    intro w hw
    rw [many_cons_tapOf] at hw
    rcases List.mem_append.mp hw with hm | hm
    · obtain ⟨j, hj, hsrc, rfl⟩ := mem_srcTaps.mp hm
      rw [many_mdl_tap E rest start vals ⟨by omega, by
        rw [show start + j - start = j by omega]; exact hj⟩]
      simp only [Nat.add_sub_cancel_left]
      rw [hsrc]
    · rw [many_mdl_rest E rest start vals (by
        rw [many_ty_tapOf rest _ s w hm]; rfl)]
      exact ih _ w hm

end PolyExpr

end PPLC
