import Mathlib
import Qtsl.Plate.TPlate

/-!
# Plates: reference evaluator of the deterministic fragment

A reference denotational semantics for plated hypernets *at an
assignment* σ — the instance family `σ ↦ eval`, as one Lean
object. Deliberately simple where simplicity is equivariance-invisible:

* tensors are **untyped total functions** `TensorV := List Nat → ℚ`;
  every box body reads coordinates through `getD`, so all computed
  values are insensitive to junk beyond their rank by construction;
* entries live in ℚ (the core `TensorValue` carries `ERat`; overflow
  is not modeled) and rounding is pointwise post-composition with the
  core `Kind.roundQ` (float accumulation order is not modeled — the
  core's own `spFact` is likewise silent off the exact fragment);
* `cell` is **opaque** (outputs `none`): boundary nondeterminism is
  owned by proof obligations in the core language, and this evaluator
  covers the deterministic fragment (the design's acid test is
  `cell`-free);
* a missing input makes the outputs `none`.

The evaluator consults the symbolic wire typing for *layout* only
(`broadcast` source shape, `reshape` source shape) — shapes are part of
the graph data, exactly as in the core serialization.
-/

namespace PPLC
namespace Plate

/-- Untyped index: a list of coordinates. -/
abbrev Idx := List Nat

/-- Untyped tensor value: a total function on indices. Meaningful
content lives on the box of the wire's (instantiated) shape; all
evaluator-computed values are junk-insensitive via `getD` reads. -/
abbrev TensorV := Idx → Rat

/-- The zero tensor. -/
def zeroT : TensorV := fun _ => 0

/-- Environments: partial assignments of values to wires. -/
abbrev Env := Wire → Option TensorV

def Env.set (env : Env) (w : Wire) (v : Option TensorV) : Env :=
  fun w' => if w' = w then v else env w'

@[simp] theorem Env.set_same (env : Env) (w : Wire) (v : Option TensorV) :
    env.set w v w = v := by simp [Env.set]

@[simp] theorem Env.set_other (env : Env) {w w' : Wire}
    (h : w' ≠ w) (v : Option TensorV) : env.set w v w' = env w' := by
  simp [Env.set, h]

/-- The canonical rank-`r` restriction of an index (pad/truncate to
exactly `r` coordinates, `getD`-style). -/
def normalizeIdx (r : Nat) (idx : Idx) : Idx :=
  List.ofFn (fun a : Fin r => idx.getD a.val 0)

@[simp] theorem normalizeIdx_length (r : Nat) (idx : Idx) :
    (normalizeIdx r idx).length = r := by
  simp [normalizeIdx]

theorem normalizeIdx_getD (r : Nat) (idx : Idx) (a : Nat) :
    (normalizeIdx r idx).getD a 0
      = if a < r then idx.getD a 0 else 0 := by
  by_cases h : a < r
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp [normalizeIdx, h]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt h)]
    simp [h]

theorem normalizeIdx_eq_self {r : Nat} {idx : Idx}
    (h : idx.length = r) : normalizeIdx r idx = idx := by
  apply List.ext_getElem (by simpa using h.symm)
  intro a h1 h2
  simp only [normalizeIdx, List.getElem_ofFn]
  exact List.getD_eq_getElem idx 0 h2

theorem normalizeIdx_idem (r : Nat) (idx : Idx) :
    normalizeIdx r (normalizeIdx r idx) = normalizeIdx r idx :=
  normalizeIdx_eq_self (normalizeIdx_length r idx)

/-- Row-major flatten of an index against a literal shape — reading the
index through its canonical rank-`length s` restriction, so
junk-insensitivity holds by construction. -/
def flattenIdx (s : Shape) (idx : Idx) : Nat :=
  ((normalizeIdx s.length idx).zip s).foldl
    (fun acc p => acc * p.2 + p.1) 0

theorem flattenIdx_normalize (s : Shape) (idx : Idx) :
    flattenIdx s (normalizeIdx s.length idx) = flattenIdx s idx := by
  unfold flattenIdx
  rw [normalizeIdx_idem]

/-- Row-major unflatten against a literal shape. -/
def unflattenIdx : Shape → Nat → Idx
  | [], _ => []
  | d :: rest, n =>
      (n / Shape.totalSize rest) % d :: unflattenIdx rest (n % Shape.totalSize rest)

@[simp] theorem unflattenIdx_length (s : Shape) (n : Nat) :
    (unflattenIdx s n).length = s.length := by
  induction s generalizing n with
  | nil => rfl
  | cons d rest ih => simp [unflattenIdx, ih]

/-- The literal tensor of a core `const`, read row-major; entries
outside the value list (or non-finite `ERat` entries) read 0. Any total
interpretation works here: equivariance at `const` is carried by the
*typing* refusal (all-literal output shape), not by the entries. -/
def constV (ty : TensorType) (c : TensorValue ty) : TensorV :=
  fun idx =>
    match c.val[flattenIdx ty.shape idx]? with
    | some e =>
        match e.val with
        | .fin q => q
        | _ => 0
    | none => 0

theorem constV_normalize (ty : TensorType) (c : TensorValue ty) (idx : Idx) :
    constV ty c (normalizeIdx ty.shape.length idx) = constV ty c idx := by
  unfold constV
  rw [flattenIdx_normalize]

/-- Exact-ℚ einsum semantics of a symbolic contraction pattern at σ:
sum over all assignments of the contraction indices (each ranging over
its instantiated extent), guarded by agreement with the queried output
coordinates; each input read at its bound coordinates. -/
def contractV (σ : Nat → Nat) {ir : List Nat} {orank : Nat}
    (pat : SContractPattern ir orank) (vals : List TensorV) : TensorV :=
  fun idx =>
    ∑ ν ∈ Fintype.piFinset
        (fun j : Fin pat.nIndices => Finset.range ((pat.indexExtent j).inst σ)),
      if ∀ a : Fin orank, ν (pat.outputBinding a) = idx.getD a.val 0 then
        ∏ i : Fin ir.length,
          (vals.getD i.val zeroT)
            (List.ofFn (fun a : Fin (ir.get i) => ν (pat.inputBinding i a)))
      else 0

/-- Trailing-axis broadcast projection: target index to source index,
directed by the *symbolic* source shape (literal-1 slots pin to
coordinate 0; all others pass the aligned target coordinate). -/
def broadcastProj (src dst : SShape) (idx : Idx) : Idx :=
  List.ofFn (fun a : Fin src.length =>
    if src.get a = SExtent.lit 1 then 0
    else idx.getD (a.val + (dst.length - src.length)) 0)

def broadcastV (src dst : SShape) (v : TensorV) : TensorV :=
  fun idx => v (broadcastProj src dst idx)

/-- One evaluation step. -/
def evalApp (σ : Nat → Nat) (swt : Wire → Option STensorType)
    (env : Env) : SPrimApp → Env
  | .const ty c out => env.set out (some (constV ty c))
  | .contract δ r ins out _ir _orank pat =>
      match ins.mapM env with
      | some vals =>
          env.set out
            (some (fun idx => δ.kind.roundQ r (contractV σ pat vals idx)))
      | none => env.set out none
  | .cast _δf δt r _shape i o =>
      match env i with
      | some v => env.set o (some (fun idx => δt.kind.roundQ r (v idx)))
      | none => env.set o none
  | .cell _schema _i outs => outs.foldl (fun e o => e.set o none) env
  | .reshape ns i o =>
      match env i, swt i with
      | some v, some τ =>
          env.set o
            (some (fun idx => v (unflattenIdx (τ.shape.inst σ) (flattenIdx ns idx))))
      | _, _ => env.set o none
  | .broadcast ts i o =>
      match env i, swt i with
      | some v, some τ => env.set o (some (broadcastV τ.shape ts v))
      | _, _ => env.set o none
  | .copy _k i outs =>
      match env i with
      | some v => outs.foldl (fun e o => e.set o (some v)) env
      | none => outs.foldl (fun e o => e.set o none) env
  | .delete _i => env
  | .swap i1 i2 o1 o2 => (env.set o1 (env i2)).set o2 (env i1)
  | .stack _k _shape ins out =>
      match ins.mapM env with
      | some vals =>
          env.set out
            (some (fun idx => (vals.getD (idx.getD 0 0) zeroT) (idx.drop 1)))
      | none => env.set out none

/-- The reference evaluator: fold the applications over an initial
environment (free wires = the interface). -/
def evalNet (σ : Nat → Nat) (swt : Wire → Option STensorType)
    (apps : List SPrimApp) (env₀ : Env) : Env :=
  apps.foldl (evalApp σ swt) env₀

@[simp] theorem evalNet_nil (σ : Nat → Nat) (swt : Wire → Option STensorType)
    (env₀ : Env) : evalNet σ swt [] env₀ = env₀ := rfl

theorem evalNet_cons (σ : Nat → Nat) (swt : Wire → Option STensorType)
    (a : SPrimApp) (apps : List SPrimApp) (env₀ : Env) :
    evalNet σ swt (a :: apps) env₀ = evalNet σ swt apps (evalApp σ swt env₀ a) :=
  rfl

/-- The empty environment (closed nets). -/
def emptyEnv : Env := fun _ => none

/-- The rank-`r` observable content of a tensor: its restriction to
canonical rank-`r` queries. Two tensors with the same observable agree
everywhere a rank-`r` wire is ever consulted. -/
def TensorV.obs (r : Nat) (t : TensorV) : TensorV :=
  fun idx => t (normalizeIdx r idx)

end Plate
end PPLC
