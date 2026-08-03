/-!
# Exact extended rationals (computational core)

`ERat` is a fresh inductive (rather than `WithBot (WithTop ℚ)`) so that
no ambient arithmetic instances exist: arithmetic on ℝ ∪ {±∞} is
partial (`∞ − ∞` and `0·∞` are the soundness-error cases), and the only
arithmetic offered is the explicitly partial `add?/mul?/sum?/prod?`,
with `none` as the error verdict. Zero-import module; the semantic
bridge to `EReal` lives in `Qtsl.ERat`.
-/

namespace PPLC

inductive ERat where
  | negInf
  | fin (q : Rat)
  | posInf
  deriving DecidableEq, Repr

namespace ERat

def isFin : ERat → Prop
  | fin _ => True
  | _     => False

instance : DecidablePred isFin := fun e => by
  cases e <;> simp only [isFin] <;> infer_instance

def toQ? : ERat → Option Rat
  | fin q => some q
  | _     => none

protected def le : ERat → ERat → Prop
  | negInf, _      => True
  | _,      posInf => True
  | fin a,  fin b  => a ≤ b
  | posInf, _      => False
  | _,      negInf => False

instance : LE ERat := ⟨ERat.le⟩

instance : DecidableRel (α := ERat) (· ≤ ·) := fun a b => by
  cases a <;> cases b <;> simp only [LE.le, ERat.le] <;> infer_instance

@[simp] theorem le_fin_fin {a b : Rat} : (fin a ≤ fin b) ↔ a ≤ b := Iff.rfl
@[simp] theorem negInf_le (e : ERat) : negInf ≤ e := by cases e <;> trivial
@[simp] theorem le_posInf (e : ERat) : e ≤ posInf := by cases e <;> trivial

def add? : ERat → ERat → Option ERat
  | posInf, negInf => none
  | negInf, posInf => none
  | negInf, _      => some negInf
  | _,      negInf => some negInf
  | posInf, _      => some posInf
  | _,      posInf => some posInf
  | fin a,  fin b  => some (fin (a + b))

def mul? : ERat → ERat → Option ERat
  | fin a, fin b => some (fin (a * b))
  | fin a, posInf => if a > 0 then some posInf else if a < 0 then some negInf else none
  | posInf, fin a => if a > 0 then some posInf else if a < 0 then some negInf else none
  | fin a, negInf => if a > 0 then some negInf else if a < 0 then some posInf else none
  | negInf, fin a => if a > 0 then some negInf else if a < 0 then some posInf else none
  | posInf, posInf => some posInf
  | negInf, negInf => some posInf
  | posInf, negInf => some negInf
  | negInf, posInf => some negInf

def sum? (l : List ERat) : Option ERat := l.foldlM add? (fin 0)

def prod? (l : List ERat) : Option ERat := l.foldlM mul? (fin 1)

@[simp] theorem sum?_nil : sum? [] = some (fin 0) := rfl
@[simp] theorem prod?_nil : prod? [] = some (fin 1) := rfl

end ERat

end PPLC
