import Qtsl.Plate.TNat

/-!
# Plates: T-DESC — descent to the multiset quotient

**T-DESC**: outputs carrying no plate axis are invariant,
hence descend to the multiset quotient — they are functions of an SDCPN
**marking**, and the total denotation of one finite syntax object is a
function on `∐ₙ Symⁿ(B)`: the ω-semialgebraic bag space, countable
piecing *expressed*.

Mechanized against the current common-ambient bag pattern: mathlib's
`Multiset Token` — the quotient of `List Token` by `List.Perm` — *is*
`∐ₙ Symⁿ(Token)` (multisets of every finite size, sectors indexed by
`Multiset.card`), so `bagDenot` below is literally one function on the
bag space, all counts at once, produced from one finite plated syntax
object. Configuration mechanized: single plate (`.pvar 0`), one
designated plated input wire (`X : ⟨[ι, d], ℚ⟩` — the token-colour
family as the token-embedding matrix, David "davidad" Dalrymple's
identification taken literally), plate-free context and output.

**Upgrade seam** (declared in the preregistration): a planned
enlargement of the mechanized ω-semialgebraic category to a free
countable coproduct completion would host exactly this space; once it
is in place, `bagDenot` should be re-exhibited as a morphism of that
category. Nothing in this module's statements moves — the target type
`Multiset Token → Option TensorV` is the underlying function either
way.

Values are compared at their rank-`r` observable (`TensorV.obs`): the
tensor's content on canonical queries — the raw closures may differ on
junk queries beyond the wire's rank, which was never data
(preregistration item O2).
-/

namespace PPLC
namespace Plate

/-- A token: one row of the token-colour family (untyped, like
`TensorV`; the colour dimension `d` lives in the wire type). -/
abbrev Token := Nat → Rat

def zeroTok : Token := fun _ => 0

/-- The token-colour family as a rank-2 tensor value: `X[t, e] = l_t(e)`
(`getD`-read: junk-insensitive, tokens beyond the count read 0). -/
def tokensV (l : List Token) : TensorV :=
  fun idx => l.getD (idx.getD 0 0) zeroTok (idx.getD 1 0)

/-- The environment of a marking: the designated plated input wire
carries the token family; everything else is the (plate-free) context. -/
def envOfTokens (X : Wire) (l : List Token) (ctx : Env) : Env :=
  ctx.set X (some (tokensV l))

/-! ## From `List.Perm` to a concrete `PermOn` -/

/-- Extraction (preregistration item O3, hand-rolled): a permutation of lists yields a
concrete `PermOn` transporting `getD`-reads. The off-range identity of
`PermOn` makes the equation hold at *every* index, junk included. -/
theorem exists_permOn_of_perm {l l' : List Token} (h : l.Perm l') :
    ∃ p : PermOn l.length, ∀ t : Nat,
      l'.getD t zeroTok = l.getD (p.f t) zeroTok := by
  induction h with
  | nil => exact ⟨PermOn.refl 0, fun t => rfl⟩
  | @cons x l₁ l₂ hperm ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨p.shift, ?_⟩
      intro t
      cases t with
      | zero => rfl
      | succ u =>
          show (x :: l₂).getD (u + 1) zeroTok
            = (x :: l₁).getD (p.shift.f (u + 1)) zeroTok
          rw [show p.shift.f (u + 1) = p.f u + 1 from rfl]
          simpa [List.getD_cons_succ] using hp u
  | swap x y l₀ =>
      refine ⟨PermOn.transposition01
        (by simp only [List.length_cons]; omega), ?_⟩
      intro t
      show (x :: y :: l₀).getD t zeroTok
        = (y :: x :: l₀).getD (PermOn.swapFn t) zeroTok
      match t with
      | 0 => rfl
      | 1 => rfl
      | (u+2) =>
          have hsw : PermOn.swapFn (u + 2) = u + 2 := by
            unfold PermOn.swapFn
            split
            · omega
            · split
              · omega
              · rfl
          rw [hsw]
          simp
  | @trans l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ =>
      obtain ⟨p₁, hp₁⟩ := ih₁
      obtain ⟨p₂, hp₂⟩ := ih₂
      have hlen : l₂.length = l₁.length := h₁.length_eq.symm
      refine ⟨p₁.comp (p₂.cast hlen), ?_⟩
      intro t
      rw [show (p₁.comp (p₂.cast hlen)).f t
          = p₁.f ((p₂.cast hlen).f t) from rfl, PermOn.cast_f]
      rw [hp₂ t, hp₁ ((p₂.f t))]

/-- The token family transforms as the plate action predicts. -/
theorem tokensV_reindex {l l' : List Token} {d : Nat}
    (p : PermOn l.length)
    (hget : ∀ t : Nat, l'.getD t zeroTok = l.getD (p.f t) zeroTok) :
    tokensV l'
      = TensorV.reindex [SExtent.pvar 0, SExtent.lit d] 0 p.f (tokensV l) := by
  funext idx
  show tokensV l' idx
    = tokensV l (permIdx [SExtent.pvar 0, SExtent.lit d] 0 p.f idx)
  rw [permIdx_cons, permIdx_cons]
  rw [if_pos rfl, if_neg (by intro hcon; exact SExtent.noConfusion hcon)]
  unfold tokensV
  have hdrop : (idx.drop 1).getD 0 0 = idx.getD 1 0 := by
    cases idx with
    | nil => simp [List.getD]
    | cons a t => simp [List.getD]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [hdrop, hget (idx.getD 0 0)]

/-- Sufficient condition for a context to be a fixed point of the
action: every populated wire is plate-free-typed and carries
rank-normalized content. -/
theorem envReindex_fixed_of_ctx {swt : Wire → Option STensorType}
    {ctx : Env} (v : Nat)
    (hctx : ∀ w t, ctx w = some t →
      ∃ τ, swt w = some τ ∧ τ.shape.noVar v ∧
        TensorV.obs τ.shape.length t = t) :
    ∀ g : Nat → Nat, envReindex swt v g ctx = ctx := by
  intro g
  funext w
  cases hw : ctx w with
  | none => simp [envReindex, hw]
  | some t =>
      obtain ⟨τ, hτ, hfree, hobs⟩ := hctx w t hw
      simp only [envReindex, hw, Option.map_some, Option.some.injEq]
      rw [wshape_eq hτ, TensorV.reindex_noVar hfree]
      exact hobs

/-- The empty context qualifies (closed-but-for-tokens nets). -/
theorem envReindex_fixed_empty (swt : Wire → Option STensorType)
    (v : Nat) (g : Nat → Nat) :
    envReindex swt v g emptyEnv = emptyEnv := by
  funext w
  simp [envReindex, emptyEnv]

/-- **T-DESC, invariance form (S13)**: permuting the token list does not
change the observable content of any plate-free-typed wire. The
permutation enters through T-NAT; the tokens are the only plated
input. -/
theorem T_DESC (P : PlatedHypernet) (X w : Wire) {d : Nat}
    {δX : Dtype} {τw : STensorType}
    (hX : P.wireTypeS X = some ⟨[.pvar 0, .lit d], δX⟩)
    (hw : P.wireTypeS w = some τw)
    (hfree : τw.shape.noVar 0)
    (ctx : Env)
    (hctx : ∀ g : Nat → Nat, envReindex P.wireTypeS 0 g ctx = ctx)
    {l l' : List Token} (hperm : l.Perm l')
    (σ : Nat → Nat) (hσ : σ 0 = l.length) :
    ((evalNet σ P.wireTypeS P.applications (envOfTokens X l' ctx)) w).map
        (TensorV.obs τw.shape.length)
      = ((evalNet σ P.wireTypeS P.applications (envOfTokens X l ctx)) w).map
          (TensorV.obs τw.shape.length) := by
  obtain ⟨p₀, hget⟩ := exists_permOn_of_perm hperm
  -- q.g = p₀.f : the reindexer that turns the l-environment into the
  -- l'-environment.
  set q : PermOn (σ 0) := (p₀.cast hσ.symm).symm with hq
  have hqg : q.g = p₀.f := by
    rw [hq]
    simp
  have henv : envOfTokens X l' ctx
      = envReindex P.wireTypeS 0 q.g (envOfTokens X l ctx) := by
    unfold envOfTokens
    rw [envReindex_set, hctx q.g]
    congr 1
    simp only [Option.map_some, Option.some.injEq]
    rw [wshape_eq hX, hqg]
    exact tokensV_reindex p₀ hget
  rw [henv]
  exact obs_invariant σ P 0 q (envOfTokens X l ctx) hw hfree

/-- **The bag denotation (S13)**: one function on the bag space
`Multiset Token = ∐ₙ Symⁿ(Token)`, produced from one finite plated
syntax object — countable piecing, expressed. The count assignment is
read off the marking itself (`σ = card`). -/
def bagDenot (P : PlatedHypernet) (X w : Wire) {d : Nat}
    {δX : Dtype} {τw : STensorType}
    (hX : P.wireTypeS X = some ⟨[.pvar 0, .lit d], δX⟩)
    (hw : P.wireTypeS w = some τw)
    (hfree : τw.shape.noVar 0)
    (ctx : Env)
    (hctx : ∀ g : Nat → Nat, envReindex P.wireTypeS 0 g ctx = ctx)
    (m : Multiset Token) : Option TensorV :=
  Quot.liftOn m
    (fun l =>
      ((evalNet (fun _ => l.length) P.wireTypeS P.applications
        (envOfTokens X l ctx)) w).map (TensorV.obs τw.shape.length))
    (by
      intro l l' hperm
      have hlen : l'.length = l.length := hperm.length_eq.symm
      have := T_DESC P X w hX hw hfree ctx hctx hperm
        (fun _ => l.length) rfl
      simpa [hlen] using this.symm)

/-- The computation rule: on a represented marking, the bag denotation
is the evaluator run at the marking's count. -/
@[simp] theorem bagDenot_coe (P : PlatedHypernet) (X w : Wire) {d : Nat}
    {δX : Dtype} {τw : STensorType}
    (hX : P.wireTypeS X = some ⟨[.pvar 0, .lit d], δX⟩)
    (hw : P.wireTypeS w = some τw)
    (hfree : τw.shape.noVar 0)
    (ctx : Env)
    (hctx : ∀ g : Nat → Nat, envReindex P.wireTypeS 0 g ctx = ctx)
    (l : List Token) :
    bagDenot P X w hX hw hfree ctx hctx (↑l)
      = ((evalNet (fun _ => l.length) P.wireTypeS P.applications
          (envOfTokens X l ctx)) w).map (TensorV.obs τw.shape.length) := rfl

end Plate
end PPLC
